/************************************************************************
 * Copyright 2012; Planning, Agents and Intelligent Systems Group,
 * Department of Informatics,
 * King's College, London, UK
 * http://www.inf.kcl.ac.uk/staff/andrew/planning/
 *
 * Amanda Coles, Andrew Coles - OPTIC
 * Amanda Coles, Andrew Coles, Maria Fox, Derek Long - POPF
 * Stephen Cresswell - PDDL Parser
 *
 * This file is part of OPTIC.
 *
 * OPTIC is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * OPTIC is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with OPTIC.  If not, see <http://www.gnu.org/licenses/>.
 *
 ************************************************************************/

#include "RPGBuilder.h"
#include "globals.h"
#include "temporalanalysis.h"
#include "numericanalysis.h"
#include "FFSolver.h"

#include <cmath>
#include <vector>
#include <iomanip>
#include <sstream>
#include <fstream>

#include "typecheck.h"
#include "TIM.h"
#include "FuncAnalysis.h"
#include "temporalconstraints.h"

#include "lpscheduler.h"

#ifdef STOCHASTICDURATIONS
#include "StochasticDurations.h"
#endif

#include "PreferenceHandler.h"

#include "colours.h"

using namespace TIM;
using namespace Inst;
using namespace VAL;

using std::cerr;
using std::endl;
using std::vector;
using std::ostringstream;
using std::ofstream;

namespace Planner
{

    


class BuildingPayload;

/** @brief Determine the earliest point at which a precondition would be satisifed in the partial order.
 *
 * This is a helper function for the heuristic evaluation.  It takes a numeric precondition,
 * and a vector containing the earliest point at which each task variable can be referred to,
 * and from these deduces the next earliest point at which the precondition could conceivably
 * be considered to be satisfied (i.e. after all the most recent effects).
 *
 * @param p  The numeric precondition
 * @param earliestNumericPOTimes  The earliest point at which each variable can be referred to,
 *                                according to the partial order so far.
 *
 * @return  The earliest time point that the precondition can be considered to be true, i.e.
 *          the earliest point at which each action with this precondition would be true, were it
 *          added to the partial order.
 */
EpsilonResolutionTimestamp earliestPointForNumericPrecondition(const RPGBuilder::RPGNumericPrecondition & p,
                                                               const vector<EpsilonResolutionTimestamp> * earliestNumericPOTimes) {
    static const int varCount = RPGBuilder::getPNECount();
    EpsilonResolutionTimestamp TS = EpsilonResolutionTimestamp::zero();

    for (int pass = 0; pass < 2; ++pass) {
        int var = (pass ? p.RHSVariable : p.LHSVariable);
        if (var == -1) continue;
        if (var >= 2 * varCount) {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(var);

            for (int i = 0; i < currAV.size; ++i) {
                int varTwo = currAV.fluents[i];
                if (varTwo >= varCount) varTwo -= varCount;
                if ((*earliestNumericPOTimes)[varTwo] > TS) {
                    TS = (*earliestNumericPOTimes)[varTwo];
                }
            }
        } else {
            if (var >= varCount) var -= varCount;
            if ((*earliestNumericPOTimes)[var] > TS) {
                TS = (*earliestNumericPOTimes)[var];
            }
        }
    }

    return TS;
}

EpsilonResolutionTimestamp earliestPointForNumericPrecondition(const RPGBuilder::RPGNumericPrecondition & p,
                                                               const MinimalState & theState,
                                                               const vector<double> & stepTimes) {
    static const int varCount = RPGBuilder::getPNECount();
    static int stepID;
    static EpsilonResolutionTimestamp actTS(EpsilonResolutionTimestamp::undefined());
    EpsilonResolutionTimestamp TS = EpsilonResolutionTimestamp::zero();

    for (int pass = 0; pass < 2; ++pass) {
        int var = (pass ? p.RHSVariable : p.LHSVariable);
        if (var == -1) continue;
        if (var >= 2 * varCount) {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(var);

            for (int i = 0; i < currAV.size; ++i) {
                int varTwo = currAV.fluents[i];
                if (varTwo >= varCount) varTwo -= varCount;
                stepID = theState.temporalConstraints->lastStepToTouchPNE[varTwo].lastInstantaneousEffect;
                if (stepID != -1) {
                    actTS = EpsilonResolutionTimestamp(stepTimes[stepID], true);  
                    if (TS < actTS) {
                        TS = actTS;
                    }
                }
            }
        } else {
            if (var >= varCount) var -= varCount;
            stepID = theState.temporalConstraints->lastStepToTouchPNE[var].lastInstantaneousEffect;
            if (stepID != -1) {
                actTS = EpsilonResolutionTimestamp(stepTimes[stepID], true);  
                if (TS < actTS) {
                    TS = actTS;
                }
            }
        }
    }

    return TS;
}


/** @brief A struct representing the intermediate goals to achieve at a layer during RPG solution extraction.
 *
 *  TRPG solution extraction introduces four kinds of intermediate goals:
 *  - Propositions to be achieved
 *  - Numeric values to be achieved (v >= c);
 *  - Action starts that must be added (as their ends were chosen later)
 *  - Action ends that must be added (the ends of actions that have been started in the plan, but not yet finished)
 *
 *  Each of these is weighted by which TIL-induced deadline it is relevant to, to support the possibility
 *  of reordering the successors so that actions relevant to sooner deadlines are considered first.
 */
struct RPGRegress {

    /** @brief The propositional subgoals to achieve in this layer */
    map<int, EpsilonResolutionTimestamp> propositionalGoals;
    
    /** @brief The negative propositional subgoals to achieve in this layer */
    map<int, EpsilonResolutionTimestamp> negativePropositionalGoals;
    
    /** @brief The numeric subgoals to achieve in this layer
     *
     *  Each numeric variable maps to a pair of doubles:
     *  - the first denotes the value it must be greater than or equal to
     *  - the second denotes the TIL deadline weight of this
     */
    map<int, pair<double,EpsilonResolutionTimestamp> > numericValueGreaterThan;
    
    /** @brief Request a numeric precondition in this layer.
     *
     *  If there is already a request for the specified variable to take a given variable, the maximum
     *  threshold out of that given and that already recorded is kept, and the earliest TIL deadline out
     *  of that given and that recorded is kept.
     *
     *  @param variable   The variable on which to request a precondition
     *  @param threshold  The value this variable must (at least) take
     *  @param weight     The TIL deadline weight of this request
     */
    void requestNumericThreshold(const int & variable, const double & threshold, const EpsilonResolutionTimestamp & weight) {
        const pair<map<int, pair<double,EpsilonResolutionTimestamp> >::iterator, bool> insPair = numericValueGreaterThan.insert(make_pair(variable, make_pair(threshold, weight)));
        
        if (!insPair.second) {
            if (insPair.first->second.first < threshold) {
                insPair.first->second.first = threshold;
            }
            if (insPair.first->second.second < weight) {
                insPair.first->second.second = weight;
            }
        }
        
    }
    

    //map<int, double> numericGoals;
    
    /** @brief Action starts that must be included in this layer.
     *
     *  Each action index maps to a pair:
     *  - the first entry denotes how many times the action must be started in this layer;
     *  - the second denotes the TIL deadline weight.
     */
    map<int, pair<int, EpsilonResolutionTimestamp> > actionStarts;
    
    /** @brief Action starts that must be included in this layer.
     *
     *  Each action index maps to a pair:
     *  - the first entry denotes how many times the action must be ended in this layer;
     *  - the second denotes the TIL deadline weight.
     */    
    map<int, pair<int, EpsilonResolutionTimestamp> > actionEnds;

};



#ifdef NDEBUG
typedef map<EpsilonResolutionTimestamp, RPGRegress> RPGRegressionMap;
#else

class RPGRegressionMap {
    
protected:
    map<EpsilonResolutionTimestamp, RPGRegress> internal;
    EpsilonResolutionTimestamp forbidLaterThan;
public:
    
    RPGRegressionMap()
    : forbidLaterThan(EpsilonResolutionTimestamp::infinite()) {        
    }
    
    typedef map<EpsilonResolutionTimestamp, RPGRegress>::iterator iterator;
    typedef map<EpsilonResolutionTimestamp, RPGRegress>::const_iterator const_iterator;
    
    typedef map<EpsilonResolutionTimestamp, RPGRegress>::reverse_iterator reverse_iterator;
    typedef map<EpsilonResolutionTimestamp, RPGRegress>::const_reverse_iterator const_reverse_iterator;
    
    RPGRegress & operator[](const EpsilonResolutionTimestamp & t) {
        #ifndef NDEBUG
        if (t >= forbidLaterThan) {
            cerr << "Fatal internal error: in solution extraction, satisfying a numeric precondition at layer " << t << ", after previously satisfied one at layer " << forbidLaterThan << " - need to work strictly backwards\n";
            assert(t < forbidLaterThan);
        }
        #endif
        return internal[t];
    }
    
    bool empty() const {
        return internal.empty();
    }
    
    reverse_iterator rbegin() {
        return internal.rbegin();
    }
    
    reverse_iterator rend() {
        return internal.rend();
    }
    
    iterator end() {
        return internal.end();
    }
    
    void erase(const EpsilonResolutionTimestamp & t) {
        forbidLaterThan = t;
        internal.erase(t);
    }
};



#endif

/** @brief A struct recording how many times an action is to be applied in a given layer.
 *
 *  This is used during solution extraction, when adding actions to support numeric
 *  preconditions: <code>FluentLayers::satisfyNumericPreconditionsAtLayer()</code> returns
 *  a list of these, indicating the actions it chose.  These then must be added to the relaxed
 *  plan and, in the case of end actions, the corresponding starts noted for insertion at an
 *  earlier layer.
 */
struct SupportingAction {
  
    int actID;
    Planner::time_spec ts;
    int howManyTimes;
    EpsilonResolutionTimestamp tilR;
    
   
    SupportingAction(const int & actionID, const Planner::time_spec & timeSpecifier,
                     const int & applyThisManyTimes, const EpsilonResolutionTimestamp & tilRelevance)
        : actID(actionID), ts(timeSpecifier),
          howManyTimes(applyThisManyTimes), tilR(tilRelevance) {
    }
};

void rpprintState(MinimalState & e)
{

    e.printState(cout);

};

/** @brief A struct used to record details about the actions capable of having each effect.
 * 
 *  This is used to update the variables' values when the values of the variables referred to by
 *  an effect have changed.
 */
struct ActionAndHowManyTimes {
    /** @brief The ID of the action. */
    int actID;
    
    /** @brief Whether the effect occurs at the start of the action or the end. */
    Planner::time_spec ts;
    
    /** @brief At most how many times the action can be applied (<code>INT_MAX</code> for infinite). */
    int howManyTimes;    

    /** @brief The minimum duration of the action. */
    double minDur;
    
    /** @brief The maximum duration of the action. */
    double maxDur;
    
    /** @brief The layer at which its gradients effect finish. */
    EpsilonResolutionTimestamp gradientsFinishAt;
    
    /** @brief If this action starts its gradients. 
     *
     *  This is set to <code>true</code> in one of two cases:
     *  - The first time this action has appeared in the RPG, in which case all its gradient
     *    effects need to be started.
     *  - When the action reappears in the RPG (after an assignment has been made to a variable
     *    upon which it has a gradient effect), and then iff the actions gradient had expired
     *    earlier in the RPG (and hence needs re-starting again).
     */    
    bool gradientNeedsStarting;
    
    /** @brief If this action (a start action) is already in the plan. */
    bool alreadyInThePlan;
    
    ActionAndHowManyTimes(const int & act, const Planner::time_spec & timeSpec, const int & lim, const double & dmin, const double & dmax, const bool alreadyIn=false)
     : actID(act), ts(timeSpec), howManyTimes(lim), minDur(dmin), maxDur(dmax), gradientsFinishAt(EpsilonResolutionTimestamp::infinite()), gradientNeedsStarting(true), alreadyInThePlan(alreadyIn)
    {
        assert(howManyTimes > 0);
    }
    
    #ifndef NDEBUG
    ActionAndHowManyTimes(const ActionAndHowManyTimes & other)
        : actID(other.actID), ts(other.ts), howManyTimes(other.howManyTimes),
          minDur(other.minDur), maxDur(other.maxDur),
          gradientsFinishAt(other.gradientsFinishAt), gradientNeedsStarting(other.gradientNeedsStarting),
          alreadyInThePlan(other.alreadyInThePlan) {
        assert(howManyTimes);
    }
    
    ActionAndHowManyTimes & operator=(const ActionAndHowManyTimes & other) {
        actID = other.actID;
        ts = other.ts;
        howManyTimes = other.howManyTimes;
        minDur = other.minDur;
        maxDur = other.maxDur;
        gradientsFinishAt = other.gradientsFinishAt;
        gradientNeedsStarting = other.gradientNeedsStarting;
        alreadyInThePlan = other.alreadyInThePlan;
        assert(howManyTimes);
        return *this;
    }
    #endif
    
    bool operator<(const ActionAndHowManyTimes & other) const {
        
        if (!alreadyInThePlan && other.alreadyInThePlan) return true;
        if (alreadyInThePlan && !other.alreadyInThePlan) return false;
        
        if (actID < other.actID) return true;
        if (actID > other.actID) return false;
        
        if (ts < other.ts) return true;
        if (ts > other.ts) return false;
        
        return false;
    }
};

/** @brief A gradient effect of an action already in the plan */
struct DelayedGradientDescriptor : public ActionAndHowManyTimes {
   
    /** @brief Variable--Value pair for a gradient effect */
    pair<int,double> gradientEffect;
    
    DelayedGradientDescriptor(const int & act, const Planner::time_spec & timeSpec, const double & dmax, const pair<int,double> & effect)
        : ActionAndHowManyTimes(act, timeSpec, 1, dmax, dmax, true), gradientEffect(effect) {
    }
    
};


/** @brief Struct to represent a fact layer, during RPG expansion. */
struct FactLayerEntry {
    
    pair<set<int>, set<int> > * endOfJustApplied;
    
    set<int> startDelayedUntilNow;
    
    /** @brief Propositional facts, new to this fact layer.
     *
     *  Each <code>int</code> corresponds to the literal with the same index
     *  in <code>RPGBuilder::literals</code>.
     */
    list<int> first;
   
    /** @brief Propositional facts, with lower cost in this fact layer.
    *
    *  Each <code>int</code> corresponds to the literal with the same index
    *  in <code>RPGBuilder::literals</code>.
    */
    set<int> firstRepeated;
        
    /** @brief Negative propositional facts, new to this fact layer. */
    list<int> negativeLiterals;
    
    /** @brief Numeric preconditions, new to this fact layer.
     *
     *  Each <code>int</code> is an index into <code>RPGBuilder::getNumericPreTable()</code>.
     */
    list<int> second;
    
    /** @brief Facts added by Timed Initial Literals.
     *
     *   Each entry used to be a pair where:
     *   - the first <code>int</code> is the index of the TIL that adds it
     *   - the second <code>int</code> is the fact added, an index into <code>RPGBuilder::literals</code>.
     */
    list<int> TILs;
    
    /** @brief  Facts deleted by Timed Initial Literals.
     *
     *  Each <code>int</code> corresponds to the literal with the same index
     *  in <code>RPGBuilder::literals</code>.
     */
    list<int> negativeTILs;

    list<pair<int, int> > preferencePairedWithFactNowFreeToAdd;
    
    /** @brief Gradient effects that finish at this layer.
     *
     *  If an action is k-shot, then any gradient effects it has finish
     *  after it has been executed k-times in sequence.  This map records
     *  the decrease in gradient effects that occur at this point in the
     *  TRPG.  Each entry is a pair, where:
     *  - the first entry, an <code>int</code>, records the variable upon which the gradient is to change;
     *  - the second entry, a <code>double</code>, records the (cumulative) effect upon that variable that
     *    ceases at this layer.
     */
    map<int,double> gradientFinishes;
    
#ifdef POPF3ANALYSIS
    
    list<int> literalGoalsWeMustHaveByNow;
    list<int> numericGoalsWeMustHaveByNow;
    
    list<int> preferenceUnreachableIfNotSatisfiedByNow;
    
#endif

    
    //@{
    /** @brief Internal representation of abstract TIL timelines */
    list<int> abstractFactBecomesFalse;
    list<int> abstractFactBecomesTrue;
    //@}
    
    
    /** @brief  Default constructor - all the member variables are initialised to empty. */
    FactLayerEntry() : endOfJustApplied(0) {};
};

class FactLayerMap {
    
protected:
    map<EpsilonResolutionTimestamp, FactLayerEntry> internal;
public:
    
    FactLayerMap() {    
    }
    
    typedef map<EpsilonResolutionTimestamp, FactLayerEntry>::iterator iterator;
    typedef map<EpsilonResolutionTimestamp, FactLayerEntry>::const_iterator const_iterator;
    
    typedef map<EpsilonResolutionTimestamp, FactLayerEntry>::reverse_iterator reverse_iterator;
    typedef map<EpsilonResolutionTimestamp, FactLayerEntry>::const_reverse_iterator const_reverse_iterator;
    
    FactLayerEntry & operator[](const EpsilonResolutionTimestamp & t) {
        #ifndef NDEBUG
        if (t < EpsilonResolutionTimestamp::zero()) {
            cerr << "Fatal internal error: in expansion, adding a fact layer at time " << t << endl;
            assert(t >= EpsilonResolutionTimestamp::zero());
        }
        #endif
        if (Globals::globalVerbosity & 32) {
            cout << "Accessing layer " << t << endl;
        }
        return internal[t];
    }
    
    bool empty() const {
        return internal.empty();
    }
    
    reverse_iterator rbegin() {
        return internal.rbegin();
    }
    
    reverse_iterator rend() {
        return internal.rend();
    }

    iterator begin() {
        return internal.begin();
    }   
    
    const_iterator begin() const {
        return internal.begin();
    }   
    
    iterator end() {
        return internal.end();
    }
    
    const_iterator end() const {
        return internal.end();
    }
    
    void erase(const EpsilonResolutionTimestamp & t) {
        internal.erase(t);
    }
    
    void erase(const iterator & t) {
        internal.erase(t);
    }
    
    void write(ostream & o) const {
        
    }
};

ostream & operator<<(ostream & o, const FactLayerMap &  flm) {
    flm.write(o);
    return o;
}


/** @brief A class representing the fluent layers in the TRPG */
class FluentLayers {

public:
    
    /** @brief A record of the assignment effect giving the maximum value of a variable in a layer.
     *
     *  During graph expansion, if the maximum value of a variable was attained through 
     *  an assignment effect, the details of that assignment are stored in an object of
     *  this type to allow them to be recalled and used, if necessary, during solution
     *  extraction.
     */
    struct RecordedAssignment {
        
        /** @brief The snap-action with the assignment effect. */
        const ActionAndHowManyTimes * act;
        
        /** @brief The effect itself, an index into <code>RPGBuilder::getNumericEff()</code>. */
        int eff;
        
        /** @brief Whether the right-hand side of the effect should be maximised or minimised.
         *
         *  If this variable is set to <code>true</code>, the maximum fluent values from the preceding
         *  fact layer should be used when evaluating the value this effect assigns to
         *  the variable it effects.  If set to <code>false</code>, the minimum fluent values
         *  should be used.
         */
        bool maximiseEffect;
        
        /** @brief Default constructor - sets <code>eff=-1</code>. */
        RecordedAssignment()
            : act(0), eff(-1), maximiseEffect(true) {
        }
        
        /** @brief Construct an object to represent an assignment effect.
         *
         *  @param a  The action with the effect
         *  @param e  The effect itself, an index into <code>RPGBuilder::getNumericEff()</code>.
         *  @param m  Whether the effect should be maximised, or minimised.  @see maximiseEffect
         */
        RecordedAssignment(const ActionAndHowManyTimes * const a, const int & e, const bool & m)
            : act(a), eff(e), maximiseEffect(m) {
        }
    };
    
    /** @brief A single fluent layer in the TRPG. @see FluentLayers */
    class FluentLayerEntry {

    protected:
        
        /** @brief The number of PNEs defined in the problem, from <code>RPGBuilder::getPNECount()</code>. */
        static int pneCount;
        friend class FluentLayers;
        
        /** @brief The layer should only be used to dictate input values to effects.
         *
         * When building the TRPG, the fluent layer epsilon before a new action layer needs
         * to be defined, purely to be able to give inputs to the RHS of the effect expressions
         * of those actions.  In this case, we can skip initialising certain data structures,
         * as no new effects appear in this layer.
         *
         * - If this variable is set to <code>true</code>, then <code>assignmentEffectThatGaveThisValue</code>
         *   and <code>effectsThatIncreasedThisVariable</code> are not initialised.
         * - Otherwise, they are resized to contain one entry per variable.
         */
        bool onlyUseLayerForEffectMagnitudes;
        
        /** @brief The maximum fluent values in the current layer.
         *
         *  - Entries <code>[0..pneCount]</code> store the maximum value of each PNE
         *  - Entries <code>[pneCount..(pneCount-1)]</code> store the negation of the minimum value of each PNE
         *  - Entries from <code>2 * pneCount</code> onwards store the maximum values of artificial variables.
         *
         *  @see RPGBuilder::ArtificialVariable
         */
        vector<double> internalValues;
        
        /** @brief The maximum gradients acting on each fluent in the current layer. */
        vector<double> gradients;
        
        /** @brief The variables with non-zero entries in <code>gradients</code>. 
         *
         *  The keys of the maps denote variables with non-zero entries.  For artificial
         *  variables, the corresponding values denote how many of the variables upon
         *  which the AV depends have non-zero entries.
         */
        map<int,int> nonZeroGradients;
        
        /** @brief If the recorded value of a variable was due to an assignment effect, note this here.
          *
          * This vector is used during solution extraction: if a precondition became true based
          * on the variable values in this layer, then if it was by assignment, we only want to
          * apply one assignment effect, rather than one or more increase effects.  An entry
          * of -1 denotes that the indexed variable wasn't assigned to; otherwise, an entry
          * <code>i</code> denotes that <code>RPGBuilder::getNumericEff()[i]</code> was used.
          */         
        vector<RecordedAssignment*> assignmentEffectThatGaveThisValue;
        
        /** @brief The effects immediately prior to this layer that increased the value of each variable. */
        vector<set<int>*> effectsThatIncreasedThisVariable;
        
        list<set<int>* > setGC;
        list<RecordedAssignment*> assignmentGC;
        
        /** @brief The instantaneous effects available directly before this layer.
         *
         *  - The keys are indices into <code>RPGBuilder::getNumericEff()</code>
         *  - The value corresponding to each key lists the available actions with this effect.
         */
        map<int, list<const ActionAndHowManyTimes*> > instantaneousEffectsDirectlyBeforeThisLayer;
        
        /** @brief The integrated effects available directly before this layer.
         *
         *  The keys in the map are the variables upon which the integrated effects act, and are indices
         *  into <code>RPGBuilder::pnes</code>.  The corresponding maps consist of pairs, where:
         *  - the first entry, a <code>double</code>, corresponds to the magnitude of the effect
         *  - the second entry lists the actions with this effect.
         */
        map<int, map<double, list<const ActionAndHowManyTimes*> > > integratedEffectsDirectlyBeforeThisLayer;
        
        /** @brief The gradient effects available directly before this layer.
         *
         *  The keys in the map are the variables upon which the gradient effects act, and are indices
         *  into <code>RPGBuilder::pnes</code>.  The corresponding maps consist of pairs, where:
         *  - the first entry, a <code>double</code>, corresponds to the magnitude of the effect
         *  - the second entry lists the actions with this effect.
         */
        map<int, map<double, list<const ActionAndHowManyTimes*> > > gradientEffectsDirectlyBeforeThisLayer;

        /** @brief The instantaneous effects to revisit in the action layer prior to this fact layer.
         *         
         *  If an effect depends on a variable's value, then if that variable's value changes,
         *  the effect needs to be reconsidered, as new preconditions may becomes satisfied.
         *  Or, if an assignment effect changes the value of a variable, increase/decrease
         *  effects upon it then need to be re-applied, to give the new upper/lower bounds
         *  after that point.
         *
         *  The entries in this set record such effects that need to be reconsidered.  Each
         *  <code>int</code> is an index into <code>RPGBuilder::getNumericEff()</code>.
         */
        set<int> instaneousEffectsToRevisitAfterThisLayer;
        
        /** The variables upon which the integrated/gradient effects need to be reconsidered
         *  in the action layer prior to this layer.
         *
         *  If an assignment effect changes the value of a variable, increase/decrease
         *  effects upon it then need to be re-applied, to give the new upper/lower bounds
         *  after that point.  The entries in this set record variables on which assignment
         *  effects have added, leading to the variable bounds needing to be recalculated.         
         */
        set<int> integratedOrGradientEffectsToRevisitAfterThisLayer;
        
        /** @brief Protected constructor - only used for testing if a layer exists. */
        FluentLayerEntry() {  
            onlyUseLayerForEffectMagnitudes = true;
        }
        
        /** @brief Supply the details of a fluent layer.
         *
         *  If a new fluent layer needs to be created, this function is used to define
         *  the values within it, based on the previous fluent layer and the time
         *  that has elapsed since then.
         *
         *  @param f                 The previous fluent layer
         *  @param timeDifference    The amount of time elapsed since then
         *  @param doApplyGradients  If <code>true</code>, apply the consequences of the gradients active
         *                           between fact layer <code>f</code> and the one constructed.
         */
        void supplyDetails(const FluentLayerEntry & f, const EpsilonResolutionTimestamp & timeDifference, const bool & doApplyGradients, const bool & ignorableLayer) {
            internalValues = f.internalValues;
            gradients = f.gradients;
            
            if (ignorableLayer) {
                onlyUseLayerForEffectMagnitudes = true;
            } else {
                onlyUseLayerForEffectMagnitudes = false;
                assignmentEffectThatGaveThisValue.resize(internalValues.size(),0);
                effectsThatIncreasedThisVariable.resize(internalValues.size(),0);
            }
            
            if (timeDifference.isZero()) return;
            
            if (doApplyGradients) {
                applyGradients(timeDifference);
            }
        }
        
        /** @brief Called when the sum gradient acting on a (non-artificial) variable becomes zero.
         *
         *  If the gradient on a non-artificial variable becomes zero, the gradients of the AVs
         *  depending on it need to be checked to see if they now have zero gradients too, i.e.
         *  have no remaining non-zero components.
         *
         *  @param  var  The variable whose gradient has become zero
         */
        void gradientBecomesZeroOn(const int & var) {
            map<int,int>::iterator delItr = nonZeroGradients.find(var);
            assert(delItr != nonZeroGradients.end());
            nonZeroGradients.erase(delItr);
            
            const list<int> & deps = RPGBuilder::getVariableDependencies(var);
            
            list<int>::const_iterator depItr = deps.begin();
            const list<int>::const_iterator depEnd = deps.end();
            
            for (; depItr != depEnd; ++depItr) {
                delItr = nonZeroGradients.find(*depItr);
                
                if (!(--(delItr->second))) {
                    nonZeroGradients.erase(delItr);
                }
            }            
        }
        
        /** @brief Called when the sum gradient acting on a (non-artificial) variable becomes non-zero.
         *
         *  If the gradient on a non-artificial variable becomes non-zero, the gradients of the AVs
         *  depending on it need to be checked to see if they now have non-zero gradients too, i.e.
         *  if this is the first non-zero components.
         *
         *  @param  var  The variable whose gradient has become non-zero
         */                
        void gradientBecomesNonZeroOn(const int & var) {
            static pair<int,int> pairWithZero(0,0);
            pair<map<int,int>::iterator,bool> insPair = nonZeroGradients.insert(make_pair(var,1));
            
            assert(insPair.second);
            
            map<int,int>::iterator insItr = nonZeroGradients.end();
            
            const list<int> & deps = RPGBuilder::getVariableDependencies(var);
            
            list<int>::const_iterator depItr = deps.begin();
            const list<int>::const_iterator depEnd = deps.end();
            
            for (; depItr != depEnd; ++depItr) {
                pairWithZero.first = *depItr;
                insItr = nonZeroGradients.insert(insItr, pairWithZero);
                ++(insItr->second);
            }            
        }
        
                
        /** @brief Start a gradient effect on the given variable.
         *
         *  - If <code>val > 0</code>, then the gradient on the upper bound on <code>var</code> is increased.
         *  - If <code>val < 0</code>, then the gradient on the negative lower bound on <code>var</code> is increased.
         *
         *  In both cases, the index of the affected variable is added to the set <code>varChanged</code>, and
         *  the value of the affected variable is increased by epsilon times the gradient.
         */
        void startGradient(const int & var, const double & val, set<int> & varChanged) {
            if (val > 0) {
                double & alter = gradients[var];
                const bool previouslyZero = (fabs(alter) < 0.0000001);
                alter += val;
                varChanged.insert(var);
                if (fabs(alter) < 0.0000001) {
                    if (!previouslyZero) gradientBecomesZeroOn(var);
                } else {
                    if (previouslyZero) gradientBecomesNonZeroOn(var);
                }
            } else if (val < 0) {
                double & alter = gradients[var + pneCount];
                const bool previouslyZero = (fabs(alter) < 0.0000001);
                alter -= val;
                varChanged.insert(var + pneCount);
                if (fabs(alter) < 0.0000001) {
                    if (!previouslyZero) gradientBecomesZeroOn(var + pneCount);
                } else {
                    if (previouslyZero) gradientBecomesNonZeroOn(var + pneCount);
                }
            }
        }
        
    public:

        /** @brief Create a fluent layer, initialised with the given variable bounds. */
        FluentLayerEntry(const vector<double> & v)
            : internalValues(v), gradients(v.size(), 0.0) {        
            pneCount = RPGBuilder::getPNECount();
            onlyUseLayerForEffectMagnitudes = false;
        }
        
        /** @brief Create a fluent layer, offset with the given time from the fluent layer given. */
        FluentLayerEntry(const FluentLayerEntry & f, const EpsilonResolutionTimestamp & timeDifference, const bool & doApplyGradients, const bool & ignorableLayer) {
            supplyDetails(f,timeDifference, doApplyGradients, ignorableLayer);            
        }
        
        /** @brief Destructor - garbage-collects internal data. */
        ~FluentLayerEntry() {
            
            if (onlyUseLayerForEffectMagnitudes) {
                return;
            }
            
            list<set<int>* >::const_iterator sgcItr = setGC.begin();
            const list<set<int>* >::const_iterator sgcEnd = setGC.end();
            
            for (; sgcItr != sgcEnd; ++sgcItr) {
                delete *sgcItr;
            }
            
            
            list<RecordedAssignment*>::const_iterator agcItr = assignmentGC.begin();
            const list<RecordedAssignment*>::const_iterator agcEnd = assignmentGC.end();
            
            for (; agcItr != agcEnd; ++agcItr) {
                delete *agcItr;
            }
        }
        
        /** @brief Return a const reference to the variable values in this layer. */
        const vector<double> & values() const {
            return internalValues;        
        }
        
        /** @brief Return a const reference to the variable gradients in this layer. */
        const vector<double> & getGradients() const {
            return gradients;        
        }
        
        
        /** @brief Return a non-const reference to the variable values in this layer. */
        vector<double> & writeableValues() {
            return internalValues;
        }

        /** @brief Return <code>true</code> if this is not a dummy intermediate layer. */
        bool initialised() const {
            return (effectsThatIncreasedThisVariable.size() == internalValues.size());
        }

        /** @brief Apply the gradients recorded in this fluent layer to the variables.
         *
         *  After recording the snap-actions in the layer preceding a new fact
         *  layer, this function is used to update the variable values to reflect
         *  the gradient-induced change between the previous fact layer, and this
         *  one.
         *
         *  @param timeDifference  The length of time elapsed between the previous
         *                         fluent layer and this one.
         */
        void applyGradients(const EpsilonResolutionTimestamp & timeDifference) {
            const int size = internalValues.size();
            
            for (int v = 0; v < size; ++v) {
                internalValues[v] += gradients[v] * timeDifference.toDouble();
            }            
        }
        
        void keepAssignmentIfBetter(const ActionAndHowManyTimes* act, const int & effID, const bool & maxEffect, const int & var, const double & val, set<int> & varChanged) {
            if (val > internalValues[var]) {
                internalValues[var] = val;
                varChanged.insert(var);
                
                RecordedAssignment *& ra = assignmentEffectThatGaveThisValue[var];
                if (ra) {
                    ra->act = act;
                    ra->eff = effID;
                    ra->maximiseEffect = maxEffect;
                } else {                   
                    ra = new RecordedAssignment(act, effID, maxEffect);
                    assignmentGC.push_back(ra);
                }
                set<int> * const sa = effectsThatIncreasedThisVariable[var];
                if (sa) {
                    sa->clear();
                }
            }
            
            if (-val > internalValues[var + pneCount]) {
                internalValues[var + pneCount] = -val;
                varChanged.insert(var + pneCount);
                
                RecordedAssignment *& ra = assignmentEffectThatGaveThisValue[var + pneCount];
                if (ra) {
                    ra->act = act;
                    ra->eff = effID;
                    ra->maximiseEffect = maxEffect;
                } else {
                    ra = new RecordedAssignment(act, effID, maxEffect);
                    assignmentGC.push_back(ra);
                }
                set<int> * const sa = effectsThatIncreasedThisVariable[var + pneCount];
                if (sa) {
                    sa->clear();
                }
            }
        }
        
        void applyIncrease(const int & effID, const int & var, const double & minVal, const double & maxVal, const int & howManyTimes, set<int> & varChanged) {            
            if (minVal > 0 || maxVal > 0) {
                double val = maxVal;
                if (minVal > val) {
                    val = minVal;
                }
                if (internalValues[var] != DBL_MAX) {
                    if (val == DBL_MAX || howManyTimes == INT_MAX) {
                        internalValues[var] = DBL_MAX;
                    } else {
                        internalValues[var] += val * howManyTimes;
                    }
                    varChanged.insert(var);
                    
                    if (effID != -1) {
                        assert(var >= 0 && (size_t) var < effectsThatIncreasedThisVariable.size());
                        set<int> *& sa = effectsThatIncreasedThisVariable[var];
                        if (!sa) {
                            setGC.push_back(sa = new set<int>());
                        }
                        sa->insert(effID);
                    }
                }
            }
            
            if (minVal < 0 || maxVal < 0) {
                double val = minVal;
                if (maxVal < val) {
                    val = maxVal;
                }
                if (internalValues[var + pneCount] != DBL_MAX) {
                    if (val == -DBL_MAX || howManyTimes == INT_MAX) {
                        internalValues[var + pneCount] = DBL_MAX;
                    } else {
                        internalValues[var + pneCount] -= val * howManyTimes;
                    }
                    varChanged.insert(var + pneCount);
                    
                    if (effID != -1) {
                        set<int> *& sa = effectsThatIncreasedThisVariable[var + pneCount];
                        if (!sa) {
                            setGC.push_back(sa = new set<int>());
                        }
                        sa->insert(effID);
                    }
                }
            }
        }


        /** @brief Stop a gradient effect on the given variable.
         *
         *  The gradient on <code>var</code> is decreased by <code>val</code>.
         *
         *  @param var  The variable for which the gradient changes (either a positive or negative variable)
         *  @param val  The amount by which to decrease the active gradient.
         *
         */
        void stopGradient(const int & var, const double & val) {
            gradients[var] -= val;

        }
                
        /** @brief Recalculate the values of the artificial variables. */
        template <typename T>
        void recalculateAVs(T & itr, const T & itrEnd) {
            for (; itr != itrEnd; ++itr) {
                internalValues[*itr] = RPGBuilder::getArtificialVariable(*itr).evaluate(internalValues);
            }
        }

        /** @brief Recalculate the gradients  of the artificial variables. */
        template <typename T>
        void recalculateAVGradients(T & itr, const T & itrEnd) {
            for (; itr != itrEnd; ++itr) {
                gradients[*itr] = RPGBuilder::getArtificialVariable(*itr).evaluateGradient(gradients);
            }
        }

        
        void markEffectsToRevisit(const set<int> & toRevisit, const vector<double> & maxNeeded) {
            set<int>::const_iterator effItr = toRevisit.begin();
            const set<int>::const_iterator effEnd = toRevisit.end();
            
            for (; effItr != effEnd; ++effItr) {
                if (instaneousEffectsToRevisitAfterThisLayer.find(*effItr) != instaneousEffectsToRevisitAfterThisLayer.end()) continue;
                
                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
                if (maxNeeded[currEff.fluentIndex] > internalValues[currEff.fluentIndex]) {
                    instaneousEffectsToRevisitAfterThisLayer.insert(*effItr);
                    continue;
                }
                
                list<int> & dependencies = RPGBuilder::getVariableDependencies(currEff.fluentIndex);
                
                list<int>::const_iterator depItr = dependencies.begin();
                const list<int>::const_iterator depEnd = dependencies.end();
                
                for (; depItr != depEnd; ++depItr) {
                    if (maxNeeded[*depItr] > internalValues[*depItr]) {
                        instaneousEffectsToRevisitAfterThisLayer.insert(*effItr);
                        break;
                    }
                }
            }
        }
        
        void markIntegratedOrGradientEffectVariableToRevisit(const int & toRevisit, const vector<double> & maxNeeded) {
            if (integratedOrGradientEffectsToRevisitAfterThisLayer.find(toRevisit) != integratedOrGradientEffectsToRevisitAfterThisLayer.end()) return;
            
            if (maxNeeded[toRevisit] > internalValues[toRevisit]) {
                integratedOrGradientEffectsToRevisitAfterThisLayer.insert(toRevisit);
                return;
            }
            
            list<int> & dependencies = RPGBuilder::getVariableDependencies(toRevisit);
                
            list<int>::const_iterator depItr = dependencies.begin();
            const list<int>::const_iterator depEnd = dependencies.end();
            
            for (; depItr != depEnd; ++depItr) {
                if (maxNeeded[*depItr] > internalValues[*depItr]) {
                    integratedOrGradientEffectsToRevisitAfterThisLayer.insert(toRevisit);
                    return;
                }
            }
            
        }
        
        map<int, list<const ActionAndHowManyTimes*> > & getInstantaneousEffectsDirectlyBeforeThisLayer() {
            return instantaneousEffectsDirectlyBeforeThisLayer;
        }
        
        map<int, map<double, list<const ActionAndHowManyTimes*> > > & getIntegratedEffectsDirectlyBeforeThisLayer() {
            return integratedEffectsDirectlyBeforeThisLayer;
        }
        
        map<int, map<double, list<const ActionAndHowManyTimes*> > > & getGradientEffectsDirectlyBeforeThisLayer() {
            return gradientEffectsDirectlyBeforeThisLayer;
        }
                        
        
        const set<int> & getInstantaneousEffectsToRevisitAfterThisLayer() const {
            return instaneousEffectsToRevisitAfterThisLayer;
        }
        
        const set<int> & getIntegratedOrGradientEffectsToRevisitAfterThisLayer() const {
            return integratedOrGradientEffectsToRevisitAfterThisLayer;
        }
        
        
        
        /** @brief Get the assignment effect used to give this value of v. */
        const RecordedAssignment * assignmentAppliedToVariable(const int & v) const {
            if (onlyUseLayerForEffectMagnitudes) {
                return 0;
            }
            return assignmentEffectThatGaveThisValue[v];
        }
        
        const set<int> * getInstantaneousEffectsThatIncreasedVariable(const int & v) const {
            if (onlyUseLayerForEffectMagnitudes) {
                return 0;
            }
            return effectsThatIncreasedThisVariable[v];
        }
        
        double willBecomeSatisfiedAfterDelay(const RPGBuilder::RPGNumericPrecondition & currPre) const {
            
            static const bool debug = false;
            
            const double currV = internalValues[currPre.LHSVariable];
            const double currG = gradients[currPre.LHSVariable];
            
            if (currPre.op == VAL::E_GREATEQ) {
                if (currV >= currPre.RHSConstant) {
                    // is true right now
                    if (debug) {
                        cout << "Is true right now\n";
                    }
                    return 0.0;
                }
                if (currG == 0) {
                    if (debug) {
                        cout << "No gradient, cannot become true yet\n";
                    } 
                    // no gradient, cannot become true
                    return DBL_MAX;
                }
                if (debug) {
                    cout << "Current LHS value is " << currV << ", RHS is " << currPre.RHSConstant << ", so with a gradient of " << currG << " that will mean a delay of " << ((currPre.RHSConstant - currV) / currG) << endl;
                }
                return (((currPre.RHSConstant + 0.00001 - currV) / currG) + EPSILON);
                
            } else {
                if (currV > currPre.RHSConstant) {
                    if (debug) {
                        cout << "Is true right now\n";
                    }                    
                    // is true right now
                    return 0.0;
                }
                if (currG == 0) {
                    if (debug) {
                        cout << "No gradient, cannot become true yet\n";
                    }                                        
                    // no gradient, cannot become true
                    return DBL_MAX;
                }
                if (debug) {
                    cout << "Current LHS value is " << currV << ", RHS is " << currPre.RHSConstant << ", so with a gradient of " << currG << " that will mean a delay of " << ((currPre.RHSConstant - currV) / currG) + EPSILON << endl;
                }                                        
                                                    
                // as it's v > c, allow epsilon extra to make sure it definitely exceeds c
                return (((currPre.RHSConstant + 0.00001) - currV) / currG) + EPSILON;
            }
        }
    };
    
protected:

    /** @brief Fluent layers, to be garbage collected upon destruction. */
    list<FluentLayerEntry*> layerGC;
        
    /** @brief The type of the map used to hold the variable and gradient values at each point in time across the RPG. */
    typedef map<EpsilonResolutionTimestamp, FluentLayerEntry*> LayerMap;
    
    /** @brief The values of the numeric variables, and the active gradients, at each point in time across the RPG. */
    LayerMap layers;
    
    inline FluentLayerEntry * newFluentLayer() {
        static FluentLayerEntry * newLayer;
        newLayer = new FluentLayerEntry();
        layerGC.push_back(newLayer);
        return newLayer;
    }
    
    inline FluentLayerEntry * newFluentLayer(const vector<double> & values) {
        static FluentLayerEntry * newLayer;
        newLayer = new FluentLayerEntry(values);
        layerGC.push_back(newLayer);
        return newLayer;
    }
    
    inline FluentLayerEntry * newFluentLayerEntry(const FluentLayerEntry * const previousFL, const EpsilonResolutionTimestamp & timeDifference, const bool & applyGradients, const bool & ignorableLayer) {
        static FluentLayerEntry * newLayer;
        newLayer = new FluentLayerEntry(*previousFL, timeDifference, applyGradients, ignorableLayer);
        layerGC.push_back(newLayer);
        return newLayer;
    }
    
    /** @brief Return the fluent layer the desired time after the seed layer given.
     *
     *  If this is the first request for such a layer, the details of the supplied 
     *  layer are copied across, updating for any gradient effects.  Otherwise,
     *  the previous layer created for that time is used.
     *
     *  @param startAt         An iterator to <code>FluentLayers::layers</code>, to seed layer creation
     *  @param timeDifference  The temporal separation between the seed layer and the new one
     *
     *  @return An iterator to <code>FluentLayers::layers</code>, pointing to the new layer.
     */
    LayerMap::iterator addLayer(LayerMap::const_iterator & startAt, const EpsilonResolutionTimestamp & timeDifference) {
        
        EpsilonResolutionTimestamp newTime = startAt->first;
        newTime += timeDifference;
        
        const pair<LayerMap::iterator,bool> insPair = layers.insert(make_pair(newTime, newFluentLayer()));
        
        if (insPair.second) {
            insPair.first->second->supplyDetails(*(startAt->second), timeDifference, false, false);
        }
        
        if (debug) {
            if (insPair.first->second->initialised()) {
                cout << COLOUR_yellow << "Layer at " << newTime << " is initialised\n";
            } else {
                cout << COLOUR_light_magenta << "Layer at " << newTime << " is not initialised\n";
            }
        }
        
        return insPair.first;
    }
    
    /** @brief Record the effects of an action's execution.
     *
     *  When adding an action to the relaxed plan, it may have numeric effects other than those intended.
     *  This function records all an action's effects, so that if it turns out a suitable effect has
     *  already been applied when considering whether another precondition is satisfied, we don't
     *  add redundant actions to the relaxed plan.
     *
     *  @param  toUse              The action to use;
     *  @param  howManyTimes       How many times it was added to the relaxed plan;
     *  @param  effectInputValues  The fluent layer immediately prior to the action being applied,
     *                             giving the variable values to take as the inputs to its effects.
     */
    void recordSideEffects(const ActionAndHowManyTimes * const toUse, const int & howManyTimes,
                           const vector<double> & effectInputValues) {
        
        /*const list<int> & numericEffs = (toUse->ts == Planner::E_AT_START ? RPGBuilder::getStartEffNumerics()[toUse->actID]
                                                                      : RPGBuilder::getEndEffNumerics()[toUse->actID]);
        list<int>::const_iterator effItr = numericEffs.begin();
        const list<int>::const_iterator effEnd = numericEffs.end();
        
        for (; effItr != effEnd; ++effItr) {
            const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
            
            const double maxRHS = currEff.evaluate(effectInputValues, toUse->minDur, toUse->maxDur);
            const double minRHS = currEff.evaluateMin(effectInputValues, toUse->minDur, toUse->maxDur);
                        
            for (int pass = 0; pass < 2; ++pass) {
                const int v = currEff.fluentIndex + (pass ? FluentLayerEntry::pneCount : 0);
                
                for (int rhsC = 0; rhsC < 2; ++rhsC) {
                    
                    double rhs = (rhsC ? maxRHS : minRHS);                                             
                
                    if (pass) {
                        if (rhs >= 0) continue;
                        rhs = -rhs;
                    } else {
                        if (rhs <= 0) continue;
                    }
                    
                    const pair<map<int,double>::iterator,bool> insPair = alreadyAchieved.insert(make_pair(v,rhs));
                    
                    if (!insPair.second) {
                        if (currEff.isAssignment) {
                            if (rhs > insPair.first->second) {
                                insPair.first->second = rhs;
                            }
                        } else {
                            if (insPair.first->second != DBL_MAX) {
                                if (rhs == DBL_MAX || howManyTimes == INT_MAX) {
                                    insPair.first->second = DBL_MAX;
                                } else {
                                    insPair.first->second += rhs * howManyTimes;
                                }
                            }
                        }
                    }
                }
            }            
        }*/
    }
    
    /**
     *  If an effect depends on a variable's value, we need to revisit that effect
     *  if that value changes.  Thus, for each variable, we store a set of which 
     *  effect IDs depend upon it.
     */
    vector<set<int> > revisitInstantaneousEffectIfVariableValueChanges;
    
    /**
    *  If a variable is assigned a new, better, value, we need to then reapply all suitable
    *  increase effects.  Thus, for each variable, we store a set of which
    *  increase effect IDs act upon it.
    */
    vector<set<int> > revisitInstantaneousEffectIfVariableIsAssignedTo;
    
    /** For garbage collection */
    list<ActionAndHowManyTimes> gc;
    
    /** @brief For each effect ID, the actions in the planning graph that have ever had that effect.
     */
    vector<list<ActionAndHowManyTimes*> > actionsThatHaveHadThisEffect;
    
    /** @brief For each variable ID, the actions in the planning graph that have ever had an integrated effect of the magnitude given.
     */
    vector<map<double, list<ActionAndHowManyTimes*> > > actionsThatHaveHadThisIntegratedEffect;
    
    /** @brief For each variable ID, the actions in the planning graph that have ever had a gradient effect of the magnitude given.
    */
    vector<map<double, list<ActionAndHowManyTimes*> > > actionsThatHaveHadThisGradientEffect;
    
    /** @brief The set of facts true at the current layer, due to gradients having been started in the past.
     *
     *  Each entry is an index into <code>RPGBuilder::getNumericPreTable()</code>.
     */
    set<int> gradientsLeadToTheseFactsNowBeingTrue;
    
    LayerMap::const_iterator effectInputs;
    LayerMap::iterator effectsAffectThisLayer;
    LayerMap::iterator layerWithEffectsToBeRevisited;
    /** @brief For convenience - for each effect ID, the actions with that effect in the most recent action layer. */
    map<int, list<const ActionAndHowManyTimes*> > * mostRecentInstantaneousEffects;
    map<int, map<double, list<const ActionAndHowManyTimes*> > > * mostRecentIntegratedEffects;
    map<int, map<double, list<const ActionAndHowManyTimes*> > > * mostRecentGradientEffects;
    
    /** @brief The time at which preconditions become true, due to active gradients.
     *
     *  - the keys of the map are time-stamps
     *  - the set of associated values contains the preconditions that become true at that time
     *    (each being an index into <code>RPGBuilder::getNumericPreTable()</code>).
     */
    map<EpsilonResolutionTimestamp, set<int> > preconditionsBecomingTrueAtTime;
    
    
    /** @brief Typedef used to record precondition satisfaction forecasts.
    *
    *  For each precondition in <code>RPGBuilder::getNumericPreTable()</code>, objects of this type
    *  are used to record details about the layer at which it is currently set to become true due to active
    *  gradients.  Each entry is a pair:
    *   - an iterator to the relevant layer in <code>preconditionsBecomingTrueAtTime</code>, or
    *     <code>preconditionsBecomingTrueAtTime.end()</code> if it is already true, or not
    *     yet forecast to become true;
    *   - an iterator into the set of preconditions within that iterator (undefined if
    *     the precondition is not yet forecast to become true).
    */
    typedef pair<map<EpsilonResolutionTimestamp, set<int> >::iterator, set<int>::iterator> PreconditionToSatisfactionLayerPair;
    
    /** @brief The current layer at which a precondition has been forecast to become true.*/        
    vector<PreconditionToSatisfactionLayerPair> layerAtWhichPreconditionBecomesTrue;
    
    bool nowExtracting;
    LayerMap::iterator currentSubgoalLayer;

    // /** @brief Record effects of actions as they are added to the plan. */
    // map<int, double> alreadyAchieved;
    
    /** @brief The earliest point at which an effect can act upon/a precondition can refer to a given variable.
     *
     *  This is a pointer to <code>RPGHeuristic::Private::earliestNumericPOTimes</code>.
     */
    const vector<EpsilonResolutionTimestamp> * earliestNumericPOTimes;

    const vector<pair<double,double> > * const payloadDurationBounds;

    const bool debug;
    
    /** @brief Common initialisation code when recording effects.
     *
     *  This function ensures that:
     *  - a fluent layer has been created for the specified time
     *  - the effects recorded at the last layer were applied
     *  - the class member variables point to the data structures inside the new layer
     *
     *  @param effectAppearsInLayer  The timestamp of the new fluent layer
     */
    void aboutToRecordAnEffect(const EpsilonResolutionTimestamp & effectAppearsInLayer) {
        if (effectsAffectThisLayer == layers.end()) {
            
            EpsilonResolutionTimestamp priorLayer = effectAppearsInLayer;
            priorLayer -= EpsilonResolutionTimestamp::epsilon();
            
            effectInputs = layers.find(priorLayer);
            #ifndef NDEBUG
            if (effectInputs == layers.end()) {
                cout << std::setprecision(8) << std::fixed;
                cout << "Internal error: current effect layer is " << effectAppearsInLayer << ", but no fluent values are defined for " << priorLayer << endl;
                exit(1);
            }
            #endif
            
            effectsAffectThisLayer = addLayer(effectInputs, EpsilonResolutionTimestamp::epsilon() );
            mostRecentInstantaneousEffects = &(effectsAffectThisLayer->second->instantaneousEffectsDirectlyBeforeThisLayer);
            mostRecentIntegratedEffects = &(effectsAffectThisLayer->second->integratedEffectsDirectlyBeforeThisLayer);
            mostRecentGradientEffects = &(effectsAffectThisLayer->second->gradientEffectsDirectlyBeforeThisLayer);
            
            if (debug) {
                cout << "New effect layer " << effectAppearsInLayer << " created\n";
            }
        } else {
            #ifndef NDEBUG
            if (!(effectAppearsInLayer == effectsAffectThisLayer->first)) {
                cout << std::setprecision(8) << std::fixed;
                cout << "Internal error: current effect layer is " << effectsAffectThisLayer->first << ", but asked for an effect to go in " << effectAppearsInLayer << endl;
                exit(1);
            }
            #endif
        }
        
    }
    
public:

    /** @brief Placeholder constructor.  The real initialisation is done in <code>setFactLayerZero()</code>.
     */
    FluentLayers(const vector<pair<double,double> > * const payloadIn) : payloadDurationBounds(payloadIn), debug(Globals::globalVerbosity & 64 || Globals::globalVerbosity & 128) {
        FluentLayerEntry::pneCount = RPGBuilder::getPNECount();
        
        nowExtracting = false;
    }
    
    ~FluentLayers() {
        list<FluentLayerEntry*>::const_iterator delItr = layerGC.begin();
        const list<FluentLayerEntry*>::const_iterator delEnd = layerGC.end();
        for (; delItr != delEnd; ++delItr) {
            delete *delItr;
        }
    }
    
    /** @brief Specify the values of the variables in fact layer zero.
     * 
     * Do not call this unless the object has not yet had any layers defined.
     *
     * @param values  The values of each variable (including negative and artificial variables)
     */
    void setFactLayerZero(const vector<double> & values, const vector<EpsilonResolutionTimestamp> & cannotReferToVariableUntilTime) {
        assert(layers.empty());
        earliestNumericPOTimes = &(cannotReferToVariableUntilTime);
        layers.insert(make_pair(EpsilonResolutionTimestamp::zero(), newFluentLayer(values)));
        revisitInstantaneousEffectIfVariableValueChanges.resize(values.size());
        revisitInstantaneousEffectIfVariableIsAssignedTo.resize(values.size());
        actionsThatHaveHadThisEffect.resize(RPGBuilder::getNumericEff().size());
        actionsThatHaveHadThisIntegratedEffect.resize(FluentLayerEntry::pneCount);
        actionsThatHaveHadThisGradientEffect.resize(FluentLayerEntry::pneCount);
        effectsAffectThisLayer = layers.end();
        layerWithEffectsToBeRevisited = layers.end();
        
        const int lptSize = RPGBuilder::getNumericPreTable().size();
        layerAtWhichPreconditionBecomesTrue.resize(lptSize);
        
        for (int p = 0; p < lptSize; ++p) {
            layerAtWhichPreconditionBecomesTrue[p].first = preconditionsBecomingTrueAtTime.end();
            // for now, the second entry of each pair is undefined - on the plus side
            // this means valgrind will scream if we try to use them
        }
            
    }
    
    /** @brief Function to access a writeable version of the fluents in fact layer zero.
     * 
     *  This is used to update for the CTS effects of currently executing actions, and find which facts are
     *  true in the state being evaluated.  Otherwise, it probably shouldn't be used.
     *
     *  @return A reference to the vector of fluent values at fact layer zero
     */
    vector<double> & borrowFactLayerZeroValues() {
        return layers.begin()->second->writeableValues();
    }
    
    /** @brief Return the next layer that is worth visiting purely on the merits of active effects.
     * 
     * This can be due to either continuous effects, or effects that need revisiting
     * as the values of the variables upon which they depend has changed.
     *
     * @param isToRevisitEffects  If set to <code>true</code>, then revisit the effects in the next layer
     * @param isDueToGradients    If set to <code>true</code>, then the gradients will cause facts to become
     *                            true EPSILON after the time returned.
     * @return  A pair, where:
     *          -  the first value is the timestamp of a layer to visit (or <code>DBL_MAX</code> if none is needed)
     *           - the secound value is <code>true</code> if this is epsilon after the previous layer (this is
     *             used to prevent rounding errors)
     */
    pair<EpsilonResolutionTimestamp,bool> nextLayerWouldBeAt(const EpsilonResolutionTimestamp & currTS, bool & isToRevisitEffects, bool & isDueToGradients) {
        
        const map<EpsilonResolutionTimestamp,set<int> >::const_iterator ptItr = preconditionsBecomingTrueAtTime.begin();
        
        // if we need to revisit effects whose input values have changed, do that right away
        if (layerWithEffectsToBeRevisited != layers.end()) {
            isToRevisitEffects = true;
            if (ptItr != preconditionsBecomingTrueAtTime.end()) {
                EpsilonResolutionTimestamp check = ptItr->first;
                check -= EpsilonResolutionTimestamp::epsilon();
                check -= EpsilonResolutionTimestamp::epsilon();
                isDueToGradients = check.isZero();
            }
            if (debug) {
                cout << COLOUR_light_blue << "Need to recalculate fluents at epsilon after the previous fluent layer\n" << COLOUR_default;
            }
            return make_pair(layerWithEffectsToBeRevisited->first, true);
        }
        
        // otherwise, consider the next point at which a precondition will become satisfied
        
        if (ptItr == preconditionsBecomingTrueAtTime.end()) {
            return make_pair(EpsilonResolutionTimestamp::infinite(),false);
        }

        isDueToGradients = true;

        // set 'is epsilon later' flag (the second entry of the pair) to true if
        // it is near as makes no odds to epsilon in the future
        
        EpsilonResolutionTimestamp toReturn = ptItr->first;
        toReturn -= EpsilonResolutionTimestamp::epsilon();

        const bool gapIsEpsilon = ((toReturn - currTS) == EpsilonResolutionTimestamp::epsilon());
        assert((toReturn - currTS) >= EpsilonResolutionTimestamp::epsilon());
        
        if (debug) {
            if (gapIsEpsilon) {
                cout << COLOUR_light_blue << "Numeric preconditions become true at " << ptItr->first << ", so returning (" << toReturn << ",true)\n" << COLOUR_default;
            } else {
                cout << COLOUR_light_blue << "Numeric preconditions become true at " << ptItr->first << ", so returning (" << toReturn << ",false)\n" << COLOUR_default;
            }
        }
        
        
        return make_pair(toReturn, gapIsEpsilon);
        
    }

    /** @brief Create a dummy fluent layer at the time given.
     * 
     *  When advancing by more than epsilon, we need to create a dummy reference layer to provide input
     *  fluent values for the actions in the subsequent action layer in the RPG.
     *
     *  @param ts  The timestamp of the fact layer preceding the new actions to be added
     */
    void createThenIgnore(const EpsilonResolutionTimestamp & ts) {        
        assert(layerWithEffectsToBeRevisited == layers.end() || (layerWithEffectsToBeRevisited->first == ts));
        assert(effectsAffectThisLayer == layers.end());
        
        LayerMap::iterator lastEntry = layers.end();
        --lastEntry;
        
        EpsilonResolutionTimestamp timeDifference = ts;
        timeDifference -= lastEntry->first;
        
        if (debug) {
            cout << "Asked to create layer at " << ts << ", previous is at " << lastEntry->first << ", so advance beyond previous fluent layer is " << timeDifference << endl;
        }
        if (!timeDifference.isZero()) {        
            if (debug) {
                cout << "Made sure that fluent layer " << ts << " exists\n";
            }
            layers.insert(lastEntry, make_pair(ts, newFluentLayerEntry(lastEntry->second, timeDifference, true, true)));        
        } else {
            if (debug) {
                cout << "A fluent layer at " << ts << " already exists\n";
            }
        }
    }

    void recordEffectsThatAreNowToBeRevisited(FactLayerMap & factLayers) {
        if (layerWithEffectsToBeRevisited == layers.end()) {
            if (debug) {
                cout << "> No effects are to be revisited\n";
            }
            return;
        }
        
        assert(effectsAffectThisLayer == layers.end());

        if (debug) {
            cout << "> Revisiting effects in layer " << layerWithEffectsToBeRevisited->first << ", so creating output layer epsilon later\n";
        }
        
        
        effectInputs = layerWithEffectsToBeRevisited;        
        effectsAffectThisLayer = addLayer(effectInputs, EpsilonResolutionTimestamp::epsilon() );
        
        mostRecentInstantaneousEffects = &(effectsAffectThisLayer->second->getInstantaneousEffectsDirectlyBeforeThisLayer());
        mostRecentIntegratedEffects = &(effectsAffectThisLayer->second->getIntegratedEffectsDirectlyBeforeThisLayer());
        mostRecentGradientEffects = &(effectsAffectThisLayer->second->getGradientEffectsDirectlyBeforeThisLayer());
        
        const set<int> & revisit = layerWithEffectsToBeRevisited->second->getInstantaneousEffectsToRevisitAfterThisLayer();

        
        {
            set<int>::const_iterator rvItr = revisit.begin();
            const set<int>::const_iterator rvEnd = revisit.end();
            
            for (; rvItr != rvEnd; ++rvItr) {
                list<const ActionAndHowManyTimes*> & dest = (*mostRecentInstantaneousEffects)[*rvItr];
                dest.insert(dest.end(), actionsThatHaveHadThisEffect[*rvItr].begin(), actionsThatHaveHadThisEffect[*rvItr].end());
            }
        }
        
        const set<int> & revisit2 = layerWithEffectsToBeRevisited->second->getIntegratedOrGradientEffectsToRevisitAfterThisLayer();
        
        {
            for (int pass = 0; pass < 2; ++pass) {
                
                set<int>::const_iterator rv2Itr = revisit2.begin();
                const set<int>::const_iterator rv2End = revisit2.end();
                
                for (; rv2Itr != rv2End; ++rv2Itr) {
                    map<double, list<const ActionAndHowManyTimes*> > & outerdest
                        = (pass ? (*mostRecentGradientEffects)[*rv2Itr] : (*mostRecentIntegratedEffects)[*rv2Itr]);

                    map<double, list<ActionAndHowManyTimes*> > & src
                        = (pass ? actionsThatHaveHadThisGradientEffect[*rv2Itr] : actionsThatHaveHadThisIntegratedEffect[*rv2Itr]);
                                        
                        
                    map<double, list<ActionAndHowManyTimes*> >::iterator effItr = src.begin();
                    const map<double, list<ActionAndHowManyTimes*> >::iterator effEnd = src.end();
                    
                    for (; effItr != effEnd; ++effItr) {
                        
                        list<const ActionAndHowManyTimes*> & dest = outerdest[effItr->first];
                        
                        list<ActionAndHowManyTimes*>::iterator actItr = effItr->second.begin();
                        const list<ActionAndHowManyTimes*>::iterator actEnd = effItr->second.end();                                                
                        
                        for (; actItr != actEnd; ++actItr) {
                            if (!pass) {
                                
                                // for instantaneous effects, copy them in
                                dest.push_back(*actItr);
                            } else {
                                
                                                                
                                
                                if ((*actItr)->gradientsFinishAt == EpsilonResolutionTimestamp::infinite()) {                                    
                                    if ((*actItr)->gradientNeedsStarting) {
                                        gc.push_back(*(*actItr));
                                        
                                        ActionAndHowManyTimes & newEntry = gc.back();                                        
                                        newEntry.gradientNeedsStarting = false;
                                        
                                        *actItr = &newEntry; // from now on, use this version which doesn't trigger an increase of the perpetual gradient
                                    }
                                    
                                    dest.push_back(*actItr);
                                    
                                } else {
                                    gc.push_back(*(*actItr));
                                                                        
                                    ActionAndHowManyTimes & newEntry = gc.back();
                                    
                                    newEntry.gradientNeedsStarting = false;
                                    
                                    EpsilonResolutionTimestamp extraTime((*actItr)->howManyTimes * ((*actItr)->maxDur), false);
                                    
                                    EpsilonResolutionTimestamp endAt = effectsAffectThisLayer->first;
                                    endAt -= EpsilonResolutionTimestamp::epsilon();     // the time of the action layer in which the effect began
                                    endAt += extraTime;                                 // plus the maximum sequential time of applications of this action
                                    
                                    if (factLayers.empty() || factLayers.begin()->first > (*actItr)->gradientsFinishAt) {
                                        // if the effect has already lapsed, start it again
                                                                            
                                        newEntry.gradientNeedsStarting = true;
                                        
                                        if (effItr->first > 0) {        
                                            factLayers[endAt].gradientFinishes.insert(make_pair(*rv2Itr,0.0)).first->second += effItr->first;
                                        } else {
                                            factLayers[endAt].gradientFinishes.insert(make_pair(*rv2Itr + FluentLayerEntry::pneCount,0.0)).first->second -= effItr->first;
                                        }
                                        
                                        newEntry.gradientsFinishAt = endAt;
                                        
                                    } else {
                                        
                                        // otherwise, don't start it again; but do delay its end
                                        
                                        if (effItr->first > 0) {        
                                            factLayers[(*actItr)->gradientsFinishAt].gradientFinishes.insert(make_pair(*rv2Itr,0.0)).first->second -= effItr->first;
                                            factLayers[endAt].gradientFinishes.insert(make_pair(*rv2Itr,0.0)).first->second += effItr->first;
                                        } else {
                                            factLayers[(*actItr)->gradientsFinishAt].gradientFinishes.insert(make_pair(*rv2Itr + FluentLayerEntry::pneCount,0.0)).first->second += effItr->first;
                                            factLayers[endAt].gradientFinishes.insert(make_pair(*rv2Itr + FluentLayerEntry::pneCount,0.0)).first->second -= effItr->first;
                                        }
                                        
                                        newEntry.gradientsFinishAt = endAt;
                                    }
                                    
                                                                                                            
                                    *actItr = &newEntry; // from now on, use the version with the most recent endAt record
                                    dest.push_back(*actItr);
                                }
                            }
                        }
                        
                    }                
                }
            }    
        }
                        
    }

    /** @brief Record consequences of active gradients, i.e. new facts becoming true at this time.
     *
     *  Only call this function if it is certain that the time given is the next time
     *  noted for preconditions becoming true.
     *
     *  @param newFactsAppearsInLayer  The next layer in which new facts are to appear,
     *                                 due to active gradients.
     */
    void recordConsequencesOfActiveGradients(const EpsilonResolutionTimestamp & newFactsAppearsInLayer) {
        
        assert(!preconditionsBecomingTrueAtTime.empty());
        
        const map<EpsilonResolutionTimestamp, set<int> >::iterator nextFacts = preconditionsBecomingTrueAtTime.begin();
        
        assert(nextFacts->first == newFactsAppearsInLayer);
        
        
        assert(gradientsLeadToTheseFactsNowBeingTrue.empty());
        
        gradientsLeadToTheseFactsNowBeingTrue.swap(nextFacts->second);
        
        
        preconditionsBecomingTrueAtTime.erase(nextFacts);
        
        set<int>::const_iterator fItr = gradientsLeadToTheseFactsNowBeingTrue.begin();
        const set<int>::const_iterator fEnd = gradientsLeadToTheseFactsNowBeingTrue.end();
        
        for (; fItr != fEnd; ++fItr) {
            layerAtWhichPreconditionBecomesTrue[*fItr].first = preconditionsBecomingTrueAtTime.end();
        }
        
        aboutToRecordAnEffect(newFactsAppearsInLayer);
    }

    /** @brief Record that a given integrated continuous numeric effect can be applied a number of times, on behalf of the specified action.
     *
     * @param action                Details on the action, including how many times it can be applied
     * @param effectAppearsInLayer  The layer in which the consequences of the effect appear
     * @param effID                 The ID of the effect (an index into <code>RPGBuilder::getNumericEff()</code>)
     */
    void recordIntegratedNumericEffect(const ActionAndHowManyTimes & action, const EpsilonResolutionTimestamp & effectAppearsInLayer, const pair<int,double> & effID) {
                
        if (debug) {
            cout << "Recording integrated effect " << *(RPGBuilder::getPNE(effID.first));
            if (effID.second > 0) {
                cout << " += " << effID.second;
            } else {
                cout << " -= " << -effID.second;
            }
            if (action.howManyTimes == 1) {
                cout << ", once, ";
            } else {
                cout << ", " << action.howManyTimes << " times, ";
            }
            cout << "affecting fact layer " << effectAppearsInLayer << endl;
        }
        
        aboutToRecordAnEffect(effectAppearsInLayer);
        
        gc.push_back(action);
        
        actionsThatHaveHadThisIntegratedEffect[effID.first][effID.second].push_back(&(gc.back()));
        
        (*mostRecentIntegratedEffects)[effID.first][effID.second].push_back(&(gc.back()));
        
        if (debug) {
            cout << COLOUR_light_green << "Added integrated effect: " << *(RPGBuilder::getPNE(effID.first));
            if (effID.second > 0) {
                cout << " += " << effID.second << COLOUR_default << endl;
            } else {
                cout << " -= " << -effID.second << COLOUR_default << endl;
            }
        }
        
        assert(gc.back().howManyTimes > 0);
    }

    /** @brief Record that a given gradient continuous numeric effect can be applied a number of times, on behalf of the specified action.
     * 
     * If the action can only be applied finitely often, the fact that the effect has to finish is recorded in
     * <code>factLayers</code>.
     *
     * @param action                Details on the action, including how many times it can be applied
     * @param effectAppearsInLayer  The layer in which the consequences of the effect appear
     * @param effID                 The ID of the effect (an index into <code>RPGBuilder::getNumericEff()</code>)
     * @param factLayers            Updated to record the point (if any) at which the effect expires
     */
    void recordGradientNumericEffect(const ActionAndHowManyTimes & action, const EpsilonResolutionTimestamp & effectAppearsInLayer,
                                     const pair<int,double> & effID, FactLayerMap & factLayers) {
                
        if (debug) {
            cout << "Recording gradient effect d" << *(RPGBuilder::getPNE(effID.first));
            if (effID.second > 0) {
                cout << "/dt += " << effID.second;
            } else {
                cout << "/dt -= " << -effID.second;
            }
            if (action.howManyTimes == 1) {
                cout << ", once, ";
            } else {
                cout << ", " << action.howManyTimes << " times, ";
            }
            cout << "starting immediately before fact layer " << effectAppearsInLayer << endl;
        }

        aboutToRecordAnEffect(effectAppearsInLayer);
        
        gc.push_back(action);
        
        actionsThatHaveHadThisGradientEffect[effID.first][effID.second].push_back(&(gc.back()));

        (*mostRecentGradientEffects)[effID.first][effID.second].push_back(&(gc.back()));
        
        if (debug) {
            cout << COLOUR_light_green << "Added gradient effect: d" << *(RPGBuilder::getPNE(effID.first));
            if (effID.second > 0) {
                cout << "/dt += " << effID.second << COLOUR_default << endl;
            } else {
                cout << "/dt -= " << -effID.second << COLOUR_default << endl;
            }
        }
        
        assert(gc.back().howManyTimes > 0);

        gc.back().gradientNeedsStarting = true;
        
        if (action.howManyTimes == INT_MAX) return;
        if (action.maxDur == DBL_MAX) return;
        
        EpsilonResolutionTimestamp endAt = effectAppearsInLayer;
        endAt -= EpsilonResolutionTimestamp::epsilon(); // the time of the action layer in which the effect began
        endAt += EpsilonResolutionTimestamp(action.howManyTimes * action.maxDur, false); // plus the maximum sequential time of applications of this action, rounded up
        
        gc.back().gradientsFinishAt = endAt;
        
        if (effID.second > 0) {        
            factLayers[endAt].gradientFinishes.insert(make_pair(effID.first,0.0)).first->second += effID.second;
        } else {
            factLayers[endAt].gradientFinishes.insert(make_pair(effID.first + FluentLayerEntry::pneCount,0.0)).first->second -= effID.second;
        }
        
    }
        
    
    /** @brief Record that a given numeric effect can be applied a number of times, on behalf of the specified action.
     *
     * @param action                Details on the action, including how many times it can be applied
     * @param effectAppearsInLayer  The layer in which the the consequences of the effect appear
     * @param effID                 The ID of the effect (an index into <code>RPGBuilder::getNumericEff()</code>)
     */
    void recordInstantaneousNumericEffect(const ActionAndHowManyTimes & action, const EpsilonResolutionTimestamp & effectAppearsInLayer, const int & effID) {
        
        
        if (debug) {
            cout << "Recording effect " << effID << " affecting fact layer " << effectAppearsInLayer << endl;
        }
            
            
        aboutToRecordAnEffect(effectAppearsInLayer);
                        
        
        if (actionsThatHaveHadThisEffect[effID].empty()) {
            RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[effID];
            for (int s = 0; s < currEff.size; ++s) {
                if (currEff.variables[s] > 0) {
                    revisitInstantaneousEffectIfVariableValueChanges[currEff.variables[s]].insert(effID);
                }
            }
        }
        
        if (debug) {
            cout << COLOUR_light_blue << "Added effect: " << RPGBuilder::getNumericEff()[effID] << COLOUR_default << endl;
        }
        gc.push_back(action);
        
        actionsThatHaveHadThisEffect[effID].push_back(&(gc.back()));
        (*mostRecentInstantaneousEffects)[effID].push_back(&(gc.back()));        
    }
                                                           
   /** @brief Apply any effects recorded in the most recent action layer, supplied via calls to <code>recordInstantaneousNumericEffect()</code>.
    *
    * If no such effects exist, this function does nothing.
    *
    *  @param achievedInLayer          Layers at which the numeric preconditions were achieved
    *  @param newNumericPreconditions  If new numeric preconditions have become true, their indices are pushed onto this list
    *  @param maxNeeded                The maximum amount of each variable needed to satisfy the preconditions
    */
    void applyRecentlyRecordedEffects(vector<EpsilonResolutionTimestamp> & achievedInLayer, list<int> & newNumericPreconditions,
                                      const vector<double> & maxNeeded) {
        if (effectsAffectThisLayer == layers.end()) return;
        
        assert(effectsAffectThisLayer->second->initialised());
        
        if (debug) {
            cout << "Applying the numeric effects noted in this layer; effects affect " << effectsAffectThisLayer->first << endl;
        }
        
        set<int> variableChanged;        
        set<int> variableAssignedTo;

        {
            
            map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator effItr = mostRecentGradientEffects->begin();
            const map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator effEnd = mostRecentGradientEffects->end();

            for (; effItr != effEnd; ++effItr) {
                if (debug) {
                    cout << "Gradient effects on " << *(RPGBuilder::getPNE(effItr->first)) << ":";
                }
                map<double, list<const ActionAndHowManyTimes*> >::const_iterator magItr = effItr->second.begin();
                const map<double, list<const ActionAndHowManyTimes*> >::const_iterator magEnd = effItr->second.end();
                
                for (; magItr != magEnd; ++magItr) {
                    if (debug) {
                        cout << " " << magItr->first;
                    }
                    
                    list<const ActionAndHowManyTimes*>::const_iterator actItr = magItr->second.begin();
                    const list<const ActionAndHowManyTimes*>::const_iterator actEnd = magItr->second.end();
                    
                    for (; actItr != actEnd; ++actItr) {
                        if ((*actItr)->gradientNeedsStarting) {
                            assert((*actItr)->howManyTimes);
                            effectsAffectThisLayer->second->startGradient(effItr->first, magItr->first, variableChanged);
                        }
                    }
                }
                if (debug) {
                    cout << ", gradients on bounds are now [";
                    const double & l = effectsAffectThisLayer->second->getGradients()[effItr->first + FluentLayerEntry::pneCount];
                    if (l == 0) {
                        cout << "0.0";
                    } else {
                        cout << -l;
                    }
                    cout << "," << effectsAffectThisLayer->second->getGradients()[effItr->first] << "]" << endl;
                }
            }

            set<int> avsToRecalculate;
        
            set<int>::const_iterator vcItr = variableChanged.begin();
            const set<int>::const_iterator vcEnd = variableChanged.end();
            
            for (; vcItr != vcEnd; ++vcItr) {
                avsToRecalculate.insert(RPGBuilder::getVariableDependencies(*vcItr).begin(), RPGBuilder::getVariableDependencies(*vcItr).end());
            }

            {
                set<int>::const_iterator avItr = avsToRecalculate.begin();
                const set<int>::const_iterator avEnd = avsToRecalculate.end();            
                
                effectsAffectThisLayer->second->recalculateAVGradients(avItr, avEnd);
            }
            
            if (debug) {
                
                set<int>::const_iterator avItr = avsToRecalculate.begin();
                const set<int>::const_iterator avEnd = avsToRecalculate.end(); 
                
                for (; avItr != avEnd; ++avItr) {
                    cout << "Gradients of AV " << RPGBuilder::getArtificialVariable(*avItr) << " is now " << effectsAffectThisLayer->second->getGradients()[*avItr] << endl;
                }
            }
            
            
            // Now give us epsilon's worth of the gradient effects
            
            LayerMap::iterator previousLayer = effectsAffectThisLayer;
            --previousLayer;
            
            #ifndef NDEBUG
            EpsilonResolutionTimestamp check = effectsAffectThisLayer->first;
            check -= previousLayer->first;
            check -= EpsilonResolutionTimestamp::epsilon();
            assert(check.isZero());
            #endif
            effectsAffectThisLayer->second->applyGradients(EpsilonResolutionTimestamp::epsilon());
        }
        
        {
            // integrated CTS effects
            
            map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator effItr = mostRecentIntegratedEffects->begin();
            const map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator effEnd = mostRecentIntegratedEffects->end();
            
            for (; effItr != effEnd; ++effItr) {
                if (debug) {
                    cout << "Integrated effects on " << *(RPGBuilder::getPNE(effItr->first)) << ":";
                }
                map<double, list<const ActionAndHowManyTimes*> >::const_iterator magItr = effItr->second.begin();
                const map<double, list<const ActionAndHowManyTimes*> >::const_iterator magEnd = effItr->second.end();
                
                for (; magItr != magEnd; ++magItr) {
                    if (debug) {
                        cout << " " << magItr->first << " (";
                    }
                    list<const ActionAndHowManyTimes*>::const_iterator actItr = magItr->second.begin();
                    const list<const ActionAndHowManyTimes*>::const_iterator actEnd = magItr->second.end();
                    
                    for (; actItr != actEnd; ++actItr) {
                        if (debug) {
                            cout << " " << (*actItr)->howManyTimes;
                        }
                        assert((*actItr)->howManyTimes);
                        effectsAffectThisLayer->second->applyIncrease(-1, effItr->first, magItr->first, magItr->first, (*actItr)->howManyTimes, variableChanged);
                    }
                    if (debug) {
                        cout << " ) ";
                    }
                }
                if (debug) {
                    cout << endl;
                    const int affectedVar = effItr->first;
                    cout << "Bounds are now [";
                    if (effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] == DBL_MAX) {
                        cout << "-inf,";
                    } else {
                        cout << -effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] << ",";
                    }
                    
                    if (effectsAffectThisLayer->second->values()[affectedVar] == DBL_MAX) {
                        cout << "inf]\n";
                    } else {
                        cout << effectsAffectThisLayer->second->values()[affectedVar] << "]\n";
                    }
                }
            }
        }
        
        for (int pass = 0; pass < 2; ++pass) {
            
            // pass 0 - increase/decrease effects
            // pass 1 - assignments
            
            map<int, list<const ActionAndHowManyTimes*> >::const_iterator effItr = mostRecentInstantaneousEffects->begin();
            const map<int, list<const ActionAndHowManyTimes*> >::const_iterator effEnd = mostRecentInstantaneousEffects->end();
            
            for (; effItr != effEnd; ++effItr) {
                RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[effItr->first];
                if (currEff.isAssignment != (pass == 1)) continue;
                const int affectedVar = currEff.fluentIndex;
                
                list<const ActionAndHowManyTimes*>::const_iterator actItr = effItr->second.begin();
                const list<const ActionAndHowManyTimes*>::const_iterator actEnd = effItr->second.end();
                
                for (; actItr != actEnd; ++actItr) {
                    const double maxVal = currEff.evaluate(effectInputs->second->values(), (*actItr)->minDur, (*actItr)->maxDur);
                    const double minVal = currEff.evaluateMin(effectInputs->second->values(), (*actItr)->minDur, (*actItr)->maxDur);
                    if (currEff.isAssignment) { 
                         if (debug) {
                            cout << "Bounds were [";                            
                            if (effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] == DBL_MAX) {
                                cout << "-inf,";
                            } else if (effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] == -DBL_MAX) {
                                cout << "inf,";
                            } else {
                                cout << -effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] << ",";
                            }
                            if (effectsAffectThisLayer->second->values()[affectedVar] == DBL_MAX) {
                                cout << "inf]\n";
                            } else if (effectsAffectThisLayer->second->values()[affectedVar] == -DBL_MAX) {
                                cout << "-inf]\n";
                            } else {
                                cout << effectsAffectThisLayer->second->values()[affectedVar] << "]\n";
                            }
                            cout << "Effect bounds: [" << minVal << "," << maxVal <<" ]" << endl;
                        }
                        
                        effectsAffectThisLayer->second->keepAssignmentIfBetter(*actItr, effItr->first, true, affectedVar, maxVal, variableAssignedTo);
                        effectsAffectThisLayer->second->keepAssignmentIfBetter(*actItr, effItr->first, false, affectedVar, minVal, variableAssignedTo);                    
                         if (debug) {
                            cout << "Bounds are now [";
                            if (effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] == DBL_MAX) {
                                cout << "-inf,";
                            } else {
                                cout << -effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] << ",";
                            }
                            if (effectsAffectThisLayer->second->values()[affectedVar] == DBL_MAX) {
                                cout << "inf]\n";
                            } else {
                                cout << effectsAffectThisLayer->second->values()[affectedVar] << "]\n";
                            }
                            
                        }
                    } else {
                        if (debug) {
                            cout << currEff << " gives us " << minVal << "," << maxVal << " of " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                            
                        }
                        effectsAffectThisLayer->second->applyIncrease(effItr->first, affectedVar, minVal, maxVal, (*actItr)->howManyTimes, variableChanged);
                        //effectsAffectThisLayer->second->applyIncrease(effItr->first, affectedVar, minVal, (*actItr)->howManyTimes, variableChanged);                    

                        if (debug) {
                            cout << "Bounds are now [";
                            if (effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] == DBL_MAX) {
                                cout << "-inf,";
                            } else {
                                cout << -effectsAffectThisLayer->second->values()[affectedVar + FluentLayerEntry::pneCount] << ",";
                            }
                            if (effectsAffectThisLayer->second->values()[affectedVar] == DBL_MAX) {
                                cout << "inf]\n";
                            } else {
                                cout << effectsAffectThisLayer->second->values()[affectedVar] << "]\n";
                            }
                            
                        }
                    }
                }
            }
            
        }
        
        // mark assigned-to variables as having changed, too
        variableChanged.insert(variableAssignedTo.begin(), variableAssignedTo.end());
        
        set<int> avsToRecalculate;
            
        {
            
            set<int>::const_iterator vcItr = variableChanged.begin();
            const set<int>::const_iterator vcEnd = variableChanged.end();
            
            for (; vcItr != vcEnd; ++vcItr) {
                avsToRecalculate.insert(RPGBuilder::getVariableDependencies(*vcItr).begin(), RPGBuilder::getVariableDependencies(*vcItr).end());
            }
            
            {
                set<int>::const_iterator avItr = avsToRecalculate.begin();
                const set<int>::const_iterator avEnd = avsToRecalculate.end();
                
                effectsAffectThisLayer->second->recalculateAVs(avItr, avEnd);
            }
            
            if (debug) {
                set<int>::const_iterator avItr = avsToRecalculate.begin();
                const set<int>::const_iterator avEnd = avsToRecalculate.end();
                
                for (; avItr != avEnd; ++avItr) {
                    cout << "Lower bound of " << RPGBuilder::getArtificialVariable(*avItr) << " is now ";
                    if (effectsAffectThisLayer->second->values()[*avItr] == DBL_MAX) {
                        cout << "inf\n";
                    } else { 
                        cout << effectsAffectThisLayer->second->values()[*avItr] << endl;
                    }

                }
            }
        }

        set<int> presToRecalculate;
        
        // pull in preconditions that gradients have satisfied, but double-check this is definitely the case
        presToRecalculate.swap(gradientsLeadToTheseFactsNowBeingTrue);
        
        for (int pass = 0; pass < 2; ++pass) {
            const set<int> & variableSet = (pass ? avsToRecalculate : variableChanged);
            
            set<int>::const_iterator varItr = variableSet.begin();
            const set<int>::const_iterator varEnd = variableSet.end();
            
            for (; varItr != varEnd; ++varItr) {
                const list<int> & recalc = RPGBuilder::affectsRPGNumericPreconditions(*varItr);
                presToRecalculate.insert(recalc.begin(), recalc.end());
            }
        }
        
        {            
            set<int>::const_iterator preItr = presToRecalculate.begin();
            const set<int>::const_iterator preEnd = presToRecalculate.end();
            
            double satisfactionDelay;
            
            for (; preItr != preEnd; ++preItr) {
                if (achievedInLayer[*preItr] != EpsilonResolutionTimestamp::undefined() ) continue;
                
                PreconditionToSatisfactionLayerPair & forecastPair = layerAtWhichPreconditionBecomesTrue[*preItr];
                
                const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*preItr];
                
                satisfactionDelay = effectsAffectThisLayer->second->willBecomeSatisfiedAfterDelay(currPre);
                
                if (satisfactionDelay == 0.0) {
                    achievedInLayer[*preItr] = effectsAffectThisLayer->first;
                    newNumericPreconditions.push_back(*preItr);
                    if (debug) {
                        cout << COLOUR_yellow << "Precondition " << *preItr << ", " << currPre << ", becomes true in layer " << effectsAffectThisLayer->first << COLOUR_default << endl;
                    }
                    
                    // Now it's satisfied, note that it isn't forecast to become true at a future point
                    if (forecastPair.first != preconditionsBecomingTrueAtTime.end()) {
                        forecastPair.first->second.erase(forecastPair.second);
                        if (forecastPair.first->second.empty()) {
                            preconditionsBecomingTrueAtTime.erase(forecastPair.first);
                        }
                                                            
                        forecastPair.first = preconditionsBecomingTrueAtTime.end();
                    }
                    
                } else if (satisfactionDelay < DBL_MAX) {
                    
                    EpsilonResolutionTimestamp delayRoundedUp(satisfactionDelay, false);
                    EpsilonResolutionTimestamp futureLayer = effectsAffectThisLayer->first;
                    futureLayer += delayRoundedUp;
                    
                    const EpsilonResolutionTimestamp earliestPOPoint = earliestPointForNumericPrecondition(currPre, earliestNumericPOTimes);
                    
                    if (futureLayer < earliestPOPoint) {
                        futureLayer = earliestPOPoint;
                    }
                    
                    if (forecastPair.first == preconditionsBecomingTrueAtTime.end()) {   
                        // never been forecast before
                        forecastPair.first = preconditionsBecomingTrueAtTime.insert(make_pair(futureLayer, set<int>())).first;
                        forecastPair.second = forecastPair.first->second.insert(*preItr).first;
                        
                        if (debug) {
                            cout << COLOUR_blue << "Precondition " << *preItr << ", " << currPre << ", becomes true in layer " << futureLayer << COLOUR_default << endl;
                        }
                        
                    } else {                    
                        map<EpsilonResolutionTimestamp, set<int> >::iterator newForecastItr = preconditionsBecomingTrueAtTime.find(futureLayer);
                        if (newForecastItr != forecastPair.first) {
                            // forecast was previously at a different time
                            
                            forecastPair.first->second.erase(forecastPair.second);
                            if (forecastPair.first->second.empty()) {
                                preconditionsBecomingTrueAtTime.erase(forecastPair.first);
                            }
                            
                            forecastPair.first = preconditionsBecomingTrueAtTime.insert(make_pair(futureLayer, set<int>())).first;
                            forecastPair.second = forecastPair.first->second.insert(*preItr).first;
                            
                            if (debug) {
                                cout << COLOUR_blue << "Revised: precondition " << *preItr << ", " << currPre << ", becomes true in layer " << futureLayer << COLOUR_default << endl;
                            }
                            
                        }
                    }
                    
                    
                } else if (forecastPair.first != preconditionsBecomingTrueAtTime.end()) {
                    // was forecast to become true, but isn't any longer - a gradient in its favour has expired
                    
                    forecastPair.first->second.erase(forecastPair.second);
                    if (forecastPair.first->second.empty()) {
                        preconditionsBecomingTrueAtTime.erase(forecastPair.first);
                    }
                    
                    forecastPair.first = preconditionsBecomingTrueAtTime.end();
                }
            }
                
        }


        {
            set<int>::const_iterator vcItr = variableChanged.begin();
            const set<int>::const_iterator vcEnd = variableChanged.end();
            
            for (; vcItr != vcEnd; ++vcItr) {
                effectsAffectThisLayer->second->markEffectsToRevisit(revisitInstantaneousEffectIfVariableValueChanges[*vcItr], maxNeeded);
            }
        }
        
        {
            set<int>::const_iterator atItr = variableAssignedTo.begin();
            const set<int>::const_iterator atEnd = variableAssignedTo.end();
            
            for (; atItr != atEnd; ++atItr) {

                effectsAffectThisLayer->second->markEffectsToRevisit(revisitInstantaneousEffectIfVariableIsAssignedTo[*atItr], maxNeeded);
                
                if (*atItr >= RPGBuilder::getPNECount()) {
                    if (!actionsThatHaveHadThisIntegratedEffect[*atItr - RPGBuilder::getPNECount()].empty()) {
                        effectsAffectThisLayer->second->markIntegratedOrGradientEffectVariableToRevisit(*atItr - RPGBuilder::getPNECount(), maxNeeded);
                    }
                    
                } else {                
                    if (!actionsThatHaveHadThisIntegratedEffect[*atItr].empty()) {
                        effectsAffectThisLayer->second->markIntegratedOrGradientEffectVariableToRevisit(*atItr, maxNeeded);
                    }
                }
            }
        }
        
        layerWithEffectsToBeRevisited = layers.end();
        
        // As all effects have now been applied, we do two things:
        
        // i) If there are effects to revisit, we note that this is the case
        if (   !effectsAffectThisLayer->second->getInstantaneousEffectsToRevisitAfterThisLayer().empty()
            || !effectsAffectThisLayer->second->getIntegratedOrGradientEffectsToRevisitAfterThisLayer().empty()    ) {
            
            layerWithEffectsToBeRevisited = effectsAffectThisLayer;
            if (debug) {
                cout << "Noting that " << layerWithEffectsToBeRevisited->first << " has effects that should be revisited\n";
            }
          
        } else {
            if (debug) {
                cout << "Noting that " << effectsAffectThisLayer->first << " has no effects that should be revisited\n";
            }
                        
        }
        
        // ii) We clear these variables, so that adding a new fluent layer is not blocked
        effectsAffectThisLayer = layers.end();
        mostRecentInstantaneousEffects = 0;
        
        if (debug) {
            cout << "Returning, having allowed the possibility of adding a new fluent layer\n";
        }
    }
    
    /** @brief Signal that the RPG has been built, and a plan is now to be extracted. */
    void prepareForExtraction() {
        assert(!nowExtracting);
        
        nowExtracting = true;
        currentSubgoalLayer = layers.end();
        --currentSubgoalLayer;
        
        if (debug) {
            cout << COLOUR_light_red << "Now extracting\n" << COLOUR_default << endl;
            cout << "Current subgoal layer is at time " << currentSubgoalLayer->first << endl;
        }
    }
    
    /** @brief Request a precondition to support an action, during solution extraction.
     *
     *  This function takes the desired numeric precondition, and ensures it is
     *  met prior to the point at which the action is applied.
     *
     * @param pre             The numeric precondition (an index into <code>RPGBuilder::getNumericPreTable()</code>
     * @param achievedAt      The fact layer at which this precondition was satisfied
     * @param forActionLayer  The action layer of the action this precondition needs to support
     * @param goalsAtLayer    The record of goals kept during solution extraction, to be updated
     *                        by this function.
     * @param tilR            The timestamp of the earliest deadline which the action this precondition
     *                        supports is relevant to.
     */
    void requestNumericPrecondition(const int & pre, const EpsilonResolutionTimestamp & achievedAt,
                                    const EpsilonResolutionTimestamp & forActionLayer, RPGRegressionMap & goalsAtLayer,
                                    const EpsilonResolutionTimestamp & tilR) {
        
        if (debug) {
            if (((forActionLayer - EpsilonResolutionTimestamp::epsilon()) - currentSubgoalLayer->first) > EpsilonResolutionTimestamp::zero()) {
                cout << "It appears there is a cycle in the RPG solution extraction\n";
                cout << "Previously, we were asking for the preconditions of actions at " << currentSubgoalLayer->first << endl;
                cout << "However, the action for which preconditions are being requested now is at " << forActionLayer << endl;
            }
        }
        // check we are definitely going backwards through the RPG
        assert((-currentSubgoalLayer->first + (forActionLayer - EpsilonResolutionTimestamp::epsilon() )) <= EpsilonResolutionTimestamp::zero());
        
        while ((currentSubgoalLayer->first - forActionLayer) > EpsilonResolutionTimestamp::zero()) {
            --currentSubgoalLayer;
            if (debug) {
                cout << "Current subgoal layer is now at time " << currentSubgoalLayer->first << endl;
            }
        }
        
        LayerMap::iterator appearedIn = layers.find(achievedAt);
        
        if (debug) {
            if (appearedIn == layers.end()) {
                cout << "Asking for a precondition, " << pre << ", that became true at time " << achievedAt << ", but there is no fluent layer recorded for that time\n";
            }
        }
        assert(appearedIn != layers.end());
        
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[pre];
        
        const double threshold = (currPre.op == VAL::E_GREATER ? currPre.RHSConstant + 0.00001 : currPre.RHSConstant);
        
        RPGRegress & addTo = goalsAtLayer[achievedAt];
        
        addTo.requestNumericThreshold(currPre.LHSVariable, threshold, tilR);
        
        if (debug) {
            cout << "\t\t\t - Translated to a threshold " << currPre.LHSVariable << " >= " << threshold << endl;
        }
    }

    /** @brief Request that a numeric goal be achieved, during solution extraction.
     *
     *  This function takes the desired numeric goal, and ensures that actions
     *  are added to the plan to support it.
     *
     * @param pre             The numeric goal (an index into <code>RPGBuilder::getNumericPreTable()</code>
     * @param achievedAt      The fact layer at which this precondition was satisfied
     * @param goalsAtLayer    The record of goals kept during solution extraction, to be updated
     *                        by this function.
     */
    void requestGoal(const int & pre, const EpsilonResolutionTimestamp & achievedAt,
                     RPGRegressionMap & goalsAtLayer) {
        
        LayerMap::iterator appearedIn = layers.find(achievedAt);
        assert(appearedIn != layers.end());
        
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[pre];
        
        const double threshold = (currPre.op == VAL::E_GREATER ? currPre.RHSConstant + 0.001 : currPre.RHSConstant);
        
        RPGRegress & addTo = goalsAtLayer[achievedAt];
        
        if (debug) {
            cout << " - Requesting " << currPre.LHSVariable << " >= " << threshold << " at time " << achievedAt << endl;
        }
        addTo.requestNumericThreshold(currPre.LHSVariable, threshold, EpsilonResolutionTimestamp::infinite());
        
    }


    /** @brief Record the numeric side-effects of an action being added to the plan.
     *
     *  If we add an action to the plan, it might have numeric effects on other variables,
     *  as well as an effect upon the intended fact.  This function records these side-effects,
     *  in case they are beneficial.
     *
     * 
     */
    void recordSideEffects(const int & act, const Planner::time_spec & ts, const EpsilonResolutionTimestamp & actLayer) {
        
        LayerMap::const_iterator rollback = layers.end();
        --rollback;
        
        while (rollback->first > actLayer) {
            --rollback;
        }
        
        ActionAndHowManyTimes tmp(act, ts, 1, (*payloadDurationBounds)[act].first, (*payloadDurationBounds)[act].second);
        
        recordSideEffects(&tmp, 1, rollback->second->values());
    }
    
    
    /** @brief Satisfy all the numeric preconditions at the given layer, by adding supporting actions.
     *
     *  This action takes the numeric preconditions to be achieved in the given fact layer (recorded
     *  as variable&ndash;value thresholds), and applies actions from those available immediately
     *  prior to this layer until the residual precondition is sufficiently small as to be
     *  satisfiable in an earlier fluent layer.
     *
     *  @param currentLayer  The layer containing the numeric preconditions to be satisfied. 
     *  @param goalsAtLayer  The record of goals kept during solution extraction, to be updated
     *                       by this function to contain those to be achieved at an earlier layer.
     *  @param actionsUsed   Each action used in this function is added to this list, along with its
     *                       time-stamp, to then allow it to be (elsewhere) added to the relaxed plan.
     */
    void satisfyNumericPreconditionsAtLayer(RPGRegressionMap::const_iterator & currentLayer,
                                            RPGRegressionMap & goalsAtLayer,
                                            list<pair<EpsilonResolutionTimestamp, SupportingAction> > & actionsUsed) {
        
        if (currentLayer->second.numericValueGreaterThan.empty()) return;
        if (currentLayer->first <= EpsilonResolutionTimestamp::zero()) return;
        
        if (debug) {
            cout << COLOUR_light_blue << "Satisfying numeric preconditions in layer " << currentLayer->first << COLOUR_default << endl;
        }
        
        const LayerMap::iterator preconditionsIn = layers.find(currentLayer->first);
        
        LayerMap::const_iterator previousFluentLayer = preconditionsIn;
        --previousFluentLayer;
        
        

        map<int, pair<double,EpsilonResolutionTimestamp> >::const_iterator thresholdItr = currentLayer->second.numericValueGreaterThan.begin();
        const map<int, pair<double,EpsilonResolutionTimestamp> >::const_iterator thresholdEnd = currentLayer->second.numericValueGreaterThan.end();
        
        for (; thresholdItr != thresholdEnd; ++thresholdItr) {
            double needToAchieve = thresholdItr->second.first;
            
            if (debug) {
                cout << ": variable " << thresholdItr->first << " >= " << needToAchieve << endl;
            }
            
            /*{
                map<int,double>::const_iterator aaItr = alreadyAchieved.find(thresholdItr->first);
                if (aaItr != alreadyAchieved.end()) {
                    needToAchieve -= aaItr->second;
                    if (debug) {
                        cout << " * becomes variable " << thresholdItr->first << " >= " << needToAchieve << endl;
                    }
                }
            }*/
            
            if (needToAchieve < borrowFactLayerZeroValues()[thresholdItr->first]) {
                // have already satisfied this when satisfying something else
                if (debug) {
                    cout << "- Already have enough " << thresholdItr->first << endl;
                }
                continue;
            }

            const double valueInPreviousLayer = previousFluentLayer->second->values()[thresholdItr->first];
                        
            // if we can push it back to an earlier layer, then do so
            if (needToAchieve <= valueInPreviousLayer) {
                if (debug) {
                    cout << "- Could have " << needToAchieve << " of " << thresholdItr->first << " in the previous layer, " << previousFluentLayer->first << endl;
                }
                
                LayerMap::const_iterator rollback = previousFluentLayer;
                while (rollback->second->values()[thresholdItr->first] > needToAchieve) {
                    --rollback;
                }
                ++rollback;
                
                if (debug) {
                    cout << "  * Earliest possible point with sufficient is layer " << rollback->first << endl;
                }
                
                if (rollback->first > EpsilonResolutionTimestamp::zero() ) {
                    goalsAtLayer[rollback->first].requestNumericThreshold(thresholdItr->first, needToAchieve, thresholdItr->second.second);
                }
                continue;
            }
            
            // otherwise, we need to put some effort in
            
            assert(preconditionsIn->second->values()[thresholdItr->first] >= thresholdItr->second.first);
            
            bool assignmentMatched = false;
            
            {
            
                const RecordedAssignment * const assignmentUsed = preconditionsIn->second->assignmentAppliedToVariable(thresholdItr->first);
                
                // if it was done with assignment...
                if (assignmentUsed && assignmentUsed->act) {
                    
                    const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[assignmentUsed->eff];
                    
                    const ActionAndHowManyTimes * const toUse = assignmentUsed->act;
                    
                    actionsUsed.push_back(make_pair(currentLayer->first,SupportingAction(toUse->actID, toUse->ts, 1, thresholdItr->second.second)));

                    if (debug) {
                        cout << "  * Using assignment by " << *(RPGBuilder::getInstantiatedOp(toUse->actID)) << endl;
                    }
                    
                    assignmentMatched = true;
                    
                    recordSideEffects(toUse, 1, previousFluentLayer->second->values());
                    
                    
                    double contributionToIncreaseFromDur = 0.0;
                    if (assignmentUsed->maximiseEffect) {
                        for (int s = 0; s < currEff.size; ++s) {
                            if (currEff.variables[s] == -3) {
                                contributionToIncreaseFromDur += (currEff.weights[s] * toUse->minDur);
                            } else if (currEff.variables[s] == -19) {
                                contributionToIncreaseFromDur += (currEff.weights[s] * toUse->maxDur);
                            }
                        }
                    } else {
                        for (int s = 0; s < currEff.size; ++s) {
                            if (currEff.variables[s] == -3) {
                                contributionToIncreaseFromDur += (currEff.weights[s] * toUse->maxDur);
                            } else if (currEff.variables[s] == -19) {
                                contributionToIncreaseFromDur += (currEff.weights[s] * toUse->minDur);
                            }
                        }
                    }
                    
                    if (currEff.size) {
                        // if assigning a value derived from other variables, we need to make sure
                        // they hold values sufficient for the desired result
                        list<pair<int,double> > subTerms;
                        breakApart(currEff.variables, currEff.weights, currEff.size, currEff.constant,
                                   assignmentUsed->maximiseEffect, thresholdItr->second.first - contributionToIncreaseFromDur,
                                   previousFluentLayer, (*payloadDurationBounds)[toUse->actID].first, (*payloadDurationBounds)[toUse->actID].second, subTerms);

                        if (!subTerms.empty()) {// duration dependent variables don't induce subterms
                            RPGRegress & prev = goalsAtLayer[previousFluentLayer->first];
                            
                            list<pair<int,double> >::const_iterator tItr = subTerms.begin();
                            const list<pair<int,double> >::const_iterator tEnd = subTerms.end();
                            
                            for (; tItr != tEnd; ++tItr) {
                                prev.requestNumericThreshold(tItr->first, tItr->second, thresholdItr->second.second);
                            }
                        }
                    }
                }
            }
            
            if (!assignmentMatched) {
                
                if (debug) {
                    cout << "  * Not using assignment" << endl;
                }
                
                list<pair<int,double> > subTerms;
                
                if (thresholdItr->first < 2 * FluentLayerEntry::pneCount) {
                    subTerms.push_back(make_pair(thresholdItr->first, thresholdItr->second.first));
                } else {
                    const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(thresholdItr->first);
                    double avRemaining = thresholdItr->second.first;
                    
                    /*for (int s = 0; s < currAV.size; ++s) {
                        const map<int,double>::const_iterator aaItr = alreadyAchieved.find(currAV.fluents[s]);
                        if (aaItr != alreadyAchieved.end()) {
                            avRemaining -= aaItr->second * currAV.weights[s];
                        }
                    }*/
                    
                    breakApart(currAV.fluents, currAV.weights, currAV.size, currAV.constant,
                               true, avRemaining,
                               preconditionsIn, EPSILON, DBL_MAX, subTerms);
                }
                
                list<pair<int,double> >::const_iterator tItr = subTerms.begin();
                const list<pair<int,double> >::const_iterator tEnd = subTerms.end();
                
                for (; tItr != tEnd; ++tItr) {
                    
                    double residual = tItr->second;
                    const double acceptableMinimum = previousFluentLayer->second->values()[tItr->first];

                    if (debug) {
                        cout << "- Considering ways of ";
                        if (tItr->first < FluentLayerEntry::pneCount) {
                            cout << "increasing " << *(RPGBuilder::getPNE(tItr->first)) << ": must have " << residual << " by now, given " << acceptableMinimum << " previously\n";
                        } else {
                            cout << "decreasing " << *(RPGBuilder::getPNE(tItr->first - FluentLayerEntry::pneCount))  << ": must have " << -residual << " by now, given " << -acceptableMinimum << " previously\n";
                        }                                                
                    }
                                        
                                        
                    bool localAssignmentMatched = false;
                    
                    {
                        const RecordedAssignment * const assignmentUsed = preconditionsIn->second->assignmentAppliedToVariable(tItr->first);
                
                        // if it was done with assignment...
                        if (assignmentUsed && assignmentUsed->act) {
                            
                            const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[assignmentUsed->eff];
                            
                            const ActionAndHowManyTimes * const toUse = assignmentUsed->act;
                            
                            actionsUsed.push_back(make_pair(currentLayer->first,SupportingAction(toUse->actID, toUse->ts, 1, thresholdItr->second.second)));

                            if (debug) {
                                cout << "  * Using assignment by " << *(RPGBuilder::getInstantiatedOp(toUse->actID)) << endl;
                            }
                            
                            localAssignmentMatched = true;
                            
                            recordSideEffects(toUse, 1, previousFluentLayer->second->values());
                            
                            
                            double contributionToIncreaseFromDur = 0.0;
                            if (assignmentUsed->maximiseEffect) {
                                for (int s = 0; s < currEff.size; ++s) {
                                    if (currEff.variables[s] == -3) {
                                        contributionToIncreaseFromDur += (currEff.weights[s] * toUse->minDur);
                                    } else if (currEff.variables[s] == -19) {
                                        contributionToIncreaseFromDur += (currEff.weights[s] * toUse->maxDur);
                                    }
                                }
                            } else {
                                for (int s = 0; s < currEff.size; ++s) {
                                    if (currEff.variables[s] == -3) {
                                        contributionToIncreaseFromDur += (currEff.weights[s] * toUse->maxDur);
                                    } else if (currEff.variables[s] == -19) {
                                        contributionToIncreaseFromDur += (currEff.weights[s] * toUse->minDur);
                                    }
                                }
                            }
                            
                            if (currEff.size) {
                                // if assigning a value derived from other variables, we need to make sure
                                // they hold values sufficient for the desired result
                                list<pair<int,double> > subTerms;
                                breakApart(currEff.variables, currEff.weights, currEff.size, currEff.constant,
                                           assignmentUsed->maximiseEffect, thresholdItr->second.first - contributionToIncreaseFromDur,
                                           previousFluentLayer, (*payloadDurationBounds)[toUse->actID].first, (*payloadDurationBounds)[toUse->actID].second, subTerms);

                                if (!subTerms.empty()) {// duration dependent variables don't induce subterms
                                    RPGRegress & prev = goalsAtLayer[previousFluentLayer->first];
                                    
                                    list<pair<int,double> >::const_iterator tItr = subTerms.begin();
                                    const list<pair<int,double> >::const_iterator tEnd = subTerms.end();
                                    
                                    for (; tItr != tEnd; ++tItr) {
                                        prev.requestNumericThreshold(tItr->first, tItr->second, thresholdItr->second.second);
                                    }
                                }
                            }
                        }
                    }                    
                    
                    if (!localAssignmentMatched) {
                    
                        const set<int> * const instantaneousEffs = preconditionsIn->second->getInstantaneousEffectsThatIncreasedVariable(tItr->first);
                        
                        if (debug) {
                            if (instantaneousEffs && !instantaneousEffs->empty()) {
                                cout << "  * Considering instantaneous effects\n";
                            } else {
                                cout << "  * No suitable instantaneous effects\n";
                            }
                        }
                        
                        
                        if (instantaneousEffs) {
                            set<int>::const_iterator effItr = instantaneousEffs->begin();
                            const set<int>::const_iterator effEnd = instantaneousEffs->end();
                            
                            for (; effItr != effEnd && residual > acceptableMinimum; ++effItr) {
                                
                                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
                                
                                if (debug) {
                                    cout << "      - One potential effect: " << currEff << endl;
                                }
                                
                                const list<const ActionAndHowManyTimes*> & actions = preconditionsIn->second->getInstantaneousEffectsDirectlyBeforeThisLayer()[*effItr];
                                
                                bool minUsed = false;
                                double minimumEffectMagnitudeNeeded;
                                bool maxUsed = false;
                                double maximumEffectMagnitudeNeeded;
                                
                                list<const ActionAndHowManyTimes*>::const_iterator aItr = actions.begin();
                                const list<const ActionAndHowManyTimes*>::const_iterator aEnd = actions.end();
                                
                                for (; aItr != aEnd && residual > acceptableMinimum; ++aItr) {
                                    
                                    if (debug) {
                                        cout << "          > Residual: " << residual << ", Acceptable Minimum: " << acceptableMinimum << endl;
                                    }
                                    
                                    //for (int pass = 0; pass < 2 && residual > acceptableMinimum; ++pass) {
                                    
                                    {
                                        
                                        const double minEff = currEff.evaluateMin(previousFluentLayer->second->values(), (*aItr)->minDur, (*aItr)->maxDur);
                                        const double maxEff = currEff.evaluate(previousFluentLayer->second->values(), (*aItr)->minDur, (*aItr)->maxDur);
                                        
                                        if (tItr->first >= FluentLayerEntry::pneCount ? (minEff < 0 || maxEff < 0) : (minEff > 0 || maxEff > 0)) {

                                            double localEff;
                                            bool * used = 0;
                                            double * magnitudeUpdate = 0;
                                            bool minRatherThanMax = false;
                                            
                                            if (tItr->first >= FluentLayerEntry::pneCount) {
                                                if (minEff < maxEff) {
                                                    localEff = minEff;
                                                    magnitudeUpdate = &(minimumEffectMagnitudeNeeded);
                                                    used = &(minUsed);
                                                    minRatherThanMax = true;
                                                } else {
                                                    localEff = maxEff;
                                                    magnitudeUpdate = &(maximumEffectMagnitudeNeeded);
                                                    used = &(maxUsed);
                                                }
                                            } else {
                                                if (minEff > maxEff) {
                                                    localEff = minEff;
                                                    magnitudeUpdate = &(minimumEffectMagnitudeNeeded);
                                                    used = &(minUsed);
                                                    minRatherThanMax = true;
                                                } else {
                                                    localEff = maxEff;
                                                    magnitudeUpdate = &(maximumEffectMagnitudeNeeded);
                                                    used = &(maxUsed);
                                                }
                                            }
                                            
                                            double contributionToIncreaseFromDur = 0.0;
                                            
                                            if (minRatherThanMax) {
                                                for (int s = 0; s < currEff.size; ++s) {
                                                    if (currEff.variables[s] == -3) {
                                                        contributionToIncreaseFromDur += (currEff.weights[s] * (*aItr)->minDur);
                                                    } else if (currEff.variables[s] == -19) {
                                                        contributionToIncreaseFromDur += (currEff.weights[s] * (*aItr)->maxDur);
                                                    }
                                                }
                                            } else {
                                                for (int s = 0; s < currEff.size; ++s) {
                                                    if (currEff.variables[s] == -3) {
                                                        contributionToIncreaseFromDur += (currEff.weights[s] * (*aItr)->maxDur);
                                                    } else if (currEff.variables[s] == -19) {
                                                        contributionToIncreaseFromDur += (currEff.weights[s] * (*aItr)->minDur);
                                                    }
                                                }
                                            }
                                            
                                            
                                            int applyTimes = (*aItr)->howManyTimes;
                                            
                                            
                                            if (debug) {
                                                cout << "          + Effect can be obtained " << applyTimes << " time(s) using ";
                                                if ((*aItr)->ts == Planner::E_AT_START) {
                                                    cout << "start of ";
                                                } else {
                                                    cout << "end of ";
                                                }
                                                cout << *(RPGBuilder::getInstantiatedOp((*aItr)->actID)) << ", yielding an effect value of " << localEff << endl;
                                            }
                                            if (tItr->first >= FluentLayerEntry::pneCount) {
                                                if (localEff == -DBL_MAX) {
                                                    applyTimes = 1;
                                                    residual = -DBL_MAX;                                        
                                                } else if (applyTimes == INT_MAX) {
                                                    const double at = (-(residual - acceptableMinimum)) / localEff;
                                                    applyTimes = at;
                                                    if (at > applyTimes) { // round up the number of times we need apply the action
                                                        ++applyTimes;
                                                    }
                                                    residual -= -(applyTimes * localEff);
                                                } else if (applyTimes * localEff <= (-(residual - acceptableMinimum))) {
                                                    const double at = (-(residual - acceptableMinimum)) / localEff;
                                                    applyTimes = at;
                                                    if (at > applyTimes) { // round up the number of times we need apply the action
                                                        ++applyTimes;
                                                    }
                                                    residual -= -(applyTimes * localEff);
                                                } else {
                                                    residual -= -(applyTimes * localEff);
                                                }
                                            } else {
                                                if (localEff == DBL_MAX) {
                                                    applyTimes = 1;
                                                    residual = -DBL_MAX;                                        
                                                } else if (applyTimes == INT_MAX) {
                                                    const double at = (residual - acceptableMinimum) / localEff;
                                                    applyTimes = at;
                                                    if (at > applyTimes) { // round up the number of times we need apply the action
                                                        ++applyTimes;
                                                    }
                                                    residual -= applyTimes * localEff;
                                                } else if (applyTimes * localEff >= (residual - acceptableMinimum)) {
                                                    const double at = (residual - acceptableMinimum) / localEff;
                                                    applyTimes = at;
                                                    if (at > applyTimes) { // round up the number of times we need apply the action
                                                        ++applyTimes;
                                                    }
                                                    residual -= applyTimes * localEff;
                                                } else {
                                                    residual -= applyTimes * localEff;
                                                }
                                            }

                                            if (debug) {
                                                cout << "Going to apply it " << applyTimes << " times, leaving a residual of " << residual << endl;
                                            }

                                            if (localEff == DBL_MAX) {
                                                if (*used) {
                                                    if (minRatherThanMax) {
                                                        if (*magnitudeUpdate > residual - acceptableMinimum - contributionToIncreaseFromDur) {
                                                            *magnitudeUpdate = residual - acceptableMinimum - contributionToIncreaseFromDur;
                                                        }
                                                    } else {
                                                        if (*magnitudeUpdate < residual - acceptableMinimum - contributionToIncreaseFromDur) {
                                                            *magnitudeUpdate = residual - acceptableMinimum - contributionToIncreaseFromDur;
                                                        }
                                                    }
                                                } else {
                                                    *magnitudeUpdate = residual - acceptableMinimum - contributionToIncreaseFromDur;
                                                }
                                            } else {
                                                if (*used) {
                                                    if (minRatherThanMax) {
                                                        if (*magnitudeUpdate < localEff - contributionToIncreaseFromDur) {
                                                            *magnitudeUpdate = localEff - contributionToIncreaseFromDur;
                                                        }
                                                    } else {
                                                        if (*magnitudeUpdate > localEff - contributionToIncreaseFromDur) {
                                                            *magnitudeUpdate = localEff - contributionToIncreaseFromDur;
                                                        }
                                                    }
                                                } else {
                                                    *magnitudeUpdate = localEff - contributionToIncreaseFromDur;
                                                }
                                            }
                                            
                                            
                                            actionsUsed.push_back(make_pair(currentLayer->first,SupportingAction((*aItr)->actID, (*aItr)->ts, applyTimes, thresholdItr->second.second)));
                                            
                                            recordSideEffects(*aItr, applyTimes, previousFluentLayer->second->values());
                                            
                                            *used = true;
                                        }                                
                                    }
                                }
                                
                                if (maxUsed) {
                                    
                                    list<pair<int,double> > inputSubTerms;
                                    breakApart(currEff.variables, currEff.weights, currEff.size, currEff.constant,
                                               true, maximumEffectMagnitudeNeeded,
                                               previousFluentLayer, 0.001, DBL_MAX, inputSubTerms);
                                               
                                   if (!inputSubTerms.empty()) {// duration dependent variables don't induce subterms
                                       RPGRegress & prev = goalsAtLayer[previousFluentLayer->first];
                                       
                                       list<pair<int,double> >::const_iterator t2Itr = inputSubTerms.begin();
                                       const list<pair<int,double> >::const_iterator t2End = inputSubTerms.end();
                                       
                                       for (; t2Itr != t2End; ++t2Itr) {
                                           prev.requestNumericThreshold(t2Itr->first, t2Itr->second, thresholdItr->second.second);
                                       }
                                    }
                                }
                                
                                    
                                if (minUsed) {
                                    list<pair<int,double> > inputSubTerms;
                                    breakApart(currEff.variables, currEff.weights, currEff.size, currEff.constant,
                                               false, -minimumEffectMagnitudeNeeded,
                                               previousFluentLayer, 0.001, DBL_MAX, inputSubTerms);
                                               
                                   if (!inputSubTerms.empty()) {// duration dependent variables don't induce subterms
                                       RPGRegress & prev = goalsAtLayer[previousFluentLayer->first];
                                       
                                       list<pair<int,double> >::const_iterator t2Itr = inputSubTerms.begin();
                                       const list<pair<int,double> >::const_iterator t2End = inputSubTerms.end();
                                       
                                       for (; t2Itr != t2End; ++t2Itr) {
                                           prev.requestNumericThreshold(t2Itr->first, t2Itr->second, thresholdItr->second.second);
                                       }
                                    }
                                }
                            }
                            
                        }
                        
                        if (residual > acceptableMinimum) {
                            if (debug) {
                                cout << "Residual = " << residual << ", acceptable minimum = " << acceptableMinimum << endl;
                            }
                            // must need some integrated effects, too
                            
                            map<int, map<double, list<const ActionAndHowManyTimes*> > > & ieffs = preconditionsIn->second->getIntegratedEffectsDirectlyBeforeThisLayer();
                            
                            map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator ieItr;
                            
                            const bool keepPositive = tItr->first < FluentLayerEntry::pneCount;
                            
                            if (keepPositive) {
                                ieItr = ieffs.find(tItr->first);
                            } else {
                                ieItr = ieffs.find(tItr->first - FluentLayerEntry::pneCount);
                            }
                            
                            
                                        
                            if (ieItr == ieffs.end()) {
                                if (debug) {
                                    cout << "  * No suitable integrated effects\n";
                                }                        
                            } else {
                                if (debug) {
                                    cout << "  * Considering integrated effects\n";
                                }
                                
                                map<double, list<const ActionAndHowManyTimes*> >::const_iterator effItr = ieItr->second.begin();
                                const map<double, list<const ActionAndHowManyTimes*> >::const_iterator effEnd = ieItr->second.end();
                                
                                for (; effItr != effEnd && residual > acceptableMinimum; ++effItr) {
                                    if (keepPositive) {
                                        if (effItr->first < 0) continue;
                                    } else {
                                        if (effItr->first > 0) continue;
                                    }
                                    
                                    const double eff = fabs(effItr->first);
                                    
                                    list<const ActionAndHowManyTimes*>::const_iterator aItr = effItr->second.begin();
                                    const list<const ActionAndHowManyTimes*>::const_iterator aEnd = effItr->second.end();
                                    
                                    for (; aItr != aEnd && residual > acceptableMinimum; ++aItr) {
                                        double needed = (residual - acceptableMinimum) / eff;
                                        
                                        int nInt = needed;
                                        if (needed > nInt) { // round up
                                            ++nInt;
                                        }
                                        
                                        if (nInt > (*aItr)->howManyTimes) {
                                            residual -= (*aItr)->howManyTimes * eff;
                                            actionsUsed.push_back(make_pair(currentLayer->first,SupportingAction((*aItr)->actID, (*aItr)->ts, (*aItr)->howManyTimes, thresholdItr->second.second)));
                                            recordSideEffects(*aItr, (*aItr)->howManyTimes, previousFluentLayer->second->values());
                                        } else {
                                            residual -= nInt * eff;
                                            actionsUsed.push_back(make_pair(currentLayer->first,SupportingAction((*aItr)->actID, (*aItr)->ts, nInt, thresholdItr->second.second)));
                                            recordSideEffects(*aItr, nInt, previousFluentLayer->second->values());
                                        }
                                    }
                                }
                                
                            }
                        }
                        
                        if (residual > acceptableMinimum) {
                            
                            if (debug) {
                                cout << "  * Needs gradient effects\n";
                            }
                            // must need some gradient effects too
                            LayerMap::iterator layerWithGradientOnThisVar = preconditionsIn;
                            
                            const bool keepPositive = (tItr->first < FluentLayerEntry::pneCount);
                            
                            map<int, map<double, list<const ActionAndHowManyTimes*> > >::const_iterator geItr;
                            
                            while (layerWithGradientOnThisVar != layers.begin()) {
                                map<int, map<double, list<const ActionAndHowManyTimes*> > > & geffs = layerWithGradientOnThisVar->second->getGradientEffectsDirectlyBeforeThisLayer();
                                if (keepPositive) {
                                    geItr = geffs.find(tItr->first);
                                } else {
                                    geItr = geffs.find(tItr->first - FluentLayerEntry::pneCount);
                                }
                                bool rightWay = false;
                                if (geItr != geffs.end()) {
                                    map<double, list<const ActionAndHowManyTimes*> >::const_iterator effItr = geItr->second.begin();
                                    const map<double, list<const ActionAndHowManyTimes*> >::const_iterator effEnd = geItr->second.end();
                                    
                                    for (; effItr != effEnd && residual > acceptableMinimum; ++effItr) {
                                        if (keepPositive) {
                                            if (effItr->first > 0) {
                                                rightWay = true;
                                                break;
                                            }
                                        } else {
                                            if (effItr->first < 0) {
                                                rightWay = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                                
                                if (rightWay) {
                                    if (debug) {
                                        cout << "    + Suitable gradient effects in layer " << layerWithGradientOnThisVar->first << endl;
                                    }                                                               
                                    break;
                                } else {
                                    if (debug) {
                                        cout << "    + No suitable gradient effects in layer " << layerWithGradientOnThisVar->first << endl;
                                    }
                                    
                                    --layerWithGradientOnThisVar;
                                }
                            }
                            
                            // there are no active gradients in fact layer 0.0, so if this happens,
                            // there's an unexplained shortfall
                            assert(layerWithGradientOnThisVar != layers.begin());
                            
                            LayerMap::iterator layerBeforeGradientOnThisVar = layerWithGradientOnThisVar;
                            --layerBeforeGradientOnThisVar;
                            
                            map<double, list<const ActionAndHowManyTimes*> >::const_iterator effItr = geItr->second.begin();
                            const map<double, list<const ActionAndHowManyTimes*> >::const_iterator effEnd = geItr->second.end();
                            
                            for (; effItr != effEnd && residual > acceptableMinimum; ++effItr) {
                                if (keepPositive) {
                                    if (effItr->first < 0) {
                                        if (debug) {
                                            cout << "    * Ignoring decrease with gradient " << effItr->first << endl;
                                        } else {
                                            cout << "    * Keeping increase with gradient " << effItr->first << endl;
                                        } 
                                        continue;
                                    }
                                } else {
                                    if (effItr->first > 0) {
                                        if (debug) {
                                            cout << "    * Ignoring increase with gradient " << effItr->first << endl;
                                        } else {
                                            cout << "    * Keeping decrease with gradient " << effItr->first << endl;
                                        } 
                                        
                                        continue;
                                    }
                                }
                                                                
                                const double eff = fabs(effItr->first);
                            
                                
                                list<const ActionAndHowManyTimes*>::const_iterator aItr = effItr->second.begin();
                                const list<const ActionAndHowManyTimes*>::const_iterator aEnd = effItr->second.end();
                                
                                for (; aItr != aEnd && residual > acceptableMinimum; ++aItr) {
                                    
                                    const EpsilonResolutionTimestamp durationOfEffect = ((*aItr)->gradientsFinishAt < preconditionsIn->first ? (*aItr)->gradientsFinishAt : preconditionsIn->first) - layerWithGradientOnThisVar->first;
                                    
                                    const double overThatTime = durationOfEffect.toDouble() * eff;
                                    
                                    const double needed = ceil(durationOfEffect.toDouble() / ((*aItr)->maxDur));
                                    
                                    if (debug) {
                                        cout << "       - Using " << needed << " of " << *(RPGBuilder::getInstantiatedOp((*aItr)->actID)) << endl;
                                    }
                                                                        
                                    residual -= overThatTime;
                                    
                                    if (!(*aItr)->alreadyInThePlan) {
                                        actionsUsed.push_back(make_pair(layerWithGradientOnThisVar->first,SupportingAction((*aItr)->actID, (*aItr)->ts, needed, thresholdItr->second.second)));
                                        recordSideEffects(*aItr, needed, layerBeforeGradientOnThisVar->second->values());
                                    }
                                }
                            }
                            
                        
                        }
                        
                        if (residual > borrowFactLayerZeroValues()[tItr->first]) {
                            LayerMap::const_iterator rollback = previousFluentLayer;
                            while (rollback->second->values()[tItr->first] > residual) {
                                --rollback;
                            }
                            ++rollback;
                            goalsAtLayer[rollback->first].requestNumericThreshold(tItr->first, residual, thresholdItr->second.second);                                        
                        }
                    }
                }
            }
        }        
        
        if (debug) {
            cout << " > Actions used: " << actionsUsed.size() << endl;
        }
    }
    
    void breakApart(const vector<int> & variables, const vector<double> & weights, const int & size, const double & constant,
                    const bool & useMaxVariables, double threshold,
                    const LayerMap::const_iterator & reachableValues, const double & minDur, const double & maxDur,
                    list<pair<int,double> > & subTerms) {
        
        if (debug) {
            cout << "Breaking apart ";
            if (!size) {
                cout << "<empty>";
            }
            for (int s = 0; s < size; ++s) {        
                if (s) cout << " + ";
                cout << weights[s] << ".";
                if (variables[s] < 0) {
                    cout << "<special>";
                } else if (variables[s] < FluentLayerEntry::pneCount) {
                    cout << *(RPGBuilder::getPNE(variables[s]));
                } else {
                    cout << "-" << *(RPGBuilder::getPNE(variables[s] - FluentLayerEntry::pneCount));
                }                
            }
            cout << " >= " << threshold - constant << endl;
        }

        threshold -= constant;
                
        const vector<double> & initValues = layers.begin()->second->values();        
        const vector<double> & values = reachableValues->second->values();
        
        double accumulatedLHS = 0.0;
        
        for (int s = 0; s < size; ++s) {
            int v = variables[s];
            double w = weights[s];
            
            if (w < 0.0) {
                w = -w;
                if (v < 0) {
                    if (v == -3) {
                        v = -19;
                    } else if (v == -19) {
                        v = -3;
                    } else {
                        cerr << "Fatal error: referring to something other than a state variable or ?duration in a precondition or effect\n";
                        exit(1);
                    }
                } else {
                    if (v < FluentLayerEntry::pneCount) {
                        v += FluentLayerEntry::pneCount;
                    } else {
                        v -= FluentLayerEntry::pneCount;
                    }
                }
            }
            
            if (!useMaxVariables) {
                if (v < 0) {
                    if (v == -3) {
                        v = -19;
                    } else if (v == -19) {
                        v = -3;
                    } else {
                        cerr << "Fatal error: referring to something other than a state variable or ?duration in a precondition or effect\n";
                        exit(1);
                    }
                } else {
                    if (v < FluentLayerEntry::pneCount) {
                        v += FluentLayerEntry::pneCount;
                    } else {
                        v -= FluentLayerEntry::pneCount;
                    }
                }
            }
                        
            if (v == -3) {
                accumulatedLHS += w * maxDur;
            } else if (v == -19) {
                accumulatedLHS += w * minDur;
            } else {
                
                assert(v >= 0);
                assert(v < 2 * FluentLayerEntry::pneCount);
            
                accumulatedLHS += w * initValues[v];
            }
        }
        
        if (debug) {
            cout << "Working upwards from LHS = " << accumulatedLHS << endl;
        }
        
        for (int s = 0; s < size && accumulatedLHS < threshold; ++s) {
                        
            int v = variables[s];
            double w = weights[s];
            
            if (v < 0) {
                if (debug) {
                    cout << "Skipping over special variable "<< v << endl;
                }
                continue;
            }
            
            if (w < 0.0) {
                w = -w;
                if (v < FluentLayerEntry::pneCount) {
                    v += FluentLayerEntry::pneCount;
                } else {
                    v -= FluentLayerEntry::pneCount;
                }
            }
            
            if (!useMaxVariables) {
                if (v < FluentLayerEntry::pneCount) {
                    v += FluentLayerEntry::pneCount;
                } else {
                    v -= FluentLayerEntry::pneCount;
                }
            }
            
            if (initValues[v] == values[v]) {
                if (debug) {
                    cout << "Skipping over unchanged variable\n";
                }
                continue;
            }
                
            
            accumulatedLHS -= w * initValues[v];
                                    
            if (debug) {
                cout << "Losing " << w * initValues[v] << ", gaining " << (values[v] * w) << endl;
            }
            
            if ( accumulatedLHS + (values[v] * w) >= threshold) {
                if (debug) {
                    cout << "That does the rest: asking for " << v << " >= " << ((threshold - accumulatedLHS) / w) << endl;
                }
                subTerms.push_back(make_pair(v, (threshold - accumulatedLHS) / w));
                return;
            } else {
                if (debug) {
                    cout << "That does some of it: asking for " << v << " >= " << values[v] << endl;
                }
                subTerms.push_back(make_pair(v, values[v]));
                accumulatedLHS += w * values[v];
            }
        }
        
    }
                                       
};


int FluentLayers::FluentLayerEntry::pneCount;

struct NextFactLayer {
    
    EpsilonResolutionTimestamp timestamp;
    
    map<EpsilonResolutionTimestamp, list<pair<int,bool> > >::iterator endActionsAppearingAtThisTime;
    map<EpsilonResolutionTimestamp, FactLayerEntry>::iterator newFactsAtThisTime;    
    bool revisitInstantaneousNumericEffects;
    bool gradientsCauseFactsToBecomeTrue;
    
    NextFactLayer() : timestamp(EpsilonResolutionTimestamp::infinite()) {
        reset();
    } 
                
    bool empty() const {
        return (timestamp == EpsilonResolutionTimestamp::infinite());
    }
    
    void reset() {
        timestamp = EpsilonResolutionTimestamp::infinite();
        revisitInstantaneousNumericEffects = false;
        gradientsCauseFactsToBecomeTrue = false;
    }
};

struct DotDetails {
    
    struct ClusterDef {
        map<string,string> nodes;
    };
    map<double, ClusterDef > factLayerNodes;
    map<double, ClusterDef > actionLayerNodes;
    
    list<string> endActionsToStarts;
    list<string> factsToActions;
    map<int, string> achieverForFact;
    
    set<int> haveAnOpenEnd;
    
    set<int> highlightedEnd;
    set<int> highlightedStart;
    
    bool rawHighlight(const string & s, const bool failureOkay=false) {
        bool found = false;
        map<double, ClusterDef >::iterator alItr = actionLayerNodes.begin();
        const map<double, ClusterDef >::iterator alEnd = actionLayerNodes.end();
        
        for (; alItr != alEnd; ++alItr) {
            map<string,string>::iterator nItr = alItr->second.nodes.find(s);
            if (nItr != alItr->second.nodes.end()) {
                nItr->second += ", color=green";
                //cout << nItr->second << endl;
                found = true;
            }
        }
        if (!failureOkay) {
            assert(found);
        }
        return found;
    }
    
    void highlightAction(const int & act, const Planner::time_spec & ts) {
        switch (ts) {
            case Planner::E_AT_START: {
                if (!highlightedStart.insert(act).second) {
                    return;
                }
                ostringstream c1;
                c1 << "act" << act << "s";
                rawHighlight(c1.str());
                break;
            }
            case Planner::E_AT_END: {
                if (!highlightedEnd.insert(act).second) {
                    return;
                }
                bool found = false;
                {
                    ostringstream c1;
                    c1 << "act" << act << "e";
                    found = rawHighlight(c1.str(),true);                    
                }
                {
                    ostringstream c1;
                    c1 << "act" << act << "ne";
                    rawHighlight(c1.str(),found);                    
                }
                break;
            }
            default: {
            }
        }
        
    }
    
    void actionMeetsFactInRP(const int & act, const Planner::time_spec & ts, const int & fact) {
        switch (ts) {
            case Planner::E_AT_START: {
                ostringstream c1;
                c1 << "\tact" << act << "s -> fact" << fact << " [color=green];\n";
                factsToActions.push_back(c1.str());
                break;
            }
            case Planner::E_AT_END: {
                if (haveAnOpenEnd.find(act) != haveAnOpenEnd.end()) {
                    ostringstream c1;
                    c1 << "\tact" << act << "ne -> fact" << fact << " [color=green];\n";
                    factsToActions.push_back(c1.str());
                    break;
                } else {
                    ostringstream c1;
                    c1 << "\tact" << act << "e -> fact" << fact << " [color=green];\n";
                    factsToActions.push_back(c1.str());
                    break;
                }
            }
            default: {
            }
        }
    };
    
    void addFactNode(const double & t, const int & fact, const bool inState=false) {
        if (RPGBuilder::isStatic(RPGBuilder::getLiteral(fact)).first) {
            return;
        }
        ostringstream c1;
        ostringstream c2;
        c1 << "fact" << fact;
        if (inState) {
            c2 << "color=red, ";
        }
        c2 << "label=\"" << *(RPGBuilder::getLiteral(fact)) << "\"";
        
        const string nn = c1.str();
        
        factLayerNodes[t].nodes[nn] = c2.str();
    }

    void addNumericFactNode(const double & t, const int & pre, const bool inState=false) {
        ostringstream c1;
        c1 << "numfact" << pre;
        const string nn = c1.str();
        
        ostringstream c;
        if (inState) {
            c << "color=red, ";
        }
        
        c << "label=\"";
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[pre];
        const int pneCount = RPGBuilder::getPNECount();
        if (currPre.LHSVariable < pneCount) {
            c << *(RPGBuilder::getPNE(currPre.LHSVariable));
            if (currPre.op == VAL::E_GREATER) {
                c << " > ";
            } else {
                c << " >= ";
            }
            c << currPre.RHSConstant;
        } else if (currPre.LHSVariable < 2 * pneCount) {
            c << *(RPGBuilder::getPNE(currPre.LHSVariable - pneCount));
            if (currPre.op == VAL::E_GREATER) {
                c << " < ";
            } else {
                c << " <= ";
            }
            if (currPre.RHSConstant == 0.0) {
                c << "0.0";
            } else {
                c << -currPre.RHSConstant;
            }
        } else {
            
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
            
            double localRHS = currPre.RHSConstant - currAV.constant;
            
            if (currAV.size == 1 && (currAV.fluents[0] >= pneCount) && (currAV.fluents[0] < (2 * pneCount))) {
                c << *(RPGBuilder::getPNE(currAV.fluents[0] - pneCount));
                if (currPre.op == VAL::E_GREATER) {
                    c << " < ";
                } else {
                    c << " <= ";
                }
                if (localRHS == 0.0) {
                    c << "0.0";
                } else {
                    c << -localRHS;
                }
            } else {
                
                for (int s = 0; s < currAV.size; ++s) {
                    if (currAV.fluents[s] < pneCount) {
                        if (currAV.weights[s] != 1.0) {
                            if (currAV.weights[s] > 0.0) {
                                c << " + " << currAV.weights[s] << "*";
                            } else {
                                c << " - " << -currAV.weights[s] << "*";
                            }                            
                        } else {
                            if (s) {
                                c << " + ";
                            }                                                                                                       
                        }
                        c << *(RPGBuilder::getPNE(currAV.fluents[s]));
                    } else {
                        if (currAV.weights[s] != 1.0) {
                            if (currAV.weights[s] > 0.0) {
                                c << " - " << currAV.weights[s] << "*";
                            } else {
                                c << " + " << -currAV.weights[s] << "*";
                            }                            
                        } else {
                            if (s) {
                                c << " - ";
                            }                                                                                                       
                        }
                        c << *(RPGBuilder::getPNE(currAV.fluents[s] - pneCount));
                    }
                }
                
                if (currPre.op == VAL::E_GREATER) {
                    c << " > ";
                } else {
                    c << " >= ";
                }
                c << localRHS;
            }
            
        }
        
        c << "\"";
        factLayerNodes[t].nodes[nn] = c.str();
    }
        
    void addActionNode(const double & t, const int & act, const Planner::time_spec & ts) {
        {
            ostringstream c1;
            ostringstream c2;
            switch (ts) {
                case Planner::E_AT: {
                    c1 << "TIL" << act;
                    break;
                }
                case Planner::E_AT_END: {
                    if (RPGBuilder::getRPGDEs(act).empty()) {
                        return;
                    }
                    c1 << "act" << act << "e";
                    c2 << "label=\"" << *(RPGBuilder::getInstantiatedOp(act)) << " end\"";
                    break;
                }
                case Planner::E_AT_START: {
                    c1 << "act" << act << "s";
                    c2 << "label=\"" << *(RPGBuilder::getInstantiatedOp(act));
                    if (!RPGBuilder::getRPGDEs(act).empty()) {
                        c2 << " start";
                    }
                    c2 << "\"";
                    break;
                }
                default: {
                    cerr << "Internal error: unexpected time specifier for action node\n";
                    exit(1);
                }
            }
            
            const string nn = c1.str();
            actionLayerNodes[t].nodes[nn] = c2.str();
        }
        
        if (ts == Planner::E_AT_END) {
            ostringstream c2;
            c2 << "act" << act << "s -> act" << act << "e;\n";
            endActionsToStarts.push_back(c2.str());
        }
        
        if (ts == Planner::E_AT) {
            return;
        }
        
        {
            const list<Literal*> & pres = (ts == Planner::E_AT_START ? RPGBuilder::getProcessedStartPropositionalPreconditions()[act] : RPGBuilder::getEndPropositionalPreconditions()[act]);
        
            list<Literal*>::const_iterator pItr = pres.begin();
            const list<Literal*>::const_iterator pEnd = pres.end();
            
            for (; pItr != pEnd; ++pItr) {
                if (RPGBuilder::isStatic(*pItr).first) {
                    continue;
                }
                addFactToActionEdge((*pItr)->getStateID(), act, ts);
            }
        }
        
        {
            const list<int> & numPres = (ts == Planner::E_AT_START ? RPGBuilder::getProcessedStartRPGNumericPreconditions()[act] : RPGBuilder::getEndRPGNumericPreconditions()[act]);
            
            list<int>::const_iterator pItr = numPres.begin();
            const list<int>::const_iterator pEnd = numPres.end();
            
            for (; pItr != pEnd; ++pItr) {
                addNumFactToActionEdge(*pItr, act, ts);
            }
        }
    }
    
    void addNeededEnd(const double & t, const int & act) {
        haveAnOpenEnd.insert(act);
        {
            ostringstream c1;
            ostringstream c2;
            c1 << "act" << act << "ne";
            c2 << "label=\"" << *(RPGBuilder::getInstantiatedOp(act)) << " n-end\"";
            
            const string nn = c1.str();
            actionLayerNodes[t].nodes[nn] = c2.str();
        }
        
        const list<Literal*> & pres = RPGBuilder::getEndPropositionalPreconditions()[act];
        
        list<Literal*>::const_iterator pItr = pres.begin();
        const list<Literal*>::const_iterator pEnd = pres.end();
        
        for (; pItr != pEnd; ++pItr) {
            if (RPGBuilder::isStatic(*pItr).first) {
                continue;
            }
            
            ostringstream c;
            c << "fact" << (*pItr)->getStateID() << " -> act" << act << "ne;\n";
            factsToActions.push_back(c.str());
        }
    }

    void addFactToActionEdge(const int & fact, const int & act, const Planner::time_spec & ts) {
        ostringstream c;
        c << "fact" << fact << " -> act" << act;
        if (ts == Planner::E_AT_END) {
            c << "e;\n";
        } else {
            c << "s;\n";
        }
        factsToActions.push_back(c.str());
    }
    
    void addNumFactToActionEdge(const int & num, const int & act, const Planner::time_spec & ts) {
        ostringstream c;
        c << "numfact" << num << " -> act" << act;
        if (ts == Planner::E_AT_END) {
            c << "e;\n";
        } else {
            c << "s;\n";
        }
        factsToActions.push_back(c.str());
    }
    
    void addActionToFactEdge(const int & act, const Planner::time_spec & ts, const int & fact) {
        ostringstream c;
        switch (ts) {
            case Planner::E_AT: {
                c << "TIL" << act;
                break;
            }
            case Planner::E_AT_END: {      
                if (haveAnOpenEnd.find(act) != haveAnOpenEnd.end()) {
                    c << "act" << act << "ne";
                } else {
                    c << "act" << act << "e";
                }
                break;
            }
            case Planner::E_AT_START: {                
                c << "act" << act << "s";
                break;
            }
            default: {
                cerr << "Internal error: unexpected time specifier for action node\n";
                exit(1);
            }
        }
        c << " -> fact" << fact << ";\n";
        achieverForFact[fact] = c.str();
    }

    
    void printLayerDef(ostream & o, const bool & factLayer, const double & atTime, const int & idx, const ClusterDef & def) const {
        o << "\tsubgraph cluster_" << idx << " {\n";
        if (factLayer) {
            o << "\t\tstyle=filled;\n";
            o << "\t\tcolor=lightgrey;\n";
            o << "\t\tnode [style=filled,color=white];\n";
            o << "\t\tlabel = \"\";\n";
            o << "\t\tc" << idx << " [label = \"fl(" << atTime << ")\"];\n";
        } else {
            o << "\t\tnode [style=filled];\n";
            o << "\t\tcolor=blue;\n";            
            o << "\t\tlabel = \"\";\n";
            o << "\t\tc" << idx << " [label = \"al(" << atTime << ")\"];\n";
        }
        
        map<string,string>::const_iterator nItr = def.nodes.begin();
        const map<string,string>::const_iterator nEnd = def.nodes.end();
        
        for (; nItr != nEnd; ++nItr) {
            o << "\t" << nItr->first << " [" << nItr->second << "];\n";
        }
        
        o << "\t}\n\n";
    };
        
};
    
    
ostream & operator <<(ostream & o, const DotDetails & d) {
    o << "digraph RPG {\n";
    o << "\trankdir = LR;\n";
    int cluster = 0;
    
    map<double, DotDetails::ClusterDef >::const_iterator flItr = d.factLayerNodes.begin();
    const map<double, DotDetails::ClusterDef >::const_iterator flEnd = d.factLayerNodes.end();
    
    map<double, DotDetails::ClusterDef >::const_iterator alItr = d.actionLayerNodes.begin();
    const map<double, DotDetails::ClusterDef >::const_iterator alEnd = d.actionLayerNodes.end();
    
    while (flItr != flEnd && alItr != alEnd) {
        if (alItr->first - flItr->first > 0.0005) {
            d.printLayerDef(o, true, flItr->first, cluster, flItr->second);
            if (cluster) {
                o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
            }
            ++flItr;
        } else if (flItr->first - alItr->first > 0.0005) {
            d.printLayerDef(o, false, alItr->first, cluster, alItr->second);
            if (cluster) {
                o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
            }                        
            ++alItr;
        } else {
            d.printLayerDef(o, true, flItr->first, cluster, flItr->second);
            ++flItr;
            if (cluster) {
                o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
            }
            ++cluster;
            d.printLayerDef(o, false, alItr->first, cluster, alItr->second);
            ++alItr;                
            if (cluster) {
                o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
            }
        }
        
        ++cluster;
    }
    
    for (; flItr != flEnd; ++flItr, ++cluster) {
        d.printLayerDef(o, true, flItr->first, cluster, flItr->second);
        if (cluster) {
            o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
        }
        
    }
    
    for (; alItr != alEnd; ++alItr, ++cluster) {
        d.printLayerDef(o, false, alItr->first, cluster, alItr->second);
        if (cluster) {
            o << "\tc" << cluster - 1 << " -> c" << cluster << " [ltail=cluster_" << cluster-1 << ", lhead=cluster_" << cluster << "];\n";
        }
        
    };
   
    {
        list<string>::const_iterator nItr = d.endActionsToStarts.begin();
        const list<string>::const_iterator nEnd = d.endActionsToStarts.end();
        
        for (; nItr != nEnd; ++nItr) {
            o << "\t" << *nItr;
        }
        
        o << "\n";
    }
    
    {
        list<string>::const_iterator nItr = d.factsToActions.begin();
        const list<string>::const_iterator nEnd = d.factsToActions.end();
        
        for (; nItr != nEnd; ++nItr) {
            o << "\t" << *nItr;
        }

        o << "\n";
    }
    
    map<int, string>::const_iterator aItr = d.achieverForFact.begin();        
    const map<int, string>::const_iterator aEnd = d.achieverForFact.end();
    
    for (; aItr != aEnd; ++aItr) {
        o << "\t" << aItr->second;
    }
            
    o << "}\n\n";
                    
    return o;
}


class RPGHeuristic::Private
{

public:
    
    Private(const bool & b,
            vector<list<Literal*> > * atse,
            vector<list<Literal*> > * atee,
            vector<list<pair<int, Planner::time_spec> > > * eta,
            vector<list<Literal*> > * atsne,
            vector<list<Literal*> > * atene,
            vector<list<pair<int, Planner::time_spec> > > * neta,
            vector<list<pair<int, Planner::time_spec> > > * pta,
            vector<list<Literal*> > * atsp,
            vector<list<Literal*> > * ati,
            vector<list<Literal*> > * atep,
            vector<list<RPGBuilder::NumericEffect> > * atnuse,
            vector<list<RPGBuilder::NumericEffect> > * atnuee,
            vector<list<int> > * atrnuse,
            vector<list<int> > * atrnuee,
            vector<list<int> > * atnusp,
            vector<list<int> > * atnui,
            vector<list<int> > * atnuep,
            vector<list<int> > * atpnuep,
            vector<int> * iusp,
            vector<int> * iuip,
            vector<int> * iuep,
            vector<EpsilonResolutionTimestamp> * ail,
            vector<EpsilonResolutionTimestamp> * ailr,
            vector<pair<int, Planner::time_spec> > * ab,
            vector<pair<int, Planner::time_spec> > * abr,
            vector<EpsilonResolutionTimestamp> * negail,
            vector<EpsilonResolutionTimestamp> * negailr,
            vector<pair<int, Planner::time_spec> > * negab,
            vector<pair<int, Planner::time_spec> > * negabr,                    
            vector<EpsilonResolutionTimestamp> * nail,
            vector<EpsilonResolutionTimestamp> * nailr,
            vector<ActionFluentModification*> * nab,
            vector<ActionFluentModification*> * nabr,
            vector<int> * iunsp,
            vector<int> * iuni,
            vector<int> * iunep,
            vector<RPGBuilder::RPGNumericPrecondition> * rnp,
            vector<RPGBuilder::RPGNumericEffect> * rne,
            vector<list<pair<int, Planner::time_spec> > > * ppta,
            vector<list<pair<int, Planner::time_spec> > > * nppta,
            vector<list<Literal*> > * atpsp,
            vector<int> * iupsp,
            vector<int> * iupsnp,
            list<pair<int, Planner::time_spec> > * pla,
            list<pair<int, Planner::time_spec> > * onpa)
            :   actionsToStartEffects(atse),
            actionsToEndEffects(atee),
            effectsToActions(eta),
            actionsToStartNegativeEffects(atsne),
            actionsToEndNegativeEffects(atene),
            negativeEffectsToActions(neta),
            preconditionsToActions(pta),
            actionsToProcessedStartPreconditions(atpsp),
            actionsToStartPreconditions(atsp),
            actionsToInvariants(ati),
            actionsToEndPreconditions(atep),
            actionsToNumericStartEffects(atnuse),
            actionsToNumericEndEffects(atnuee),
            actionsToRPGNumericStartEffects(atrnuse),
            actionsToRPGNumericEndEffects(atrnuee),
            actionsToNumericStartPreconditions(atnusp),
            actionsToNumericInvariants(atnui),
            actionsToNumericEndPreconditions(atnuep),
            actionsToProcessedStartNumericPreconditions(atpnuep),
            initialUnsatisfiedStartPreconditions(iusp),
            initialUnsatisfiedInvariants(iuip),
            initialUnsatisfiedEndPreconditions(iuep),
            #ifdef POPF3ANALYSIS
            achieverDetails(ail->size()),
            isAGoalFactWithIndependentAchivementCosts(ail->size()),
            #else
            achievedInLayer(ail),
            achievedInLayerReset(ailr),
            achievedBy(ab),
            achievedByReset(abr),
            #endif
            negativeAchievedInLayer(negail),
            negativeAchievedInLayerReset(negailr),
            negativeAchievedBy(negab),
            negativeAchievedByReset(negabr),
            numericAchievedInLayer(nail),
            numericAchievedInLayerReset(nailr),
            numericAchievedBy(nab),
            numericAchievedByReset(nabr),
            initialUnsatisfiedNumericStartPreconditions(iunsp),
            initialUnsatisfiedNumericInvariants(iuni),
            initialUnsatisfiedNumericEndPreconditions(iunep),
            rpgNumericPreconditions(rnp),
            rpgNumericEffects(rne),
            processedPreconditionsToActions(ppta),
            processedNumericPreconditionsToActions(nppta),
            initialUnsatisfiedProcessedStartPreconditions(iupsp),
            initialUnsatisfiedProcessedStartNumericPreconditions(iupsnp),
            preconditionlessActions(pla),
            onlyNumericPreconditionActions(onpa),
            deleteArrays(b), expandFully(false), doneIntegration(false), evaluateDebug(false) {

            
        earliestPropositionPOTimes = vector<EpsilonResolutionTimestamp>(ail->size(), EpsilonResolutionTimestamp::undefined());
        earliestNumericPOTimes = vector<EpsilonResolutionTimestamp>(RPGBuilder::getPNECount(), EpsilonResolutionTimestamp::undefined());
//            earliestNumericPrePOTimes = vector<double>(numericAchievedInLayer->size());
        
        numericIsTrueInState.resize(numericAchievedInLayer->size(), false);

    }


    struct EndPrecRescale {
        int ID;
        int var;
        double offset;
        double totalchange;
        double duration;

        EndPrecRescale(const int & v, const double & off, const double & tc, const double & dur) : var(v), offset(off), totalchange(tc), duration(dur) {};

        EndPrecRescale() {};

        EndPrecRescale(const EndPrecRescale & e, const double & remaining) : var(e.var), offset(e.offset), totalchange(e.totalchange *(remaining / duration)), duration(remaining) {};

        bool operator <(const EndPrecRescale & r) const;

        bool isSatisfied(const vector<double> & tab) const {
            return (tab[var] >= totalchange + offset);
        }

    };

    
    class BuildingPayload
    {

    public:

        DotDetails dot;
        
        const MinimalState & startState;
        const list<StartEvent> * startEventQueue;
        
        vector<pair<double,double> > actionDurations;
        
        vector<int> startPreconditionCounts;
        vector<int> endPreconditionCounts;
        vector<int> numericStartPreconditionCounts;
        vector<int> numericEndPreconditionCounts;
        
        vector<vector<NNF_Flat*> > initialUnsatisfiedPreferenceConditions;
        map<EpsilonResolutionTimestamp, list<int> > becomesUnreachableAtLayer;
        
        /** @brief This contains the layer in which the goal/trigger (0/1) of the indexed preference became true. */
        vector<vector<EpsilonResolutionTimestamp> > preferencePartTrueAtLayer;
        
        /** @brief Preferences violated by each start action.  First part of pair: preconditions.  Second part of pair: itself. */
        vector<ActionViolationData> startActionCosts;
        
        /** @brief Preferences violated by each end action.  First part of pair: preconditions.  Second part of pair: itself. */
        vector<ActionViolationData> endActionCosts;
        
        /** @brief Preferences violated by each TIL. */
        vector<ActionViolationData> tilCosts;
        
        /** @brief Status of each preference. If it's unsatisfied in the RPG, it has to be unsatisfied in the LP, too. */
        vector<AutomatonPosition::Position> optimisticPrefStatus;
        
        #ifdef POPF3ANALYSIS
        /* The actions waiting for the costs of their preconditions to be reduced, before they're considered applicable. */
        set<pair<int,Planner::time_spec> > actionsWaitingForForLowerCostPreconditions;        
        #endif

        /** @brief Garbage collection for <code>FactLayer::endOfJustApplied</code>. */
        list<pair<set<int>, set<int> > > setsToForbid;
        
        FactLayerMap factLayers;
        FluentLayers fluentLayers;
        map<double, map<int, list<ActionFluentModification> >, EpsilonComp> fluentModifications;
        
        /** @brief Actions that end at the given time.
         *
         * Each entry on the list pairs an action ID with <code>true</code> if it's not appeared in the RPG before, or <code>false</code> otherwise.
         */
        map<EpsilonResolutionTimestamp, list<pair<int,bool> > > endActionsAtTime;

        /** @brief Find the timestamp of the next fact layer to visit.
         * 
         * This is based on the earliest interesting point out of:
         *  - new propositional facts/numeric preconditions just added by actions
         *  - the ends of actions which have been scheduled to appear
         *  - new facts due to TILs
         *  - the next point at which a numeric precondition becomes satisfied based on
         *    the available continuous effects
         *
         *  @param currTS  The current timestamp (that of the last fact last layer visited)
         *  @param next    A reference to a <code>NextFactLayer</code> object, which is updated
         *                 to contain the iterators and timestamp for the next layer to visit.
         */
        void nextThingToVisit(const EpsilonResolutionTimestamp & currTS, NextFactLayer & next) {
           
            const bool debug = (Globals::globalVerbosity & 64);
            next.reset();
            next.endActionsAppearingAtThisTime = endActionsAtTime.end();
            next.newFactsAtThisTime = factLayers.end();
            
            if (debug) {
                cout << "Working out when the next thing to happen is, based on a current time of " << currTS << endl;
            }
            
            const map<EpsilonResolutionTimestamp, list<pair<int,bool> > >::iterator eaItr = endActionsAtTime.begin();
            if (eaItr != endActionsAtTime.end()) {
                next.endActionsAppearingAtThisTime = eaItr;
                next.timestamp = eaItr->first;
                                                               
                if (debug) {
                    cout << "Next action layer could occur alongside actions applicable due to fact layer " << next.timestamp << endl;
                }
                if (next.timestamp.isEpsilonAhead(currTS)) {
                    if (debug) {
                        cout << " - i.e. epsilon ahead of now\n";
                    }
                }                
            }
            
            const FactLayerMap::iterator flItr = factLayers.begin();
            if (flItr != factLayers.end()) {
                const bool isEpsilonLater = flItr->first.isEpsilonAhead(currTS);
                if (debug) {                    
                    if (isEpsilonLater) {
                        cout << " -> Next fact layer is at " << flItr->first << ": epsilon later\n";
                    } else {
                        cout << " -> Next fact layer is at " << flItr->first << ": not epsilon later\n";
                    }
                }
                if (isEpsilonLater) {
                    if (debug) {
                        cout << "Next fact layer would be " << flItr->first << ", i.e. epsilon after now - keeping\n";
                    }
                    next.newFactsAtThisTime = flItr;
                    if (!next.timestamp.isEpsilonAhead(currTS)) {
                        // if the next thing to visit wasn't epsilon in the future
                        // then it's later than this - make sure the iterator is wiped                        
                        next.endActionsAppearingAtThisTime = endActionsAtTime.end();
                        next.timestamp = flItr->first;
                    }                    
                } else { // if the facts are greater than epsilon ahead, and so is the other option so far (if any)
                    if (next.timestamp == flItr->first) {
                        // the same time point
                        next.newFactsAtThisTime = flItr;
                        if (debug) {
                            cout << "Next fact layer would be at " << flItr->first << ", i.e. the same time as the end actions\n";
                        }
                        
                    } else if (flItr->first < next.timestamp) {
                        // this is sooner than the point at which ends of actions appear
                        if (debug) {
                            cout << "Next fact layer would be at " << flItr->first << ", i.e. sooner than the end actions, so not visiting those for now\n";
                        }
                                                                        
                        next.endActionsAppearingAtThisTime = endActionsAtTime.end();
                        next.newFactsAtThisTime = flItr;
                        next.timestamp = flItr->first;
                    } else {
                        if (debug) {
                            cout << "Next fact layer would be " << flItr->first << ", later than the end actions need\n";
                        }
                    }
                }
            }
            
            bool isToRecalculate = false;
            bool isDueToGradients = false;
            const pair<EpsilonResolutionTimestamp,bool> fluentLayersWantToRevisit = fluentLayers.nextLayerWouldBeAt(currTS, isToRecalculate, isDueToGradients);
            
            if (fluentLayersWantToRevisit.first != EpsilonResolutionTimestamp::infinite() ) {

                if (fluentLayersWantToRevisit.second) {
                    
                    next.revisitInstantaneousNumericEffects = isToRecalculate;
                    next.gradientsCauseFactsToBecomeTrue = isDueToGradients;
                    
                    if (next.timestamp.isEpsilonAhead(currTS)) {
                        if (debug) {
                            if (next.revisitInstantaneousNumericEffects) {
                                cout << "Also revisiting effects at the time epsilon from now\n";
                            } else {
                                cout << "Also revisiting preconditions that have become true due to gradients, epsilon from now\n";
                            }
                        }
                    } else {
                        if (debug) {
                            if (next.revisitInstantaneousNumericEffects) {
                                cout << "Revisiting effects at the time epsilon from now (" << currTS << " -> " << fluentLayersWantToRevisit.first << "), ignoring other later options\n";
                            } else {
                                cout << "Also revisiting preconditions that have become true due to gradients, epsilon from now; ignoring other later options\n";
                            }
                        }
                        next.endActionsAppearingAtThisTime = endActionsAtTime.end();
                        next.newFactsAtThisTime = factLayers.end();
                        next.timestamp = fluentLayersWantToRevisit.first;
                    }
                } else {
                    
                    if (next.timestamp.isEpsilonAhead(currTS)) {
                        if (debug) {
                            cout << "Ignoring fluent-layer update at " << fluentLayersWantToRevisit.first << ", is later than the other options that are only epsilon ahead\n";
                        }
                        assert(next.timestamp < fluentLayersWantToRevisit.first);
                    } else {
                        
                        if (fluentLayersWantToRevisit.first > next.timestamp) {
                            if (debug) {
                                cout << "Ignoring fluent-layer update at " << fluentLayersWantToRevisit.first << ", is later than the other options\n";
                            }
                        } else if (fluentLayersWantToRevisit.first == next.timestamp) {
                            next.revisitInstantaneousNumericEffects = isToRecalculate;
                            next.gradientsCauseFactsToBecomeTrue = isDueToGradients;
                            if (debug) {
                                cout << "Fluent-layer update at " << fluentLayersWantToRevisit.first << ", alongside the other options\n";
                            }                            
                        } else {
                            next.endActionsAppearingAtThisTime = endActionsAtTime.end();
                            next.newFactsAtThisTime = factLayers.end();
                            next.timestamp = fluentLayersWantToRevisit.first;
                            
                            next.revisitInstantaneousNumericEffects = isToRecalculate;
                            next.gradientsCauseFactsToBecomeTrue = isDueToGradients;
                            if (debug) {
                                cout << "Fluent-layer update at " << fluentLayersWantToRevisit.first << ", earlier than the other options\n";
                            }
                        }
                    }
                }
            }
            
            if (debug) {
                cout << "After that: timestamp of next layer is " << next.timestamp << endl;
            }
        }
        
        vector<EpsilonResolutionTimestamp> startActionSchedule;
        vector<EpsilonResolutionTimestamp> endActionSchedule;
        vector<EpsilonResolutionTimestamp> openEndActionSchedule;

        const map<int, set<int> > & startedActions;
        int unsatisfiedGoals;
        int unappearedEnds;
        #ifdef NDEBUG
        inline void markEndAppeared(const int & actID, const EpsilonResolutionTimestamp & ts) {
            --unappearedEnds;
            if (openEndActionSchedule[actID].isUndefined() || ts > openEndActionSchedule[actID]) {
                openEndActionSchedule[actID] = ts;
            }
        }
        #else
        set<int> unappearedEndSet;
        void markEndAppeared(const int & actID, const EpsilonResolutionTimestamp & ts) {
            set<int>::const_iterator ueItr = unappearedEndSet.find(actID);
            assert(ueItr != unappearedEndSet.end());
            unappearedEndSet.erase(ueItr);
            --unappearedEnds;
            if (openEndActionSchedule[actID].isUndefined() || ts > openEndActionSchedule[actID]) {
                openEndActionSchedule[actID] = ts;
            }
        }
        #endif
        
        int fakeGoalCount;
        bool tooExpensive;
        #ifdef POPF3ANALYSIS
        double withinCosts;
        #endif
        map<int, set<int> > insistUponEnds;
        map<int, int> forbiddenStart;
        map<int, int> forbiddenEnd;
        const int vCount;
        const int avCount;

        const vector<double> & minTimestamps;
        const EpsilonResolutionTimestamp stateTS;
        
        list<ActionSegment> & helpfulActions;

        map<int, double> earliestStartOf;

        map<int, pair<EpsilonResolutionTimestamp, EpsilonResolutionTimestamp> > propositionMustBeDeletedAddedAfter;

        list<pair<set<int>, set<int> > > gc;

        /** @brief The cost of deleting a fact (from always constraints).  Set details which prefs would be broken.
         */
        map<int, set<int> > prefCostOfDeletingFact;
        
        /** @brief The cost of adding a fact (from sometime before/after constraints).
        */
        map<int, AddingConstraints > prefCostOfAddingFact;

        /** @brief The cost of changing a numeric value (from always constraints).
         * 
         *  The set details which prefs would be broken by a change of the key to the second map.
         */
        map<int, map<double, set<int> > > prefCostOfChangingNumberA;

        /** @brief The cost of changing a numeric value (from sometime before/after constraints).
         */
        map<int, map<double, AddingConstraints > > prefCostOfChangingNumberB;
        
        /** @brief A map from preferences to which (applicable) actions would violate them, were they to be applied.
         */
        map<int, set<pair<int, Planner::time_spec> > > preferenceWouldBeViolatedByAction;
        
        /** @brief A map from actions to which preferences to satisfy before applying them.
         */
        map<pair<int, Planner::time_spec>, list<pair<int,bool> > > preferencePartsToSatisfyBeforeAction;
        
        double rpgGoalPrefViolation;
        double goalPrefViolationAtLastLayer;

        /** @brief The first layer at which all goals appeared. */
        EpsilonResolutionTimestamp admissibleMakespanEstimate;
        
        /** @brief The maximum cost any remaining action can have.
         * 
         * Right now this is only used to set min/max action durations on actions with duration-dependent costs.
         */
        double remainingCostLimit;
        
        vector<bool> abstractFactCurrentlyTrue;
        
        BuildingPayload(const MinimalState & theState, const list<StartEvent> * seq,
                        vector<int> & spc, vector<int> & epc, vector<int> & nspc, vector<int> & nepc,
                        const int & easSize, const int goalCount,
                        const vector<double> & mtsIn, const double & tsIn, list<ActionSegment> & haIn,
                        const double & costLimit
                       )
                : startState(theState), startEventQueue(seq),
                startPreconditionCounts(spc), endPreconditionCounts(epc),
                numericStartPreconditionCounts(nspc), numericEndPreconditionCounts(nepc),                
                fluentLayers(&actionDurations),
                startActionSchedule(easSize, EpsilonResolutionTimestamp::undefined()),
                endActionSchedule(easSize, EpsilonResolutionTimestamp::undefined()),
                openEndActionSchedule(easSize, EpsilonResolutionTimestamp::undefined()),
                startedActions(theState.startedActions),
                unsatisfiedGoals(goalCount), unappearedEnds(0), fakeGoalCount(0),
#ifdef POPF3ANALYSIS
                tooExpensive(!NumericAnalysis::getGoalNumericUsageLimits().empty()),
                withinCosts(0.0),
#endif
                vCount(theState.secondMin.size()), avCount(RPGBuilder::getAVCount()),
                minTimestamps(mtsIn), stateTS(tsIn,true), helpfulActions(haIn),
                admissibleMakespanEstimate(EpsilonResolutionTimestamp::zero()),
                remainingCostLimit(costLimit)

        {
            assert(vCount == instantiatedOp::howManyNonStaticPNEs());
            const int mtsCount = minTimestamps.size();
            for (int mts = 0; mts < mtsCount; ++mts) {
                assert(minTimestamps[mts] >= 0.0);
                EpsilonResolutionTimestamp local(minTimestamps[mts], true);
                if (local > admissibleMakespanEstimate) {
                    admissibleMakespanEstimate = local;
                }
            }

            TemporalAnalysis::doDurationLimitingEffectAnalysis(remainingCostLimit, actionDurations);
            
            const int actCount = startPreconditionCounts.size();

            for (int act = 0; act < actCount; ++act) {
                 if (actionDurations[act].first > actionDurations[act].second) {
                     ++(startPreconditionCounts[act]);
                 }
            }
        }

    };

#ifdef MDIDEBUG

#define MAKEENDMDI(dest,iv,ot,a) MaxDependentInfo dest(iv,ot,a)
#define MAKESTARTMDI(dest,a) MaxDependentInfo dest(a)


    class MaxDependentInfo
    {

    private:

        double offsetToEarlier;
        bool haveCalculated;
        double value;

        Planner::time_spec ts;
        int currAct;


        static BuildingPayload * referTo;

    public:

        static bool debug;

        static void updatePayload(BuildingPayload* const p) {
            referTo = p;
        }



        MaxDependentInfo(const double & initialValue, const double & offsetTE, const int & actID)
                : offsetToEarlier(offsetTE), haveCalculated(false), value(initialValue),
                ts(Planner::E_AT_END), currAct(actID) {


            if (debug) {
                cout << "Made MDI for " << *(RPGBuilder::getInstantiatedOp(currAct)) << " end\n";
            }

        }


        MaxDependentInfo(const int & actID)
                : offsetToEarlier(0.001), haveCalculated(false), value(0.0),
                ts(Planner::E_AT_START), currAct(actID) {

#ifdef MDIDEBUG
            if (debug) {
                cout << "Made MDI for " << *(RPGBuilder::getInstantiatedOp(currAct)) << " start\n";
            }
#endif
        }


        const double & get() {
            if (haveCalculated) return value;
            if (debug) {
                cout << "MDI for " << *currAct;
                if (ts == Planner::E_AT_START) {
                    cout << " start";
                } else {
                    cout << " end";
                }

                cout << " = max[";
            }
            /*
                            for (int pass = 0; pass < 3; ++pass) {
                                double offset;
                                const list<Literal*> * loopOn;
                                const list<int> * numLoopOn;

                                switch(pass) {
                                    case 0:
                                    {
                                        offset = offsetToEarlier;
                                        loopOn = &(RPGBuilder::getStartPropositionalPreconditions()[currAct]);
                                        numLoopOn = &(RPGBuilder::getStartPreNumerics()[currAct]);
                                        break;
                                    }

                                    case 1:
                                    {
                                        offset = offsetToEarlier - 0.001;
                                        loopOn = &(RPGBuilder::getInvariantPropositionalPreconditions()[currAct]);
                                        numLoopOn = &(RPGBuilder::getInvariantNumerics()[currAct]);
                                        break;
                                    }

                                    case 2:
                                    {
                                        if (ts == Planner::E_AT_START) {
                                            loopOn = (list<Literal*>*)0;
                                            numLoopOn = (list<int>*)0;
                                        } else {
                                            offset = 0.001;
                                            loopOn = &(RPGBuilder::getEndPropositionalPreconditions()[currAct]);
                                            numLoopOn = &(RPGBuilder::getEndPreNumerics()[currAct]);
                                        }
                                        break;
                                    }

                                }

                                if (loopOn) {

                                    list<Literal*>::const_iterator preItr = loopOn->begin();
                                    const list<Literal*>::const_iterator preEnd = loopOn->end();

                                    for (; preItr != preEnd; ++preItr) {
                                        const int ID = (*preItr)->getID();
                                        const double poTS = RPGHeuristic::Private::earliestPropositionPOTimes[ID] + offset;
                                        if (debug) {
                                            if (pass == 0) {
                                                cout << " " << *(*preItr) << "s=" << poTS;
                                            } else if (pass == 1) {
                                                cout << " " << *(*preItr) << "i=" << poTS;
                                            } else {
                                                cout << " " << *(*preItr) << "e=" << poTS;
                                            }
                                        }
                                        if (poTS > value) value = poTS;
                                    }
                                }

                                if (numLoopOn) {
                                    list<int>::const_iterator preItr = numLoopOn->begin();
                                    const list<int>::const_iterator preEnd = numLoopOn->end();

                                    for (; preItr != preEnd; ++preItr) {
                                        RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*preItr];
                                        const double poTS = RPGHeuristic::Private::earliestPointForNumericPrecondition(currPre) + offset;
                                        if (debug) {
                                            if (pass == 0) {
                                                cout << " num" << *preItr << "sn=" << poTS;
                                            } else if (pass == 1) {
                                                cout << " num" << *preItr << "in=" << poTS;
                                            } else {
                                                cout << " num" << *preItr << "en=" << poTS;
                                            }
                                        }

                                        if (poTS > value) value = poTS;
                                    }
                                }

                            }

                            const int passCount = (ts == Planner::E_AT_START ? 1 : 2);
                            for (int pass = 0; pass < passCount; ++pass) {
                                const double offset = (pass ? 0.001 : offsetToEarlier);
                                const list<Literal*> * const addLoop = (pass ? &(RPGBuilder::getEndPropositionAdds()[currAct]) : &(RPGBuilder::getStartPropositionAdds()[currAct]));
                                const list<Literal*> * const delLoop = (pass ? &(RPGBuilder::getEndPropositionDeletes()[currAct]) : &(RPGBuilder::getStartPropositionDeletes()[currAct]));
                                const list<int> * const numLoop = (pass ? &(RPGBuilder::getEndEffNumerics()[currAct]) : &(RPGBuilder::getStartEffNumerics()[currAct]));

                                {
                                    list<Literal*>::const_iterator preItr = addLoop->begin();
                                    const list<Literal*>::const_iterator preEnd = addLoop->end();

                                    for (; preItr != preEnd; ++preItr) {
                                        const int ID = (*preItr)->getID();
                                        const map<int, pair<double,double> >::iterator poRestrictItr = referTo->propositionMustBeDeletedAddedAfter.find(ID);
                                        if (poRestrictItr != referTo->propositionMustBeDeletedAddedAfter.end()) {
                                            const double poTS = poRestrictItr->second.second + offset;
                                            #ifdef MDIDEBUG
                                            if (debug) {
                                                if (pass == 0) {
                                                    cout << " " << *(*preItr) << "s+=" << poTS;
                                                } else {
                                                    cout << " " << *(*preItr) << "e-=" << poTS;
                                                }
                                            }
                                            #endif
                                            if (poTS > value) value = poTS;
                                        }
                                        #ifdef MDIDEBUG
                                        else {
                                            if (debug) {
                                                if (pass == 0) {
                                                    cout << " " << *(*preItr) << "s+=I";
                                                } else {
                                                    cout << " " << *(*preItr) << "e+=I";
                                                }
                                            }
                                        }
                                        #endif
                                    }
                                }

                                {
                                    list<Literal*>::const_iterator preItr = delLoop->begin();
                                    const list<Literal*>::const_iterator preEnd = delLoop->end();

                                    for (; preItr != preEnd; ++preItr) {
                                        const int ID = (*preItr)->getID();
                                        const map<int, pair<double,double> >::iterator poRestrictItr = referTo->propositionMustBeDeletedAddedAfter.find(ID);
                                        if (poRestrictItr != referTo->propositionMustBeDeletedAddedAfter.end()) {
                                            const double poTS = poRestrictItr->second.first + offset;
                                            #ifdef MDIDEBUG
                                            if (debug) {
                                                if (pass == 0) {
                                                    cout << " " << *(*preItr) << "s-=" << poTS;
                                                } else {
                                                    cout << " " << *(*preItr) << "e-=" << poTS;
                                                }
                                            }
                                            #endif
                                            if (poTS > value) value = poTS;
                                        }
                                        #ifdef MDIDEBUG
                                        else {
                                            if (debug) {
                                                if (pass == 0) {
                                                    cout << " " << *(*preItr) << "s-=I";
                                                } else {
                                                    cout << " " << *(*preItr) << "e-=I";
                                                }
                                            }
                                        }
                                        #endif

                                    }
                                }

                                {
                                    list<int>::const_iterator preItr = numLoop->begin();
                                    const list<int>::const_iterator preEnd = numLoop->end();

                                    for (; preItr != preEnd; ++preItr) {
                                        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*preItr];
                                        const double poTS = RPGHeuristic::Private::earliestPointForNumericEffect(currEff) + offset;
                                        #ifdef MDIDEBUG
                                        if (debug) {
                                            if (pass == 0) {
                                                cout << " " << *preItr << "sne=" << poTS;
                                            } else {
                                                cout << " " << *preItr << "ene=" << poTS;
                                            }
                                        }
                                        #endif
                                        if (poTS > value) value = poTS;

                                    }
                                }

                            }

                            if (RPGBuilder::getRPGDEs(currAct).empty()) {
                                const double poTS = earliestPointForDuration(*(RPGBuilder::getRPGDEs(currAct)[0])) + (ts == Planner::E_AT_START ? 0.001 : offsetToEarlier);

                                #ifdef MDIDEBUG
                                if (debug) {
                                    cout << " dur=" << poTS;
                                }
                                #endif
                                if (poTS > value) value = poTS;
                            }
            */

            if (debug) {
                cout << "] = " << value << "\n";
            }

            haveCalculated = true;


            return value;
        }

    };

#else

    typedef int MaxDependentInfo;

#define MAKEENDMDI(dest,iv,ot,a) MaxDependentInfo dest = a
#define MAKESTARTMDI(dest,a) MaxDependentInfo dest = a
#endif

    set<int> goals;
    set<int>::iterator gsEnd;
    set<int> goalFluents;
    set<int>::iterator gfEnd;

    vector<Literal*> literalGoalVector;

    vector<double> maxNeeded;

    vector<list<Literal*> > * const actionsToStartEffects;
    vector<list<Literal*> > * const actionsToEndEffects;
    vector<list<pair<int, Planner::time_spec> > > * const effectsToActions;

    vector<list<Literal*> > * const actionsToStartNegativeEffects;
    vector<list<Literal*> > * const actionsToEndNegativeEffects;
    vector<list<pair<int, Planner::time_spec> > > * const negativeEffectsToActions;


    vector<list<pair<int, Planner::time_spec> > > * const preconditionsToActions;

    vector<list<Literal*> > * const actionsToProcessedStartPreconditions;
    vector<list<Literal*> > * const actionsToStartPreconditions;
    vector<list<Literal*> > * const actionsToInvariants;
    vector<list<Literal*> > * const actionsToEndPreconditions;

    vector<list<RPGBuilder::NumericEffect> > * const actionsToNumericStartEffects;
    vector<list<RPGBuilder::NumericEffect> > * const actionsToNumericEndEffects;

    vector<list<int> > integratedCTSEffectVar;
    vector<list<double> > integratedCTSEffectChange;

    vector<list<int> > gradientCTSEffectVar;
    vector<list<double> > gradientCTSEffectChange;

    list<int> backgroundProcesses;
    
    vector<list<int> > * const actionsToRPGNumericStartEffects;
    vector<list<int> > * const actionsToRPGNumericEndEffects;

    vector<list<int> > * const actionsToNumericStartPreconditions;
    vector<list<int> > * const actionsToNumericInvariants;
    vector<list<int> > * const actionsToNumericEndPreconditions;
    vector<list<int> > * const actionsToProcessedStartNumericPreconditions;

    vector<int> * const initialUnsatisfiedStartPreconditions;
    vector<int> * const initialUnsatisfiedInvariants;
    vector<int> * const initialUnsatisfiedEndPreconditions;

    #ifdef POPF3ANALYSIS
    vector<list<CostedAchieverDetails> > achieverDetails;
    vector<bool> isAGoalFactWithIndependentAchivementCosts;
    vector<double> nullCosts;                  
    vector<double> currentCosts;
    #else 
    vector<EpsilonResolutionTimestamp> * const achievedInLayer;
    vector<EpsilonResolutionTimestamp> * const achievedInLayerReset;
    vector<pair<int, Planner::time_spec> > * const achievedBy;
    vector<pair<int, Planner::time_spec> > * const achievedByReset;
    #endif
    
    vector<EpsilonResolutionTimestamp> * const negativeAchievedInLayer;
    vector<EpsilonResolutionTimestamp> * const negativeAchievedInLayerReset;
    vector<pair<int, Planner::time_spec> > * const negativeAchievedBy;
    vector<pair<int, Planner::time_spec> > * const negativeAchievedByReset;
    
    vector<EpsilonResolutionTimestamp> * const numericAchievedInLayer;
    vector<EpsilonResolutionTimestamp> * const numericAchievedInLayerReset;
    vector<bool> numericIsTrueInState;
    vector<ActionFluentModification*> * const numericAchievedBy;
    vector<ActionFluentModification*> * const numericAchievedByReset;

    vector<int> * const initialUnsatisfiedNumericStartPreconditions;
    vector<int> * const initialUnsatisfiedNumericInvariants;
    vector<int> * const initialUnsatisfiedNumericEndPreconditions;

    vector<RPGBuilder::RPGNumericPrecondition> * const rpgNumericPreconditions;
    vector<RPGBuilder::RPGNumericEffect> * const rpgNumericEffects;


    vector<list<pair<int, Planner::time_spec> > > * const processedPreconditionsToActions;
    vector<list<pair<int, Planner::time_spec> > > * const processedNumericPreconditionsToActions;

    vector<int> * const initialUnsatisfiedProcessedStartPreconditions;
    vector<int> * const initialUnsatisfiedProcessedStartNumericPreconditions;

    list<pair<int, Planner::time_spec> > * const preconditionlessActions;
    list<pair<int, Planner::time_spec> > * const onlyNumericPreconditionActions;
    list<pair<int, Planner::time_spec> > noLongerForbidden;


    static vector<EpsilonResolutionTimestamp> earliestStartAllowed;
    static vector<EpsilonResolutionTimestamp> earliestEndAllowed;
    static vector<EpsilonResolutionTimestamp> latestStartAllowed;
    static vector<EpsilonResolutionTimestamp> latestEndAllowed;
    static vector<EpsilonResolutionTimestamp> deadlineAtTime;
    static vector<EpsilonResolutionTimestamp> earliestDeadlineRelevancyStart;
    static vector<EpsilonResolutionTimestamp> earliestDeadlineRelevancyEnd;

    static vector<list<int> > tilEffects;
    static vector<list<int> > tilNegativeEffects;
    static vector<list<int> > tilTemporaryNegativeEffects;
    static vector<double> tilTimes;
    static bool tilInitialised;
    static int tilCount;

    static vector<EpsilonResolutionTimestamp> earliestPropositionPOTimes;
    static vector<EpsilonResolutionTimestamp> earliestNumericPOTimes;
//    static vector<double> earliestNumericPrePOTimes;

    static vector<vector<set<int> > > actionsAffectedByFluent;

    #ifdef POPF3ANALYSIS
    static vector<vector<double> > startEffectsOnResourceLimits;
    static vector<vector<double> > dynamicStartEffectsOnResourceLimits;
    static vector<vector<double> > endEffectsOnResourceLimits;
    static vector<vector<double> > dynamicEndEffectsOnResourceLimits;
    static vector<bool> costsAreIndependentGoalCosts;
    
    /** @brief The maximum possible useful cost of a given literal.
     *
     *  If all the actions needing a fact have an effect on a limited resource, then the maximum
     *  possible cost of that fact is that such that the minimum resulting effect does not
     *  violate the resource bounds.
     */
    static vector<vector<double> > maxPermissibleCostOfAFact;
    static double metricWeightOfMakespan;
    
    #endif


    // variables to support preferences
    vector<double> prefCosts;
    
    const bool deleteArrays;
    bool expandFully;
    bool doneIntegration;
    bool evaluateDebug;

    // For convenience, we keep pointers to the information provided by the PreferenceHandler class
    
    /** @brief Pointer to the result of PreferenceHandler::getPreconditionsToPrefs();
     */
    const vector<list<LiteralCellDependency<pair<int,bool> > > >  * preconditionsToPrefs;

    /** @brief Pointer to the result of PreferenceHandler::getNegativePreconditionsToPrefs();
    */        
    const vector<list<LiteralCellDependency<pair<int,bool> > > >  * negativePreconditionsToPrefs;
    
    /** @brief Pointer to the result of PreferenceHandler::getNumericPreconditionsToPrefs();
     */    
    const vector<list<LiteralCellDependency<pair<int,bool> > > >  * numericPreconditionsToPrefs;

    
    
    #ifdef POPF3ANALYSIS
    EpsilonResolutionTimestamp getEarliestAchievedAt(const int & factID) {
        EpsilonResolutionTimestamp toReturn(EpsilonResolutionTimestamp::undefined());
        
        if (!achieverDetails[factID].empty()) {                        
            toReturn = achieverDetails[factID].front().getLayer();
        } else {
            cerr << "Warning: asking for the earliest achiever for " << *(RPGBuilder::getLiteral(factID)) << ", which never appeared in the RPG\n";
        }
        
        return toReturn;
    }
    #else
    EpsilonResolutionTimestamp & getEarliestAchievedAt(const int & factID) {
        return (*achievedInLayer)[factID];
    }
    #endif
    
    /** @brief Find which action achieved a given fact, and when.
     *
     * This function is used during solution extraction to find which action to use to achieve a given fact.
     *
     * @param  factID   The ID of the propositional fact
     * @param  layerTS  The action layer containing the action whose precondition needs to be supported
     * @param  returnAchievedIn   After execution, contains the layer in which to add the proposition as an intermediate goal
     * @param  returnAchiever     After execution, contains the achiever to use.
     */
    void getAchieverDetails(const int & factID, const EpsilonResolutionTimestamp & layerTS,
                            EpsilonResolutionTimestamp & returnAchievedIn, pair<int, Planner::time_spec> & returnAchiever) {
        
        #ifdef POPF3ANALYSIS
        if (Globals::globalVerbosity & 16) {
            cout << achieverDetails[factID].size() << " achievers, from " << achieverDetails[factID].front().getLayer() << " to " <<  achieverDetails[factID].back().getLayer() << ",";
            cout.flush();
        }
        list<CostedAchieverDetails>::const_reverse_iterator abItr = achieverDetails[factID].rbegin();
        assert(abItr != achieverDetails[factID].rend());
        while (abItr->getLayer() > layerTS) {
            ++abItr;
            #ifndef NDEBUG
            if (abItr == achieverDetails[factID].rend()) {
                cerr << std::setprecision(8) << std::fixed;
                cerr << "Internal error evaluating state no. " << RPGHeuristic::statesEvaluated << ": asking for precondition " << factID << ", " << *(RPGBuilder::getLiteral(factID)) << ", at time " << layerTS << ", but the achievers were:\n";
                list<CostedAchieverDetails>::const_iterator abfItr = achieverDetails[factID].begin();
                const list<CostedAchieverDetails>::const_iterator abfEnd = achieverDetails[factID].end();
                
                for (; abfItr != abfEnd; ++abfItr) {
                    cout << "- at " << abfItr->getLayer() << " - ";
                    if (abfItr->getAchiever().second == Planner::E_AT) {
                        cout << "TIL " << abfItr->getAchiever().first << endl;
                    } else if (abfItr->getAchiever().second == Planner::E_AT_END) {
                        cout << "end of " << *(RPGBuilder::getInstantiatedOp(abfItr->getAchiever().first)) << endl;
                    } else {
                        cout << "start of " << *(RPGBuilder::getInstantiatedOp(abfItr->getAchiever().first)) << endl;
                    }
                }
                exit(1);
            }
            #endif
        }
        //cout << "Using achiever that adds fact in layer " << abItr->layer << " to support a need in " << layerTS << endl;        
        returnAchievedIn = abItr->getLayer();
        returnAchiever = abItr->getAchiever();
        //++abItr;
        //if (abItr != achieverDetails[factID].rend()) {
        //    cout << "Previous achiever was in layer " << abItr->layer << endl;
        //}
        #else 
        returnAchievedIn = (*achievedInLayer)[factID];
        returnAchiever = (*achievedBy)[factID];
        #endif
        
    }
    
    #ifdef POPF3ANALYSIS
    void computeDynamicCost(const int & actID, const Planner::time_spec & ts, 
                            const EpsilonResolutionTimestamp & cTime) {

        static const bool localDebug = false;
        
        const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();
        
        static const int ulCount = limits.size();
        
        const vector<list<NumericAnalysis::CostAtTime*>* > & dynamicCosts
            = (ts == Planner::E_AT_END ? NumericAnalysis::getTimeDependentEndCosts()
                                   : NumericAnalysis::getTimeDependentStartCosts());
            
        if (!dynamicCosts[actID] || dynamicCosts[actID]->empty()) {
            return;
        }
                        
        if (localDebug) {
            cout << "Computing dynamic costs on " << *(RPGBuilder::getInstantiatedOp(actID)) << " at " << cTime << endl;
        }
        
        vector<double> & toUpdate = (ts == Planner::E_AT_END ? dynamicEndEffectsOnResourceLimits[actID]
                                                         : dynamicStartEffectsOnResourceLimits[actID]);
            
        for (int i = 0; i < ulCount; ++i) {
            toUpdate[i] = 0.0;
        }
        
        list<NumericAnalysis::CostAtTime*>::const_iterator costItr = dynamicCosts[actID]->begin();
        const list<NumericAnalysis::CostAtTime*>::const_iterator costEnd = dynamicCosts[actID]->end();
        
        for (; costItr != costEnd; ++costItr) {
            if ((*costItr)->start > cTime) {
                if (localDebug) {
                    cout << "Outcome [" << (*costItr)->start << "," << (*costItr)->end << "] comes later\n";
                }
                continue;
            }
            if ((*costItr)->end < cTime) {
                if (localDebug) {
                    cout << "Outcome [" << (*costItr)->start << "," << (*costItr)->end << "] came earlier\n";
                }
                continue;
            }
            
            list<NumericAnalysis::EffectDeterminedByTime*>::const_iterator deltaItr = (*costItr)->limitCosts.begin();
            const list<NumericAnalysis::EffectDeterminedByTime*>::const_iterator deltaEnd = (*costItr)->limitCosts.end();
            
            for (; deltaItr != deltaEnd; ++deltaItr) {
                if ((*deltaItr)->m == 0.0) {
                    toUpdate[(*deltaItr)->y] += (*deltaItr)->c;
                    if (localDebug) {                        
                        cout << "Increases limit " << (*deltaItr)->y << " by " << (*deltaItr)->c << " towards cap of " << NumericAnalysis::getGoalNumericUsageLimits()[(*deltaItr)->y].limit << endl;
                    }
                } else {
                    toUpdate[(*deltaItr)->y] += (*deltaItr)->m * cTime.toDouble() + (*deltaItr)->c;
                    if (localDebug) {
                        cout << "Increases limit " << (*deltaItr)->y << " by " << (*deltaItr)->m * cTime.toDouble() + (*deltaItr)->c << " towards cap of " << NumericAnalysis::getGoalNumericUsageLimits()[(*deltaItr)->y].limit << endl;
                    }
                }
            }
        }
        
    }
    #endif
    
    void addPreconditionCost(ActionViolationData & costData, const int & currAct, const Planner::time_spec & currTS, const EpsilonResolutionTimestamp & factLayerTS, BuildingPayload * payload) {
    
        costData.precViolationCost = 0.0;
        costData.preconditionsMeanViolating.clear();
        
        if (currTS != Planner::E_AT) {
        
            const list<Literal*> & actionPreconditionlist = (currTS == Planner::E_AT_START ? (*actionsToProcessedStartPreconditions)[currAct] : (*actionsToEndPreconditions)[currAct]);
            list<Literal*>::const_iterator aplItr = actionPreconditionlist.begin();
            const list<Literal*>::const_iterator aplEnd = actionPreconditionlist.end();
            
            for (; aplItr != aplEnd; ++aplItr) {
                
                if (TemporalAnalysis::getFactIsAbstract()[(*aplItr)->getStateID()]) {
                    continue;
                }
                
                list<CostedAchieverDetails> & currPreData = achieverDetails[(*aplItr)->getStateID()];
                
                list<CostedAchieverDetails>::const_reverse_iterator abItr = currPreData.rbegin();
                assert(abItr != achieverDetails[(*aplItr)->getStateID()].rend());
                while (abItr->getLayer() > factLayerTS) {
                    ++abItr;
                    assert(abItr != achieverDetails[(*aplItr)->getStateID()].rend());
                }
                
                set<int>::const_iterator viItr = abItr->preferenceCosts.needsToViolate.begin();
                const set<int>::const_iterator viEnd = abItr->preferenceCosts.needsToViolate.end();
                
                for (; viItr != viEnd; ++viItr) {
                    if (costData.preconditionsMeanViolating.insert(*viItr).second) {
                        costData.precViolationCost += prefCosts[*viItr];
                    }
                }
            }
            
            if (!RPGBuilder::getPreferences().empty()) {
                const vector<int> & actPrefs = (currTS == Planner::E_AT_START ? RPGBuilder::getStartPreferences()[currAct] : RPGBuilder::getEndPreferences()[currAct]);
                
                static int ppCount;
                
                ppCount = actPrefs.size();
                
                for (int p = 0; p < ppCount; ++p) {
                    const NNF_Flat* const f = payload->initialUnsatisfiedPreferenceConditions[actPrefs[p]][0];        
                    
                    if (f) {
                        if (!f->isSatisfied()) {
                            costData.precViolationCost += prefCosts[actPrefs[p]];
                            costData.preconditionsMeanViolating.insert(actPrefs[p]);
                            //cout << "Applying " << *(RPGBuilder::getInstantiatedOp(currAct)) << " would mean violating precondition pref " << RPGBuilder::getPreferences()[actPrefs[p]].name << ":" << actPrefs[p] << ", as it is not currently satisfied - ";
                            //cout << "cost of violation = " << prefCosts[actPrefs[p]] << endl;
                        }
                    } else {
                        if (RPGBuilder::getPreferences()[actPrefs[p]].neverTrue) {
                            costData.precViolationCost += prefCosts[actPrefs[p]];
                            costData.preconditionsMeanViolating.insert(actPrefs[p]);
                        }
                    }
                }
            }
        }        
                        
    }

    void addEffectCost(ActionViolationData & costData, const int & currAct, const Planner::time_spec & currTS, BuildingPayload * payload) {
    
        if (RPGBuilder::getPreferences().empty()) {
            costData.precViolationCost = 0.0;
            costData.effViolationCost = 0.0;
            costData.overallViolationCost = 0.0;
            return;
            
        }
        
        set<int> allViols;
        
        {
            list<Literal*> & addEffects = (currTS == Planner::E_AT
                                            ? RPGBuilder::getNonAbstractedTILVec()[currAct]->addEffects
                                            : (currTS == Planner::E_AT_START ? (*actionsToStartEffects)[currAct] : (*actionsToEndEffects)[currAct]));

            list<Literal*>::iterator addEffItr = addEffects.begin();
            const list<Literal*>::iterator addEffEnd = addEffects.end();
            
            for (; addEffItr != addEffEnd; ++addEffItr) {
                const int currEff = (*addEffItr)->getStateID();
                
                map<int, AddingConstraints >::const_iterator addConsItr = payload->prefCostOfAddingFact.find(currEff);
                if (addConsItr == payload->prefCostOfAddingFact.end()) continue;
                
                allViols.insert(addConsItr->second.addingWillViolate.begin(), addConsItr->second.addingWillViolate.end());
        
                set<int>::const_iterator vItr = addConsItr->second.addingWillViolate.begin();
                const set<int>::const_iterator vEnd = addConsItr->second.addingWillViolate.end();
                
                for (; vItr != vEnd; ++vItr) {
                    payload->preferenceWouldBeViolatedByAction[*vItr].insert(make_pair(currAct, currTS));
                }
                
                if (Globals::globalVerbosity & 32768) {
                    
                    
                    for (; vItr != vEnd; ++vItr) {
                        cout << "Add effect " << *(*addEffItr) << " Would violate " << RPGBuilder::getPreferences()[*vItr].name << ":" << *vItr << endl;
                    }
                }
            }
        }
        
        {
            list<Literal*> & delEffects = (currTS == Planner::E_AT
                                            ? RPGBuilder::getNonAbstractedTILVec()[currAct]->delEffects
                                            : (currTS == Planner::E_AT_START ? (*actionsToStartNegativeEffects)[currAct] : (*actionsToEndNegativeEffects)[currAct]));

            list<Literal*>::iterator delEffItr = delEffects.begin();
            const list<Literal*>::iterator delEffEnd = delEffects.end();
            
            for (; delEffItr != delEffEnd; ++delEffItr) {
                const int currEff = (*delEffItr)->getStateID();
                
                map<int, set<int> >::const_iterator delConsItr = payload->prefCostOfDeletingFact.find(currEff);
                if (delConsItr == payload->prefCostOfDeletingFact.end()) continue;
                
                allViols.insert(delConsItr->second.begin(), delConsItr->second.end());
                
                set<int>::const_iterator vItr = delConsItr->second.begin();
                const set<int>::const_iterator vEnd = delConsItr->second.end();
                
                for (; vItr != vEnd; ++vItr) {
                    payload->preferenceWouldBeViolatedByAction[*vItr].insert(make_pair(currAct, currTS));
                }
                
                if (Globals::globalVerbosity & 32768) {
                    set<int>::const_iterator vItr = delConsItr->second.begin();
                    const set<int>::const_iterator vEnd = delConsItr->second.end();
                    
                    for (; vItr != vEnd; ++vItr) {
                        cout << "Delete effect " << *(*delEffItr) << " Would violate " << RPGBuilder::getPreferences()[*vItr].name << ":" << *vItr << endl;
                    }
                }
                
            }
        }            
        
        costData.effectsMeanViolating.clear();
        
        std::set_difference(allViols.begin(), allViols.end(),
                            costData.preconditionsMeanViolating.begin(), costData.preconditionsMeanViolating.end(),
                            insert_iterator<set<int> >(costData.effectsMeanViolating, costData.effectsMeanViolating.begin()));
        
        double & toIncrease = costData.effViolationCost = 0.0;
        
        set<int>::const_iterator vItr = costData.effectsMeanViolating.begin();
        const set<int>::const_iterator vEnd = costData.effectsMeanViolating.end();
        
        for (; vItr != vEnd; ++vItr) {
            toIncrease += prefCosts[*vItr];
        }
        
        costData.overallViolationCost = costData.effViolationCost + costData.precViolationCost;
        costData.overallViolations = costData.preconditionsMeanViolating;
        costData.overallViolations.insert(costData.effectsMeanViolating.begin(), costData.effectsMeanViolating.end());
        
    }

    
    CostedAchieverDetails::AchieverProposalResult proposeNewAchiever(const int & factID,
                                                                     const int & actID, const Planner::time_spec & ts, const ActionViolationData & prefCosts,
                                                                     const bool & openEnd,
                                                                     const EpsilonResolutionTimestamp & cTime) {
        #ifdef POPF3ANALYSIS
        if (!achieverDetails[factID].empty() && achieverDetails[factID].back().isCostFree()) {
            // already have a cost-free achiever, can't do better
            return CostedAchieverDetails::not_added;
        }
        if (ts == Planner::E_AT || currentCosts.size() == 0) {
            // if it's a TIL, or there are no action costs
            achieverDetails[factID].push_back(CostedAchieverDetails(cTime, make_pair(actID, ts), currentCosts, PreferenceSetAndCost(true), true));
            return (achieverDetails[factID].size() > 1 ? CostedAchieverDetails::replaced_existing_achiever : CostedAchieverDetails::first_achiever);
        }
        const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();
        
        const int ulCount = limits.size();
        
        vector<double> actCosts(currentCosts);
        
        bool costFree = prefCosts.isCostFree();
        
        for (int pPass = (openEnd ? 1 : 0); pPass < 2; ++pPass) {
            
            if (pPass == 1 && ts == Planner::E_AT_START) {
                break;
            }
            
            const list<Literal*> & pres = (pPass == 1 ? (*actionsToEndPreconditions)[actID] : (*actionsToProcessedStartPreconditions)[actID]);
            list<Literal*>::const_iterator pItr = pres.begin();
            const list<Literal*>::const_iterator pEnd = pres.end();
            
            for (; pItr != pEnd; ++pItr) {
                list<CostedAchieverDetails>::const_reverse_iterator cItr = achieverDetails[(*pItr)->getStateID()].rbegin();
                while (cTime <= cItr->getLayer()) {
                    // find the achiever before now
                    ++cItr;
                    assert(cItr != achieverDetails[(*pItr)->getStateID()].rend());
                }
                for (int ul = 0; ul < ulCount; ++ul) {
                    if (cItr->costs[ul] > 0.0) {
                        if (actCosts[ul] < cItr->costs[ul]) {                        
                            actCosts[ul] = cItr->costs[ul];                        
                        }
                    } else if (cItr->costs[ul] < 0.0) {
                        if (actCosts[ul] > cItr->costs[ul]) {                        
                            actCosts[ul] = cItr->costs[ul];                        
                        }
                    }
                }
            }
            
            if (pPass == 0 && ts == Planner::E_AT_END) {
                // equivalent to an imaginary fact that the action has started: max of its preconditions, + the cost of the action itself
                
                {
                    const vector<double> & addOn = startEffectsOnResourceLimits[actID];
                
                    for (int ul = 0; ul < ulCount; ++ul) {
                        actCosts[ul] += addOn[ul];           
                        if (fabs(actCosts[ul] - currentCosts[ul]) > 0.0000001)  {
                            costFree = false;
                        }                    
                    }
                }
                {
                    const vector<double> & addOn = dynamicStartEffectsOnResourceLimits[actID];
                    
                    for (int ul = 0; ul < ulCount; ++ul) {
                        actCosts[ul] += addOn[ul];           
                        if (fabs(actCosts[ul] - currentCosts[ul]) > 0.0000001)  {
                            costFree = false;
                        }                    
                    }
                }
            }
        }
        
        {
            const vector<double> & addOn = (ts == Planner::E_AT_END ? endEffectsOnResourceLimits[actID] : startEffectsOnResourceLimits[actID]);
            
            for (int ul = 0; ul < ulCount; ++ul) {
                actCosts[ul] += addOn[ul];               
                if (fabs(actCosts[ul] - currentCosts[ul]) > 0.0000001)  {
                    costFree = false;
                }
            }
        }

        {
            const vector<double> & addOn = (ts == Planner::E_AT_END ? dynamicEndEffectsOnResourceLimits[actID] : dynamicStartEffectsOnResourceLimits[actID]);
            
            for (int ul = 0; ul < ulCount; ++ul) {
                actCosts[ul] += addOn[ul];               
                if (fabs(actCosts[ul] - currentCosts[ul]) > 0.0000001)  {
                    costFree = false;
                }
            }
        }
        
        
        if (costFree) {
            // short-circuit the rest of the code: have a zero-cost achiever, which is great
            achieverDetails[factID].push_back(CostedAchieverDetails(cTime, make_pair(actID, ts), currentCosts, PreferenceSetAndCost(true), true));
            return (achieverDetails[factID].size() > 1 ? CostedAchieverDetails::replaced_existing_achiever : CostedAchieverDetails::first_achiever);
        }
                      
        for (int ul = 0; ul < ulCount; ++ul) {
            double offset = (NumericAnalysis::getGoalNumericUsageLimits()[ul].optimisationLimit ? prefCosts.overallViolationCost : 0.0);
            switch (limits[ul].op) {
                case E_GREATER:
                {
                    if (actCosts[ul] + offset <= maxPermissibleCostOfAFact[factID][ul]) {
                        // don't even keep it as an achiever if it could never be used
                        return CostedAchieverDetails::not_added;
                    }
                    break;
                }
                case E_GREATEQ:
                {
                    if (actCosts[ul] + offset < maxPermissibleCostOfAFact[factID][ul]) {
                        // don't even keep it as an achiever if it could never be used
                        return CostedAchieverDetails::not_added;
                    }
                    break;
                }
                
                default:
                {
                    cerr << "Internal error: limits should be defined in terms of > or >=\n";
                    exit(1);
                }
            }
        }
        
        
        // if we get this far it's a plausible achiever
        
        if (achieverDetails[factID].empty()) {
            // first achiever - keep it
            achieverDetails[factID].push_back(CostedAchieverDetails(cTime, make_pair(actID, ts), actCosts, PreferenceSetAndCost(prefCosts.overallViolationCost, prefCosts.overallViolations), false));
            return CostedAchieverDetails::first_achiever;
        }
        
        // otherwise, do an admissible intersection approximation of the costs compared to the best recorded achiever
        
        bool anyImprovement = false;
        vector<double> admissibleCosts(achieverDetails[factID].back().costs);
        
        for (int ul = 0; ul < ulCount; ++ul) {
            if (admissibleCosts[ul] == currentCosts[ul]) {
                continue;
            }
            if (actCosts[ul] == currentCosts[ul]) {
                admissibleCosts[ul] = currentCosts[ul];
                anyImprovement = true;
                continue;
            }
            
            // now, both costs are non-zero
            if (actCosts[ul] > 0.0) {
                // for increases (towards upper bounds) keep the lowest increase
                if (admissibleCosts[ul] > actCosts[ul]) {
                    admissibleCosts[ul] = actCosts[ul];
                    anyImprovement = true;
                }
            } else if (actCosts[ul] < 0.0) {
                // for decreases (towards lower bounds) keep the smallest magnitude decrease
                if (admissibleCosts[ul] < actCosts[ul]) {
                    admissibleCosts[ul] = actCosts[ul];
                    anyImprovement = true;
                }
            }                
        }
        
        anyImprovement = (anyImprovement || (achieverDetails[factID].back().preferenceCosts.cost > prefCosts.overallViolationCost));
        
        if (!anyImprovement) {
            // better off in all ways to use the previous achiever
            return CostedAchieverDetails::not_added;
        }
        
        costFree = prefCosts.isCostFree();
        
        for (int ul = 0; ul < ulCount; ++ul) {
            if (fabs(admissibleCosts[ul] - currentCosts[ul]) > 0.0000001) {
                costFree = false;
                break;
            }
        }
        
        if (cTime == achieverDetails[factID].back().getLayer()) {
            achieverDetails[factID].push_back(CostedAchieverDetails(cTime, achieverDetails[factID].back().getAchiever(), admissibleCosts, PreferenceSetAndCost(prefCosts.overallViolationCost, prefCosts.overallViolations), costFree));
            return CostedAchieverDetails::same_time_as_first_achiever;
        }
        
        achieverDetails[factID].push_back(CostedAchieverDetails(cTime, achieverDetails[factID].back().getAchiever(), admissibleCosts, PreferenceSetAndCost(prefCosts.overallViolationCost, prefCosts.overallViolations), costFree));
        return CostedAchieverDetails::replaced_existing_achiever;

        
        #else
        double & currAIL = (*(achievedInLayer))[factID];
        if (currAIL == -1.0) { // this is new
            currAIL = cTime;
            (*(achievedBy))[factID] = pair<int, Planner::time_spec>(actID, ts);
            return 2;
        }
        return 0;
        #endif
    }
    
    void setDebugFlag(const bool & b) {
        evaluateDebug = b;
    }

    void buildEmptyActionFluentLookupTable() {

        const int varCount = RPGBuilder::getPNECount();
        actionsAffectedByFluent = vector<vector<set<int> > >(varCount, vector<set<int> >(2));


    }

    void populateActionFluentLookupTable() {

        static bool populated = false;

        if (populated) return;

        populated = true;

        const int actCount = actionsToNumericStartPreconditions->size();
        const int varCount = RPGBuilder::getPNECount();
        
        const vector<RPGBuilder::RPGNumericPrecondition> & preTable = RPGBuilder::getNumericPreTable();
        const vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();

        for (int pass = 0; pass < 2; ++pass) {
            const vector<list<int> > * const nowOn = (pass ? actionsToNumericEndPreconditions : actionsToProcessedStartNumericPreconditions);

            for (int a = 0; a < actCount; ++a) {
                if (RPGBuilder::rogueActions[a]) continue;
                list<int>::const_iterator pItr = ((*nowOn)[a]).begin();
                const list<int>::const_iterator pEnd = ((*nowOn)[a]).end();

                for (; pItr != pEnd; ++pItr) {
                    const RPGBuilder::RPGNumericPrecondition & currPre = preTable[*pItr];
                    for (int side = 0; side < 2; ++side) {
                        int var = (side ? currPre.RHSVariable : currPre.LHSVariable);
                        if (var == -1) continue;

                        if (var < 2 * varCount) {
                            if (var >= varCount) var -= varCount;
                            assert(var < varCount);
                            assert(var >= 0);
                            assert(!RPGBuilder::rogueActions[a]);
                            actionsAffectedByFluent[var][pass].insert(a);
                        } else {
                            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(var);

                            for (int i = 0; i < currAV.size; ++i) {
                                int lvar = currAV.fluents[i];
                                if (lvar >= varCount) lvar -= varCount;
                                assert(lvar < varCount);
                                assert(lvar >= 0);
                                assert(!RPGBuilder::rogueActions[a]);
                                actionsAffectedByFluent[lvar][pass].insert(a);
                            }
                        }
                    }
                }
            }
        }

        
         
        for (int pass = 0; pass < 2; ++pass) {
            const vector<list<int> > * const nowOn = (pass ? actionsToRPGNumericEndEffects : actionsToRPGNumericStartEffects);

            for (int a = 0; a < actCount; ++a) {
                if (RPGBuilder::rogueActions[a]) continue;



                list<int>::const_iterator eItr = ((*nowOn)[a]).begin();
                const list<int>::const_iterator eEnd = ((*nowOn)[a]).end();

                for (; eItr != eEnd; ++eItr) {
                    const RPGBuilder::RPGNumericEffect & currEff = effTable[*eItr];
                    assert(!RPGBuilder::rogueActions[a]);
                    
                    
                    
                    actionsAffectedByFluent[currEff.fluentIndex][pass].insert(a);

                    for (int i = 0; i < currEff.size; ++i) {
                        int var = currEff.variables[i];
                        if (var < 0) continue;
                        if (var >= varCount) var -= varCount;
                        actionsAffectedByFluent[var][pass].insert(a);
                    }
                }
                
                
            }
        }


        for (int a = 0; a < actCount; ++a) {
            if (RPGBuilder::rogueActions[a]) continue;
            const vector<RPGBuilder::RPGDuration*> & currDEs = RPGBuilder::getRPGDEs(a);
            if (currDEs.empty()) continue;

            for (int pass = 0; pass < 3; ++pass) {
                const list<RPGBuilder::DurationExpr*> & currList = (*(currDEs[0]))[pass];

                list<RPGBuilder::DurationExpr*>::const_iterator clItr = currList.begin();
                const list<RPGBuilder::DurationExpr*>::const_iterator clEnd = currList.end();

                for (; clItr != clEnd; ++clItr) {
                    const int loopLim = (*clItr)->variables.size();
                    for (int i = 0; i < loopLim; ++i) {
                        assert(!RPGBuilder::rogueActions[a]);
                        #ifdef STOCHASTICDURATIONS
                        int & vToUse = (*clItr)->variables[i].first;
                        #else
                        int & vToUse = (*clItr)->variables[i];
                        #endif
                        if (vToUse != -1) {
                            actionsAffectedByFluent[vToUse][0].insert(a);
                        }
                    }
                }
            }
        }



        vector<RPGBuilder::LinearEffects*> & LD = RPGBuilder::getLinearDiscretisation();

        if (!LD.empty()) {

            for (int a = 0; a < actCount; ++a) {
                if (RPGBuilder::rogueActions[a]) continue;
                const RPGBuilder::LinearEffects * const currLD = LD[a];

                if (!currLD) continue;
                const int effCount = currLD->vars.size();

                for (int eff = 0; eff < effCount; ++eff) {
                    assert(!RPGBuilder::rogueActions[a]);
                    actionsAffectedByFluent[currLD->vars[eff]][0].insert(a);
                }
            }

        }
        
        #ifdef POPF3ANALYSIS
        
        metricHasChanged();
                
        #endif
    }
    
    #ifdef POPF3ANALYSIS
    
    void metricHasChanged() {
        
        static const bool dumpActCosts = false;
        
        const int actCount = actionsToNumericStartPreconditions->size();
                        
        const vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();
         
        
        const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();
        
        const int ulCount = limits.size();
        
        nullCosts.resize(ulCount);
        
        for (int l = 0; l < ulCount; ++l) {
            nullCosts[l] = 0.0;
        }
                                                                
        TemporalAnalysis::doGlobalDurationLimitingEffectAnalysis();                                                             
        
        startEffectsOnResourceLimits.clear();
        startEffectsOnResourceLimits.resize(actCount, nullCosts);
        endEffectsOnResourceLimits.clear();
        endEffectsOnResourceLimits.resize(actCount, nullCosts);        
        
        dynamicStartEffectsOnResourceLimits.clear();
        dynamicStartEffectsOnResourceLimits.resize(actCount, nullCosts);
        dynamicEndEffectsOnResourceLimits.clear();
        dynamicEndEffectsOnResourceLimits.resize(actCount, nullCosts);        
        
        costsAreIndependentGoalCosts.clear();
        costsAreIndependentGoalCosts.resize(actCount, false);
        
        metricWeightOfMakespan = 0.0;
        
        if (RPGBuilder::getMetric()) {
            
            list<int>::const_iterator vItr = RPGBuilder::getMetric()->variables.begin();
            const list<int>::const_iterator vEnd = RPGBuilder::getMetric()->variables.end();
            
            list<double>::const_iterator wItr = RPGBuilder::getMetric()->weights.begin();
            
            for (; vItr != vEnd; ++vItr, ++wItr) {
                if (*vItr == -4) {
                    metricWeightOfMakespan = *wItr;
                    break;
                }
            }
        }        
        
        
        {            
            
            vector<double> nanCosts(ulCount);
            for (int l = 0; l < ulCount; ++l) {
                nanCosts[l] = std::numeric_limits< double >::signaling_NaN();
            }
            maxPermissibleCostOfAFact.clear();
            maxPermissibleCostOfAFact.resize(achieverDetails.size(), nanCosts);                                
            
            if (dumpActCosts) {
                cout << "Created space for cost details of " << maxPermissibleCostOfAFact.size() << " facts, and " << nanCosts.size() << " costs\n";
            }
            vector<double> hardLimits(ulCount);
            for (int l = 0; l < ulCount; ++l) {
                hardLimits[l] = limits[l].limit;
                if (limits[l].optimisationLimit && limits[l].limit > Globals::bestSolutionQuality) {
                    hardLimits[l] = Globals::bestSolutionQuality;
                }
            }
            
            set<int>::const_iterator goalItr = goals.begin();
            const set<int>::const_iterator goalEnd = goals.end();
            for (; goalItr != goalEnd; ++goalItr) {
                maxPermissibleCostOfAFact[*goalItr] = hardLimits;
            }
        
            if (!RPGBuilder::getPreferences().empty()) {
                const vector<list<LiteralCellDependency<pair<int,bool> > > > * const pToP = PreferenceHandler::getPreconditionsToPrefs();
                const int fCount = pToP->size();
                for (int fID = 0; fID < fCount; ++fID) {
                    if (!(*pToP)[fID].empty()) {
                        maxPermissibleCostOfAFact[fID] = hardLimits;
                    }
                }
            }
            
        
        }
            
        
        // Make some maps to quickly determine which variables are relevant to which limits        
        map<int,set<pair<int,double> > > varToLowerResourceLimitVariable;
        
        if (RPGHeuristic::estimateCosts) {          
            for (int l = 0; l < ulCount; ++l) {
                switch (limits[l].op) {
                    case VAL::E_GREATEQ:
                    case VAL::E_GREATER:
                    {
                        map<int,double>::const_iterator vItr = limits[l].var.begin();
                        const map<int,double>::const_iterator vEnd = limits[l].var.end();                        
                        
                        for (; vItr != vEnd; ++vItr) {
                            varToLowerResourceLimitVariable[vItr->first].insert(make_pair(l, vItr->second));
                            
                        }
                        break;
                    }
                    default:
                    {
                        cerr << "Internal error: should not have limits specified as anything other than >= or >\n";
                        exit(1);
                    }
                }
            }
        }
        
        {
            const vector<map<int, list<int> > > & igc = NumericAnalysis::getIndependentGoalCosts();
            
            const int igcSize = igc.size();
            
            for (int gID = 0; gID < igcSize; ++gID) {
                if (literalGoalVector[gID] && !igc[gID].empty()) {
                    
                    isAGoalFactWithIndependentAchivementCosts[literalGoalVector[gID]->getStateID()] = true;
                    
                    map<int, list<int> >::const_iterator lItr = igc[gID].begin();
                    const map<int, list<int> >::const_iterator lEnd = igc[gID].end();
                    
                    for (; lItr != lEnd; ++lItr) {
                        list<int>::const_iterator alItr = lItr->second.begin();
                        const list<int>::const_iterator alEnd = lItr->second.end();
                        
                        for (; alItr != alEnd; ++alItr) {
                            costsAreIndependentGoalCosts[*alItr] = true;
                        }
                    }
                }
            }
            
        }
        
        for (int pass = 0; pass < 2; ++pass) {
            const vector<list<int> > * const nowOn = (pass ? actionsToRPGNumericEndEffects : actionsToRPGNumericStartEffects);
            vector<vector<double> > & costsGoIn = (pass ? endEffectsOnResourceLimits : startEffectsOnResourceLimits);
            const vector<list<NumericAnalysis::CostAtTime*>* > & dynamicCosts = (pass ? NumericAnalysis::getTimeDependentEndCosts()
                                                                     : NumericAnalysis::getTimeDependentStartCosts());
                        
            for (int a = 0; a < actCount; ++a) {
                if (RPGBuilder::rogueActions[a]) continue;

                set<int> costsChanged;

                list<int>::const_iterator eItr = ((*nowOn)[a]).begin();
                const list<int>::const_iterator eEnd = ((*nowOn)[a]).end();

                for (; eItr != eEnd; ++eItr) {
                    const RPGBuilder::RPGNumericEffect & currEff = effTable[*eItr];
                    assert(!RPGBuilder::rogueActions[a]);
                    
                    if (!currEff.isAssignment) {
                        // resource limits are only detectable from constant-valued increase/decrease effects
                        // or we can fake it with bounded durations
                        // so check that is the case first
                        
                        bool evaluatesSafely = false;
                        
                        // a lower-bound -- upper-bound pair
                        pair<double,double> evaluatesTo(0.0,0.0);
                        
                        if (!currEff.size) {
                            evaluatesSafely = true;
                            evaluatesTo.first = evaluatesTo.second = currEff.constant;
                            
                            if (dumpActCosts) {
                                cout << "Simple constant effect: " << currEff << endl;
                            }
                        } else if (currEff.size == 1) {
                            // find bound on duration, evaluate costs
                            if (currEff.variables[0] == -3) {
                                
                                evaluatesTo.first = evaluatesTo.second = currEff.constant; // start with the constant offset
                                                                
                                assert(currEff.weights[0] >= 0.0);
                                evaluatesTo.first += currEff.weights[0] * RPGBuilder::getOpMinDuration(a,-1);     // this is okay - is working at a global level
                                evaluatesTo.second += currEff.weights[0] * RPGBuilder::getOpMaxDuration(a,-1);    // this is okay - is working at a global level
                                
                                evaluatesSafely = true;
                             
                                if (dumpActCosts) {
                                    cout << "Duration-dependent effect: " << currEff << " evaluates to " << evaluatesTo.first << ", " << evaluatesTo.second << endl;
                                }
                                
                            } else if (currEff.variables[0] == -19) {
                                                                                                
                                evaluatesTo.first = evaluatesTo.second = currEff.constant; // start with the constant offset
                                                                
                                assert(currEff.weights[0] >= 0.0);
                                evaluatesTo.first += -currEff.weights[0] * RPGBuilder::getOpMaxDuration(a,-1);    // this is okay - is working at a global level
                                evaluatesTo.second += -currEff.weights[0] * RPGBuilder::getOpMinDuration(a,-1);   // this is okay - is working at a global level
                                
                                if (dumpActCosts) {
                                    cout << "Duration-dependent effect: " << currEff << " evaluates to " << evaluatesTo.first << ", " << evaluatesTo.second << endl;
                                }
                                
                                evaluatesSafely = true;
                            }   
                        } else {
                            if (dumpActCosts) {
                                cout << "Ignoring effect " << currEff << endl;
                            }
                        }
                            
                            
                        
                        if (evaluatesSafely) {
                            // does it act on a lower bound?
                            map<int,set<pair<int,double> > >::const_iterator lsItr = varToLowerResourceLimitVariable.find(currEff.fluentIndex);
                            if (lsItr != varToLowerResourceLimitVariable.end()) {
                                set<pair<int,double> >::const_iterator lItr = lsItr->second.begin();
                                const set<pair<int,double> >::const_iterator lEnd = lsItr->second.end();
                                
                                for (; lItr != lEnd; ++lItr) {
                                    if (lItr->second > 0) {
                                        costsGoIn[a][lItr->first] += evaluatesTo.second * lItr->second;
                                        costsChanged.insert(lItr->first);
                                        if (dumpActCosts) {
                                            cout << "Cost of " << *(RPGBuilder::getInstantiatedOp(a)) << " gone up by " << evaluatesTo.second * lItr->second << endl;
                                        }

                                    } else if (lItr->second < 0) {
                                        costsGoIn[a][lItr->first] += evaluatesTo.first * lItr->second;                                                        
                                        costsChanged.insert(lItr->first);
                                        if (dumpActCosts) {
                                            cout << "Cost of " << *(RPGBuilder::getInstantiatedOp(a)) << " gone up by " << evaluatesTo.first * lItr->second << endl;
                                        }

                                    } else {
                                        continue;
                                    }
                                }
                            }
                        }

                    }
                }

                
                set<int>::const_iterator ccItr = costsChanged.begin();
                const set<int>::const_iterator ccEnd = costsChanged.end();
                
                for (; ccItr != ccEnd; ++ccItr) {
                    for (int ipass = 0; ipass <= pass; ++ipass) {
                        const list<Literal*> & pres = (ipass ? RPGBuilder::getEndPropositionalPreconditions()[a]
                                                            : RPGBuilder::getProcessedStartPropositionalPreconditions()[a]);
                            
                                                            
                        double toUse = limits[*ccItr].limit;
                        
                        if (Globals::bestSolutionQuality > -DBL_MAX && limits[*ccItr].optimisationLimit) {
                            if (Globals::bestSolutionQuality + 0.001 > toUse) {
                                toUse = Globals::bestSolutionQuality + 0.001;
                            }
                        }
                        
                        if (toUse > -DBL_MAX) {
                            const double newPreLimit = toUse - costsGoIn[a][*ccItr];
                            {
                                list<Literal*>::const_iterator preItr = pres.begin();
                                const list<Literal*>::const_iterator preEnd = pres.end();
                                for (; preItr != preEnd; ++preItr) {
                                    vector<double> & toUpdate = maxPermissibleCostOfAFact[(*preItr)->getStateID()];
                                    if (toUpdate[*ccItr] == std::numeric_limits<double>::signaling_NaN()) {
                                        toUpdate[*ccItr] = newPreLimit;
                                    } else if (newPreLimit < toUpdate[*ccItr]) {
                                        toUpdate[*ccItr] = newPreLimit;
                                    }
                                }
                            }
                        }
                    }
                }
                
                if (dynamicCosts[a]) {
                    costsGoIn[a] = nullCosts;
                }
            }
        }

        const int factCount = achieverDetails.size();
        for (int l = 0; l < ulCount; ++l) {
            for (int f = 0; f < factCount; ++f) {
                if (maxPermissibleCostOfAFact[f][l] == std::numeric_limits<double>::signaling_NaN()) {
                    maxPermissibleCostOfAFact[f][l] = limits[l].limit;
                }
            }
        }
    }
    
    #endif

    void integrateContinuousEffects() {
        if (doneIntegration) return;

        if (evaluateDebug) {
            cout << "Integrating actions' effects\n";
        }
        maxNeeded = RPGBuilder::getMaxNeeded();

        vector<RPGBuilder::LinearEffects*> & LD = RPGBuilder::getLinearDiscretisation();

        const int loopLim = LD.size();

        integratedCTSEffectVar.resize(loopLim);
        integratedCTSEffectChange.resize(loopLim);
        gradientCTSEffectVar.resize(loopLim);
        gradientCTSEffectChange.resize(loopLim);
        

        set<int> cannotUseAsGradients;
        
        LiteralSet initialState;
        vector<double> initialFluents;
        
        RPGBuilder::getInitialState(initialState, initialFluents);
        
        MinimalState refState;
        refState.insertFacts(initialState.begin(), initialState.end(), StepAndBeforeOrAfter());
        
        refState.secondMin = initialFluents;
        refState.secondMax = initialFluents;
        
        
        
        if (!RPGHeuristic::makeCTSEffectsInstantaneous) {
            
            const vector<RPGBuilder::RPGNumericEffect> & numEffs = RPGBuilder::getNumericEff();
            
            const int lim = numEffs.size();
            
            int s;
            
            for (int e = 0; e < lim; ++e) {
                const RPGBuilder::RPGNumericEffect & currEff = numEffs[e];
                
                if ((s = currEff.size)) {
                    for (int v = 0; v < s; ++v) {
                        if (currEff.variables[v] >= 0) {
                            if (currEff.variables[v] >= RPGBuilder::getPNECount()) {
                                cannotUseAsGradients.insert(currEff.variables[v] - RPGBuilder::getPNECount());
                            } else {
                                cannotUseAsGradients.insert(currEff.variables[v]);
                            }
                        }
                    }
                }
            }
        }
        
        
        for (int lda = 0; lda < loopLim; ++lda) {
            if (RPGBuilder::rogueActions[lda] == RPGBuilder::OT_INVALID_ACTION) {
                continue;
            }
            
            RPGBuilder::LinearEffects * const currLD = LD[lda];
            if (currLD) {
                
                bool mustIntegrate = RPGHeuristic::makeCTSEffectsInstantaneous;
                if (!mustIntegrate) {
                    mustIntegrate = (RPGBuilder::rogueActions[lda] == RPGBuilder::OT_NORMAL_ACTION && !RPGBuilder::isSelfMutex(lda) && RPGBuilder::howManyTimesOptimistic(lda, refState) > 1);
                }
                
                const double dur = (RPGBuilder::rogueActions[lda] == RPGBuilder::OT_PROCESS ? DBL_MAX : RPGBuilder::getOpMaxDuration(lda, -1));
                const int effCount = currLD->vars.size();
                
                for (int eff = 0; eff < effCount; ++eff) {
                    if (mustIntegrate || cannotUseAsGradients.find(currLD->vars[eff]) != cannotUseAsGradients.end()) {
                        if (evaluateDebug) {
                            cout << "Integrating effect of ";
                            if (!RPGBuilder::isSelfMutex(lda)) {
                                cout << " non-self-mutex action ";
                            }
                            cout << *(RPGBuilder::getInstantiatedOp(lda)) << ":";
                        }
                        integratedCTSEffectVar[lda].push_back(currLD->vars[eff]);
                        integratedCTSEffectChange[lda].push_back(currLD->effects[0][eff].constant * dur);
                        if (evaluateDebug) {                            
                            cout << " " << integratedCTSEffectChange[lda].back() << " of " << *(RPGBuilder::getPNE(integratedCTSEffectVar[lda].back())) << endl;
                        } 
                    } else {
                        if (evaluateDebug) {
                            cout << "Not integrating effect of " << *(RPGBuilder::getInstantiatedOp(lda)) << ":";
                        }
                        gradientCTSEffectVar[lda].push_back(currLD->vars[eff]);
                        gradientCTSEffectChange[lda].push_back(currLD->effects[0][eff].constant);
                        if (evaluateDebug) {                            
                            cout << "d" << *(RPGBuilder::getPNE(gradientCTSEffectVar[lda].back())) << "/dt = " << gradientCTSEffectChange[lda].back() << endl;
                        } 
                    }
                }
                
                if (RPGBuilder::rogueActions[lda] == RPGBuilder::OT_PROCESS) {
                    backgroundProcesses.push_back(lda);
                }
                
            }
            
        }

        doneIntegration = true;
    }

    BuildingPayload * spawnNewPayload(const MinimalState & theState, const double & costLimit, const list<StartEvent> * seq, const vector<double> & minTimestamps, const double & stateTS, list<ActionSegment> & haIn) {

        static const int easSize = initialUnsatisfiedEndPreconditions->size();

        BuildingPayload * const toReturn =
            new BuildingPayload(theState, seq,
                                *(initialUnsatisfiedProcessedStartPreconditions),
                                *(initialUnsatisfiedEndPreconditions),
                                *(initialUnsatisfiedProcessedStartNumericPreconditions),
                                *(initialUnsatisfiedNumericEndPreconditions),
                                easSize, goals.size() + goalFluents.size(),
                                minTimestamps, stateTS, haIn, costLimit);

        
        vector<double> maxFluentTable(toReturn->vCount * 2 + toReturn->avCount);

        {
            if (evaluateDebug && toReturn->vCount) {
                cout << "Fluent table bounds for fluents in the range " << 0 << ".." << toReturn->vCount - 1 << ".  Number of non-static PNEs: " << instantiatedOp::howManyNonStaticPNEs() << endl;
            }
            for (int i = 0; i < toReturn->vCount; ++i) {
                if (evaluateDebug) {
                    cout << "Fluent " << i << " ";
                    cout.flush();
                    cout << *(RPGBuilder::getPNE(i)) << " bounds: [";
                }
                {
                    const double ov = theState.secondMax[i];
                    maxFluentTable[i] = ov;

                }
                {
                    const double ov = theState.secondMin[i];
                    if (ov != 0.0) {
                        maxFluentTable[i + toReturn->vCount] = 0.0 - ov;
                    } else {
                        maxFluentTable[i + toReturn->vCount] = 0.0;
                    }
                    if (evaluateDebug) cout << ov << ",";
                }
                if (evaluateDebug) {
                    cout << maxFluentTable[i] << "]\n";
                }
            }
        }
        {
            const int startLim = toReturn->vCount * 2;
            const int endLim = startLim + RPGBuilder::getAVCount();
            for (int i = startLim; i < endLim; ++i) {
                maxFluentTable[i] = RPGBuilder::getArtificialVariable(i).evaluate(maxFluentTable);
                if (evaluateDebug) cout << "AV " << i << " = " << maxFluentTable[i] << "\n";
            }
        }

        toReturn->fluentLayers.setFactLayerZero(maxFluentTable, earliestNumericPOTimes);



        {
            map<int, set<int> >::const_iterator saItr = theState.startedActions.begin();
            const map<int, set<int> >::const_iterator saEnd = theState.startedActions.end();

            for (; saItr != saEnd; ++saItr) {
                double earliest = DBL_MAX;

                set<int>::const_iterator instanceItr = saItr->second.begin();
                const set<int>::const_iterator instanceEnd = saItr->second.end();

                for (; instanceItr != instanceEnd; ++instanceItr) {
                    const double newTS = minTimestamps[*instanceItr];
                    if (newTS < earliest) earliest = newTS;
                }

                earliest += RPGBuilder::getOpMinDuration(saItr->first, -1);

                toReturn->earliestStartOf.insert(make_pair(saItr->first, earliest));
            }
        }

#ifdef MDIDEBUG
        MaxDependentInfo::updatePayload(toReturn);
#endif
        return toReturn;
    }

    /** @brief Prime the TRPG with the gradient effects of executing actions.
     *
     * @param payload                      The current TRPG data
     * @param timeAtWhichValueIsDefined    If the state numeric bound was immediately after the last relevant action, this is that time point.
     * @param gradientsToStart             Updated by this function to contain gradient effects to start corresponding to actions already in the plan that have not yet finished.
     */
    void giveUsTheEffectsOfExecutingActions(BuildingPayload * const payload,
                                            const vector<double> & timeAtWhichValueIsDefined,
                                            map<double, list<DelayedGradientDescriptor> > & gradientsToStart) {
        if (!payload->startEventQueue) {
            assert(payload->startState.startedActions.empty());
            return;
        }
        
        vector<double> * maxFluentTable = 0;
        vector<RPGBuilder::LinearEffects*> & LD = RPGBuilder::getLinearDiscretisation();
                
        list<StartEvent>::const_iterator evItr = payload->startEventQueue->begin();
        const list<StartEvent>::const_iterator evEnd = payload->startEventQueue->end();
        
        for (; evItr != evEnd; ++evItr) {

            const RPGBuilder::LinearEffects* currLD = LD[evItr->actID];
            if (!currLD) continue;
                       
            const double multiplier = evItr->maxDuration - evItr->elapsed;
            
            const vector<int> & varList = currLD->vars;
            const vector<RPGBuilder::LinearEffects::EffectExpression> & changeList = currLD->effects[0];

            const int effCount = varList.size();
            
            for (int e = 0; e < effCount; ++e) {
                if (timeAtWhichValueIsDefined.empty() || timeAtWhichValueIsDefined[varList[e]] < 0.0) {
                    const double change = changeList[e].constant * multiplier;
                    if (change > 0.0) {
                        if (!maxFluentTable) {
                            maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
                        }
                        (*maxFluentTable)[varList[e]] += change;
                    } else if (change < 0.0) {
                        if (!maxFluentTable) {
                            maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
                        }
                        (*maxFluentTable)[payload->vCount + varList[e]] += (0.0 - change);
                    }
                } else {
                    // if this is the case, we've been passed a time at which the bound on this
                    // variable was determined - which means we can fire off the 'effects of executing
                    // actions' as a proper gradient.
                    #ifdef DEBUG
                    if (RPGHeuristic::makeCTSEffectsInstantaneous) {
                        cerr << "Error: making continuous effects instantaneous (as in the the Colin IJCAI paper) is incompatible with the revised approach to state variable bounds for heuristic purposes.\n";
                        exit(1);
                    }
                    #endif      
                    
                    gradientsToStart[timeAtWhichValueIsDefined[varList[e]]].push_back(DelayedGradientDescriptor(evItr->actID, Planner::E_AT_START, multiplier, make_pair(varList[e], changeList[e].constant)));
                                                      
                }
            }

            //if (evaluateDebug || eeDebug) cout << "Clearing extra ends attached to " << *(RPGBuilder::getInstantiatedOp(saItr->first)) << "\n";
        }


    }

    /** @brief Add delayed gradient effects as slope functions rather than using integration.
     */
    void addDelayedGradientEffects(BuildingPayload * const payload, const map<double, list<DelayedGradientDescriptor> > & delayedGradients) {
        
        if (RPGBuilder::modifiedRPG) {
            // popf heuristic, so gradients might not start straight away
            cerr << "The -/ option is currently not implemented for the POPF heuristic - add -c or -T to the command line\n";
            exit(1);
        }
        
        static const bool localDebug = false;
        
        map<double, list<DelayedGradientDescriptor> >::const_iterator dgItr = delayedGradients.begin();
        const map<double, list<DelayedGradientDescriptor> >::const_iterator dgEnd = delayedGradients.end();
        
        for (; dgItr != dgEnd; ++dgItr) {
            // ignore the first entry of the pair, as we start everything straight away
            
            list<DelayedGradientDescriptor>::const_iterator gItr = dgItr->second.begin();
            const list<DelayedGradientDescriptor>::const_iterator gEnd = dgItr->second.end();
            
            for (; gItr != gEnd; ++gItr) {           
                if (localDebug) {
                    cout << "-- Adding gradient effect from executing action, d" << *(RPGBuilder::getPNE(gItr->gradientEffect.first)) << "/dt = " << gItr->gradientEffect.second << " until " << gItr->maxDur;
                    cout << ", from initial bounds [" << payload->startState.secondMin[gItr->gradientEffect.first] << "," << payload->startState.secondMax[gItr->gradientEffect.first] << "]\n";
                }
                payload->fluentLayers.recordGradientNumericEffect(*gItr, EpsilonResolutionTimestamp::epsilon(), gItr->gradientEffect, payload->factLayers);
            }
        }
    }

    void initPrefCosts() {
        static bool initPrefCosts = false;
    
    
        if (!initPrefCosts) {
            initPrefCosts = true;
            
            const vector<RPGBuilder::Constraint> & prefTable = RPGBuilder::getPreferences();
            const int pSize = prefTable.size();
            prefCosts.resize(pSize);
            for (int p = 0 ; p < pSize; ++p) {
                prefCosts[p] = prefTable[p].cost;
            }
        }
    }

    void resetAchievedBy(BuildingPayload * payload) {
        #ifdef POPF3ANALYSIS
        const int fCount = achieverDetails.size();
        for (int f = 0; f < fCount; ++f) {
            achieverDetails[f].clear();
        }        
        #else
        *achievedBy = (*achievedByReset);
        *achievedInLayer = (*achievedInLayerReset);
        #endif
        
        *negativeAchievedBy = (*negativeAchievedByReset);
        *negativeAchievedInLayer = (*negativeAchievedInLayerReset);
        
        *numericAchievedBy = (*numericAchievedByReset);
        *numericAchievedInLayer = (*numericAchievedInLayerReset);
        
        preconditionsToPrefs = PreferenceHandler::getPreconditionsToPrefs();
        negativePreconditionsToPrefs = PreferenceHandler::getNegativePreconditionsToPrefs();
        
        numericPreconditionsToPrefs = PreferenceHandler::getNumericPreconditionsToPrefs();

        PreferenceHandler::getUnsatisfiedConditionCounts(payload->startState, payload->initialUnsatisfiedPreferenceConditions, payload->becomesUnreachableAtLayer);
        payload->preferencePartTrueAtLayer.resize(payload->initialUnsatisfiedPreferenceConditions.size(), vector<EpsilonResolutionTimestamp>(2,EpsilonResolutionTimestamp::infinite()));
        
        
        payload->startActionCosts.resize(initialUnsatisfiedStartPreconditions->size());
        payload->endActionCosts.resize(initialUnsatisfiedEndPreconditions->size());
        payload->tilCosts.resize(RPGBuilder::getNonAbstractedTILVec().size());
        payload->optimisticPrefStatus = payload->startState.preferenceStatus;        
        
        PreferenceHandler::getCostsOfDeletion(payload->startState, payload->prefCostOfDeletingFact, payload->prefCostOfChangingNumberA);
        PreferenceHandler::getCostsOfAdding(payload->startState, payload->prefCostOfAddingFact, payload->prefCostOfChangingNumberB);
        
        {
            StateFacts::const_iterator stateItr = payload->startState.first.begin();
            const StateFacts::const_iterator stateEnd = payload->startState.first.end();
            
            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = FACTA(stateItr);
                (*negativeAchievedInLayer)[factID] = EpsilonResolutionTimestamp::undefined();                
            }
        }
        
    }

    static EpsilonResolutionTimestamp localEarliestPointForNumericPrecondition(const RPGBuilder::RPGNumericPrecondition & p) {
        return earliestPointForNumericPrecondition(p, &earliestNumericPOTimes);
    }

    static EpsilonResolutionTimestamp earliestPointForNumericEffect(const RPGBuilder::RPGNumericEffect & p) {

        static const int varCount = RPGBuilder::getPNECount();

        EpsilonResolutionTimestamp TS = EpsilonResolutionTimestamp::zero();

        if (earliestNumericPOTimes[p.fluentIndex] > TS) TS = earliestNumericPOTimes[p.fluentIndex];

        for (int s = 0; s < p.size; ++s) {
            int var = p.variables[s];
            if (var < 0) continue;
            if (var >= varCount) var -= varCount;
            if (earliestNumericPOTimes[var] > TS) TS = earliestNumericPOTimes[var];
        }

        return TS;
    }


    static EpsilonResolutionTimestamp earliestPointForDuration(const RPGBuilder::RPGDuration & currDE) {
        EpsilonResolutionTimestamp TS = EpsilonResolutionTimestamp::zero();

        for (int pass = 0; pass < 3; ++pass) {
            const list<RPGBuilder::DurationExpr*> & currList = currDE[pass];
            list<RPGBuilder::DurationExpr*>::const_iterator lItr = currList.begin();
            const list<RPGBuilder::DurationExpr*>::const_iterator lEnd = currList.end();

            for (; lItr != lEnd; ++lItr) {
                const int vSize = ((*lItr)->variables.size());
                for (int i = 0; i < vSize; ++i) {
                    #ifdef STOCHASTICDURATIONS
                    const int var = (*lItr)->variables[i].first;
                    if (var == -1) continue;
                    #else
                    const int var = (*lItr)->variables[i];
                    #endif
                    if (earliestNumericPOTimes[var] > TS) TS = earliestNumericPOTimes[var];
                    
                }
            }
        }
        return TS;
    }

#ifdef TOTALORDERSTATES
    void recordFactLayerZero(BuildingPayload * const payload) {
        
        #ifdef POPF3ANALYSIS
        
        const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();
        
        const int ulCount = limits.size();
        
        currentCosts = vector<double>(ulCount,0.0);
        
        for (int ul = 0; ul < ulCount; ++ul) {
            map<int,double>::const_iterator vItr = limits[ul].var.begin();
            const map<int,double>::const_iterator vEnd = limits[ul].var.end();
            
            for (; vItr != vEnd; ++vItr) {
                if (vItr->second >= 0.0) {
                    currentCosts[ul] += payload->startState.secondMax[vItr->first] * vItr->second;
                } else {
                    currentCosts[ul] += payload->startState.secondMin[vItr->first] * vItr->second;
                }
            }                     
        }
        
        #endif
    
        assert(!RPGBuilder::modifiedRPG);
        
        {
            StateFacts::const_iterator stateItr = payload->startState.first.begin();
            const StateFacts::const_iterator stateEnd = payload->startState.first.end();
            
            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = FACTA(stateItr);
                #ifdef POPF3ANALYSIS
                achieverDetails[factID].push_back(CostedAchieverDetails(currentCosts,true));                
                #else
                (*achievedInLayer)[factID] = 0.0;
                #endif
                payload->factPreferenceCost[factID].push_back(PreferenceSetAndCost(true));
            }
        }

        

        {
            const int loopLim = earliestNumericPOTimes.size();
            
            for (int i = 0; i < loopLim; ++i) {
                earliestNumericPOTimes[i] = EpsilonResolutionTimestamp::zero();
            }
        }

        {
            const int loopLim = rpgNumericPreconditions->size();

            if (loopLim) {
                const vector<double> * const maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
                for (int i = 0; i < loopLim; ++i) {
                    if (ignoreNumbers || (*rpgNumericPreconditions)[i].isSatisfied(*maxFluentTable)) {
                        numericIsTrueInState[i] = true;
                        const EpsilonResolutionTimestamp poTS = localEarliestPointForNumericPrecondition((*rpgNumericPreconditions)[i]);
                        //earliestNumericPrePOTimes[i] = poTS;
                        (*numericAchievedBy)[i] = 0;
                        if (RPGBuilder::modifiedRPG && poTS >= EpsilonResolutionTimestamp::epsilon()) {
                            (*numericAchievedInLayer)[i] = poTS;
                            --((*numericAchievedInLayer)[i]);
                        } else {
                            (*numericAchievedInLayer)[i] = EpsilonResolutionTimestamp::zero();
                        }
                        if (evaluateDebug && RPGBuilder::modifiedRPG && (*numericAchievedInLayer)[i] > EpsilonResolutionTimestamp::zero()) {
                            cout << "RPG modified: delaying numeric fact " << i << " to layer " << (*numericAchievedInLayer)[i] << "\n";
                        }
                        if (evaluateDebug && ignoreNumbers) {
                            cout << "Assuming numeric precondition " << i << " is satisfied\n";
                        }
                    } else {
                        numericIsTrueInState[i] = false;
                    }
                }
            }
        }

    }
#else

    void recordFactLayerZero(BuildingPayload * const payload) {
        
        #ifdef POPF3ANALYSIS
        
        const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();
        
        const int ulCount = limits.size();
        
        currentCosts = vector<double>(ulCount,0.0);
        
        for (int ul = 0; ul < ulCount; ++ul) {
            map<int,double>::const_iterator vItr = limits[ul].var.begin();
            const map<int,double>::const_iterator vEnd = limits[ul].var.end();
            
            for (; vItr != vEnd; ++vItr) {
                if (vItr->first >= 0.0) {
                    if (vItr->second >= 0.0) {
                        currentCosts[ul] += payload->startState.secondMax[vItr->first] * vItr->second;
                    } else {
                        currentCosts[ul] += payload->startState.secondMin[vItr->first] * vItr->second;
                    }
                }
            }
        }
        
        #endif
        
        if (RPGBuilder::modifiedRPG) {
            StateFacts::const_iterator stateItr = payload->startState.first.begin();
            const StateFacts::const_iterator stateEnd = payload->startState.first.end();

            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = FACTA(stateItr);
                #ifdef POPF3ANALYSIS
                achieverDetails[factID].push_back(CostedAchieverDetails(currentCosts,PreferenceSetAndCost(true),true));
                CostedAchieverDetails & achievedTS = achieverDetails[factID].back();
                #else
                EpsilonResolutionTimestamp * const achievedTS = &((*achievedInLayer)[factID] = EpsilonResolutionTimestamp::zero());
                #endif
                pair<EpsilonResolutionTimestamp, EpsilonResolutionTimestamp> * toUpdate = 0;
                const StepAndBeforeOrAfter & from = stateItr->second.availableFrom;
                if (from.beforeOrAfter == StepAndBeforeOrAfter::BEFORE) { // special case: initial state is anything achieved /before/ step 0, rather than at step 0
                    earliestPropositionPOTimes[factID] = EpsilonResolutionTimestamp::zero();
                    //if (!stateItr->second.deletableFrom.empty()) {
                    //    toUpdate = (&payload->propositionMustBeDeletedAddedAfter.insert(make_pair(factID,make_pair(0.0,0.0))).first->second);
                    //}
                    //if (!expandFully) cout << "Initial Fact " << *(RPGBuilder::getLiteral(factID)) << " is true in the initial state\n";
                } else {
                    const unsigned int dependsOnActionAtStep = from.stepID;
                    const EpsilonResolutionTimestamp actTS(payload->minTimestamps[dependsOnActionAtStep],true);
                    earliestPropositionPOTimes[factID] = actTS;
                    //if (!expandFully) cout << "Initial Fact " << *(RPGBuilder::getLiteral(factID)) << " appears in PO no earlier than action " << dependsOnActionAtStep << ", i.e. t=" << earliestPropositionPOTimes[factID] << "\n";

                    toUpdate = &(payload->propositionMustBeDeletedAddedAfter.insert(make_pair(factID, make_pair(EpsilonResolutionTimestamp::zero(), EpsilonResolutionTimestamp::zero()))).first->second);

                    if (toUpdate->first < actTS) toUpdate->first = actTS;
                    if (toUpdate->second < actTS) toUpdate->second = actTS;

                    if (RPGBuilder::modifiedRPG && actTS >= EpsilonResolutionTimestamp::zero()) {
                        /*if (evaluateDebug) cout << "RPG modified: delaying " << *(RPGBuilder::getLiteral(factID)) << " to layer " << (actTS - EpsilonResolutionTimestamp::epsilon()) << "\n";
                        #ifdef POPF3ANALYSIS
                        achievedTS.updateLayer(actTS - EpsilonResolutionTimestamp::epsilon());
                        #else
                        *achievedTS = actTS - EpsilonResolutionTimestamp::epsilon();
                        #endif*/
                        EpsilonResolutionTimestamp shiftedTS(actTS);
                        ++shiftedTS;
                        if (evaluateDebug) cout << "RPG modified: delaying " << *(RPGBuilder::getLiteral(factID)) << " to layer " << shiftedTS << "\n";
                        #ifdef POPF3ANALYSIS
                        achievedTS.updateLayer(shiftedTS);
                        #else
                        *achievedTS = shiftedTS;
                        #endif
                    }

                }

                if (toUpdate) {
                    map<StepAndBeforeOrAfter, bool>::const_iterator invItr = stateItr->second.deletableFrom.begin();
                    const map<StepAndBeforeOrAfter, bool>::const_iterator invEnd = stateItr->second.deletableFrom.end();

                    for (; invItr != invEnd; ++invItr) {
                        const EpsilonResolutionTimestamp actTS(payload->minTimestamps[invItr->first.stepID] - (invItr->first.beforeOrAfter == StepAndBeforeOrAfter::BEFORE ? 0.001 : 0.0), true);
                        if (actTS > EpsilonResolutionTimestamp::zero()) {
                            if (toUpdate->first < actTS) toUpdate->first = actTS;
                            if (evaluateDebug) cout << "RPG modified: cannot delete " << *(RPGBuilder::getLiteral(factID)) << " until layer " << actTS << "\n";
                        }
                    }
                }
                
            }

            //if (!expandFully) MaxDependentInfo::debug = true;
        } else {
            map<int, PropositionAnnotation>::const_iterator stateItr = payload->startState.first.begin();
            const map<int, PropositionAnnotation>::const_iterator stateEnd = payload->startState.first.end();
            
            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = stateItr->first;
                #ifdef POPF3ANALYSIS
                achieverDetails[factID].push_back(CostedAchieverDetails(currentCosts,PreferenceSetAndCost(true),true));                
                #else
                (*achievedInLayer)[factID] = 0.0;
                #endif
            }
        }

        if (RPGBuilder::modifiedRPG) {
            map<int, PropositionAnnotation>::const_iterator stateItr = payload->startState.retired.begin();
            const map<int, PropositionAnnotation>::const_iterator stateEnd = payload->startState.retired.end();

            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = stateItr->first;

                const StepAndBeforeOrAfter & from = stateItr->second.negativeAvailableFrom;
                const unsigned int dependsOnActionAtStep = from.stepID;
                const EpsilonResolutionTimestamp actTS(payload->minTimestamps[dependsOnActionAtStep],true);
                pair<EpsilonResolutionTimestamp, EpsilonResolutionTimestamp> & toUpdate = payload->propositionMustBeDeletedAddedAfter.insert(make_pair(factID, make_pair(EpsilonResolutionTimestamp::zero(), EpsilonResolutionTimestamp::zero()))).first->second;

                if (toUpdate.first < actTS) {
                    if (evaluateDebug) cout << "RPG modified: cannot delete " << *(RPGBuilder::getLiteral(factID)) << " until layer " << actTS << ", due to existing deletor\n";
                    toUpdate.first = actTS;
                }
                if (toUpdate.second < actTS) {
                    if (evaluateDebug) cout << "RPG modified: cannot add " << *(RPGBuilder::getLiteral(factID)) << " until layer " << actTS << ", due to existing deletor\n";
                    toUpdate.second = actTS;
                }

                map<StepAndBeforeOrAfter, bool>::const_iterator invItr = stateItr->second.deletableFrom.begin();
                const map<StepAndBeforeOrAfter, bool>::const_iterator invEnd = stateItr->second.deletableFrom.end();

                for (; invItr != invEnd; ++invItr) {
                    const EpsilonResolutionTimestamp actTS(payload->minTimestamps[invItr->first.stepID] - (invItr->first.beforeOrAfter == StepAndBeforeOrAfter::BEFORE ? 0.001 : 0.0),true);
                    if (actTS > EpsilonResolutionTimestamp::zero()) {
                        if (toUpdate.first < actTS) {
                            if (evaluateDebug) cout << "RPG modified: cannot delete " << *(RPGBuilder::getLiteral(factID)) << " until layer " << actTS << ", due to previous additions\n";
                            toUpdate.first = actTS;
                        }
                    }
                }
            }

        }

        if (RPGBuilder::modifiedRPG) {
            
            /*{
                const int mts = payload->minTimestamps.size();
                
                cout << "[ ";
                for (int m = 0; m < mts; ++m) {
                    cout << " " << m << ":" << payload->minTimestamps[m];
                }
                cout << " ]\n";
            }*/
            const vector<FluentInteraction> & lastStepToTouchPNE = payload->startState.temporalConstraints->lastStepToTouchPNE;

            const int loopLim = lastStepToTouchPNE.size();

            for (int i = 0; i < loopLim; ++i) {
                const int stepID = lastStepToTouchPNE[i].lastInstantaneousEffect;                 
                if (stepID == -1) {
                    if (evaluateDebug) {
                        cout << *(RPGBuilder::getPNE(i)) << " never touched\n";
                    }
                    earliestNumericPOTimes[i] = EpsilonResolutionTimestamp::zero() - EpsilonResolutionTimestamp::epsilon();
                } else {
                    if (evaluateDebug) {
                        cout << *(RPGBuilder::getPNE(i)) << " last touched by step " << stepID;
                        cout.flush();
                    }
                    #ifndef NDEBUG
                    if (payload->minTimestamps[stepID] < 0.0) {
                        cerr << "Fatal error: for variable " << i << ", timestamp of step " << stepID << " is " << payload->minTimestamps[stepID] << endl;
                        assert(payload->minTimestamps[stepID] >= 0.0);
                    }
                    #endif
                    assert(payload->minTimestamps[stepID] != DBL_MAX);
                    if (evaluateDebug) {
                        cout << " at time " << payload->minTimestamps[stepID] << endl;
                    }
                    earliestNumericPOTimes[i] =  EpsilonResolutionTimestamp(payload->minTimestamps[stepID],true);
                }
            }
        } else {
            const int loopLim = earliestNumericPOTimes.size();
            
            for (int i = 0; i < loopLim; ++i) {
                earliestNumericPOTimes[i] = EpsilonResolutionTimestamp::zero();
            }
        }

        {
            const int loopLim = rpgNumericPreconditions->size();

            if (loopLim) {
                const vector<double> * const maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
                for (int i = 0; i < loopLim; ++i) {
                    if (ignoreNumbers || (*rpgNumericPreconditions)[i].isSatisfied(*maxFluentTable)) {
                        numericIsTrueInState[i] = true;
                        const EpsilonResolutionTimestamp poTS = localEarliestPointForNumericPrecondition((*rpgNumericPreconditions)[i]);
                        //earliestNumericPrePOTimes[i] = poTS;
                        (*numericAchievedBy)[i] = 0;
                        (*numericAchievedInLayer)[i] = (RPGBuilder::modifiedRPG && poTS > EpsilonResolutionTimestamp::zero() ? (poTS - EpsilonResolutionTimestamp::epsilon()) : EpsilonResolutionTimestamp::zero());
                        if (evaluateDebug && RPGBuilder::modifiedRPG && (*numericAchievedInLayer)[i] > EpsilonResolutionTimestamp::zero()) {
                            cout << "RPG modified: delaying numeric fact " << i << " to layer " << (*numericAchievedInLayer)[i] << "\n";
                        }
                        if (evaluateDebug && ignoreNumbers) {
                            cout << "Assuming numeric precondition " << i << " is satisfied\n";
                        }
                    } else {
                        numericIsTrueInState[i] = false;
                    }
                }
            }
        }

    }
#endif

    void setInitialNegativePreconditionsOfPreferences(BuildingPayload * payload)
    {
        {
            StateFacts::const_iterator stateItr = payload->startState.first.begin();
            const StateFacts::const_iterator stateEnd = payload->startState.first.end();

            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = FACTA(stateItr);
                const list<LiteralCellDependency<pair<int,bool> > > & dependents = (*negativePreconditionsToPrefs)[factID];
                list<LiteralCellDependency<pair<int,bool> > >::const_iterator depItr = dependents.begin();
                const list<LiteralCellDependency<pair<int,bool> > >::const_iterator depEnd = dependents.end();
                
                for (; depItr != depEnd; ++depItr) {
                    
                    NNF_Flat* const toUpdate = payload->initialUnsatisfiedPreferenceConditions[depItr->dest.first][depItr->dest.second ? 1 : 0];
                    
                    if (!toUpdate) continue;
                    
                    toUpdate->unsatisfy(depItr->index);
                }
            }
        }
    }

    void addRequirementToHaveSeenTheEndOfAllCurrentlyExecutingActions(BuildingPayload * const payload) {
        map<int, set<int> >::const_iterator saItr = payload->startedActions.begin();
        const map<int, set<int> >::const_iterator saEnd = payload->startedActions.end();

        for (; saItr != saEnd; ++saItr) {
            if (!TemporalAnalysis::canSkipToEnd(saItr->first)) {
                payload->insistUponEnds.insert(*saItr);
                if (evaluateDebug) cout << "Insisting on the end of " << saItr->first << " - " << *(RPGBuilder::getInstantiatedOp(saItr->first)) << " - is not skippable\n";
                #ifndef NDEBUG
                payload->unappearedEndSet.insert(saItr->first);
                #endif
            } else {
                if (evaluateDebug) cout << "End of " << *(RPGBuilder::getInstantiatedOp(saItr->first)) << " is a skippable\n";
            }

        }

        payload->unappearedEnds = payload->insistUponEnds.size();
    }

    bool seeWhatGoalsAreTrueToStartWith(BuildingPayload * const payload) {
        
        {
            set<int>::iterator gsItr = goals.begin();

            for (; gsItr != gsEnd; ++gsItr) {
                const StateFacts::const_iterator gfItr = payload->startState.first.find(*gsItr);
                if (gfItr != payload->startState.first.end()) {
                    if (evaluateDebug) {
                        cout << "\t" << *gsItr << " true in initial state\n";
                    }
                    --(payload->unsatisfiedGoals);
                }
            }
        }


        {

            set<int>::iterator gfItr = goalFluents.begin();

            if (gfItr != gfEnd) {

                const vector<double> * const maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());

                for (; gfItr != gfEnd; ++gfItr) {
                    if (ignoreNumbers || (*rpgNumericPreconditions)[*gfItr].isSatisfied(*maxFluentTable)) {
                        if (evaluateDebug) {
                            cout << "\t" << (*rpgNumericPreconditions)[*gfItr] << " true in initial state\n";
                        }

                        --(payload->unsatisfiedGoals);
                    } else if (evaluateDebug) {
                        cout << "\t" << (*rpgNumericPreconditions)[*gfItr] << " false in initial state\n";
                    }
                }
            }
        }

        return (!payload->unsatisfiedGoals && !payload->unappearedEnds);

    }


    void delayOpenEndsUntilTheirPOPositions(BuildingPayload * const payload) {
        if (!RPGBuilder::modifiedRPG) {
            return;
        }
        
        if (!payload->startEventQueue) {
            return;
        }
        
        list<StartEvent>::const_iterator seqItr = payload->startEventQueue->begin();
        const list<StartEvent>::const_iterator seqEnd = payload->startEventQueue->end();
        
        for (; seqItr != seqEnd; ++seqItr) {
            EpsilonResolutionTimestamp & eas = payload->openEndActionSchedule[seqItr->actID];
            const EpsilonResolutionTimestamp localTS(payload->minTimestamps[seqItr->stepID + 1],true);
            if (eas.isUndefined() || localTS < eas) {
                eas = localTS;
            }
        }
    }

    void addTemporalConstraintsFromActiveActions(BuildingPayload * const payload) {
        if (!RPGBuilder::modifiedRPG) {
            return;
        }

        map<int, pair<EpsilonResolutionTimestamp, EpsilonResolutionTimestamp> >::iterator constrItr = payload->propositionMustBeDeletedAddedAfter.begin();
        const map<int, pair<EpsilonResolutionTimestamp, EpsilonResolutionTimestamp> >::iterator constrEnd = payload->propositionMustBeDeletedAddedAfter.end();

        for (; constrItr != constrEnd; ++constrItr) {

            const int litID = constrItr->first;

            for (int pass = 0; pass < 2; ++pass) {
                const list<pair<int, Planner::time_spec> > & effList = (pass ? (*negativeEffectsToActions)[litID] : (*effectsToActions)[litID]);
                const EpsilonResolutionTimestamp layer = (pass ? constrItr->second.second : constrItr->second.first) - EpsilonResolutionTimestamp::epsilon();

                if (layer <= EpsilonResolutionTimestamp::epsilon()) continue;

                assert(layer >= EpsilonResolutionTimestamp::zero());
                FactLayerEntry & layerEntry = payload->factLayers[layer];

                if (!layerEntry.endOfJustApplied) {
                    payload->gc.push_back(make_pair(set<int>(), set<int>()));
                    layerEntry.endOfJustApplied = &(payload->gc.back());
                }

                pair<set<int>, set<int> > * const dest = layerEntry.endOfJustApplied;

                list<pair<int, Planner::time_spec> >::const_iterator effItr = effList.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator effEnd = effList.end();

                for (; effItr != effEnd; ++effItr) {
                    if (effItr->second == Planner::E_AT) {
                        continue;
                    }
                    if (RPGBuilder::rogueActions[effItr->first] == RPGBuilder::OT_NORMAL_ACTION) {
                        if (effItr->second == Planner::E_AT_START) {
                            if (dest->first.insert(effItr->first).second) {
                                ++(payload->forbiddenStart.insert(pair<int, int>(effItr->first, 0)).first->second);
                            }
                        } else {
                            assert(effItr->second == Planner::E_AT_END); 
                            if (dest->second.insert(effItr->first).second) {
                                ++(payload->forbiddenEnd.insert(pair<int, int>(effItr->first, 0)).first->second);
                            }
                        }
                    }
                }

                if (layerEntry.endOfJustApplied->first.empty() && layerEntry.endOfJustApplied->second.empty()) {
                    layerEntry.endOfJustApplied = 0;
                    payload->gc.pop_back();
                }
            }

        }

        const int varCount = earliestNumericPOTimes.size();

        for (int v = 0; v < varCount; ++v) {
            const EpsilonResolutionTimestamp layer = earliestNumericPOTimes[v] - EpsilonResolutionTimestamp::epsilon();
            if (layer <= EpsilonResolutionTimestamp::epsilon()) continue;
            assert(layer >= EpsilonResolutionTimestamp::zero());
            FactLayerEntry & layerEntry = payload->factLayers[layer];

            if (!layerEntry.endOfJustApplied) {
                payload->gc.push_back(make_pair(set<int>(), set<int>()));
                layerEntry.endOfJustApplied = &(payload->gc.back());
            }

            pair<set<int>, set<int> > * const dest = layerEntry.endOfJustApplied;

            for (int pass = 0; pass < 2; ++pass) {
                set<int> & destSet = (pass ? dest->second : dest->first);
                const set<int> & loopSet = actionsAffectedByFluent[v][pass];

                set<int>::const_iterator aItr = loopSet.begin();
                const set<int>::const_iterator aEnd = loopSet.end();

                for (; aItr != aEnd; ++aItr) {
                    if (RPGBuilder::rogueActions[*aItr] == RPGBuilder::OT_NORMAL_ACTION) {
                        if (destSet.insert(*aItr).second) {
                            if (pass) {
                                ++(payload->forbiddenEnd.insert(pair<int, int>(*aItr, 0)).first->second);
                            } else {
                                ++(payload->forbiddenStart.insert(pair<int, int>(*aItr, 0)).first->second);
                            }
                        }
                    }
                }
            }


            if (layerEntry.endOfJustApplied->first.empty() && layerEntry.endOfJustApplied->second.empty()) {
                layerEntry.endOfJustApplied = 0;
                payload->gc.pop_back();
            }

        }

        //static vector<double> earliestNumericPOTimes;
    }


    bool addTemporalConstraintsFromActiveActions(BuildingPayload * const payload, map<double, list<pair<int, int> > > * const justApplied, const EpsilonResolutionTimestamp & stateTS, const int & nextTIL, const double & tilFrom) {

        if (!justApplied) {
            if (evaluateDebug) {
                cout << "Not just applied a start, so no definitely active invariants\n";
            }

            return true;
        }

        EpsilonResolutionTimestamp TILoffset((nextTIL < tilCount ? tilTimes[nextTIL] - tilFrom : 0.0),true);

        list<pair<set<int>, set<int> > > & setsToForbid = payload->setsToForbid;        
        

        map<double, list<pair<int, int> > >::iterator jaItr = justApplied->begin();
        const map<double, list<pair<int, int> > >::iterator jaEnd = justApplied->end();
        for (; jaItr != jaEnd; ++jaItr) {
            const EpsilonResolutionTimestamp insLayer(jaItr->first, true);
            if (insLayer > EpsilonResolutionTimestamp::zero()) {
                setsToForbid.push_back(pair<set<int>, set<int> >());
                set<int> & affectedStarts = setsToForbid.back().first;
                set<int> & affectedEnds = setsToForbid.back().second;

                list<pair<int, int> >::iterator liItr = jaItr->second.begin();
                const list<pair<int, int> >::iterator liEnd = jaItr->second.end();

                for (; liItr != liEnd; ++liItr) {
                    const int currActID = liItr->first;
                    {

                        list<Literal*> & invs = (*actionsToInvariants)[currActID];
                        list<Literal*>::iterator invItr = invs.begin();
                        const list<Literal*>::iterator invEnd = invs.end();

                        for (; invItr != invEnd; ++invItr) {
                            const int litID = (*invItr)->getStateID();
                            list<pair<int, Planner::time_spec> > & affected = (*negativeEffectsToActions)[litID];
                            list<pair<int, Planner::time_spec> >::iterator affItr = affected.begin();
                            const list<pair<int, Planner::time_spec> >::iterator affEnd = affected.end();
                            for (; affItr != affEnd; ++affItr) {
                                if (affItr->second == Planner::E_AT_START) {
                                    if (evaluateDebug) {
                                        cout << "Delaying start of " << affItr->first << " to " << insLayer << "\n";
                                    }
                                    affectedStarts.insert(affItr->first);
                                } else {
                                    affectedEnds.insert(affItr->first);
                                    if (evaluateDebug) {
                                        cout << "i) Delaying end of " << affItr->first << " to " << insLayer << "\n";
                                    }

                                }
                            }
                            if (nextTIL < tilCount) {

                                for (int i = nextTIL; i < tilCount; ++i) {
                                    const EpsilonResolutionTimestamp earliestTILtime = EpsilonResolutionTimestamp(tilTimes[i],true) - TILoffset;

                                    if (earliestTILtime < insLayer) {
                                        list<int>::iterator effItr = tilTemporaryNegativeEffects[i].begin();
                                        const list<int>::iterator effEnd = tilTemporaryNegativeEffects[i].end();

                                        for (; effItr != effEnd; ++effItr) {
                                            if (*effItr == litID) {
                                                TILoffset -= ((insLayer - earliestTILtime) + EpsilonResolutionTimestamp::epsilon());
                                                if (TILoffset < stateTS) {
                                                    if (evaluateDebug) cout << "Dead end found: TIL definitely going to delete invariant of open action\n";
                                                    return false;
                                                }
                                                break;
                                            }

                                        }
                                    }
                                }

                            }
                        }
                    }
                    if (nextTIL < tilCount) {
                        list<Literal*> & invs = (*actionsToEndPreconditions)[currActID];
                        list<Literal*>::iterator precItr = invs.begin();
                        const list<Literal*>::iterator precEnd = invs.end();

                        for (; precItr != precEnd; ++precItr) {
                            const int litID = (*precItr)->getStateID();
                            for (int i = nextTIL; i < tilCount; ++i) {
                                const EpsilonResolutionTimestamp earliestTILtime = EpsilonResolutionTimestamp(tilTimes[i],true) - TILoffset;

                                if (earliestTILtime < insLayer) {
                                    list<int>::iterator effItr = tilNegativeEffects[i].begin();
                                    const list<int>::iterator effEnd = tilNegativeEffects[i].end();

                                    for (; effItr != effEnd; ++effItr) {
                                        if (*effItr == litID) {
                                            TILoffset -= ((insLayer - earliestTILtime) + EpsilonResolutionTimestamp::epsilon());
                                            if (TILoffset < stateTS) {
                                                if (evaluateDebug) cout << "Dead end found: TIL definitely going to delete invariant of open action\n";
                                                return false;
                                            }
                                            break;
                                        }

                                    }
                                }
                            }
                        }

                    }
                }

                if (!affectedStarts.empty() || !affectedEnds.empty()) {
                    assert(insLayer >= EpsilonResolutionTimestamp::zero());
                    payload->factLayers[insLayer].endOfJustApplied = &(setsToForbid.back());
                    {
                        set<int>::iterator sItr = affectedStarts.begin();
                        const set<int>::iterator sEnd = affectedStarts.end();
                        for (; sItr != sEnd; ++sItr) {
                            assert(*sItr < RPGBuilder::getStartPropositionalPreconditions().size());
                            ++(payload->forbiddenStart.insert(pair<int, int>(*sItr, 0)).first->second);
                            if (evaluateDebug) {
                                cout << "Start of " << *sItr << " now delayed because of " << payload->forbiddenStart[*sItr] << " actions\n";
                            }
                        }
                    }
                    {
                        set<int>::iterator sItr = affectedEnds.begin();
                        const set<int>::iterator sEnd = affectedEnds.end();
                        for (; sItr != sEnd; ++sItr) {
                            assert(*sItr < RPGBuilder::getStartPropositionalPreconditions().size());
                            ++(payload->forbiddenEnd.insert(pair<int, int>(*sItr, 0)).first->second);
                            if (evaluateDebug) {
                                cout << "End of " << *sItr << " now delayed because of " << payload->forbiddenEnd[*sItr] << " actions\n";
                            }
                        }
                    }

                }
                if (!affectedEnds.empty()) {
                    set<int>::iterator sItr = affectedEnds.begin();
                    const set<int>::iterator sEnd = affectedEnds.end();

                    for (; sItr != sEnd; ++sItr) {
                        const double actDur = payload->actionDurations[*sItr].second;
                        const EpsilonResolutionTimestamp earlierIns = insLayer - EpsilonResolutionTimestamp(actDur,false);
                        if (earlierIns > EpsilonResolutionTimestamp::zero()) {
                            assert(earlierIns >= EpsilonResolutionTimestamp::zero());
                            FactLayerEntry & fle = payload->factLayers[earlierIns];
                            if (!fle.endOfJustApplied) {
                                setsToForbid.push_back(pair<set<int>, set<int> >());
                                fle.endOfJustApplied = &(setsToForbid.back());
                                fle.endOfJustApplied->first.insert(*sItr);
                                ++(payload->forbiddenStart.insert(pair<int, int>(*sItr, 0)).first->second);
                            } else if (fle.endOfJustApplied->first.insert(*sItr).second) {
                                ++(payload->forbiddenStart.insert(pair<int, int>(*sItr, 0)).first->second);
                            }

                        }

                    }


                }
            }
            if (insLayer > EpsilonResolutionTimestamp::zero()) {
                list<pair<int, int> >::iterator liItr = jaItr->second.begin();
                const list<pair<int, int> >::iterator liEnd = jaItr->second.end();

                for (; liItr != liEnd; ++liItr) {
                    const int currActID = liItr->first;
                    EpsilonResolutionTimestamp & eas = payload->openEndActionSchedule[currActID];
                    if (eas.isUndefined()) {
                        eas = insLayer;
                        if (evaluateDebug) cout << "ii) Delaying end of " << currActID << " until " << insLayer << "\n";
                    }

                }

            }
        }

        return true;
    }

    void performTILInitialisation() {

        if (tilInitialised) return;

        tilInitialised = true;
        vector<RPGBuilder::FakeTILAction*> & TILs = RPGBuilder::getNonAbstractedTILVec();
        tilCount = TILs.size();
        tilEffects = vector<list<int> >(tilCount);
        tilNegativeEffects = vector<list<int> >(tilCount);
        tilTemporaryNegativeEffects = vector<list<int> >(tilCount);
        tilTimes = vector<double>(tilCount);

        {
            const int loopLim = processedPreconditionsToActions->size();
            deadlineAtTime = vector<EpsilonResolutionTimestamp>(loopLim,EpsilonResolutionTimestamp::infinite());

        }

        earliestDeadlineRelevancyStart = vector<EpsilonResolutionTimestamp>(initialUnsatisfiedEndPreconditions->size(), EpsilonResolutionTimestamp::undefined());
        earliestDeadlineRelevancyEnd = vector<EpsilonResolutionTimestamp>(initialUnsatisfiedEndPreconditions->size(), EpsilonResolutionTimestamp::undefined());


        vector<RPGBuilder::FakeTILAction*>::reverse_iterator tilItr = TILs.rbegin();
        const vector<RPGBuilder::FakeTILAction*>::reverse_iterator tilEnd = TILs.rend();

        set<int> addedLater;

        for (int i = tilCount - 1; tilItr != tilEnd; ++tilItr, --i) {

            tilTimes[i] = (*tilItr)->duration;


            {
                list<Literal*>::iterator effItr = (*tilItr)->addEffects.begin();
                const list<Literal*>::iterator effEnd = (*tilItr)->addEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    tilEffects[i].push_back(currEffID);
                    addedLater.insert(currEffID);
                }
            }

            {
                list<Literal*>::iterator effItr = (*tilItr)->delEffects.begin();
                const list<Literal*>::iterator effEnd = (*tilItr)->delEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    tilTemporaryNegativeEffects[i].push_back(currEffID);
                    if ((*effectsToActions)[currEffID].empty() && addedLater.find(currEffID) == addedLater.end()) {
                        tilNegativeEffects[i].push_back(currEffID);
                        deadlineAtTime[currEffID] = EpsilonResolutionTimestamp(tilTimes[i],true);
                    }
                }
            }


        }


    }

    void initialiseLatestArrays() {

        static bool initLatestArrays = false;


        static const int easSize = initialUnsatisfiedEndPreconditions->size();

        if (!initLatestArrays) {
            earliestStartAllowed = vector<EpsilonResolutionTimestamp>(easSize, EpsilonResolutionTimestamp::undefined());
            earliestEndAllowed = vector<EpsilonResolutionTimestamp>(easSize, EpsilonResolutionTimestamp::undefined());
            latestStartAllowed = vector<EpsilonResolutionTimestamp>(easSize, EpsilonResolutionTimestamp::undefined());
            latestEndAllowed = vector<EpsilonResolutionTimestamp>(easSize, EpsilonResolutionTimestamp::undefined());
            initLatestArrays = true;
        }



        for (int i = 0; i < easSize; ++i) latestStartAllowed[i] = EpsilonResolutionTimestamp::infinite();
        for (int i = 0; i < easSize; ++i) latestEndAllowed[i] = EpsilonResolutionTimestamp::infinite();

        if (expandFully) {
            for (int i = 0; i < easSize; ++i) earliestStartAllowed[i] = EpsilonResolutionTimestamp::infinite();
            for (int i = 0; i < easSize; ++i) earliestEndAllowed[i] = EpsilonResolutionTimestamp::infinite();
        }
    }

    void addTILsBeforeExpansion(BuildingPayload * const payload, const int & nextTIL, FactLayerMap & factLayers, const MinimalState & stateBeingEvaluated, const EpsilonResolutionTimestamp & stateTS, const double & tilFrom) {
        if (nextTIL < tilCount) {

            static const int easSize = initialUnsatisfiedEndPreconditions->size();

            for (int i = 0; i < easSize; ++i) earliestDeadlineRelevancyStart[i] = EpsilonResolutionTimestamp::infinite();
            for (int i = 0; i < easSize; ++i) earliestDeadlineRelevancyEnd[i] = EpsilonResolutionTimestamp::infinite();


            set<int> earlier;

            const double TILoffset = (RPGBuilder::modifiedRPG ? 0.000 : (nextTIL < tilCount ? tilTimes[nextTIL] - tilFrom : 0.0));

            for (int i = nextTIL; i < tilCount; ++i) {
                const EpsilonResolutionTimestamp thisTS(tilTimes[i] - TILoffset,true);
                assert(thisTS >= EpsilonResolutionTimestamp::zero());
                factLayers[thisTS].TILs.push_back(i);
                /*{
                    list<int>::iterator effItr = tilEffects[i].begin();
                    const list<int>::iterator effEnd = tilEffects[i].end();

                    for (; effItr != effEnd; ++effItr) {

                        const int currEff = (*effItr);
                        #ifdef POPF3ANALYSIS
                        if (achieverDetails[currEff].empty()) {
                            if (earlier.insert(currEff).second) {
                                assert(thisTS >= EpsilonResolutionTimestamp::zero());
                                factLayers[thisTS].TILs.push_back(pair<int, int>(i, currEff));
                            }
                        }
                        #else
                        double & currAIL = (*achievedInLayer)[currEff];                
                        if (currAIL == EpsilonResolutionTimestamp::undefined() && (*achievedBy)[currEff].first == -1) { // not in initial state
                            if (earlier.insert(currEff).second) {
                                assert(thisTS >= EpsilonResolutionTimestamp::zero());
                                factLayers[thisTS].TILs.push_back(pair<int, int>(i, currEff));
                            }
                        }
                        #endif

                    }
                }*/


            }

            for (int i = nextTIL; i < tilCount; ++i) {
                const EpsilonResolutionTimestamp thisTS = EpsilonResolutionTimestamp(tilTimes[i],true) - stateTS;

                list<int>::iterator effItr = tilNegativeEffects[i].begin();
                const list<int>::iterator effEnd = tilNegativeEffects[i].end();

                for (; effItr != effEnd; ++effItr) {

                    list<pair<int, Planner::time_spec> > & currList = (*preconditionsToActions)[*effItr];

                    list<pair<int, Planner::time_spec> >::iterator ioItr = currList.begin();
                    const list<pair<int, Planner::time_spec> >::iterator ioEnd = currList.end();

                    for (; ioItr != ioEnd; ++ioItr) {
                        const int actID = ioItr->first;
                        if (ioItr->second == Planner::E_AT_START) {
                            if (latestStartAllowed[actID] > thisTS) latestStartAllowed[actID] = thisTS;
                            const EpsilonResolutionTimestamp maxDur(RPGBuilder::getOpMaxDuration(actID, 0),false);
                            if (latestEndAllowed[actID] > thisTS + maxDur) latestEndAllowed[actID] = thisTS + maxDur;
                        } else {
                            const EpsilonResolutionTimestamp minDur(payload->actionDurations[actID].first,false);
                            if (latestStartAllowed[actID] > thisTS - minDur) latestStartAllowed[actID] = thisTS - minDur;
                            if (latestEndAllowed[actID] > thisTS) latestEndAllowed[actID] = thisTS;
                        }
                    }


                }

            }
        }
        
        // now deal with limits from abstracted TILs
        
        if (RPGBuilder::modifiedRPG) {
        
            static const double abstractTILDebug = (Globals::globalVerbosity & 64);
            
            payload->abstractFactCurrentlyTrue.resize(RPGBuilder::getNegativeEffectsToActions().size(),false);
            
            const map<int, TILTimeline> & timelines = TemporalAnalysis::getTILTimelines();
            
            map<int, TILTimeline>::const_iterator factItr = timelines.begin();
            const map<int, TILTimeline>::const_iterator factEnd = timelines.end();
            
            for (; factItr != factEnd; ++factItr) {
                if (!TemporalAnalysis::getFactIsAbstract()[factItr->first]) {
                    continue;
                }
                
                StateFacts::const_iterator presentItr = stateBeingEvaluated.first.find(factItr->first);
                if (presentItr == stateBeingEvaluated.first.end()) {
                    if (abstractTILDebug) {
                        cout << COLOUR_light_blue << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << " - not in state, assuming it's expired\n" << COLOUR_default;
                    }
                    continue;
                }
                
                if (abstractTILDebug) {
                    cout << COLOUR_light_blue << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << ":";
                    cout.flush();
                }
                
                EpsilonResolutionTimestamp earliestPossibleOccurrence(EpsilonResolutionTimestamp::zero());
                
                if (presentItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {                
                    const double & earliestAsDouble = payload->minTimestamps[presentItr->second.availableFrom.stepID];
                    assert(earliestAsDouble >= 0.0); // initial state adds should have a 'BEFORE' label
                    
                    // because TILs true initially need to have a 'zero' timestamp for their fact layer index,
                    // TIL facts that are (at x y) are actually put in fact layer x + epsilon
                    
                    earliestPossibleOccurrence = EpsilonResolutionTimestamp(earliestAsDouble, true);
                    ++earliestPossibleOccurrence;

                }

                bool currentlyFalse = true;
                
                TILTimeline::const_iterator tItr = factItr->second.begin();
                const TILTimeline::const_iterator tEnd = factItr->second.end();
                
                if (tItr->first < 0.0) {
                    // skip over initial-state adds for our sanity
                    assert(tItr->second.added);
                    currentlyFalse = false;
                    ++tItr;
                }
                
                for (; tItr != tEnd; ++tItr) {
                    
                    EpsilonResolutionTimestamp thisEvent(tItr->first, true);
                    ++thisEvent; // fact layer in which facts added by this TIL will appear
                    
                    if (thisEvent < earliestPossibleOccurrence) {
                    
                        if (tItr->second.deleted) {
                            currentlyFalse = true;
                        }
                        if (tItr->second.added) {
                            currentlyFalse = false;
                        }
                        
                    } else {
                        break;
                    }                
                }
                
                // tItr now points to the first TIL event on the timeline after the lower bound taken in
                
                if (!currentlyFalse) {
                    // if it's true at this point, add it to the TRPG to be come true then
                    factLayers[earliestPossibleOccurrence].abstractFactBecomesTrue.push_back(factItr->first);
                    if (abstractTILDebug) {
                        cout << " +" << earliestPossibleOccurrence << ";";
                        cout.flush();
                    }
                }
                
                for (; tItr != tEnd; ++tItr) {
                    
                    EpsilonResolutionTimestamp thisEvent(tItr->first, true);
                    ++thisEvent; // fact layer in which facts added by this TIL will appear
                    
                    if (currentlyFalse) {
                        if (tItr->second.added) {
                            factLayers[thisEvent].abstractFactBecomesTrue.push_back(factItr->first);
                            if (abstractTILDebug) {
                                cout << " +" << thisEvent << ";";
                                cout.flush();
                            }
                            currentlyFalse = false;
                        }
                    } else {
                        if (tItr->second.deleted && !tItr->second.added) {
                            factLayers[thisEvent].abstractFactBecomesFalse.push_back(factItr->first);
                            currentlyFalse = true;
                            if (abstractTILDebug) {
                                cout << " -" << thisEvent << ";";
                                cout.flush();
                            }
                        }
                    }
                    
                }
                
                if (abstractTILDebug) {
                    cout << endl << COLOUR_default;
                }
            }
        }
    }

    void addBoundsFromTemporalAnalysis(const double & stateTS) {

        const int actCount = latestStartAllowed.size();

        if (RPGBuilder::modifiedRPG) {
            for (int a = 0; a < actCount; ++a) {
                {
                    double firmUpper = TemporalAnalysis::getActionTSBounds()[a][0].second;
                    if (firmUpper != DBL_MAX) {
                        EpsilonResolutionTimestamp rounded(firmUpper,false);
                        if (rounded < latestStartAllowed[a]) latestStartAllowed[a] = rounded;
                    }
                }
                {
                    double firmUpper = TemporalAnalysis::getActionTSBounds()[a][1].second;
                    if (firmUpper != DBL_MAX) {
                        EpsilonResolutionTimestamp rounded(firmUpper,false);
                        if (rounded < latestEndAllowed[a]) latestEndAllowed[a] = rounded;
                    }
                }
            }
        } else {
        
            for (int a = 0; a < actCount; ++a) {
                {
                    double firmUpper = TemporalAnalysis::getActionTSBounds()[a][0].second;
                    if (firmUpper != DBL_MAX) {
                        firmUpper -= stateTS;
                        EpsilonResolutionTimestamp rounded(firmUpper,false);
                        if (rounded < latestStartAllowed[a]) latestStartAllowed[a] = rounded;
                    }
                    if (latestStartAllowed[a] < EpsilonResolutionTimestamp::zero() ) latestEndAllowed[a] = EpsilonResolutionTimestamp::undefined();
                }
                {
                    double firmUpper = TemporalAnalysis::getActionTSBounds()[a][1].second;
                    if (firmUpper != DBL_MAX) {
                        firmUpper -= stateTS;
                        EpsilonResolutionTimestamp rounded(firmUpper,false);
                        if (rounded < latestEndAllowed[a]) latestEndAllowed[a] = rounded;
                    }
                    if (latestEndAllowed[a] < EpsilonResolutionTimestamp::zero() ) latestStartAllowed[a] = EpsilonResolutionTimestamp::undefined();
                }

            }
        }

    }

    EpsilonResolutionTimestamp earliestTILForAction(const unsigned int & i, const bool & isStart);
    void findApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions);
    void filterApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions);
    bool testApplicability(const MinimalState & theState, const double & stateTime, const ActionSegment & actID, const bool & fail, const bool & ignoreDeletes);

    instantiatedOp* getOp(const unsigned int & i) {

        assert(i >= 0);
        assert(i < actionsToEndEffects->size());
        return RPGBuilder::getInstantiatedOp(i);

    };


    bool sensiblePair(const BuildingPayload * const payload, const pair<int, Planner::time_spec> & achiever, const unsigned int & fact) {
        assert(fact >= 0);
        assert(fact < preconditionsToActions->size());

        if (achiever.second == Planner::E_AT) {
            assert(tilInitialised);
            assert(achiever.first >= 0);
            assert(achiever.first < tilCount);
        } else {
            if (achiever.first < 0) {
                cerr << "\t\tTrying to use a negative indexed action as an achiever for fact " << *(RPGBuilder::getLiteral(fact)) << "\n";
                if (payload->startState.first.find(fact) != payload->startState.first.end()) {
                    cerr << "\t\t\tWas true in the initial state\n";
                }

                assert(achiever.first >= 0);
            }
            assert((unsigned int) achiever.first < actionsToEndPreconditions->size());
        }

        return true;
    }

    void addGoalsForPreferences(BuildingPayload * const payload, RPGRegressionMap & goalsAtLayer) {
        
        
        list<list<Literal*> > desired;
        list<list<Literal*> > desiredNegative;
        list<list<int> > desiredNumeric;
        
        PreferenceHandler::getDesiredGoals(desired, desiredNegative,
                                           &desiredNumeric,
                                           payload->startState, payload->initialUnsatisfiedPreferenceConditions, payload->optimisticPrefStatus,
                                           achieverDetails, *negativeAchievedInLayer, numericAchievedInLayer);
        
        {
            list<list<Literal*> >::const_iterator dItr = desired.begin();
            const list<list<Literal*> >::const_iterator dEnd = desired.end();
        
            for (; dItr != dEnd; ++dItr) {
            
                list<Literal*>::const_iterator fItr = (*dItr).begin();
                const list<Literal*>::const_iterator fItrEnd = (*dItr).end();
                
                for (; fItr != fItrEnd; ++fItr) {

                    const int currGoal = (*fItr)->getStateID();
                    const EpsilonResolutionTimestamp & insLayer = achieverDetails[currGoal].back().getLayer();
                    if (insLayer > EpsilonResolutionTimestamp::zero()) {
                        const int achiever = achieverDetails[currGoal].back().getAchiever().first;
                        if (achiever != -1) {
                            goalsAtLayer[insLayer].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currGoal, EpsilonResolutionTimestamp::infinite()));
                            if (evaluateDebug) cout << "Preference goal " << *(*fItr) << " to be achieved in layer with TS " << insLayer << "\n";
                        } else {
                            assert(payload->startState.first.find(currGoal) != payload->startState.first.end());
                            if (evaluateDebug) cout << "Preference goal " << *(*fItr) << " achieved in initial state at layer " << insLayer << "\n";
                        }
                    } else if (evaluateDebug) cout << "Preference goal " << *(*fItr) << " achieved in initial state, not adding to RPG regression\n";

                }
            }
        }
        
        {
            list<list<Literal*> >::const_iterator dItr = desiredNegative.begin();
            const list<list<Literal*> >::const_iterator dEnd = desiredNegative.end();
        
            for (; dItr != dEnd; ++dItr) {
            
                list<Literal*>::const_iterator fItr = (*dItr).begin();
                const list<Literal*>::const_iterator fItrEnd = (*dItr).end();
                
                for (; fItr != fItrEnd; ++fItr) {

                    const int currGoal = (*fItr)->getStateID();
                    const EpsilonResolutionTimestamp & insLayer = (*negativeAchievedInLayer)[currGoal];
                    if (insLayer > EpsilonResolutionTimestamp::zero()) {
                        const int achiever = (*negativeAchievedBy)[currGoal].first;
                        if (achiever != -1) {
                            goalsAtLayer[insLayer].negativePropositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currGoal, EpsilonResolutionTimestamp::infinite()));
                            if (evaluateDebug) cout << "Preference goal ¬" << *(*fItr) << " to be achieved in layer with TS " << insLayer << "\n";
                        } else {
                            assert(payload->startState.first.find(currGoal) == payload->startState.first.end());
                            if (evaluateDebug) cout << "Preference goal ¬" << *(*fItr) << " achieved in initial state at layer " << insLayer << "\n";
                        }
                    } else if (evaluateDebug) cout << "Preference goal ¬" << *(*fItr) << " achieved in initial state, not adding to RPG regression\n";

                }
            }
        }
        {
            list<list<int> >::const_iterator dNumItr = desiredNumeric.begin();
            const list<list<int> >::const_iterator dNumEnd = desiredNumeric.end();
            for (; dNumItr != dNumEnd; ++dNumItr) {

                list<int>::const_iterator nItr = (*dNumItr).begin();
                const list<int>::const_iterator nEnd = (*dNumItr).end();
                for (; nItr != nEnd; ++nItr) {

                    const int currGoal = *nItr;
                    const EpsilonResolutionTimestamp & insLayer = (*numericAchievedInLayer)[currGoal];
                
                    if (numericIsTrueInState[currGoal]) {
                        
                        if (evaluateDebug) cout << "Numeric goal achieved in state, not adding to RPG regression\n";
                        continue;
                    }
                    
                    assert(insLayer > EpsilonResolutionTimestamp::zero());
                        
                    if (evaluateDebug) cout << "Numeric goal to be achieved in layer with TS " << insLayer << "\n";                    
                    payload->fluentLayers.requestGoal(currGoal, insLayer, goalsAtLayer);
                }
            }
        }
        
    }

    void addExtraPreconditionsForPreferences(BuildingPayload * const payload,
                                             const int & act, const Planner::time_spec & ts,
                                             const EpsilonResolutionTimestamp & currTS, const EpsilonResolutionTimestamp & tilR,
                                             RPGRegressionMap & goalsAtLayer) {
        
        map<pair<int, Planner::time_spec>, list<pair<int,bool> > >::const_iterator extras =  payload->preferencePartsToSatisfyBeforeAction.find(make_pair(act,ts));
        
        if (extras != payload->preferencePartsToSatisfyBeforeAction.end()) {
        
            list<pair<int,bool> >::const_iterator prefPItr = extras->second.begin();
            const list<pair<int,bool> >::const_iterator prefPEnd = extras->second.end();
            for (; prefPItr != prefPEnd; ++prefPItr) {
                
                const EpsilonResolutionTimestamp & trueInLayer = payload->preferencePartTrueAtLayer[prefPItr->first][prefPItr->second ? 1 : 0];
                
                if (trueInLayer >= currTS) {
                    if (evaluateDebug) cout << COLOUR_yellow << "\t\tToo early to manage to satisfy preference " << prefPItr->first << COLOUR_default << endl;
                    continue;
                } else {
                    if (evaluateDebug) cout << COLOUR_yellow << "\t\tPreference " << prefPItr->first << " was satisfied in layer " << trueInLayer << " - adding preconditions" << COLOUR_default << endl;
                }
                
                
                list<Literal*> extraPreconditionList;
                list<Literal*> extraNegativePreconditionList;
                list<int> extraNumericPreconditionList;
                
                PreferenceHandler::getPreconditionsToSatisfy(extraPreconditionList, extraNegativePreconditionList,
                                                             &extraNumericPreconditionList,
                                                             *prefPItr, currTS,
                                                             achieverDetails, *negativeAchievedInLayer,
                                                             numericAchievedInLayer);
                
                {
                    list<Literal*>::const_iterator aplItr = extraPreconditionList.begin();
                    const list<Literal*>::const_iterator aplEnd = extraPreconditionList.end();
                    for (; aplItr != aplEnd; ++aplItr) {

                        const int currPrec = (*aplItr)->getStateID();
                        EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                        pair<int, Planner::time_spec> acBy;
                        
                        if (evaluateDebug) {
                            cout << "\t\tPreference precondition " << currPrec << " " << *(RPGBuilder::getLiteral(currPrec)) << ": ";
                            cout.flush();
                        }
                        
                        getAchieverDetails(currPrec, currTS, acIn, acBy);
                            
                        if (acIn > EpsilonResolutionTimestamp::zero()) {
                            if (acBy.first != -1) {
                                map<int, EpsilonResolutionTimestamp>::iterator insItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                if (insItr->second > tilR) insItr->second = tilR;
                                if (evaluateDebug) cout << "required at time " << acIn << "\n";
                                assert(acIn < currTS);
                                //isHelpful = false;
                            } else {
                                if (evaluateDebug) cout << "in initial state at layer " << acIn << "\n";
                            }
                        } else {
                            if (evaluateDebug) cout << "in initial state\n";
                        }

                    }
                }
                
                {
                    list<Literal*>::const_iterator aplItr = extraNegativePreconditionList.begin();
                    const list<Literal*>::const_iterator aplEnd = extraNegativePreconditionList.end();
                    for (; aplItr != aplEnd; ++aplItr) {

                        const int currPrec = (*aplItr)->getStateID();
                        const EpsilonResolutionTimestamp & acIn = (*negativeAchievedInLayer)[currPrec];
                        const pair<int, Planner::time_spec> acBy = (*negativeAchievedBy)[currPrec];
                        
                        if (evaluateDebug) {
                            cout << "\t\tPreference precondition " << currPrec << " ¬" << *(RPGBuilder::getLiteral(currPrec)) << ": ";
                            cout.flush();
                        }
                        if (acIn > EpsilonResolutionTimestamp::zero()) {
                            if (acBy.first != -1) {
                                map<int, EpsilonResolutionTimestamp>::iterator insItr = goalsAtLayer[acIn].negativePropositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                if (insItr->second > tilR) insItr->second = tilR;
                                if (evaluateDebug) cout << "required at time " << acIn << "\n";
                                assert(acIn < currTS);
                                //isHelpful = false;
                            } else {
                                if (evaluateDebug) cout << "in initial state at layer " << acIn << "\n";
                            }
                        } else {
                            if (evaluateDebug) cout << "in initial state\n";
                        }

                    }
                }
                
                {
                    list<int>::const_iterator aplItr = extraNumericPreconditionList.begin();
                    const list<int>::const_iterator aplEnd = extraNumericPreconditionList.end();
                    
                    for (; aplItr != aplEnd; ++aplItr) {

                        const int currPrec = (*aplItr);
                        const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                        if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                            if (evaluateDebug) cout << "\t\tAdding requirement for numeric preference precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " at time " << acIn << "\n";
                            
                            payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS, goalsAtLayer, tilR);
                            //isHelpful = false;
                        } else {
                            if (evaluateDebug) cout << "\t\tNumeric preference precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << ", satisfied in initial state\n";
                        }

                    }
                                    
                }
            }
        }
    
        
    }


    void extractRP(BuildingPayload * const payload, int & h, list<pair<double, list<ActionSegment> > > & relaxedPlan, pair<int, Planner::time_spec> & earliestTIL, double & makespanEstimate,
                   const vector<EpsilonResolutionTimestamp> & earliestRelevanceOfGoal) {

        makespanEstimate = 0.0;
        
        int latestTIL = 0;
        {
            const int mtSize = payload->minTimestamps.size();
            for (int mt = 0; mt < mtSize; ++mt) {
                if (payload->minTimestamps[mt] > makespanEstimate) {
                    makespanEstimate = payload->minTimestamps[mt];
                }
            }
        }

        const MinimalState & theState = payload->startState;
        map<int, set<int> > & insistUponEnds = payload->insistUponEnds;
        vector<EpsilonResolutionTimestamp> & startActionSchedule = payload->startActionSchedule;
        vector<EpsilonResolutionTimestamp> & openEndActionSchedule = payload->openEndActionSchedule;

        payload->fluentLayers.prepareForExtraction();
        
        static const set<int> emptyIntSet;

        RPGRegressionMap goalsAtLayer;

        {
            set<int>::iterator gsItr = goals.begin();
            const set<int>::iterator gsEnd = goals.end();

            for (; gsItr != gsEnd; ++gsItr) {
                const int currGoal = *gsItr;
                #ifdef POPF3ANALYSIS
                const EpsilonResolutionTimestamp & insLayer = achieverDetails[currGoal].back().getLayer();
                if (insLayer > EpsilonResolutionTimestamp::zero()) {
                    const int achiever = achieverDetails[currGoal].back().getAchiever().first;
                #else
                const EpsilonResolutionTimestamp & insLayer = (*achievedInLayer)[currGoal];
                if (insLayer > 0.0) {
                    const int achiever = (*achievedBy)[currGoal].first;                    
                #endif
                    if (achiever != -1) {
                        #ifdef POPF3ANALYSIS
                        const map<int,int>::const_iterator fToG = RPGBuilder::getLiteralsToGoalIndex().find(*gsItr);
                        assert(fToG != RPGBuilder::getLiteralsToGoalIndex().end());                        
                        #ifndef NDEBUG
                        if (earliestRelevanceOfGoal.size() <= fToG->second) {
                            cerr << "Fatal error: fact " << *(RPGBuilder::getLiteral(*gsItr)) << " is down as being goal " << fToG->second << ", but this does not exist\n";
                            cerr << "Number of literal goals: " << RPGBuilder::getLiteralGoals().size() << ", size of the local goal set: " << goals.size() << endl;
                            exit(1);
                        }
                        #endif
                        goalsAtLayer[insLayer].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currGoal, earliestRelevanceOfGoal[fToG->second]));
                        #else
                        goalsAtLayer[insLayer].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currGoal, EpsilonResolutionTimestamp::infinite()));
                        #endif
                        if (evaluateDebug) cout << "Goal " << *(RPGBuilder::getLiteral(*gsItr)) << " to be achieved in layer with TS " << insLayer << "\n";
                    } else {
                        assert(payload->startState.first.find(currGoal) != payload->startState.first.end());
                        if (evaluateDebug) cout << "Goal " << *(RPGBuilder::getLiteral(*gsItr)) << " achieved in initial state at layer " << insLayer << "\n";
                    }
                } else if (evaluateDebug) cout << "Goal " << *(RPGBuilder::getLiteral(*gsItr)) << " achieved in initial state, not adding to RPG regression\n";


                if (insLayer.toDouble() > makespanEstimate) {
                    makespanEstimate = insLayer.toDouble();
                }
            }
        }

        if (!ignoreNumbers) {
            set<int>::iterator gfItr = goalFluents.begin();
            set<int>::iterator gfEnd = goalFluents.end();

            for (; gfItr != gfEnd; ++gfItr) {
                const int currGoal = *gfItr;
                const EpsilonResolutionTimestamp & insLayer = (*numericAchievedInLayer)[currGoal];
                
                if (insLayer.toDouble() > makespanEstimate) {
                    makespanEstimate = insLayer.toDouble();
                }
                
                if (numericIsTrueInState[currGoal]) {
                    
                    if (evaluateDebug) cout << "Numeric goal achieved in state, not adding to RPG regression\n";
                    continue;
                }
                
                assert(insLayer > EpsilonResolutionTimestamp::zero());
                    
                if (evaluateDebug) cout << "Numeric goal to be achieved in layer with TS " << insLayer << "\n";                    
                payload->fluentLayers.requestGoal(currGoal, insLayer, goalsAtLayer);

                

            }
        }


        if (!RPGBuilder::nonTemporalProblem()) {
            map<int, set<int> >::iterator ueItr = insistUponEnds.begin();
            const map<int, set<int> >::iterator ueEnd = insistUponEnds.end();

            for (; ueItr != ueEnd; ++ueItr) {
                const int currAct = ueItr->first;
                const EpsilonResolutionTimestamp & insLayer = openEndActionSchedule[currAct];
                if (evaluateDebug) cout << "End of " << *(RPGBuilder::getInstantiatedOp(currAct)) << " goes at " << insLayer << endl;
                const EpsilonResolutionTimestamp tilR = earliestTILForAction(currAct, false);
                (goalsAtLayer[insLayer + EpsilonResolutionTimestamp::epsilon()].actionEnds.insert(pair<int, pair<int, EpsilonResolutionTimestamp> >(currAct, pair<int, EpsilonResolutionTimestamp>(0, tilR))).first->second.first) += ueItr->second.size();
                // HACK
            }
        }
        
        addGoalsForPreferences(payload, goalsAtLayer);


        while (!goalsAtLayer.empty()) {

            const EpsilonResolutionTimestamp currTS = goalsAtLayer.rbegin()->first;
            map<int, EpsilonResolutionTimestamp> & currPositiveGAL = goalsAtLayer.rbegin()->second.propositionalGoals;
            map<int, EpsilonResolutionTimestamp> & currNegativeGAL = goalsAtLayer.rbegin()->second.negativePropositionalGoals;
            
            if (evaluateDebug) cout << COLOUR_light_green << currTS << ":\n" <<     COLOUR_default;
            map<int, pair<int, EpsilonResolutionTimestamp> > & actionStarts = goalsAtLayer.rbegin()->second.actionStarts;
            map<int, pair<int, EpsilonResolutionTimestamp> > & actionEnds   = goalsAtLayer.rbegin()->second.actionEnds;
            
            bool alreadyPushed = false;

            {


                map<int, pair<int, EpsilonResolutionTimestamp> >::iterator asItr = actionStarts.begin();
                const map<int, pair<int, EpsilonResolutionTimestamp> >::iterator asEnd = actionStarts.end();

                if (evaluateDebug && asItr != asEnd) cout << "Adding starts at TS " << currTS << "\n";

                for (; asItr != asEnd; ++asItr) {

                    if (evaluateDebug) cout << "\t\tAdding start of " << asItr->first << ": " << *(RPGBuilder::getInstantiatedOp(asItr->first)) << endl;

                    EpsilonResolutionTimestamp tilR = earliestTILForAction(asItr->first, true);
                    if (tilR > asItr->second.second) tilR = asItr->second.second;

                    if (!alreadyPushed) {
                        relaxedPlan.push_front(pair<double, list<ActionSegment> >((currTS - EpsilonResolutionTimestamp::epsilon()).toDouble(), list<ActionSegment>()));
                        alreadyPushed = true;
                    }

                    relaxedPlan.front().second.insert(relaxedPlan.front().second.end(), asItr->second.first, ActionSegment(getOp(asItr->first), Planner::E_AT_START, -1, emptyIntList));
                    ++h;

                    if (RPGHeuristic::printRPGAsDot) {
                        payload->dot.highlightAction(asItr->first, Planner::E_AT_START);
                    }
                    
    //              if (currTS == EPSILON) {
    //                  helpfulActions.push_back(pair<int, Planner::time_spec>(*asItr, Planner::E_AT_START));
    //                  if (evaluateDebug) cout << "\t\tIs a helpful action\n";
    //              }

                    for (int pass = 0; pass < 2; ++pass) {
                        
                        map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                        
                        list<Literal*> & actionEffectsList = (pass ? (*actionsToStartNegativeEffects)[asItr->first] : (*actionsToStartEffects)[asItr->first]);
                        list<Literal*>::iterator aelItr = actionEffectsList.begin();
                        const list<Literal*>::iterator aelEnd = actionEffectsList.end();

                        for (; aelItr != aelEnd; ++aelItr) {
                            map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                            if (cgItr != currGAL.end()) {
                                if (tilR > cgItr->second) tilR = cgItr->second;
                                currGAL.erase(cgItr);
                            }
                        }
                    }
                    

                    bool isHelpful = true;

                    {
                        list<Literal*> & actionPreconditionlist = (*actionsToProcessedStartPreconditions)[asItr->first];
                        list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                        const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();

                        if (evaluateDebug) cout << "\t\tPreconditions:\n";

                        for (; aplItr != aplEnd; ++aplItr) {

                            const int currPrec = (*aplItr)->getStateID();
                            EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                            pair<int, Planner::time_spec> acBy;
                            
                            if (evaluateDebug) {
                                cout << "\t\tPrecondition " << currPrec << " " << *(RPGBuilder::getLiteral(currPrec)) << ": ";
                                cout.flush();
                            }
                            
                            getAchieverDetails(currPrec, currTS, acIn, acBy);
                                
                            if (acIn > EpsilonResolutionTimestamp::zero()) {
                                if (acBy.first != -1) {
                                    map<int, EpsilonResolutionTimestamp>::iterator insItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                    if (insItr->second > tilR) insItr->second = tilR;
                                    if (evaluateDebug) cout << "required at time " << acIn << " to support current time of " << currTS << "\n";
                                    assert(acIn <= currTS);
                                    isHelpful = false;
                                } else {
                                    if (evaluateDebug) cout << "in initial state at layer " << acIn << "\n";
                                }
                            } else {
                                if (evaluateDebug) cout << "in initial state\n";
                            }

                        }

                        if (evaluateDebug) cout << "\t\tPreconditions done.\n";
                    }

                    if (!ignoreNumbers) {
                        list<int> & actionPreconditionlist = (*actionsToProcessedStartNumericPreconditions)[asItr->first];
                        list<int>::iterator aplItr = actionPreconditionlist.begin();
                        const list<int>::iterator aplEnd = actionPreconditionlist.end();

                        if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                        for (; aplItr != aplEnd; ++aplItr) {

                            const int currPrec = (*aplItr);
                            const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                            if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " at time " << acIn << "\n";
                                
                                payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS, goalsAtLayer, tilR);
                                isHelpful = false;
                            } else {
                                if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << ", satisfied in initial state\n";
                            }

                        }

                        if (evaluateDebug) cout << "\t\tPreconditions done.\n";
                    }

                    addExtraPreconditionsForPreferences(payload, asItr->first, Planner::E_AT_START, currTS, tilR, goalsAtLayer);


                    if (isHelpful) {
                        payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(asItr->first), Planner::E_AT_START, -1, emptyIntSet));
                        if (evaluateDebug) cout << "\t\tIs a helpful action\n";
                    }

                    EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyStart[asItr->first];
                    if (oldR > tilR) oldR = tilR;

                }
            }

            {


                map<int, pair<int, EpsilonResolutionTimestamp> >::iterator asItr = actionEnds.begin();
                const map<int, pair<int, EpsilonResolutionTimestamp> >::iterator asEnd = actionEnds.end();

                if (evaluateDebug && asItr != asEnd) cout << "Adding ends at TS " << currTS << "\n";

                for (; asItr != asEnd; ++asItr) {

                    if (evaluateDebug) cout << "\t\tAdding end of " << asItr->first << "\n";

                    EpsilonResolutionTimestamp tilR = earliestTILForAction(asItr->first, false);
                    if (tilR > asItr->second.second) tilR = asItr->second.second;

                    if (RPGHeuristic::printRPGAsDot) {
                        payload->dot.highlightAction(asItr->first, Planner::E_AT_END);
                    }
                    

                    if (!alreadyPushed) {
                        relaxedPlan.push_front(pair<double, list<ActionSegment> >((currTS - EpsilonResolutionTimestamp::epsilon()).toDouble(), list<ActionSegment>()));
                        alreadyPushed = true;
                    }

                    if (!TemporalAnalysis::canSkipToEnd(asItr->first)) {
                        const int loopLim = asItr->second.first;
                        const ActionSegment theOp(getOp(asItr->first), Planner::E_AT_END, -1, emptyIntList);
                        for (int pb = 0; pb < loopLim; ++pb) {
                            relaxedPlan.front().second.push_back(theOp);
                        }
                        h += loopLim;
                    }


                    for (int pass = 0; pass < 2; ++pass) {
                        
                        map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                        
                        list<Literal*> & actionEffectsList = (pass ? (*actionsToEndNegativeEffects)[asItr->first] : (*actionsToEndEffects)[asItr->first]);
                        list<Literal*>::iterator aelItr = actionEffectsList.begin();
                        const list<Literal*>::iterator aelEnd = actionEffectsList.end();

                        for (; aelItr != aelEnd; ++aelItr) {
                            map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                            if (cgItr != currGAL.end()) {
                                if (tilR > cgItr->second) tilR = cgItr->second;
                                currGAL.erase(cgItr);
                            }
                        }
                    }

                    
                    bool isHelpful = true;

                    {
                        list<Literal*> & actionPreconditionlist = (*actionsToEndPreconditions)[asItr->first];
                        list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                        const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();

                        for (; aplItr != aplEnd; ++aplItr) {

                            const int currPrec = (*aplItr)->getStateID();
                            EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                            pair<int, Planner::time_spec> acBy;
                            
                            getAchieverDetails(currPrec, currTS, acIn, acBy);
                            
                            if (acIn > EpsilonResolutionTimestamp::zero()) {
                                if (acBy.first != -1) {
                                    map<int, EpsilonResolutionTimestamp>::iterator galItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                    if (galItr->second > tilR) galItr->second = tilR;
                                    isHelpful = false;
                                }
                            }

                        }


                    }

                    if (!ignoreNumbers) {
                        list<int> & actionPreconditionlist = (*actionsToNumericEndPreconditions)[asItr->first];
                        list<int>::iterator aplItr = actionPreconditionlist.begin();
                        const list<int>::iterator aplEnd = actionPreconditionlist.end();

                        if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                        for (; aplItr != aplEnd; ++aplItr) {

                            const int currPrec = (*aplItr);
                            const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                            if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " at time " << acIn << "\n";
                                
                                payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS, goalsAtLayer, tilR);
                                
                                isHelpful = false;
                            } else {
                                if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " satisfied in initial state\n";
                            }

                        }


                    }

                    addExtraPreconditionsForPreferences(payload, asItr->first, Planner::E_AT_END, currTS, tilR, goalsAtLayer);

                    if (evaluateDebug) cout << "\t\tPreconditions done.\n";


                    if (isHelpful) {
                        if (payload->startState.startedActions.find(asItr->first) != payload->startState.startedActions.end()) {
                            payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(asItr->first), Planner::E_AT_END, -1, emptyIntSet));
                            if (evaluateDebug) cout << "\t\tIs a helpful action\n";
                        }
                    }

                    EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyEnd[asItr->first];
                    if (oldR > tilR) oldR = tilR;

                }
            }


            
            if (!ignoreNumbers) {
                
                RPGRegressionMap::const_iterator thisLayer = goalsAtLayer.end();
                --thisLayer;
                
                list<pair<EpsilonResolutionTimestamp, SupportingAction> > actionsUsed;
                payload->fluentLayers.satisfyNumericPreconditionsAtLayer(thisLayer, goalsAtLayer, actionsUsed);
                
                if (!actionsUsed.empty()) {
                    
                    if (!alreadyPushed) {
                        relaxedPlan.push_front(pair<double, list<ActionSegment> >((currTS - EpsilonResolutionTimestamp::epsilon()).toDouble(), list<ActionSegment>()));
                        alreadyPushed = true;
                    }
                    
                    if (evaluateDebug) cout << "Adding achievers for numeric goals at TS " << currTS << "\n";

                    list<pair<EpsilonResolutionTimestamp, SupportingAction> >::const_iterator sapItr = actionsUsed.begin();
                    const list<pair<EpsilonResolutionTimestamp, SupportingAction> >::const_iterator sapEnd = actionsUsed.end();
            
                    for (; sapItr != sapEnd; ++sapItr) {
                        
                        const SupportingAction* const saItr = &(sapItr->second);
                        
                        if (sapItr->first < currTS) {
                            
                            if (saItr->ts == Planner::E_AT_START) {
                                map<int, pair<int, EpsilonResolutionTimestamp> >::iterator galItr = goalsAtLayer[sapItr->first].actionStarts.insert(pair<int, pair<int, EpsilonResolutionTimestamp> >(saItr->actID, make_pair(saItr->howManyTimes, saItr->tilR))).first;
                                if (galItr->second.second > saItr->tilR) galItr->second.second = saItr->tilR;
                                if (evaluateDebug) cout << "\t\tAdding requirement for start of action at time " << sapItr->first << "\n";
                                                                    
                            } else {
                                cerr << "Adding actions other than EPSILON earlier (in this case " << currTS << " - " << sapItr->first << ") should only occur for gradient actions\n";
                                exit(1);
                            }
                            
                            continue;
                        }
                        
                        pair<int, Planner::time_spec> currAchievedBy(saItr->actID, saItr->ts);
                        
                        
                        if (currAchievedBy.second == Planner::E_AT_START) {
                            if (evaluateDebug) {
                                cout << "\t\tUsing start of " << currAchievedBy.first << " - " << *(RPGBuilder::getInstantiatedOp(currAchievedBy.first));
                                if (saItr->howManyTimes > 1) {
                                    cout << ", " << saItr->howManyTimes << " times";
                                }
                                cout << endl;
                            }
                            if (evaluateDebug && currTS == EpsilonResolutionTimestamp::epsilon()) cout << "\t\tIs a helpful action\n";
                            relaxedPlan.front().second.insert(relaxedPlan.front().second.end(), saItr->howManyTimes, ActionSegment(getOp(currAchievedBy.first), Planner::E_AT_START, -1, emptyIntList));
                            h += saItr->howManyTimes;

                            if (RPGHeuristic::printRPGAsDot) {
                                payload->dot.highlightAction(currAchievedBy.first, Planner::E_AT_START);
                            }

                            const EpsilonResolutionTimestamp sTIL = earliestTILForAction(currAchievedBy.first, true);
                            EpsilonResolutionTimestamp tilR = saItr->tilR;
                            
                            if (tilR > sTIL) tilR = sTIL;

                            for (int pass = 0; pass < 2; ++pass) {
                        
                                map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                                
                                list<Literal*> & actionEffectsList = (pass ? (*actionsToStartNegativeEffects)[currAchievedBy.first] : (*actionsToStartEffects)[currAchievedBy.first]);
                                list<Literal*>::iterator aelItr = actionEffectsList.begin();
                                const list<Literal*>::iterator aelEnd = actionEffectsList.end();
                                
                                for (; aelItr != aelEnd; ++aelItr) {
                                    map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                                    if (cgItr != currGAL.end()) {
                                        if (tilR > cgItr->second) tilR = cgItr->second;
                                        currGAL.erase(cgItr);
                                    }
                                }
                            }
                                                        
                                                                                    
                                                                                                                
                            bool isHelpful = true;

                            {
                                list<Literal*> & actionPreconditionlist = (*actionsToProcessedStartPreconditions)[currAchievedBy.first];
                                list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                                const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();
                                if (evaluateDebug) cout << "\t\tPreconditions:\n";
                                for (; aplItr != aplEnd; ++aplItr) {

                                    const int currPrec = (*aplItr)->getStateID();
                                    
                                    EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                    pair<int, Planner::time_spec> acBy;

                                    if (evaluateDebug) {
                                        cout << "\t\tPrecondition " << currPrec << " " << *(RPGBuilder::getLiteral(currPrec)) << ": ";
                                        cout.flush();
                                    }
                                    
                                    getAchieverDetails(currPrec, currTS - EpsilonResolutionTimestamp::epsilon(), acIn, acBy);
                                    
                                    
                                    if (acIn > EpsilonResolutionTimestamp::zero()) {
                                        if (acBy.first != -1) {
                                            map<int, EpsilonResolutionTimestamp>::iterator galItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                            if (galItr->second > tilR) galItr->second = tilR;
                                            if (evaluateDebug) cout << "required at time " << acIn << "\n";
                                            assert(acIn < currTS);
                                            isHelpful = false;
                                        } else {
                                            if (evaluateDebug) cout << "in initial state at time " << acIn << "\n";
                                        }
                                    } else {
                                        if (evaluateDebug) cout << "in initial state\n";
                                    }

                                }

                                if (evaluateDebug) cout << "\t\tPreconditions done\n";

                            }

                            if (!ignoreNumbers) {
                                list<int> & actionPreconditionlist = (*actionsToProcessedStartNumericPreconditions)[currAchievedBy.first];
                                list<int>::iterator aplItr = actionPreconditionlist.begin();
                                const list<int>::iterator aplEnd = actionPreconditionlist.end();

                                if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                                for (; aplItr != aplEnd; ++aplItr) {

                                    const int currPrec = (*aplItr);
                                    const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                                    if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                        
                                        if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " at time " << acIn << "\n";                                    
                                        payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS, goalsAtLayer, tilR);
                                        isHelpful = false;
                                    } else {
                                        if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " satisfied in initial state\n";
                                    }

                                }

                                if (evaluateDebug) cout << "\t\tPreconditions done.\n";                                                        
                            }

                            addExtraPreconditionsForPreferences(payload, currAchievedBy.first, Planner::E_AT_START, currTS - EpsilonResolutionTimestamp::epsilon(), tilR, goalsAtLayer);

                            if (isHelpful) {
                                payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(currAchievedBy.first), Planner::E_AT_START, -1, emptyIntSet));
                            }

                            EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyStart[currAchievedBy.first];
                            if (oldR > tilR) oldR = tilR;

                        } else {
                            if (evaluateDebug) cout << "\t\tUsing end of " << currAchievedBy.first << " - " << *(RPGBuilder::getInstantiatedOp(currAchievedBy.first)) << endl;
                            if (evaluateDebug && currTS == EpsilonResolutionTimestamp::epsilon()) cout << "\t\tIs a helpful action\n";
                            relaxedPlan.front().second.push_back(ActionSegment(getOp(currAchievedBy.first), Planner::E_AT_END, -1, emptyIntList));
    //                  if (currTS == EPSILON) {
    //                      helpfulActions.push_back(pair<int, Planner::time_spec>(currAchievedBy->act, Planner::E_AT_END));
    //                  }
                            h += saItr->howManyTimes;

                            if (RPGHeuristic::printRPGAsDot) {
                                payload->dot.highlightAction(currAchievedBy.first, Planner::E_AT_END);
                            }

                            
                            const EpsilonResolutionTimestamp sTIL = earliestTILForAction(currAchievedBy.first, false);
                            EpsilonResolutionTimestamp tilR = saItr->tilR;
                            if (tilR > sTIL) tilR = sTIL;

                            for (int pass = 0; pass < 2; ++pass) {
                        
                                map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                                
                                list<Literal*> & actionEffectsList = (pass ? (*actionsToEndNegativeEffects)[currAchievedBy.first] : (*actionsToEndEffects)[currAchievedBy.first]);
                                list<Literal*>::iterator aelItr = actionEffectsList.begin();
                                const list<Literal*>::iterator aelEnd = actionEffectsList.end();
                                
                                for (; aelItr != aelEnd; ++aelItr) {
                                    map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                                    if (cgItr != currGAL.end()) {
                                        if (tilR > cgItr->second) tilR = cgItr->second;
                                        currGAL.erase(cgItr);
                                    }
                                }
                            }
                            
                            bool isHelpful = true;

                            {
                                list<Literal*> & actionPreconditionlist = (*actionsToEndPreconditions)[currAchievedBy.first];
                                list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                                const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();

                                if (evaluateDebug) cout << "\t\tPreconditions:\n";

                                for (; aplItr != aplEnd; ++aplItr) {

                                    const int currPrec = (*aplItr)->getStateID();

                                    EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                    pair<int, Planner::time_spec> acBy;
                                    
                                    getAchieverDetails(currPrec, currTS - EpsilonResolutionTimestamp::epsilon(), acIn, acBy);
                                    
                                    if (acIn > EpsilonResolutionTimestamp::zero()) {
                                        if (acBy.first != -1) {
                                            map<int, EpsilonResolutionTimestamp>::iterator galItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                            if (galItr->second > tilR) galItr->second = tilR;

                                            if (evaluateDebug) cout << "\t\tAdding requirement for " << currPrec << ", " << RPGBuilder::getNumericPreTable()[currPrec] << " at time " << acIn << "\n";
                                            assert(acIn < currTS);
                                            isHelpful = false;
                                        } else {
                                            if (evaluateDebug) cout << "\t\tPrecondition " << currPrec << " in initial state at time " << acIn << "\n";
                                        }
                                    } else {
                                        if (evaluateDebug) cout << "\t\tPrecondition " << currPrec << " in initial state\n";
                                    }

                                }

                                if (evaluateDebug) cout << "\t\tPreconditions done\n";

                                int addToThePast = saItr->howManyTimes;
                                
                                {
                                    map<int, set<int> >::const_iterator saItr = payload->startState.startedActions.find(currAchievedBy.first);
                                    if (saItr != payload->startState.startedActions.end()) {
                                        addToThePast -= saItr->second.size();
                                    }
                                }

                                if (addToThePast > 0) {
                                    map<int, pair<int, EpsilonResolutionTimestamp> >::iterator galItr = goalsAtLayer[startActionSchedule[currAchievedBy.first] + EpsilonResolutionTimestamp::epsilon()].actionStarts.insert(pair<int, pair<int, EpsilonResolutionTimestamp> >(currAchievedBy.first, make_pair(addToThePast, tilR))).first;
                                    if (galItr->second.second > tilR) galItr->second.second = tilR;
                                    if (evaluateDebug) cout << "\t\tAdding requirement for start of action at time " << (startActionSchedule[currAchievedBy.first] + EpsilonResolutionTimestamp::epsilon()) << "\n";
                                    isHelpful = false;
                                } else {
                                    if (evaluateDebug) cout << "\t\tAction has already been started, do not need to schedule start in RPG\n";
                                }
                            }

                            if (!ignoreNumbers) {
                                list<int> & actionPreconditionlist = (*actionsToNumericEndPreconditions)[currAchievedBy.first];
                                list<int>::iterator aplItr = actionPreconditionlist.begin();
                                const list<int>::iterator aplEnd = actionPreconditionlist.end();

                                if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                                for (; aplItr != aplEnd; ++aplItr) {

                                    const int currPrec = (*aplItr);
                                    const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                                    if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                        if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << " at time " << acIn << "\n";
                                        payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS, goalsAtLayer, tilR);
                                        isHelpful = false;
                                        
                                    } else {
                                        if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << " satisfied in initial state\n";
                                    }

                                }


                            }
                            
                            addExtraPreconditionsForPreferences(payload, currAchievedBy.first, Planner::E_AT_END, currTS - EpsilonResolutionTimestamp::epsilon(), tilR, goalsAtLayer);

                            if (evaluateDebug) cout << "\t\tPreconditions done.\n";

                            if (isHelpful) {
                                payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(currAchievedBy.first), Planner::E_AT_END, -1, emptyIntSet));
                            }


                            EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyEnd[currAchievedBy.first];
                            if (oldR > tilR) oldR = tilR;

                        }

                    }
                    
                }

            }
            
            for (int galPass = 0; galPass < 2; ++galPass) {
                
                map<int, EpsilonResolutionTimestamp> & currSupportingGAL = (galPass ? currNegativeGAL : currPositiveGAL);
                                
                if (currSupportingGAL.empty()) {
                    continue;
                }


                if (!alreadyPushed) {
                    relaxedPlan.push_front(pair<double, list<ActionSegment> >((currTS - EpsilonResolutionTimestamp::epsilon()).toDouble(), list<ActionSegment>()));
                    alreadyPushed = true;
                }

                if (evaluateDebug && !currSupportingGAL.empty()) {
                    if (galPass) {
                        cout << "Finding achievers for " << currSupportingGAL.size() << " negative goal(s) at TS " << currTS << "\n";
                    } else {
                        cout << "Finding achievers for " << currSupportingGAL.size() << " goal(s) at TS " << currTS << "\n";
                    }
                }
                
                while (!currSupportingGAL.empty()) {
                    const map<int, EpsilonResolutionTimestamp>::iterator nta = currSupportingGAL.begin();
                    const int nextToAchieve = nta->first;
                    EpsilonResolutionTimestamp tilR = nta->second;
                    currSupportingGAL.erase(nta);
                    if (evaluateDebug) cout << "\tGoal " << nextToAchieve << ", " << *(RPGBuilder::getLiteral(nextToAchieve)) << "\n";
                    
                    EpsilonResolutionTimestamp layerIgnore(EpsilonResolutionTimestamp::undefined());
                    pair<int, Planner::time_spec> currAchievedBy;
                    
                    if (galPass) {
                        layerIgnore = (*negativeAchievedInLayer)[nextToAchieve];
                        currAchievedBy = (*negativeAchievedBy)[nextToAchieve];
                    } else {
                        getAchieverDetails(nextToAchieve, currTS/* + EpsilonResolutionTimestamp::epsilon()*/, layerIgnore, currAchievedBy);
                        assert(sensiblePair(payload, currAchievedBy, nextToAchieve));
                    }
                    
                    

                    if (currAchievedBy.second == Planner::E_AT_START) {
                        if (evaluateDebug) cout << "\t\tUsing start of " << currAchievedBy.first << " - " << *(RPGBuilder::getInstantiatedOp(currAchievedBy.first)) << " at " << layerIgnore << "\n";
                        if (evaluateDebug && currTS == EpsilonResolutionTimestamp::epsilon()) cout << "\t\tIs a helpful action\n";
                        relaxedPlan.front().second.push_back(ActionSegment(getOp(currAchievedBy.first), Planner::E_AT_START, -1, emptyIntList));
                        ++h;

                        if (RPGHeuristic::printRPGAsDot) {
                            payload->dot.highlightAction(currAchievedBy.first, Planner::E_AT_START);
                            payload->dot.actionMeetsFactInRP(currAchievedBy.first, Planner::E_AT_START, nextToAchieve);
                        }
                        
                        const EpsilonResolutionTimestamp sTIL = earliestTILForAction(currAchievedBy.first, true);
                        if (tilR > sTIL) tilR = sTIL;
    //                  if (currTS == EPSILON) {
    //                      helpfulActions.push_back(currAchievedBy);
                        //
    //                  }

                        for (int pass = galPass; pass < 2; ++pass) {
                            list<Literal*> & actionEffectsList = (pass ? (*actionsToStartNegativeEffects)[currAchievedBy.first] : (*actionsToStartEffects)[currAchievedBy.first]);
                            map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                            
                            list<Literal*>::iterator aelItr = actionEffectsList.begin();
                            const list<Literal*>::iterator aelEnd = actionEffectsList.end();

                            for (; aelItr != aelEnd; ++aelItr) {
                                map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                                if (cgItr != currGAL.end()) {
                                    if (tilR > cgItr->second) tilR = cgItr->second;
                                    currGAL.erase(cgItr);
                                }
                            }
                        }

                        bool isHelpful = true;

                        {
                            list<Literal*> & actionPreconditionlist = (*actionsToProcessedStartPreconditions)[currAchievedBy.first];
                            list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                            const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();
                            if (evaluateDebug) cout << "\t\tPreconditions:\n";
                            for (; aplItr != aplEnd; ++aplItr) {

                                const int currPrec = (*aplItr)->getStateID();
                                
                                if (evaluateDebug) {
                                    cout << "\t\tPrecondition " << currPrec << ", " << *(*aplItr) << ": ";
                                    cout.flush();
                                }
                                
                                EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                pair<int, Planner::time_spec> acBy;
                                
                                getAchieverDetails(currPrec, currTS - EpsilonResolutionTimestamp::epsilon(), acIn, acBy);
                                
                                if (acIn > EpsilonResolutionTimestamp::zero()) {
                                    if (acBy.first != -1) {
                                        map<int, EpsilonResolutionTimestamp>::iterator galItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                        if (galItr->second > tilR) galItr->second = tilR;
                                        if (evaluateDebug) cout << "adding requirement at time " << acIn << "\n";
                                        assert(acIn < currTS);
                                        isHelpful = false;
                                    } else {
                                        if (evaluateDebug) cout << "initial state at time " << acIn << "\n";
                                    }
                                } else {
                                    if (evaluateDebug) cout << "in initial state\n";
                                }

                            }

                            if (evaluateDebug) cout << "\t\tPreconditions done\n";

                        }

                        if (!ignoreNumbers) {
                            list<int> & actionPreconditionlist = (*actionsToProcessedStartNumericPreconditions)[currAchievedBy.first];
                            list<int>::iterator aplItr = actionPreconditionlist.begin();
                            const list<int>::iterator aplEnd = actionPreconditionlist.end();

                            if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                            for (; aplItr != aplEnd; ++aplItr) {

                                const int currPrec = (*aplItr);
                                const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                                if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                    if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << " at time " << acIn << "\n";
                                    
                                    payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS - EpsilonResolutionTimestamp::epsilon(), goalsAtLayer, tilR);
                                    isHelpful = false;
                                } else {
                                    if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << " satisfied in initial state\n";
                                }

                            }

                            payload->fluentLayers.recordSideEffects(currAchievedBy.first, currAchievedBy.second, currTS - EpsilonResolutionTimestamp::epsilon());
                            
                        }
                                                                     
                                                                     
                        addExtraPreconditionsForPreferences(payload, currAchievedBy.first, Planner::E_AT_START, currTS - EpsilonResolutionTimestamp::epsilon(), tilR, goalsAtLayer);
                        
                        if (evaluateDebug) cout << "\t\tPreconditions done.\n";

                        if (isHelpful) {
                            payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(currAchievedBy.first), Planner::E_AT_START, -1, emptyIntSet));
                            if (evaluateDebug) cout << "\t\tIs a helpful action\n";
                        }

                        EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyStart[currAchievedBy.first];
                        if (oldR > tilR) oldR = tilR;


                    } else if (currAchievedBy.second == Planner::E_AT_END) {
                        if (evaluateDebug) cout << "\t\tUsing end of " << currAchievedBy.first << " - " << *(RPGBuilder::getInstantiatedOp(currAchievedBy.first)) << endl;
                        
                        if (RPGHeuristic::printRPGAsDot) {
                            payload->dot.highlightAction(currAchievedBy.first, Planner::E_AT_END);
                            payload->dot.actionMeetsFactInRP(currAchievedBy.first, Planner::E_AT_END, nextToAchieve);
                        }
                                                            
                        
                        if (evaluateDebug && currTS == EpsilonResolutionTimestamp::epsilon()) cout << "\t\tIs a helpful action\n";
                        relaxedPlan.front().second.push_back(ActionSegment(getOp(currAchievedBy.first), Planner::E_AT_END, -1, emptyIntList));
    //                  if (currTS == EPSILON) {
    //                      helpfulActions.push_back(currAchievedBy);
    //                  }
                        if (!TemporalAnalysis::canSkipToEnd(currAchievedBy.first)) ++h;

                        const EpsilonResolutionTimestamp sTIL = earliestTILForAction(currAchievedBy.first, false);
                        if (tilR > sTIL) tilR = sTIL;


                        for (int pass = galPass; pass < 2; ++pass) {
                            
                            list<Literal*> & actionEffectsList = (pass ? (*actionsToEndNegativeEffects)[currAchievedBy.first] : (*actionsToEndEffects)[currAchievedBy.first]);
                            map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                            
                            list<Literal*>::iterator aelItr = actionEffectsList.begin();
                            const list<Literal*>::iterator aelEnd = actionEffectsList.end();

                            for (; aelItr != aelEnd; ++aelItr) {
                                map<int, EpsilonResolutionTimestamp>::iterator cgItr = currGAL.find((*aelItr)->getStateID());
                                if (cgItr != currGAL.end()) {
                                    if (tilR > cgItr->second) tilR = cgItr->second;
                                    currGAL.erase(cgItr);
                                }
                            }
                        }

                        bool isHelpful = true;
                        {
                            list<Literal*> & actionPreconditionlist = (*actionsToEndPreconditions)[currAchievedBy.first];
                            list<Literal*>::iterator aplItr = actionPreconditionlist.begin();
                            const list<Literal*>::iterator aplEnd = actionPreconditionlist.end();

                            if (evaluateDebug) cout << "\t\tPreconditions:\n";

                            for (; aplItr != aplEnd; ++aplItr) {

                                const int currPrec = (*aplItr)->getStateID();
                                EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                pair<int, Planner::time_spec> acBy;
                                
                                getAchieverDetails(currPrec, currTS - EpsilonResolutionTimestamp::epsilon(), acIn, acBy);
                                
                                if (acIn > EpsilonResolutionTimestamp::zero()) {
                                    if (acBy.first != -1) {
                                        map<int, EpsilonResolutionTimestamp>::iterator galItr = goalsAtLayer[acIn].propositionalGoals.insert(pair<int, EpsilonResolutionTimestamp>(currPrec, tilR)).first;
                                        if (galItr->second > tilR) galItr->second = tilR;
                                        if (evaluateDebug) cout << "\t\tAdding requirement for " << currPrec << " at time " << acIn << "\n";
                                        assert(acIn < currTS);
                                        isHelpful = false;
                                    } else {
                                        if (evaluateDebug) cout << "\t\tPrecondition " << currPrec << " in initial state at layer " << acIn << "\n";
                                    }
                                } else {
                                    if (evaluateDebug) cout << "\t\tPrecondition " << currPrec << " in initial state\n";
                                }

                            }

                            if (evaluateDebug) cout << "\t\tPreconditions done\n";

                            if (theState.startedActions.find(currAchievedBy.first) == theState.startedActions.end()) {
                                const EpsilonResolutionTimestamp sas = startActionSchedule[currAchievedBy.first];
                                if (sas.isUndefined()) {
                                    assert(TemporalAnalysis::canSkipToEnd(currAchievedBy.first));
                                    if (!TemporalAnalysis::canSkipToEnd(currAchievedBy.first)) {
                                        cerr << "Critical error - trying to schedule goal to before start of plan\n";
                                        exit(1);
                                    }
                                } else {
                                    map<int, pair<int,EpsilonResolutionTimestamp> >::iterator galItr = goalsAtLayer[sas + EpsilonResolutionTimestamp::epsilon()].actionStarts.insert(pair<int, pair<int, EpsilonResolutionTimestamp> >(currAchievedBy.first, pair<int,EpsilonResolutionTimestamp>(1,tilR))).first;
                                    if (galItr->second.second > tilR) galItr->second.second = tilR;
                                    if (evaluateDebug) cout << "\t\tAdding requirement for start of action at time " << (startActionSchedule[currAchievedBy.first] + EpsilonResolutionTimestamp::epsilon()) << "\n";
                                }

                                isHelpful = false;
                            } else {
                                if (evaluateDebug) cout << "\t\tAction has already been started, do not need to schedule start in RPG\n";
                            }
                        }

                        if (!ignoreNumbers) {
                            list<int> & actionPreconditionlist = (*actionsToNumericEndPreconditions)[currAchievedBy.first];
                            list<int>::iterator aplItr = actionPreconditionlist.begin();
                            const list<int>::iterator aplEnd = actionPreconditionlist.end();

                            if (evaluateDebug) cout << "\t\tNumeric preconditions:\n";

                            for (; aplItr != aplEnd; ++aplItr) {

                                const int currPrec = (*aplItr);
                                const EpsilonResolutionTimestamp & acIn = (*numericAchievedInLayer)[currPrec];
                                if (acIn > EpsilonResolutionTimestamp::zero() && !numericIsTrueInState[currPrec]) {
                                    if (evaluateDebug) cout << "\t\tAdding requirement for numeric precondition " << currPrec << " at time " << acIn << "\n";
                                    
                                    payload->fluentLayers.requestNumericPrecondition(currPrec, acIn, currTS - EpsilonResolutionTimestamp::epsilon(), goalsAtLayer, tilR);
                                } else {
                                    if (evaluateDebug) cout << "\t\tNumeric precondition " << currPrec << " satisfied in initial state\n";
                                }

                            }

                            payload->fluentLayers.recordSideEffects(currAchievedBy.first,  currAchievedBy.second, currTS - EpsilonResolutionTimestamp::epsilon());                            

                        }

                        addExtraPreconditionsForPreferences(payload, currAchievedBy.first, Planner::E_AT_END, currTS - EpsilonResolutionTimestamp::epsilon(), tilR, goalsAtLayer);

                        if (evaluateDebug) cout << "\t\tPreconditions done.\n";

                        if (isHelpful) {
                            payload->helpfulActions.push_front(ActionSegment(RPGBuilder::getInstantiatedOp(currAchievedBy.first), Planner::E_AT_END, -1, emptyIntSet));
                            if (evaluateDebug) cout << "\t\tIs a helpful action\n";
                        }


                        EpsilonResolutionTimestamp & oldR = earliestDeadlineRelevancyEnd[currAchievedBy.first];
                        if (oldR > tilR) oldR = tilR;

                    } else { // aha, is a timed initial literal!

    //                  if (currTS == EPSILON) {
    //                      helpfulActions.push_back(currAchievedBy);
    //                  }
                        earliestTIL = currAchievedBy;
                        
                        if (latestTIL < currAchievedBy.first) {
                            latestTIL = currAchievedBy.first;
                        }

                        //relaxedPlan.front().second.push_back(ActionSegment(0, Planner::E_AT, currAchievedBy.first, emptyIntList));
                        ++h;
                        
                        for (int pass = galPass; pass < 2; ++pass) {
                            const list<int> & tilEffectsList = (pass ? tilTemporaryNegativeEffects[currAchievedBy.first] : tilEffects[currAchievedBy.first]);
                            map<int, EpsilonResolutionTimestamp> & currGAL = (pass ? currNegativeGAL : currPositiveGAL);
                            
                            list<int>::const_iterator aelItr = tilEffectsList.begin();
                            const list<int>::const_iterator aelEnd = tilEffectsList.end();

                            for (; aelItr != aelEnd; ++aelItr) {
                                currGAL.erase(*aelItr);
                            }
                        }
                        
                        addExtraPreconditionsForPreferences(payload, currAchievedBy.first, Planner::E_AT, currTS - EpsilonResolutionTimestamp::epsilon(), tilR, goalsAtLayer);

                    }

                }

            }                        
            if (evaluateDebug) cout << "All goals at this TS now satisfied\n";
                                        
            goalsAtLayer.erase(currTS);
        }
        
        /*if (latestTIL > earliestTIL.first) {
            h += latestTIL - earliestTIL.first;
        }*/
    }
    
    /** @brief Add the numeric effects of an action to the RPG.
     * 
     * @param payload  The data describing the RPG currently being built
     * @param currAct  The action ID to apply     
     * @param currTS   The time specifier of the action: <code>Planner::E_AT_START</code> or <code>Planner::E_AT_END</code>
     * @param nlTime   The fact layer altered by the consequences of its effects
     * @param limitTo  A limit on how many times the action can be applied
     *
     * @return <code>true</code> if adding the action led to all goals being achieved; <code>false</code> otherwise.
     */                
    bool applyNumericEffects(Private::BuildingPayload * const payload, const int & currAct, const Planner::time_spec & currTS, const EpsilonResolutionTimestamp & nlTime, const int & limitTo);
    
    
    /** @brief Add the propositional effects of an action to the RPG
     * 
     * @param payload  The data describing the RPG currently being built
     * @param currAct  The action ID to apply     
     * @param currTS   The time specifier of the action: <code>Planner::E_AT_START</code> or <code>Planner::E_AT_END</code>
     * @param prefCosts  The preference violations incurred if the action is used at the current layer
     * @param nlTime   The fact layer altered by the consequences of its effects
     * @param POtime   Data to support use of the partial-order modified heuristic.
     *
     * @return <code>true</code> if adding the action led to all goals being achieved; <code>false</code> otherwise.
     */                
    bool applyPropositionalEffects(Private::BuildingPayload * const payload,
                                   const int & currAct, const Planner::time_spec & currTS, const ActionViolationData & prefCosts,
                                   const bool & openEnd, const EpsilonResolutionTimestamp & nlTime);//, MaxDependentInfo & POtime);

    bool checkPreconditionsAreSatisfied(const int & currAct, const Planner::time_spec & ts, const EpsilonResolutionTimestamp & layer);

    bool updateActionsForNewLiteralFact(BuildingPayload * const payload, const int & toPropagate, const EpsilonResolutionTimestamp & factLayerTime, const bool & isActuallyNew);
    bool updateActionsForNewNumericFact(BuildingPayload * const payload, const int & toPropagate, const EpsilonResolutionTimestamp & factLayerTime);
    bool applyEndEffectNow(BuildingPayload * const payload, const int & currAct, const bool & openAct, const EpsilonResolutionTimestamp & factLayerTime, const bool & isActuallyNew);

    
    bool revisitActs(BuildingPayload * payload, const EpsilonResolutionTimestamp & factLayerTime, const list<pair<int, Planner::time_spec> > & actsToVisit);
    bool updatePreferencesForFact(BuildingPayload * const payload, const int & fID, const bool & isALiteral, const bool & polarity, const bool & isActuallyNew, const EpsilonResolutionTimestamp & factLayerTime);    
    bool updateForPreferencesInBetterPositions(BuildingPayload * const payload, const list<pair<int, int> > & preferencePairedWithFactNowFreeToAdd, const EpsilonResolutionTimestamp & factLayerTime);
    
#ifdef POPF3ANALYSIS
    void calculateGoalCost(BuildingPayload * const payload, double * calculatedCost=0);
    void updateAdditiveCosts(BuildingPayload * const payload, const int & ci, const EpsilonResolutionTimestamp & deadline, const int & updateForGoal, double & costToUpdate);
#endif
    
    bool startShouldBeDelayed(const int & currAct, const EpsilonResolutionTimestamp & factLayerTime, BuildingPayload * const payload);
};

#ifdef MDIDEBUG
RPGHeuristic::Private::BuildingPayload * RPGHeuristic::Private::MaxDependentInfo::referTo = 0;
bool RPGHeuristic::Private::MaxDependentInfo::debug = false;
#endif

vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestStartAllowed;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestEndAllowed;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::latestStartAllowed;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::latestEndAllowed;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::deadlineAtTime;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestDeadlineRelevancyStart;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestDeadlineRelevancyEnd;

vector<list<int> > RPGHeuristic::Private::tilEffects;
vector<list<int> > RPGHeuristic::Private::tilNegativeEffects;
vector<list<int> > RPGHeuristic::Private::tilTemporaryNegativeEffects;
vector<double> RPGHeuristic::Private::tilTimes;
bool RPGHeuristic::Private::tilInitialised = false;
int RPGHeuristic::Private::tilCount = 0;

vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestPropositionPOTimes;
vector<EpsilonResolutionTimestamp> RPGHeuristic::Private::earliestNumericPOTimes;
//vector<double> RPGHeuristic::Private::earliestNumericPrePOTimes;

vector<vector<set<int> > > RPGHeuristic::Private::actionsAffectedByFluent;

#ifdef POPF3ANALYSIS
vector<vector<double> > RPGHeuristic::Private::startEffectsOnResourceLimits;
vector<vector<double> > RPGHeuristic::Private::endEffectsOnResourceLimits;    
vector<vector<double> > RPGHeuristic::Private::dynamicStartEffectsOnResourceLimits;
vector<vector<double> > RPGHeuristic::Private::dynamicEndEffectsOnResourceLimits;    

vector<bool> RPGHeuristic::Private::costsAreIndependentGoalCosts;
vector<vector<double> > RPGHeuristic::Private::maxPermissibleCostOfAFact;
double RPGHeuristic::Private::metricWeightOfMakespan;
#endif

vector<EpsilonResolutionTimestamp> & RPGHeuristic::getEarliestForStarts()
{
    return Private::earliestStartAllowed;
};
vector<EpsilonResolutionTimestamp> & RPGHeuristic::getEarliestForEnds()
{
    return Private::earliestEndAllowed;
};

EpsilonResolutionTimestamp & RPGHeuristic::getDeadlineRelevancyStart(const int & i)
{
    return Private::earliestDeadlineRelevancyStart[i];
}

EpsilonResolutionTimestamp & RPGHeuristic::getDeadlineRelevancyEnd(const int & i)
{
    return Private::earliestDeadlineRelevancyEnd[i];
}


void RPGHeuristic::doFullExpansion(MinimalState & refState, const list<FFEvent> & dummyPlan)
{
    set<int> dummyGoals;
    set<int> dummyGoalFluents;
    list<ActionSegment> dummyHelpful;
    list<pair<double, list<ActionSegment> > > dummyRP;
    vector<double> minTimestamps(dummyPlan.size(), 0.0);
    
    list<FFEvent>::const_iterator pItr = dummyPlan.begin();
    const list<FFEvent>::const_iterator pEnd = dummyPlan.end();
    
    for (int p = 0; pItr != pEnd; ++pItr, ++p) {
        minTimestamps[p] = pItr->lpMinTimestamp;
        if (minTimestamps[p] < 0.0) {
            minTimestamps[p] = 0.0;
        }
    }
    
    double dummyEstimate;
    d->buildEmptyActionFluentLookupTable();
    
    const bool wasBlind = blindSearch;
    const bool wasNoNumbers = ignoreNumbers;
    
    d->expandFully = true;
    blindSearch = false;
    ignoreNumbers = false;
    
    vector<double> timeAtWhichValueIsDefined(refState.secondMin.size(),0.0);

    {
        refState.preferenceStatus = PreferenceHandler::getInitialAutomataPositions();    
        refState.prefPreconditionViolations = 0.0;
    }
    
    
    delete getRelaxedPlan(refState, 0, minTimestamps, 0.0, -DBL_MAX, refState.secondMin, refState.secondMax, timeAtWhichValueIsDefined, dummyHelpful, dummyRP, dummyEstimate);
    
    d->expandFully = false;    
    blindSearch = wasBlind;
    ignoreNumbers = wasNoNumbers;
}

RPGHeuristic::RPGHeuristic(const bool & b,
                           vector<list<Literal*> > * atse,
                           vector<list<Literal*> > * atee,
                           vector<list<pair<int, Planner::time_spec> > > * eta,
                           vector<list<Literal*> > * atsne,
                           vector<list<Literal*> > * atene,
                           vector<list<pair<int, Planner::time_spec> > > * neta,
                           vector<list<pair<int, Planner::time_spec> > > * pta,
                           vector<list<Literal*> > * atsp,
                           vector<list<Literal*> > * ati,
                           vector<list<Literal*> > * atep,
                           vector<list<RPGBuilder::NumericEffect> > * atnuse,
                           vector<list<RPGBuilder::NumericEffect> > * atnuee,
                           vector<list<int> > * atrnuse,
                           vector<list<int> > * atrnuee,
                           vector<list<int> > * atnusp,
                           vector<list<int> > * atnui,
                           vector<list<int> > * atnuep,
                           vector<list<int> > * atpnuep,
                           vector<int> * iusp,
                           vector<int> * iuip,
                           vector<int> * iuep,
                           vector<EpsilonResolutionTimestamp> * ail,
                           vector<EpsilonResolutionTimestamp> * ailr,
                           vector<pair<int, Planner::time_spec> > * ab,
                           vector<pair<int, Planner::time_spec> > * abr,
                           vector<EpsilonResolutionTimestamp> * negail,
                           vector<EpsilonResolutionTimestamp> * negailr,
                           vector<pair<int, Planner::time_spec> > * negab,
                           vector<pair<int, Planner::time_spec> > * negabr,                    
                           vector<EpsilonResolutionTimestamp> * nail,
                           vector<EpsilonResolutionTimestamp> * nailr,
                           vector<ActionFluentModification*> * nab,
                           vector<ActionFluentModification*> * nabr,
                           vector<int> * iunsp,
                           vector<int> * iuni,
                           vector<int> * iunep,
                           vector<RPGBuilder::RPGNumericPrecondition> * rnp,
                           vector<RPGBuilder::RPGNumericEffect> * rne,
                           vector<list<pair<int, Planner::time_spec> > > * ppta,
                           vector<list<pair<int, Planner::time_spec> > > * nppta,
                           vector<list<Literal*> > * atpsp,
                           vector<int> * iupsp,
                           vector<int> * iupsnp,
                           list<pair<int, Planner::time_spec> > * pla,
                           list<pair<int, Planner::time_spec> > * onpa)
        :   d(new Private(b,
                          atse,
                          atee,
                          eta,
                          atsne,
                          atene,
                          neta,
                          pta,
                          atsp,
                          ati,
                          atep,
                          atnuse,
                          atnuee,
                          atrnuse,
                          atrnuee,
                          atnusp,
                          atnui,
                          atnuep,
                          atpnuep,
                          iusp,
                          iuip,
                          iuep,
                          ail,
                          ailr,
                          ab,
                          abr,
                          negail,
                          negailr,
                          negab,
                          negabr,
                          nail,
                          nailr,
                          nab,
                          nabr,
                          iunsp,
                          iuni,
                          iunep,
                          rnp,
                          rne,
                          ppta,
                          nppta,
                          atpsp,
                          iupsp,
                          iupsnp,
                          pla,
                          onpa))
{

    {
        
        d->literalGoalVector.resize(RPGBuilder::getLiteralGoals().size(), (Literal*) 0);
        
        list<Literal*>::iterator gsItr = RPGBuilder::getLiteralGoals().begin();
        const list<Literal*>::iterator gsEnd = RPGBuilder::getLiteralGoals().end();

        for (int gID = 0; gsItr != gsEnd; ++gsItr, ++gID) {
            if (!RPGBuilder::isStatic(*gsItr).first) {
                d->goals.insert((*gsItr)->getStateID());
                d->literalGoalVector[gID] = *gsItr;
            }
        }

        d->gsEnd = d->goals.end();
    }

    {
        list<pair<int, int> >::iterator gsItr = RPGBuilder::getNumericRPGGoals().begin();
        const list<pair<int, int> >::iterator gsEnd = RPGBuilder::getNumericRPGGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            if (gsItr->first != -1) {
                d->goalFluents.insert(gsItr->first);
            }
            if (gsItr->second != -1) {
                d->goalFluents.insert(gsItr->second);
            }
        }

        d->gfEnd = d->goalFluents.end();
    }

};

RPGHeuristic::~RPGHeuristic()
{
    if (d->deleteArrays) {
        assert(false);
    }
}



RPGHeuristic* RPGBuilder::generateRPGHeuristic()
{

    // for now, don't prune the RPG

    return new RPGHeuristic(false,  // subproblem does not own the arrays
                            &actionsToStartEffects,
                            &actionsToEndEffects,
                            &effectsToActions,
                            &actionsToStartNegativeEffects,
                            &actionsToEndNegativeEffects,
                            &negativeEffectsToActions,
                            &preconditionsToActions,
                            &actionsToStartPreconditions,
                            &actionsToInvariants,
                            &actionsToEndPreconditions,
                            &actionsToStartNumericEffects,
                            &actionsToEndNumericEffects,
                            &actionsToRPGNumericStartEffects,
                            &actionsToRPGNumericEndEffects,
                            &actionsToRPGNumericStartPreconditions,
                            &actionsToRPGNumericInvariants,
                            &actionsToRPGNumericEndPreconditions,
                            &actionsToProcessedStartRPGNumericPreconditions,
                            &initialUnsatisfiedStartPreconditions,
                            &initialUnsatisfiedInvariants,
                            &initialUnsatisfiedEndPreconditions,
                            &achievedInLayer,
                            &achievedInLayerReset,
                            &achievedBy,
                            &achievedByReset,
                            &negativeAchievedInLayer,
                            &negativeAchievedInLayerReset,
                            &negativeAchievedBy,
                            &negativeAchievedByReset,
                            &numericAchievedInLayer,
                            &numericAchievedInLayerReset,
                            &numericAchievedBy,
                            &numericAchievedByReset,
                            &initialUnsatisfiedNumericStartPreconditions,
                            &initialUnsatisfiedNumericInvariants,
                            &initialUnsatisfiedNumericEndPreconditions,
                            &rpgNumericPreconditions,
                            &rpgNumericEffects,
                            &processedPreconditionsToActions,
                            &processedRPGNumericPreconditionsToActions,
                            &actionsToProcessedStartPreconditions,
                            &initialUnsatisfiedProcessedStartPreconditions,
                            &initialUnsatisfiedProcessedStartNumericPreconditions,
                            &preconditionlessActions,
                            &onlyNumericPreconditionActions);

};

bool RPGHeuristic::Private::EndPrecRescale::operator <(const RPGHeuristic::Private::EndPrecRescale & r) const
{

    if (var < r.var) return true;
    if (r.var > var) return false;

    if (offset < r.offset) return true;
    if (offset > r.offset) return false;

    if (totalchange < r.totalchange) return true;
    if (totalchange > r.totalchange) return false;

    if (duration < r.duration) return true;
    if (duration > r.duration) return false;

    return false;


};


set<int> RPGHeuristic::emptyIntList;
unsigned int RPGHeuristic::statesEvaluated = 0;
bool RPGHeuristic::orderByDeadlineRelevance = false;
bool RPGHeuristic::alwaysExpandFully = false;
bool RPGHeuristic::addTheMaxCosts = false;

#ifdef POPF3ANALYSIS
void RPGHeuristic::metricHasChanged()
{
    d->metricHasChanged();
}
#endif

RPGHeuristic::EvaluationInfo* RPGHeuristic::getRelaxedPlan(MinimalState & theState, const list<StartEvent> * startEventQueue,
                                 const vector<double> & minTimestamps, const double & stateTS, const double & costLimit,
                                 const vector<double> & extrapolatedMin, const vector<double> & extrapolatedMax, const vector<double> & timeAtWhichValueIsDefined,
                                 list<ActionSegment> & helpfulActions, list<pair<double, list<ActionSegment> > > & relaxedPlan,double & finalPlanMakespanEstimate,
                                 map<double, list<pair<int, int> > > * justApplied, double tilFrom)
{

    const bool evaluateDebug = Globals::globalVerbosity & 64;
    const bool prefDebug = Globals::globalVerbosity & 32768 || PreferenceHandler::preferenceDebug;

    d->setDebugFlag(evaluateDebug);
    
    if (!d->expandFully) {
        ++statesEvaluated;
    }
    

        
//    const int vCount = theState.secondMin.size();
//    const int avCount = RPGBuilder::getAVCount();

    const int nextTIL = theState.nextTIL;

    finalPlanMakespanEstimate = 0.0;

    d->integrateContinuousEffects();

//  startedActionExtraEndPreconditions.clear();

    
    d->populateActionFluentLookupTable();

    if (evaluateDebug) cout << "Evaluating a state with " << theState.startedActions.size() << " sorts of actions on the go\n";

    //rpprintState(theState);

    auto_ptr<Private::BuildingPayload> payload(d->spawnNewPayload(theState, costLimit, startEventQueue, minTimestamps, stateTS, helpfulActions));

    map<double, list<DelayedGradientDescriptor> > delayedGradients;
    
    d->giveUsTheEffectsOfExecutingActions(payload.get(), timeAtWhichValueIsDefined, delayedGradients);

    /*if (evaluateDebug || eeDebug) {
    const int eeuSize = extraEndUnsatisfied.size();
    for (int i = 0; i < eeuSize; ++i) {
    if (extraEndUnsatisfied[i]) cout << "Still extra ends attached to " << *(RPGBuilder::getInstantiatedOp(i)) << "\n";
    }
    }*/
//  MILPRPG(theState.second);

    int heuristicOffset = 0;

    d->addRequirementToHaveSeenTheEndOfAllCurrentlyExecutingActions(payload.get());

    if (evaluateDebug) {
        cout << "Aiming for number of goals satisfied: " << payload->unsatisfiedGoals << "\n";
    }

    const bool realGoalsSatisfied = d->seeWhatGoalsAreTrueToStartWith(payload.get());

    if (realGoalsSatisfied) {
        cout << "(G)"; cout.flush();
    }
    
    if (evaluateDebug) {
        cout << "Goals unsatisfied in initial state: " << payload->unsatisfiedGoals << "\n";
        cout << "Ends not appeared so far: " << payload->unappearedEnds << "\n";
    }

    const double currentPreferenceCost = PreferenceHandler::getCurrentCost(theState);
    const double reachablePreferenceCost = PreferenceHandler::getReachableCost(theState);
    
    if (RPGBuilder::getMetric()) {
        if (RPGBuilder::getMetric()->minimise) {
            if (currentPreferenceCost - reachablePreferenceCost >= 0.0001) {
                if (evaluateDebug) {
                    cout << "-- Adding dummy goal to try to reach the theoretical minimum preference violation penalty (" << reachablePreferenceCost << "\n";
                }
                ++payload->unsatisfiedGoals;
                ++payload->fakeGoalCount;
            } else {
                if (evaluateDebug) {
                    cout << "-- Already at the reachable preference cost of " << reachablePreferenceCost << endl;
                }
            }
        } else {
            if (currentPreferenceCost - reachablePreferenceCost <= 0.0001) {
                if (evaluateDebug) {
                    cout << "-- Adding dummy goal to try to reach the theoretical maximum preference violation penalty (" << reachablePreferenceCost << "\n";
                }
                ++payload->unsatisfiedGoals;
                ++payload->fakeGoalCount;
            } else {
                if (evaluateDebug) {
                    cout << "-- Already at the reachable preference cost of " << reachablePreferenceCost << endl;
                }
            }
        }
    }

    if (d->expandFully) payload->unsatisfiedGoals = INT_MAX;

    if (RPGHeuristic::alwaysExpandFully && Globals::optimiseSolutionQuality && !d->currentCosts.empty()) {
        if (evaluateDebug) {
            cout << "-- Adding dummy goal to expand fully\n";
        }
        ++payload->unsatisfiedGoals;
    }

    
    
    payload->rpgGoalPrefViolation = currentPreferenceCost;
    payload->goalPrefViolationAtLastLayer = currentPreferenceCost;
    
    if ((!payload->unsatisfiedGoals && !payload->unappearedEnds) || blindSearch) {
        if (evaluateDebug) {
            if (blindSearch) {
                cout << "Blind search, returning\n";
            } else {
                cout << "Current cost of state is " << currentPreferenceCost << ", reachable cost is " << reachablePreferenceCost << ", so returning\n";
            }
        }
        const int fakeH = (!payload->unsatisfiedGoals && !payload->unappearedEnds ? 0 : 1);
        if (RPGBuilder::getMetric() && Globals::optimiseSolutionQuality) {
            if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
                
                double admissibleCost = reachablePreferenceCost/* + definiteWithinCost*/ + RPGBuilder::getMetric()->constant;
                        
                const int pneCount = RPGBuilder::getPNECount();
                list<int>::const_iterator vItr = RPGBuilder::getMetric()->variables.begin();
                const list<int>::const_iterator vEnd = RPGBuilder::getMetric()->variables.end();
                
                list<double>::const_iterator wItr = RPGBuilder::getMetric()->weights.begin();
                const list<double>::const_iterator wEnd = RPGBuilder::getMetric()->weights.end();
                
                for (; wItr != wEnd; ++wItr, ++vItr) {
                    if (*vItr < 0) {
                        if (*wItr < 0.0) {
                            // Would need upper-bound on makespan
                            return new EvaluationInfo(fakeH,std::numeric_limits< double >::signaling_NaN(),!payload->unsatisfiedGoals && !payload->unappearedEnds);
                        } else {
                            admissibleCost += finalPlanMakespanEstimate * *wItr;
                        }
                    } else if (*vItr < pneCount) {
                        const double value = payload->startState.secondMin[*vItr];
                        admissibleCost += value * *wItr;
                    } else {
                        const double value = -payload->startState.secondMax[*vItr];
                        admissibleCost += value * *wItr;
                    }        
                }           
                if (evaluateDebug) {
                    cout << "Returned admissible cost = " << admissibleCost << endl;
                }
                return new EvaluationInfo(fakeH,admissibleCost,!payload->unsatisfiedGoals && !payload->unappearedEnds);
            } else {
                return new EvaluationInfo(fakeH,std::numeric_limits< double >::signaling_NaN(),!payload->unsatisfiedGoals && !payload->unappearedEnds);
            }
        }
    
        return new EvaluationInfo(fakeH,reachablePreferenceCost,!payload->unsatisfiedGoals && !payload->unappearedEnds);
    }                    

    
    d->initPrefCosts();
    
    d->resetAchievedBy(payload.get());
    d->setInitialNegativePreconditionsOfPreferences(payload.get());
    d->recordFactLayerZero(payload.get());    
    d->performTILInitialisation();

    d->initialiseLatestArrays();

    d->addTemporalConstraintsFromActiveActions(payload.get());
    
    if (RPGBuilder::modifiedRPG) {
        d->delayOpenEndsUntilTheirPOPositions(payload.get());
    }

    if (!d->addTemporalConstraintsFromActiveActions(payload.get(), justApplied, EpsilonResolutionTimestamp(stateTS,true), nextTIL, tilFrom)) {

        // will return false in cases where there's a direct contradiction between a TIL
        // and an executing action's invariants

        return new EvaluationInfo(-1,0.0,false);
    }
    d->addTILsBeforeExpansion(payload.get(), nextTIL, payload->factLayers, payload->startState, EpsilonResolutionTimestamp(stateTS,true), tilFrom);
    d->addBoundsFromTemporalAnalysis(stateTS);


    d->noLongerForbidden.clear();

    {
        if (evaluateDebug) cout << "Considering preconditionless actions\n";
        d->updateActionsForNewLiteralFact(payload.get(), -1, EpsilonResolutionTimestamp::zero(), true);
    }


    if (payload->unsatisfiedGoals || payload->unappearedEnds) {

        if (!RPGBuilder::modifiedRPG && RPGBuilder::sortedExpansion) {

            map<double, list<int> > expansionOrder;
                        
            StateFacts::const_iterator stateItr = theState.first.begin();
            const StateFacts::const_iterator stateEnd = theState.first.end();

            for (; stateItr != stateEnd; ++stateItr) {
                const int factID = FACTA(stateItr);
                const double poTS = d->earliestPropositionPOTimes[factID].toDouble();
                expansionOrder[poTS].push_back(factID);
            }


            map<double, list<int> >::const_iterator eoItr = expansionOrder.begin();
            const map<double, list<int> >::const_iterator eoEnd = expansionOrder.end();

            for (; eoItr != eoEnd; ++eoItr) {
                list<int>::const_iterator fItr = eoItr->second.begin();
                const list<int>::const_iterator fEnd = eoItr->second.end();

                for (; fItr != fEnd; ++fItr) {
                    if (d->updateActionsForNewLiteralFact(payload.get(), *fItr, EpsilonResolutionTimestamp::zero(), true)) break;
                }
                if (fItr != fEnd) break;
            }


        } else {            
            if (evaluateDebug) cout << "Considering " << theState.first.size() << " initial propositional facts\n";
            
            if (!RPGBuilder::getPreferences().empty()) {
                StateFacts::const_iterator stateItr = theState.first.begin();
                const StateFacts::const_iterator stateEnd = theState.first.end();


                for (; stateItr != stateEnd; ++stateItr) {
                    const int factID = FACTA(stateItr);
                    if (TemporalAnalysis::getFactIsAbstract()[factID]) {
                        if (evaluateDebug) cout << "Not yet updating preferences from abstract fact " << factID << ", " << *(RPGBuilder::getLiteral(factID)) << endl;
                        continue;
                    }
                    #ifdef POPF3ANALYSIS
                    const EpsilonResolutionTimestamp & layer = d->achieverDetails[factID].back().getLayer();
                    #else
                    const EpsilonResolutionTimestamp & layer = (*(d->achievedInLayer))[factID];
                    #endif
                    if (layer.isZero()) {
                        if (evaluateDebug) cout << "Updating preferences from fact " << factID << ", " << *(RPGBuilder::getLiteral(factID)) << endl;
                        if (d->updatePreferencesForFact(payload.get(), factID, true, true, true, layer)) break;                    
                    } else {
                        if (evaluateDebug) cout << "Modified RPG: Not updating preferences from fact " << factID << " until " << layer << "\n";
                    }
                }

            }
            
            {
                StateFacts::const_iterator stateItr = theState.first.begin();
                const StateFacts::const_iterator stateEnd = theState.first.end();

                for (; stateItr != stateEnd; ++stateItr) {
                    const int factID = FACTA(stateItr);
                     if (TemporalAnalysis::getFactIsAbstract()[factID]) {
                         if (evaluateDebug) cout << "Not yet updating preferences from abstract fact " << factID << ", " << *(RPGBuilder::getLiteral(factID)) << endl;
                        continue;
                    }
                    //const double poTS = (RPGBuilder::modifiedRPG ? 0.0 : d->earliestPropositionPOTimes[factID]);
                    #ifdef POPF3ANALYSIS
                    const EpsilonResolutionTimestamp & layer = d->achieverDetails[factID].back().getLayer();
                    #else
                    const EpsilonResolutionTimestamp & layer = (*(d->achievedInLayer))[factID];
                    #endif
                    if (layer.isZero()) {
                        if (RPGHeuristic::printRPGAsDot) {
                            payload->dot.addFactNode(layer.toDouble(), factID, true);
                        }
                        if (evaluateDebug) cout << "Updating from fact " << factID << " " << *(RPGBuilder::getLiteral(factID)) << "\n";
                        if (d->updateActionsForNewLiteralFact(payload.get(), factID, layer, true)) break;
                    } else {
                        if (evaluateDebug) cout << "Modified RPG: Not updating from fact " << factID << " until " << layer << "\n";
                        payload->factLayers[layer].first.push_back(factID);
                        if (RPGHeuristic::printRPGAsDot) {
                            payload->dot.addFactNode(layer.toDouble(), factID, true);
                        }
                    }
                }
            }
            
        }

    }

    if (payload->unsatisfiedGoals || payload->unappearedEnds) {       
        const int loopLim = d->rpgNumericPreconditions->size();

        if (loopLim) {
            if (evaluateDebug) cout << "Considering initial numeric facts\n";
            
            const vector<double> * const maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
            
            if (!RPGBuilder::getPreferences().empty()) {
                for (int i = 0; i < loopLim; ++i) {
                    RPGBuilder::RPGNumericPrecondition & currPre = (*(d->rpgNumericPreconditions))[i];
                    if (ignoreNumbers || currPre.isSatisfied(*maxFluentTable)) {
                        const EpsilonResolutionTimestamp & layer = (*(d->numericAchievedInLayer))[i];
                        if (layer.isZero()) {
                            if (evaluateDebug) {
                                cout << "Updating preferences from numeric fact " << i << ":  " << (*(d->rpgNumericPreconditions))[i] << endl;
                            }
                            if (d->updatePreferencesForFact(payload.get(), i, false, true, true, layer)) {
                                break;
                            }
                        } else {
                            if (evaluateDebug) {
                                cout << "Not updating preferences from numeric fact " << i << ":  " << (*(d->rpgNumericPreconditions))[i] << " until " << layer << "\n";
                            }
                        }
                    }
                }

            
            }
            
            {
                for (int i = 0; i < loopLim; ++i) {
                    RPGBuilder::RPGNumericPrecondition & currPre = (*(d->rpgNumericPreconditions))[i];
                    if (ignoreNumbers || currPre.isSatisfied(*maxFluentTable)) {
                        const EpsilonResolutionTimestamp & layer = (*(d->numericAchievedInLayer))[i];
                        if (layer.isZero()) {
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(0.0, i, true);
                            }
                            if (evaluateDebug) {
                                cout << "Updating from numeric fact " << i << ":  " << (*(d->rpgNumericPreconditions))[i];
                                cout << "; was achieved in the initial state\n";                            
                            }
                            if (d->updateActionsForNewNumericFact(payload.get(), i, EpsilonResolutionTimestamp::zero())) {
                                break;
                            }
                        } else {
                            if (evaluateDebug) cout << "Modified RPG: Not updating from numeric fact " << i << ":  " << (*(d->rpgNumericPreconditions))[i] << " until " << layer << "\n";
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(layer.toDouble(), i, true);
                            }
                            payload->factLayers[layer].second.push_back(i);
                        }
                    }
                }
            }
                        
        }
        
        
        {
        
            list<int>::const_iterator procItr = d->backgroundProcesses.begin();
            const list<int>::const_iterator procEnd = d->backgroundProcesses.end();
            
            for (; procItr != procEnd; ++procItr) {
                
                const int currAct = *procItr;

                const RPGBuilder::LinearEffects* currLD = RPGBuilder::getLinearDiscretisation()[currAct];
                
                assert(currLD);
                
                const vector<int> & varList = currLD->vars;
                const vector<RPGBuilder::LinearEffects::EffectExpression> & changeList = currLD->effects[0];
                
                const int effCount = varList.size();
                
                for (int e = 0; e < effCount; ++e) {
                    DelayedGradientDescriptor proc(currAct, Planner::E_AT_START, DBL_MAX, make_pair(varList[e], changeList[e].constant));                
                    payload->fluentLayers.recordGradientNumericEffect(proc, EpsilonResolutionTimestamp::epsilon(), proc.gradientEffect, payload->factLayers);
                }
                
                
                
            }
            
        }
    
        
        if (!delayedGradients.empty()) {
            d->addDelayedGradientEffects(payload.get(), delayedGradients);
        }
                    
        
        list<int> newNumericPreconditions;
        
        payload->fluentLayers.applyRecentlyRecordedEffects(*(d->numericAchievedInLayer), newNumericPreconditions, d->maxNeeded);
        
        if (!newNumericPreconditions.empty()) {
            list<int>::const_iterator npItr = newNumericPreconditions.begin();
            const list<int>::const_iterator npEnd = newNumericPreconditions.end();
            
            for (; npItr != npEnd; ++npItr) {
                if (d->goalFluents.find(*npItr) != d->gfEnd) {
                    --(payload->unsatisfiedGoals);
                }
            }
                            
            if (payload->unsatisfiedGoals || payload->unappearedEnds) {
                if (RPGBuilder::modifiedRPG) {
                    
                    list<int>::const_iterator preID = newNumericPreconditions.begin();
                    const list<int>::const_iterator preIDEnd = newNumericPreconditions.end();
                    
                    for (; preID != preIDEnd; ++preID) {
                        const EpsilonResolutionTimestamp earliestPOPoint = earliestPointForNumericPrecondition(RPGBuilder::getNumericPreTable()[*preID], &(d->earliestNumericPOTimes));
                        if (earliestPOPoint > EpsilonResolutionTimestamp::epsilon()) {
                            payload->factLayers[earliestPOPoint].second.push_back(*preID);
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(earliestPOPoint.toDouble(), *preID);
                            }                            
                        } else {
                            payload->factLayers[EpsilonResolutionTimestamp::epsilon()].second.push_back(*preID);
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(EpsilonResolutionTimestamp::epsilon().toDouble(), *preID);
                            }
                            
                        }
                    }
                    
                } else {
                    list<int> & dest = payload->factLayers[EpsilonResolutionTimestamp::epsilon()].second;
                    dest.insert(dest.end(), newNumericPreconditions.begin(), newNumericPreconditions.end());
                }
            }
        }
    }


    if (evaluateDebug) {
        cout << "Unsatisfied goals: " << payload->unsatisfiedGoals << ", Unappeared ends: " << payload->unappearedEnds << "\n";
    }


    {
        if (payload->unsatisfiedGoals && payload->unsatisfiedGoals == payload->fakeGoalCount) {
            if (evaluateDebug || prefDebug) {
                cout << "All remaining goals are fake\n";
            }
            
            assert(RPGBuilder::getMetric());
            
            const bool prefsPreviouslyRemaining = (RPGBuilder::getMetric()->minimise ? (payload->goalPrefViolationAtLastLayer - reachablePreferenceCost >= 0.0001)
                                                                                     : (payload->goalPrefViolationAtLastLayer - reachablePreferenceCost <= -0.0001));
            
            payload->goalPrefViolationAtLastLayer = payload->rpgGoalPrefViolation;
               
            if (prefsPreviouslyRemaining) {                
                if (RPGBuilder::getMetric()->minimise ? (payload->goalPrefViolationAtLastLayer - reachablePreferenceCost < 0.0001)
                                                      : (payload->goalPrefViolationAtLastLayer - reachablePreferenceCost > -0.0001)) {
                    if (prefDebug) {
                        cout << "All preferences now satisfied\n";
                    }
                    --payload->fakeGoalCount;
                    --payload->unsatisfiedGoals;
                }
            }
            
        }
    }

#ifdef POPF3ANALYSIS
    const bool deadline2Debug = false;
#endif

    NextFactLayer nextHappening;
    
    vector<EpsilonResolutionTimestamp> earliestRelevanceOfGoal(RPGBuilder::getLiteralGoals().size(), EpsilonResolutionTimestamp::infinite());
    
    if (payload->unsatisfiedGoals || payload->unappearedEnds) {
        
#ifdef POPF3ANALYSIS
        {
            
            const list<Literal*> & literalGoals = RPGBuilder::getLiteralGoals();
            const list<double> & literalGoalDeadlines = RPGBuilder::getLiteralGoalDeadlines();

            //earliestRelevanceOfGoal.resize(literalGoals.size(), EpsilonResolutionTimestamp::infinite());
                                    
            list<Literal*>::const_iterator gItr = literalGoals.begin();        
            const list<Literal*>::const_iterator gEnd = literalGoals.end();
            
            list<double>::const_iterator gdItr = literalGoalDeadlines.begin();
            
            int gID = 0;            
            
            for (int fID; gItr != gEnd; ++gItr, ++gdItr, ++gID) {
                
                if (RPGBuilder::isStatic(*gItr).first) {
                    continue;
                }
                
                fID = (*gItr)->getStateID();
                          
                if (theState.first.find(fID) != theState.first.end()) {
                    continue;
                }

                if (*gdItr != DBL_MAX) {
                    payload->factLayers[EpsilonResolutionTimestamp(*gdItr,true)].literalGoalsWeMustHaveByNow.push_back(fID);
                    earliestRelevanceOfGoal[gID] = EpsilonResolutionTimestamp(*gdItr,true);
                    
                    if (deadline2Debug) {
                        cout << "Must have " << *(*gItr) << " by " << *gdItr << endl;
                    }
                }
                
                
            
                
            }
            
            map<EpsilonResolutionTimestamp, list<int> >::const_iterator costItr = payload->becomesUnreachableAtLayer.begin();
            const map<EpsilonResolutionTimestamp, list<int> >::const_iterator costEnd = payload->becomesUnreachableAtLayer.end();
            
            for (; costItr != costEnd; ++costItr) {

                payload->factLayers[costItr->first].preferenceUnreachableIfNotSatisfiedByNow = costItr->second;
                
//                 if (RPGBuilder::getTILs().empty()) { // if all deadlines are soft
//                     if (costItr->first < earliestRelevanceOfGoal[gID]) {
//                         earliestRelevanceOfGoal[gID] = costItr->first;
//                     }
//                 }
                
            }
            
        }
        
        
        {
         
            const list<pair<int,int> > & numericGoals = RPGBuilder::getNumericRPGGoals();
            const list<double> & numericGoalDeadlines = RPGBuilder::getNumericRPGGoalDeadlines();
            
            const vector<double> * const maxFluentTable = &(payload->fluentLayers.borrowFactLayerZeroValues());
            
            list<pair<int,int> >::const_iterator gItr = numericGoals.begin();
            const list<pair<int,int> >::const_iterator gEnd = numericGoals.end();
            
            list<double>::const_iterator gdItr = numericGoalDeadlines.begin();
            
            for (int fID; gItr != gEnd; ++gItr, ++gdItr) {
                
                for (int ipass = 0; ipass < 2; ++ipass) {
                    fID = (ipass ? gItr->second : gItr->first);
                    
                    if (fID < 0) continue;
                    
                    if (*gdItr == DBL_MAX) {
                        continue;
                    }                    
                    
                    const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[fID];

                    if (!ignoreNumbers && !currPre.isSatisfied(*maxFluentTable)) {

                        payload->factLayers[EpsilonResolutionTimestamp(*gdItr,true)].numericGoalsWeMustHaveByNow.push_back(fID);
                        
                        if (deadline2Debug) {
                            cout << "Must have " << currPre << " by " << *gdItr << endl;
                        }
                    }
                }
                
            }
        }

#endif
        
        payload->nextThingToVisit(EpsilonResolutionTimestamp::zero(), nextHappening);
    } else {
        #ifdef POPF3ANALYSIS
        payload->tooExpensive = false;
        #endif
    }
    
    #ifdef POPF3ANALYSIS
    const bool breakOnGoalsAndEnds = NumericAnalysis::getGoalNumericUsageLimits().empty();
    #else
    const bool breakOnGoalsAndEnds = true;
    #endif
    
    #ifdef POPF3ANALYSIS
    bool failedToMeetDeadline = false;
    #endif

    while (!nextHappening.empty()) {

        if (evaluateDebug) {
            cout << "Unsatisfied goals: " << payload->unsatisfiedGoals << ", Unappeared ends: " << payload->unappearedEnds << "\n";
            cout << "Expanding RPG forwards, next happening: " << nextHappening.timestamp << "\n";
        }

        #ifdef STOCHASTICDURATIONS        
        if (nextHappening.timestamp.toDouble() > solutionDeadlineTime + (EPSILON / 2)) {
            break;
        }        
        #endif

        {
            // make sure the fluent layer just before the actions that are about to appear exists            
            payload->fluentLayers.createThenIgnore(nextHappening.timestamp);
        }
        
        if (nextHappening.revisitInstantaneousNumericEffects) {
            payload->fluentLayers.recordEffectsThatAreNowToBeRevisited(payload->factLayers);
        }
        
        if (nextHappening.gradientsCauseFactsToBecomeTrue) {
            payload->fluentLayers.recordConsequencesOfActiveGradients(nextHappening.timestamp + EpsilonResolutionTimestamp::epsilon());
        }

         if (nextHappening.newFactsAtThisTime != payload->factLayers.end() && !RPGBuilder::getPreferences().empty()) {
            
            const map<EpsilonResolutionTimestamp, FactLayerEntry>::iterator currFactLayerItr = nextHappening.newFactsAtThisTime;
            if (evaluateDebug) cout << "FACT LAYER UPDATING PREFERENCES AT TIME " << currFactLayerItr->first << "\n";

            const EpsilonResolutionTimestamp & cTime = nextHappening.timestamp; // currFactLayerItr->first;


            {
                list<int>::iterator stateItr = currFactLayerItr->second.first.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.first.end();

                for (; stateItr != stateEnd; ++stateItr) {
                    if (evaluateDebug) cout << "Updating preferences from fact " << *stateItr << ", " << *(RPGBuilder::getLiteral(*stateItr)) << endl;
                    if (d->updatePreferencesForFact(payload.get(), *stateItr, true, true, true, cTime) && breakOnGoalsAndEnds) break;                    
                }

            }
            
            {
                set<int>::iterator stateItr = currFactLayerItr->second.firstRepeated.begin();
                const set<int>::iterator stateEnd = currFactLayerItr->second.firstRepeated.end();
                
                for (; stateItr != stateEnd; ++stateItr) {
                    if (evaluateDebug) cout << "Updating preferences from repeated fact " << *stateItr << ", " << *(RPGBuilder::getLiteral(*stateItr)) << endl;
                    if (d->updatePreferencesForFact(payload.get(), *stateItr, true, true, false, cTime) && breakOnGoalsAndEnds) break;                    
                }
                
            }
            
            {
                list<int>::iterator stateItr = currFactLayerItr->second.negativeLiterals.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.negativeLiterals.end();

                for (; stateItr != stateEnd; ++stateItr) {
                    if (evaluateDebug) cout << "Updating preferences from negative fact " << *stateItr << ", " << *(RPGBuilder::getLiteral(*stateItr)) << endl;
                    if (d->updatePreferencesForFact(payload.get(), *stateItr, true, false, true, cTime) && breakOnGoalsAndEnds) break;                    
                }

            }
            
            {
                list<int>::iterator stateItr = currFactLayerItr->second.second.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.second.end();

                for (; stateItr != stateEnd; ++stateItr) {

                    if (evaluateDebug) {
                        cout << "Updating preferences from numeric fact " << *stateItr << ":  " << (*(d->rpgNumericPreconditions))[*stateItr] << endl;
                    }
                    if (d->updatePreferencesForFact(payload.get(), *stateItr, false, true, true, cTime) && breakOnGoalsAndEnds) {
                        break;
                    }
                }

            }
        }
            

        
        if (nextHappening.endActionsAppearingAtThisTime != payload->endActionsAtTime.end()) {

            if (evaluateDebug) cout << "ACTION LAYER AT TIME " << nextHappening.endActionsAppearingAtThisTime->first << "\n";

            const map<EpsilonResolutionTimestamp, list<pair<int,bool> > >::iterator & eaatItr = nextHappening.endActionsAppearingAtThisTime;

            list<pair<int,bool> >::iterator eaItr = eaatItr->second.begin();
            const list<pair<int,bool> >::iterator eaEnd = eaatItr->second.end();

            const EpsilonResolutionTimestamp & cTime = nextHappening.timestamp; // eaatItr->first;

            for (; eaItr != eaEnd; ++eaItr) {
                int actToPass = eaItr->first;
                bool actIsOpen = false;
                if (actToPass < 0) {
                    actToPass = -actToPass - 1;
                    actIsOpen = true;
                }
                if (cTime > Private::latestEndAllowed[actToPass]) {
                    if (evaluateDebug) {
                        cout << "End of action has been cancelled: invariant or one-way end precondition deleted by TIL\n";
                    }
                } else {
                    
                    int abstractFalse = 0;
                    
                    if (eaItr->second) {
                        const map<int, list<int> > & endUses = TemporalAnalysis::getAbstractFactsUsedByActionEnd();                        
                        
                        map<int, list<int> >::const_iterator euItr = endUses.find(actToPass);                        
                        
                        if (euItr != endUses.end()) {
                            list<int>::const_iterator preItr = euItr->second.begin();
                            const list<int>::const_iterator preEnd = euItr->second.end();
                            
                            for (; preItr != preEnd; ++preItr) {
                                if (!payload->abstractFactCurrentlyTrue[*preItr]) {
                                    ++abstractFalse;
                                }
                            }
                        }
                    }
                    
                    if (abstractFalse > 0) {
                        if (evaluateDebug) {
                            cout << "Not applying ";
                            if (actIsOpen) cout << "open ";
                            cout << "end effect of " << actToPass << " " << *(RPGBuilder::getInstantiatedOp(actToPass)) << ": " << abstractFalse << " as some support is false:";
                            const map<int, list<int> > & endUses = TemporalAnalysis::getAbstractFactsUsedByActionEnd();                        
                        
                            map<int, list<int> >::const_iterator euItr = endUses.find(actToPass);                        
                            
                            if (euItr != endUses.end()) {
                                list<int>::const_iterator preItr = euItr->second.begin();
                                const list<int>::const_iterator preEnd = euItr->second.end();
                                
                                for (; preItr != preEnd; ++preItr) {
                                    if (!payload->abstractFactCurrentlyTrue[*preItr]) {
                                        cout << " " << *(RPGBuilder::getLiteral(*preItr));
                                    }
                                }
                            }
                            cout << endl;
                        }
                        
                        payload->endPreconditionCounts[actToPass] += abstractFalse;                        
                    } else {
                    
                        if (evaluateDebug) {
                            if (!eaItr->second) {
                                cout << "Re-";
                            }
                            cout << "Applying ";
                            if (actIsOpen) cout << "open ";
                            cout << "end effect of " << actToPass << " " << *(RPGBuilder::getInstantiatedOp(actToPass)) << "\n";
                        }
                        
                        if (actIsOpen && eaItr->second) {                            
                            payload->markEndAppeared(actToPass, cTime);
                            if (breakOnGoalsAndEnds && !payload->unappearedEnds && !payload->unsatisfiedGoals) {
                                break;
                            }
                        }
                        if (d->applyEndEffectNow(payload.get(), actToPass, actIsOpen, cTime, eaItr->second) && breakOnGoalsAndEnds) break;
                    }
                }
            }
            if (evaluateDebug) cout << "Finished action layer\n";
            payload->endActionsAtTime.erase(eaatItr);

        }
        
        if (nextHappening.newFactsAtThisTime != payload->factLayers.end()) {
            
            const map<EpsilonResolutionTimestamp, FactLayerEntry>::iterator currFactLayerItr = nextHappening.newFactsAtThisTime;
            if (evaluateDebug) cout << "FACT LAYER AT TIME " << currFactLayerItr->first << "\n";

            const EpsilonResolutionTimestamp & cTime = nextHappening.timestamp; // currFactLayerItr->first;


            {
                list<int>::iterator stateItr = currFactLayerItr->second.first.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.first.end();

                for (; stateItr != stateEnd; ++stateItr) {
                    assert(!RPGBuilder::modifiedRPG || !TemporalAnalysis::getFactIsAbstract()[*stateItr]);
                    if (evaluateDebug) cout << "Updating from fact " << *stateItr << ", " << *(RPGBuilder::getLiteral(*stateItr)) << endl;
                    if (d->updateActionsForNewLiteralFact(payload.get(), *stateItr, cTime, true) && breakOnGoalsAndEnds) break;
                }

            }
            
            {
                set<int>::iterator stateItr = currFactLayerItr->second.firstRepeated.begin();
                const set<int>::iterator stateEnd = currFactLayerItr->second.firstRepeated.end();
                
                for (; stateItr != stateEnd; ++stateItr) {
                    if (evaluateDebug) cout << "Updating from repeated fact " << *stateItr << ", " << *(RPGBuilder::getLiteral(*stateItr)) << endl;
                    if (d->updateActionsForNewLiteralFact(payload.get(), *stateItr, cTime, false) && breakOnGoalsAndEnds) break;
                }
                
            }


            {
                list<int>::iterator stateItr = currFactLayerItr->second.second.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.second.end();

                for (; stateItr != stateEnd; ++stateItr) {

                    if (evaluateDebug) {
                        cout << "Updating from numeric fact " << *stateItr << ":  " << (*(d->rpgNumericPreconditions))[*stateItr] << endl;
                    }
                    if (d->updateActionsForNewNumericFact(payload.get(), *stateItr, cTime) && breakOnGoalsAndEnds) {
                        break;
                    }
                }

            }


//             {
//                 list<pair<int, int> >::iterator stateItr = currFactLayerItr->second.TILs.begin();
//                 const list<pair<int, int> >::iterator stateEnd = currFactLayerItr->second.TILs.end();
// 
//                 for (; stateItr != stateEnd; ++stateItr) {
//                     if (evaluateDebug) cout << "Updating from TIL " << stateItr->first << ", fact " << stateItr->second << "\n";
// 
//                     ActionViolationData & costData = payload->tilCosts[stateItr->first];
//                     
//                     costData.canBeApplied = true;
//                     
//                     d->addPreconditionCost(costData, stateItr->first, Planner::E_AT, EpsilonResolutionTimestamp::undefined(), payload.get());
//                     d->addEffectCost(costData, stateItr->first, Planner::E_AT, payload.get());
// 
//                     const CostedAchieverDetails::AchieverProposalResult applyResult = d->proposeNewAchiever(stateItr->second, stateItr->first, Planner::E_AT, costData, false, cTime);
//                     if (applyResult != CostedAchieverDetails::not_added) {
//                         if (d->updateActionsForNewLiteralFact(payload.get(), stateItr->second, cTime, (applyResult == CostedAchieverDetails::first_achiever)) && breakOnGoalsAndEnds) break;
//                     }
// 
// 
//                 }
//             }

            {
                list<int>::iterator stateItr = currFactLayerItr->second.TILs.begin();
                const list<int>::iterator stateEnd = currFactLayerItr->second.TILs.end();
                
                for (; stateItr != stateEnd; ++stateItr) {
                    ActionViolationData & costData = payload->tilCosts[*stateItr];
                     
                     costData.canBeApplied = true;

                     if (evaluateDebug) {
                         cout << "Updating from TIL " << *stateItr << " @ " << RPGBuilder::getNonAbstractedTILVec()[*stateItr]->duration << " (cTime = " << cTime << ")" << endl;
                     }
                     
                     
                     d->addPreconditionCost(costData, *stateItr, Planner::E_AT, EpsilonResolutionTimestamp::undefined(), payload.get());
                     d->addEffectCost(costData, *stateItr, Planner::E_AT, payload.get());
                     
                     EpsilonResolutionTimestamp nlTime = cTime;
                     ++nlTime;
                     if (d->applyPropositionalEffects(payload.get(), *stateItr, Planner::E_AT, costData, false, nlTime) && breakOnGoalsAndEnds) break;
                }
            }

            if (!currFactLayerItr->second.startDelayedUntilNow.empty()) {
                
                d->noLongerForbidden.clear();
                
                set<int>::const_iterator aItr = currFactLayerItr->second.startDelayedUntilNow.begin();
                const set<int>::const_iterator aEnd = currFactLayerItr->second.startDelayedUntilNow.end();
                
                for (; aItr != aEnd; ++aItr) {
                    d->noLongerForbidden.push_back(make_pair(*aItr, Planner::E_AT_START));
                }
                
                if (d->updateActionsForNewLiteralFact(payload.get(), -2, cTime, true) && breakOnGoalsAndEnds) break;
                
            }
            
            if (currFactLayerItr->second.endOfJustApplied) {
                d->noLongerForbidden.clear();
                set<int> & startSet = currFactLayerItr->second.endOfJustApplied->first;
                set<int> & endSet = currFactLayerItr->second.endOfJustApplied->second;

                bool spawn = false;

                {
                    set<int>::iterator fItr = startSet.begin();
                    const set<int>::iterator fEnd = startSet.end();

                    for (; fItr != fEnd; ++fItr) {
                        map<int, int>::iterator nrItr = payload->forbiddenStart.find(*fItr);
                        if (!(--(nrItr->second))) {
                            payload->forbiddenStart.erase(nrItr);
                            if (!payload->startPreconditionCounts[*fItr]) {
                                assert(*fItr < RPGBuilder::getStartPropositionalPreconditions().size());
                                d->noLongerForbidden.push_back(pair<int, Planner::time_spec>(*fItr, Planner::E_AT_START));
                                spawn = true;
                            }
                        }
                    }
                }
                {
                    set<int>::iterator fItr = endSet.begin();
                    const set<int>::iterator fEnd = endSet.end();

                    for (; fItr != fEnd; ++fItr) {
                        map<int, int>::iterator nrItr = payload->forbiddenEnd.find(*fItr);
                        if (!(--(nrItr->second))) {
                            payload->forbiddenEnd.erase(nrItr);
                            if (!payload->endPreconditionCounts[*fItr]) {
                                assert(*fItr < RPGBuilder::getStartPropositionalPreconditions().size());
                                d->noLongerForbidden.push_back(pair<int, Planner::time_spec>(*fItr, Planner::E_AT_END));
                                spawn = true;
                            }
                        }
                    }
                }

                if (spawn) {
                    if (d->updateActionsForNewLiteralFact(payload.get(), -2, cTime, true) && breakOnGoalsAndEnds) break;
                }
            }

            
            if (RPGBuilder::modifiedRPG && (!currFactLayerItr->second.abstractFactBecomesTrue.empty() || !currFactLayerItr->second.abstractFactBecomesFalse.empty())) {
                // abstract TIL stuff
                d->noLongerForbidden.clear();
                
                bool spawn = false;
                
                {
                    list<int>::iterator delItr = currFactLayerItr->second.abstractFactBecomesFalse.begin();
                    const list<int>::iterator delEnd = currFactLayerItr->second.abstractFactBecomesFalse.end();

                    for (; delItr != delEnd; ++delItr) {
                        
                        if (!payload->abstractFactCurrentlyTrue[*delItr]) {
                            continue;
                        }
                
                        payload->abstractFactCurrentlyTrue[*delItr] = false;
                
                        if (evaluateDebug) {
                            cout << COLOUR_light_blue << "Abstract fact " << *(RPGBuilder::getLiteral(*delItr)) << " becomes false.";
                            cout.flush();
                        }
                
                        list<pair<int, Planner::time_spec> > & currList = (*d->preconditionsToActions)[*delItr];

                        list<pair<int, Planner::time_spec> >::iterator ioItr = currList.begin();
                        const list<pair<int, Planner::time_spec> >::iterator ioEnd = currList.end();

                        int uncounted = 0;
                        for (; ioItr != ioEnd; ++ioItr) {
                            const int actID = ioItr->first;
                            if (ioItr->second == Planner::E_AT_START || ioItr->second == Planner::E_OVER_ALL) {
                                if (payload->startPreconditionCounts[ioItr->first] || payload->numericStartPreconditionCounts[ioItr->first]) {
                                    // still not appeared in the TRPG                                    
                                    ++(payload->startPreconditionCounts[ioItr->first]); // one of its start preconditions has become unsatisfied
                                    ++uncounted;
                                }
                            }
                            if (ioItr->second == Planner::E_AT_END  || ioItr->second == Planner::E_OVER_ALL) {
                                if (payload->endPreconditionCounts[ioItr->first] || payload->numericEndPreconditionCounts[ioItr->first]) {
                                    // still not appeared in the TRPG                                    
                                    ++(payload->endPreconditionCounts[ioItr->first]); // one of its start preconditions has become unsatisfied
                                    ++uncounted;
                                }                                
                            }
                        }
                        
                        if (evaluateDebug) {
                            cout << " Unsupported " << uncounted << " actions\n" << COLOUR_default;                            
                        }
                    }
                }
                
                {
                    list<int>::iterator addItr = currFactLayerItr->second.abstractFactBecomesTrue.begin();
                    const list<int>::iterator addEnd = currFactLayerItr->second.abstractFactBecomesTrue.end();

                    for (; addItr != addEnd; ++addItr) {
                        
                        if (payload->abstractFactCurrentlyTrue[*addItr]) {
                            continue;
                        }
                        
                        payload->abstractFactCurrentlyTrue[*addItr] = true;
                        
                        if (evaluateDebug) {
                            cout << COLOUR_light_blue << "Abstract fact " << *(RPGBuilder::getLiteral(*addItr)) << " becomes true.";
                            cout.flush();
                        }
                
                        
                        list<pair<int, Planner::time_spec> > & currList = (*d->preconditionsToActions)[*addItr];

                        int counted = 0;
                        list<pair<int, Planner::time_spec> >::iterator ioItr = currList.begin();
                        const list<pair<int, Planner::time_spec> >::iterator ioEnd = currList.end();

                        for (; ioItr != ioEnd; ++ioItr) {
                            const int actID = ioItr->first;
                            if (ioItr->second == Planner::E_AT_START || ioItr->second == Planner::E_OVER_ALL) {
                                if (payload->startPreconditionCounts[ioItr->first]) { // still being disabled by at least the absence of this fact
                                    // still not appeared in the TRPG                                    
                                    ++counted;
                                    if (!(--(payload->startPreconditionCounts[ioItr->first])) &&  !(payload->numericStartPreconditionCounts[ioItr->first])) {
                                        d->noLongerForbidden.push_back(pair<int, Planner::time_spec>(actID, Planner::E_AT_START));
                                        spawn = true;
                                    }
                                }
                            }
                            if (ioItr->second == Planner::E_AT_END || ioItr->second == Planner::E_OVER_ALL) {
                                if (payload->endPreconditionCounts[ioItr->first]) { // still being disabled by at least the absence of this fact
                                    // still not appeared in the TRPG                                    
                                    ++counted;
                                    if (!(--(payload->endPreconditionCounts[ioItr->first])) &&  !(payload->numericEndPreconditionCounts[ioItr->first])) {
                                        d->noLongerForbidden.push_back(pair<int, Planner::time_spec>(actID, Planner::E_AT_END));
                                        payload->endActionSchedule[ioItr->first] = cTime;
                                        spawn = true;
                                    }
                                }                                
                            }
                        }
                        
                        if (evaluateDebug) {
                            cout << " Supported " << counted << " actions\n" << COLOUR_default;                            
                        }
                    }
                }
                    
                if (spawn) {
                    if (d->updateActionsForNewLiteralFact(payload.get(), -2, cTime, true) && breakOnGoalsAndEnds) break;
                }
            }
            /*{
                list<int>::iterator negItr = currFactLayerItr->second.negativeTILs.begin();
                const list<int>::iterator negEnd = currFactLayerItr->second.negativeTILs.end();

                for (; negItr != negEnd; ++negItr) {

                    list<pair<int, Planner::time_spec> > & currList = (*(d->preconditionsToActions))[*negItr];

                    list<pair<int, Planner::time_spec> >::iterator ioItr = currList.begin();
                    const list<pair<int, Planner::time_spec> >::iterator ioEnd = currList.end();

                    for (; ioItr != ioEnd; ++ioItr) {
                        if (ioItr->second == Planner::E_AT_START) {
                            {
                                int & checkAndIncr = payload->startPreconditionCounts[ioItr->first];
                                if (checkAndIncr) {
                                    ++checkAndIncr;
                                    //++(payload->endPreconditionCounts[ioItr->first]);
                                }
                            }
                        } else {
                            ++(payload->startPreconditionCounts[ioItr->first]);
                            ++(payload->endPreconditionCounts[ioItr->first]);
                        }
                    }

                }
            }*/

            #ifdef POPF3ANALYSIS
            {
                list<int>::const_iterator gItr = currFactLayerItr->second.literalGoalsWeMustHaveByNow.begin();
                const list<int>::const_iterator gEnd = currFactLayerItr->second.literalGoalsWeMustHaveByNow.end();
                
                for (; gItr != gEnd; ++gItr) {
                    #ifdef POPF3ANALYSIS
                    if (d->achieverDetails[*gItr].empty()) {
                    #else
                    if ((*(d->achievedInLayer))[*gItr] < 0.0) {
                    #endif
                        failedToMeetDeadline = true;
                        break;
                    }

                }
            }
            
            if (!failedToMeetDeadline) {
                
                list<int>::const_iterator gItr = currFactLayerItr->second.numericGoalsWeMustHaveByNow.begin();
                const list<int>::const_iterator gEnd = currFactLayerItr->second.numericGoalsWeMustHaveByNow.end();
                
                for (; gItr != gEnd; ++gItr) {
                    if ((*(d->numericAchievedInLayer))[(*gItr)].isUndefined()) {
                        failedToMeetDeadline = true;
                        break;
                    }
                }
                
            }
            
            if (!failedToMeetDeadline) {
                list<int>::const_iterator gItr = currFactLayerItr->second.preferenceUnreachableIfNotSatisfiedByNow.begin();
                const list<int>::const_iterator gEnd = currFactLayerItr->second.preferenceUnreachableIfNotSatisfiedByNow.end();
                
                bool costChanged = false;
                
                for (; gItr != gEnd; ++gItr) {
                    if (isSatisfied(payload->optimisticPrefStatus[*gItr])) {
                        continue;
                    }
                    
                    payload->optimisticPrefStatus[*gItr] = AutomatonPosition::unreachable;
                    
                    payload->withinCosts += RPGBuilder::getPreferences()[*gItr].cost;
                    costChanged = true;                   
                }
                
                if (costChanged && Globals::bestSolutionQuality > -DBL_MAX) {
                    assert(RPGBuilder::getMetric());
                    if (RPGBuilder::getMetric()->variables.empty()) {
                        double localCost = RPGBuilder::getMetric()->constant + reachablePreferenceCost + payload->withinCosts;
                        if (RPGBuilder::getMetric()->minimise && localCost != 0.0) {
                            localCost = -localCost;
                        }
                        
                        if (localCost <= Globals::bestSolutionQuality) {
                            if (evaluateDebug || PreferenceHandler::preferenceDebug) {
                                cout << "Pruning state: within costs alone would mean the solution cost is " << localCost << " by layer " << currFactLayerItr->first << endl;
                            }
                            failedToMeetDeadline = true;                            
                        }
                        
                    }
                }
            }
            #endif

            if (evaluateDebug) cout << "Finished fact layer\n";


            payload->factLayers.erase(currFactLayerItr);

        }
        
        #ifdef POPF3ANALYSIS
        if (!failedToMeetDeadline) 
        #endif
        {
            // now we've applied all the effects we're going to get, see if new numeric preconditions are true
            // epsilon in the future
            
            list<int> newNumericPreconditions;            
            payload->fluentLayers.applyRecentlyRecordedEffects(*(d->numericAchievedInLayer), newNumericPreconditions, d->maxNeeded);
            
            if (!newNumericPreconditions.empty()) {
                                
                list<int>::const_iterator npItr = newNumericPreconditions.begin();
                const list<int>::const_iterator npEnd = newNumericPreconditions.end();
                
                for (; npItr != npEnd; ++npItr) {
                    if (d->goalFluents.find(*npItr) != d->gfEnd) {
                        --(payload->unsatisfiedGoals);
                        if (payload->unsatisfiedGoals == payload->fakeGoalCount && payload->unappearedEnds == 0) {
                            if (payload->admissibleMakespanEstimate <= nextHappening.timestamp) {
                                payload->admissibleMakespanEstimate = nextHappening.timestamp;
                                ++payload->admissibleMakespanEstimate;
                            }
                        }
                    }
                }
                
                if (RPGBuilder::modifiedRPG) {
                    
                    list<int>::const_iterator preID = newNumericPreconditions.begin();
                    const list<int>::const_iterator preIDEnd = newNumericPreconditions.end();
                    
                    for (; preID != preIDEnd; ++preID) {
                        const EpsilonResolutionTimestamp earliestPOPoint = earliestPointForNumericPrecondition(RPGBuilder::getNumericPreTable()[*preID], &(d->earliestNumericPOTimes));
                        if (earliestPOPoint > nextHappening.timestamp + EpsilonResolutionTimestamp::epsilon()) {
                            payload->factLayers[earliestPOPoint].second.push_back(*preID);
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(earliestPOPoint.toDouble(), *preID);
                            }
                        } else {
                            payload->factLayers[nextHappening.timestamp + EpsilonResolutionTimestamp::epsilon()].second.push_back(*preID);
                            if (printRPGAsDot) {
                                payload->dot.addNumericFactNode(nextHappening.timestamp.toDouble() + EPSILON, *preID);
                            }
                            
                        }
                    }
                                        
                } else {
                    FactLayerEntry & factsGoAt = payload->factLayers[nextHappening.timestamp + EpsilonResolutionTimestamp::epsilon()];
                                        
                    factsGoAt.second.insert(factsGoAt.second.end(), newNumericPreconditions.begin(), newNumericPreconditions.end());
                }
            } else {
                if (evaluateDebug) {
                    cout << "No new numeric preconditions became true\n";
                }                
            }
        }
        
        #ifdef POPF3ANALYSIS
        if (failedToMeetDeadline) {
            break;
        }
        #endif
    
        if (payload->unsatisfiedGoals && payload->unsatisfiedGoals == payload->fakeGoalCount) {
            
            if (evaluateDebug || prefDebug) {
                cout << "All remaining goals are fake\n";
            }
            
            assert(RPGBuilder::getMetric());
            
            const bool prefsPreviouslyRemaining = (RPGBuilder::getMetric()->minimise ? payload->goalPrefViolationAtLastLayer - reachablePreferenceCost >= 0.0001
                                                                                     : payload->goalPrefViolationAtLastLayer - reachablePreferenceCost <= -0.0001);
            
            payload->goalPrefViolationAtLastLayer = payload->rpgGoalPrefViolation;
               
            if (prefsPreviouslyRemaining) {
                if (RPGBuilder::getMetric()->minimise ? payload->goalPrefViolationAtLastLayer - reachablePreferenceCost < 0.0001
                                                      : payload->goalPrefViolationAtLastLayer - reachablePreferenceCost > -0.0001) {
                    if (prefDebug) {
                        cout << "All preferences now satisfied\n";
                    }
                    --payload->fakeGoalCount;
                    --payload->unsatisfiedGoals;
                }
            }
            
        }
    
    
#ifdef POPF3ANALYSIS
        if ((payload->unsatisfiedGoals == payload->fakeGoalCount) && !payload->unappearedEnds) {
            d->calculateGoalCost(payload.get());
        }
#endif

        if (payload->unsatisfiedGoals || payload->unappearedEnds
            #ifdef POPF3ANALYSIS
            || payload->tooExpensive
            #endif            
        ) {
            const EpsilonResolutionTimestamp thisTS = nextHappening.timestamp;
            payload->nextThingToVisit(thisTS, nextHappening);
        } else {
            break;
        }
        
    }

    double calculatedAdmissibleCostThroughFullExpansion;
    
    if (RPGHeuristic::alwaysExpandFully && Globals::optimiseSolutionQuality && !d->currentCosts.empty()) {
        --(payload->unsatisfiedGoals); // undo dummy goal to expand fully
        if (!((payload->unsatisfiedGoals > payload->fakeGoalCount) || payload->unappearedEnds || failedToMeetDeadline)) {
            d->calculateGoalCost(payload.get(), &calculatedAdmissibleCostThroughFullExpansion);        
        }
    }
    
    
    if ((payload->unsatisfiedGoals > payload->fakeGoalCount) || payload->unappearedEnds
#ifdef POPF3ANALYSIS
        || payload->tooExpensive
        || failedToMeetDeadline
#endif                
    ) {
        if (RPGHeuristic::printRPGAsDot) {
            const DotDetails & dot = payload->dot;
            ostringstream dotfn;
            dotfn << "rpg" << statesEvaluated << ".dot";
            const string fn = dotfn.str();
            ofstream dotfile(fn.c_str());
            if (dotfile.bad()) {
                cerr << "Warning: cannot write dot file to " << fn << endl;
            } else {
                dotfile << dot;
                dotfile.close();
            }
        }
        
        
        if (evaluateDebug) {
            cout << "Dead end found in RPG\n";
            
            cout << "unsatisfiedGoals = " << payload->unsatisfiedGoals << ", fake goals " << payload->fakeGoalCount << ", unappearedEnds = " << payload->unappearedEnds;
            #ifdef POPF3ANALYSIS
            if (payload->tooExpensive) {
                cout << ", too expensive";
            }
            if (failedToMeetDeadline) {
                cout << ", failed to meet deadline";
            }
            #endif            
            cout << endl;
            
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (!Globals::remainingActionsInPlan.empty()) {
                list<ActionSegment>::const_iterator actItr = Globals::remainingActionsInPlan.begin();
                const list<ActionSegment>::const_iterator actEnd = Globals::remainingActionsInPlan.end();
                
                for (; actItr != actEnd; ++actItr) {
                    if (actItr->second == Planner::E_AT) {
                        // skip TILs
                        continue;
                    }
                
                    cout << "Seeing if preconditions of " << *(actItr->first);
                    if (actItr->second == Planner::E_AT_START) {
                        cout << ", start, are satisfied\n";
                        if (payload->startPreconditionCounts[actItr->first->getID()]) {
                            cout << "Noted number of unsatisfied start preconditions: " << payload->startPreconditionCounts[actItr->first->getID()] << endl;
                        }
                        map<int,int>::iterator fItr = payload->forbiddenStart.find(actItr->first->getID());
                        if (fItr != payload->forbiddenStart.end()) {
                            cout << "Noted as being forbidden: " << fItr->second << endl;
                        }
                    } else {
                        cout << ", end, are satisfied\n";
                        if (payload->endPreconditionCounts[actItr->first->getID()]) {
                            cout << "Noted number of unsatisfied end preconditions: " << payload->endPreconditionCounts[actItr->first->getID()] << endl;
                        }                        
                        map<int,int>::iterator fItr = payload->forbiddenEnd.find(actItr->first->getID());
                        if (fItr != payload->forbiddenEnd.end()) {
                            cout << "Noted as being forbidden: " << fItr->second << endl;
                        }                        
                    }
                    
                    {
                        const list<Literal*> pres = (actItr->second == Planner::E_AT_START
                                                        ? (*(d->actionsToProcessedStartPreconditions))[actItr->first->getID()]
                                                        : (*(d->actionsToEndPreconditions))[actItr->first->getID()]);
                        
                        list<Literal*>::const_iterator pItr = pres.begin();
                        const list<Literal*>::const_iterator pEnd = pres.end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                            pair<int, Planner::time_spec> acBy;
                            
                            d->getAchieverDetails((*pItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                            
                            if (acIn.isUndefined()) {                                
                                cout << "\tPrecondition " << *(*pItr) << " was never seen. ";
                            } else {                                
                                if (theState.first.find((*pItr)->getStateID()) != theState.first.end()) {
                                    cout << "\tPrecondition " << *(*pItr) << " was achieved in layer " << acIn << endl;
                                } else {
                                    cout << "\tPrecondition " << *(*pItr) << " was true in the partial order at " << acIn << endl;
                                }
                            }
                        }
                    }
                    
                    {
                        const list<int> & pres = (actItr->second == Planner::E_AT_START
                                                    ? (*(d->actionsToProcessedStartNumericPreconditions))[actItr->first->getID()]
                                                    : (*(d->actionsToNumericEndPreconditions))[actItr->first->getID()]);

                        list<int>::const_iterator pItr = pres.begin();
                        const list<int>::const_iterator pEnd = pres.end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            
                            if ((*(d->numericAchievedInLayer))[(*pItr)].isUndefined()) {                                
                                cout << "\tNumeric precondition " << RPGBuilder::getNumericPreTable()[*pItr] << " was never seen. ";
                            } else {
                                if (d->numericIsTrueInState[*pItr]) {
                                    cout << "\tNumeric precondition " << RPGBuilder::getNumericPreTable()[*pItr] << " is true in state, PO time " << (*(d->numericAchievedInLayer))[(*pItr)] << endl;
                                } else {
                                    cout << "\tNumeric precondition " << RPGBuilder::getNumericPreTable()[*pItr] << " was achieved at time " << (*(d->numericAchievedInLayer))[(*pItr)] << endl;
                                } 
                            
                            }
                        }
                        
                    }
                }
            }
            #endif
            
            set<int>::const_iterator gItr = d->goals.begin();
            const set<int>::const_iterator gEnd = d->goals.end();

            for (; gItr != gEnd; ++gItr) {
                #ifdef POPF3ANALYSIS
                if (d->achieverDetails[*gItr].empty()) {
                #else
                if ((*(d->achievedInLayer))[*gItr] < 0.0) {
                #endif
                    cout << "Goal " << *gItr << ", " << *(RPGBuilder::getLiteral(*gItr)) << ", was never seen. ";
                    assert(!(RPGBuilder::isStatic(RPGBuilder::getLiteral(*gItr)).first));
                    cout << "Possible achievers: " << (*(d->effectsToActions))[*gItr].size() << endl;
                    list<pair<int, Planner::time_spec> >::const_iterator aItr = (*(d->effectsToActions))[*gItr].begin();
                    const list<pair<int, Planner::time_spec> >::const_iterator aEnd = (*(d->effectsToActions))[*gItr].end();

                    for (; aItr != aEnd; ++aItr) {
                        if (aItr->second == Planner::E_AT_START) {
                            if (payload->startActionSchedule[aItr->first].isUndefined()) {
                                cout << "- Start of " << aItr->first << ", " << *(RPGBuilder::getInstantiatedOp(aItr->first)) << ", was never seen\n";
                            }
                            list<Literal*> & actPres = (*(d->actionsToProcessedStartPreconditions))[aItr->first];
                            list<Literal*>::const_iterator preItr = actPres.begin();
                            const list<Literal*>::const_iterator preEnd = actPres.end();
                            for (; preItr != preEnd; ++preItr) {
                                EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                pair<int, Planner::time_spec> acBy;
                                
                                #ifdef POPF3ANALYSIS
                                if (d->achieverDetails[(*preItr)->getStateID()].empty()) {
                                    acIn = EpsilonResolutionTimestamp::undefined();
                                } else {
                                    d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                }
                                #else
                                d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                #endif
                                
                                if (acIn.isUndefined()) {
                                    cout << "   * Start precondition " << *(*preItr) << " never appeared\n";
                                }
                            }
                        } else {
                            if (payload->endActionSchedule[aItr->first].isUndefined() && payload->openEndActionSchedule[aItr->first].isUndefined()) {
                                if (!payload->startActionSchedule[aItr->first].isUndefined()) {
                                    cout << "- End of " << aItr->first << ", " << *(RPGBuilder::getInstantiatedOp(aItr->first)) << ", was never seen\n";
                                } else {
                                    cout << "- End of " << aItr->first << ", " << *(RPGBuilder::getInstantiatedOp(aItr->first)) << " was never seen (nor was its start)\n";

                                    list<Literal*> & actPres = (*(d->actionsToProcessedStartPreconditions))[aItr->first];
                                    list<Literal*>::const_iterator preItr = actPres.begin();
                                    const list<Literal*>::const_iterator preEnd = actPres.end();
                                    for (; preItr != preEnd; ++preItr) {
                                        EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                        pair<int, Planner::time_spec> acBy;
                                        
                                        #ifdef POPF3ANALYSIS
                                        if (d->achieverDetails[(*preItr)->getStateID()].empty()) {
                                            acIn = EpsilonResolutionTimestamp::undefined();
                                        } else {
                                            d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                        }
                                        #else
                                        d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                        #endif

                                        if (acIn.isUndefined()) {
                                            cout << "   * Start precondition " << *(*preItr) << " never appeared\n";
                                        }
                                    }
                                }
                                list<Literal*> & actPres = (*(d->actionsToEndPreconditions))[aItr->first];
                                list<Literal*>::const_iterator preItr = actPres.begin();
                                const list<Literal*>::const_iterator preEnd = actPres.end();
                                for (; preItr != preEnd; ++preItr) {
                                    EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                                    pair<int, Planner::time_spec> acBy;
                                    
                                    #ifdef POPF3ANALYSIS
                                    if (d->achieverDetails[(*preItr)->getStateID()].empty()) {
                                        acIn = EpsilonResolutionTimestamp::undefined();
                                    } else {
                                        d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                    }
                                    #else
                                    d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                                    #endif
                                    if (acIn.isUndefined()) {
                                        cout << "   * End precondition " << *(*preItr) << " never appeared\n";
                                    }
                                }

                            }
                        }
                    }
                }
            }
            
            if (startEventQueue) {
                list<StartEvent>::const_iterator seqItr = startEventQueue->begin();
                const list<StartEvent>::const_iterator seqEnd = startEventQueue->end();
                
                for (; seqItr != seqEnd; ++seqItr) {
                    cout << "- End of " << seqItr->actID << ", " << *(RPGBuilder::getInstantiatedOp(seqItr->actID)) << ":\n";

                    bool presHere = true;
                    list<Literal*> & actPres = (*(d->actionsToEndPreconditions))[seqItr->actID];
                    list<Literal*>::const_iterator preItr = actPres.begin();
                    const list<Literal*>::const_iterator preEnd = actPres.end();
                    for (; preItr != preEnd; ++preItr) {
                        EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                        pair<int, Planner::time_spec> acBy;
                        
                        #ifdef POPF3ANALYSIS
                        if (d->achieverDetails[(*preItr)->getStateID()].empty()) {
                            acIn = EpsilonResolutionTimestamp::undefined();
                        } else {
                            d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                        }
                        #else
                        d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                        #endif
                        
                        if (acIn.isUndefined()) {
                            cout << "   * End precondition " << *(*preItr) << " never appeared\n";
                            presHere = false;
                        }
                    }

                    if (presHere) {
                        list<Literal*> & actEffs = (*(d->actionsToEndEffects))[seqItr->actID];
                        
                        list<Literal*>::const_iterator preItr = actEffs.begin();
                        const list<Literal*>::const_iterator preEnd = actEffs.end();
                        for (; preItr != preEnd; ++preItr) {
                            EpsilonResolutionTimestamp acIn(EpsilonResolutionTimestamp::undefined());
                            pair<int, Planner::time_spec> acBy;
                            
                            #ifdef POPF3ANALYSIS
                            if (d->achieverDetails[(*preItr)->getStateID()].empty()) {
                                acIn = EpsilonResolutionTimestamp::undefined();
                            } else {
                                d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                            }
                            #else
                            d->getAchieverDetails((*preItr)->getStateID(), EpsilonResolutionTimestamp::infinite(), acIn, acBy);
                            #endif
                            
                            if (acIn.isUndefined()) {
                                cout << "   * Internal error: effect " << *(*preItr) << " never appeared\n";
                                exit(1);
                            }
                        }
                        
                    }
                }
            }

        }
        if (evaluateDebug) cout << "Leaving getRelaxedPlan()\n";
        return new EvaluationInfo(-1,0.0,false);
    } else {
        if (payload->fakeGoalCount) {
            --payload->unsatisfiedGoals;
            if (evaluateDebug) cout << "RPG found all goals and ends, but could not satisfy some preferences\n";
        } else {
            if (evaluateDebug) cout << "RPG found all goals and ends, and satisfied all preferences\n";
        }
        
        if (prefDebug) {
            cout << COLOUR_red << "Got preference violations down to " << payload->goalPrefViolationAtLastLayer << COLOUR_default << endl;
        }
    }


    


    int h = heuristicOffset;

//  evaluateDebug = true;


    if (!ignoreNumbers && !timeAtWhichValueIsDefined.empty()) {
        const int loopLim = d->rpgNumericPreconditions->size();
        for (int i = 0; i < loopLim; ++i) {
            if (!d->numericIsTrueInState[i]) {
                if ((*(d->rpgNumericPreconditions))[i].isSatisfiedWCalculate(extrapolatedMin, extrapolatedMax)) {
                    d->numericIsTrueInState[i] = true;
                }
            }
        }        
    }

    pair<int, Planner::time_spec> earliestTIL(INT_MAX, Planner::E_AT);

    d->extractRP(payload.get(), h, relaxedPlan, earliestTIL, finalPlanMakespanEstimate, earliestRelevanceOfGoal);

    if (earliestTIL.first != INT_MAX) {
        for (int tilID = theState.nextTIL; tilID <= earliestTIL.first; ++tilID) {
            const double tilTime = RPGBuilder::getNonAbstractedTILVec()[tilID]->duration;
            
            list<pair<double, list<ActionSegment> > >::iterator rpItr = relaxedPlan.begin();
            const list<pair<double, list<ActionSegment> > >::iterator rpEnd = relaxedPlan.end();
            
            for (; rpItr != rpEnd; ++rpItr) {
                if (rpItr->first > tilTime) {
                    break;
                }
            }
            
            if (rpItr != rpEnd) {
                if (EpsilonResolutionTimestamp(rpItr->first,true) == EpsilonResolutionTimestamp(tilTime,true) ) {
                    rpItr->second.push_back(ActionSegment((instantiatedOp*) 0,Planner::E_AT,tilID, RPGHeuristic::emptyIntList));
                    //++h;
                    if (tilID == theState.nextTIL) {
                        helpfulActions.push_back(rpItr->second.back());
                    }
                    
                } else {
                    pair<double, list<ActionSegment> > insPair;
                    
                    insPair.first = tilTime;                    
                    rpItr = relaxedPlan.insert(rpItr, insPair);
                    
                    rpItr->second.push_back(ActionSegment((instantiatedOp*) 0,Planner::E_AT,tilID, RPGHeuristic::emptyIntList));
                    //++h;
                    
                    if (tilID == theState.nextTIL) {
                        helpfulActions.push_back(rpItr->second.back());
                    }
                    
                }
            } else {
                pair<double, list<ActionSegment> > insPair;
                    
                insPair.first = tilTime;                    
                relaxedPlan.push_back(insPair);
                relaxedPlan.back().second.push_back(ActionSegment((instantiatedOp*) 0,Planner::E_AT,tilID, RPGHeuristic::emptyIntList));
                //++h;
                if (tilID == theState.nextTIL) {
                    helpfulActions.push_back(rpItr->second.back());
                }
            }
        }
    }
    

    if (RPGHeuristic::printRPGAsDot) {
        const DotDetails & dot = payload->dot;
        ostringstream dotfn;
        dotfn << "rpg" << statesEvaluated << ".dot";
        const string fn = dotfn.str();
        ofstream dotfile(fn.c_str());
        if (dotfile.bad()) {
            cerr << "Warning: cannot write dot file to " << fn << endl;
        } else {
            dotfile << dot;
            dotfile.close();
        }
    }
    
    

    {
        // HACK

        map<int, int> started;
        map<int, int>::iterator insItr = started.end();
        
        {
            map<int, set<int> >::const_iterator saItr = theState.startedActions.begin();
            const map<int, set<int> >::const_iterator saEnd = theState.startedActions.end();

            for (; saItr != saEnd; ++saItr) {
                insItr = started.insert(insItr, make_pair(saItr->first, saItr->second.size()));                
            }

        }
        list<pair<double, list<ActionSegment> > >::iterator rpItr = relaxedPlan.begin();
        const list<pair<double, list<ActionSegment> > >::iterator rpEnd = relaxedPlan.end();

        for (; rpItr != rpEnd; ++rpItr) {

            list<ActionSegment>::iterator rlItr = rpItr->second.begin();
            const list<ActionSegment>::iterator rlEnd = rpItr->second.end();

            for (; rlItr != rlEnd; ++rlItr) {
                if (rlItr->second == Planner::E_AT) continue;
                if (rlItr->second == Planner::E_AT_END) {
                    if (!TemporalAnalysis::canSkipToEnd(rlItr->first->getID())) {
                        insItr = started.insert(insItr, make_pair(rlItr->first->getID(), 0));
                        --(insItr->second);
                    }
                } else {
                    if (!RPGBuilder::getRPGDEs(rlItr->first->getID()).empty()
                        && !TemporalAnalysis::canSkipToEnd(rlItr->first->getID())) {                        
                        insItr = started.insert(insItr, make_pair(rlItr->first->getID(), 0));
                        ++(insItr->second);
                    }
                }
            }

        }

        map<int, int>::iterator sItr = started.begin();
        const map<int, int>::iterator sEnd = started.end();

        for (; sItr != sEnd; ++sItr) {
            //assert(sItr->second >= 0);
            if (sItr->second > 0) {
                h += sItr->second;
            }
        }


    }

    list<double> haWeights;

    if (RPGBuilder::fullFFHelpfulActions) {

        set<int> startsIn;
        set<int> endsIn;

        {
            list<ActionSegment>::iterator haItr = helpfulActions.begin();
            const list<ActionSegment>::iterator haEnd = helpfulActions.end();

            for (; haItr != haEnd; ++haItr) {
                if (haItr->second == Planner::E_AT_START) {
                    startsIn.insert(haItr->first->getID());
                } else if (haItr->second == Planner::E_AT_END) {
                    endsIn.insert(haItr->first->getID());
                }
            }
        }

        {
            list<ActionSegment>::iterator haItr = helpfulActions.begin();
            const list<ActionSegment>::iterator haEnd = helpfulActions.end();

            for (; haItr != haEnd; ++haItr) {
                list<ActionSegment>::iterator haNext = haItr;
                ++haNext;
                const list<Literal*> * effs = 0;
                if (haItr->second == Planner::E_AT_START) {
                    effs = &((*(d->actionsToStartEffects))[haItr->first->getID()]);
                } else {
                    continue;
                }

                const EpsilonResolutionTimestamp & sas = payload->startActionSchedule[haItr->first->getID()];

                list<Literal*>::const_iterator eItr = effs->begin();
                const list<Literal*>::const_iterator eEnd = effs->end();

                for (; eItr != eEnd; ++eItr) {
                    const list<pair<int, Planner::time_spec> > & acBy = (*(d->effectsToActions))[(*eItr)->getStateID()];
                    list<pair<int, Planner::time_spec> >::const_iterator candItr = acBy.begin();
                    const list<pair<int, Planner::time_spec> >::const_iterator candEnd = acBy.end();

                    for (; candItr != candEnd; ++candItr) {
                        set<int> * checkIn = 0;
                        const list<Literal*> * deps = 0;
                        if (candItr->second == Planner::E_AT_START) {
                            const EpsilonResolutionTimestamp & thisSAS = payload->startActionSchedule[candItr->first];
                            if (thisSAS.isUndefined()) continue;
                            if (thisSAS > sas) continue;
                            checkIn = &startsIn;
                            deps = &((*(d->actionsToProcessedStartPreconditions))[candItr->first]);
                        } else {
                            continue;
                        }
                        if (checkIn->insert(candItr->first).second) {
                            /*                            // first time we've had to work out if this is helpful
                                                        list<Literal*>::const_iterator depItr = deps->begin();
                                                        const list<Literal*>::const_iterator depEnd = deps->end();

                                                        for (; depItr != depEnd; ++depItr) {
                                                            const int factID = (*depItr)->getID();
                                                            const double acIn = (*(d->achievedInLayer))[factID];
                                                            if (acIn == -1.0) break;
                                                            if (acIn > 0.0 && (*(d->achievedBy))[factID].first == -1) break;
                                                        }
                                                        if (depItr == depEnd) {*/
                            helpfulActions.insert(haNext, ActionSegment(RPGBuilder::getInstantiatedOp(candItr->first), candItr->second, -1, emptyIntList));
                            /*}*/
                        }
                    }
                }

                if (haItr->second == Planner::E_AT_START) {
                    effs = &((*(d->actionsToEndEffects))[haItr->first->getID()]);

                    const EpsilonResolutionTimestamp & endStamp = payload->endActionSchedule[haItr->first->getID()];
                    list<Literal*>::const_iterator eItr = effs->begin();
                    const list<Literal*>::const_iterator eEnd = effs->end();

                    for (; eItr != eEnd; ++eItr) {
                        const list<pair<int, Planner::time_spec> > & acBy = (*(d->effectsToActions))[(*eItr)->getStateID()];
                        list<pair<int, Planner::time_spec> >::const_iterator candItr = acBy.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator candEnd = acBy.end();
                        for (; candItr != candEnd; ++candItr) {
                            if (candItr->second != Planner::E_AT_END) continue;
                            if (payload->endActionSchedule[candItr->first] == endStamp) {
                                if (endsIn.insert(candItr->first).second && startsIn.insert(candItr->first).second) {
                                    /*const list<Literal*> * deps = &((*(d->actionsToProcessedStartPreconditions))[candItr->first]);

                                    list<Literal*>::const_iterator depItr = deps->begin();
                                    const list<Literal*>::const_iterator depEnd = deps->end();

                                    for (; depItr != depEnd; ++depItr) {
                                        const int factID = (*depItr)->getID();
                                        const double acIn = (*(d->achievedInLayer))[factID];
                                        if (acIn == -1.0) break;
                                        if (acIn > 0.0 && (*(d->achievedBy))[factID].first == -1) break;
                                    }
                                    if (depItr == depEnd) {                                                                */
                                    helpfulActions.insert(haNext, ActionSegment(RPGBuilder::getInstantiatedOp(candItr->first), Planner::E_AT_START, -1, emptyIntList));
                                    /*}*/
                                }

                            }
                        }
                    }

                }

            }
        }
    }


    if (RPGHeuristic::orderByDeadlineRelevance && !relaxedPlan.empty()) {

        if (Globals::globalVerbosity & 1048576) {
            cout << "Unordered helpful actions:\n";
            
            list<ActionSegment>::iterator haItr = helpfulActions.begin();
            const list<ActionSegment>::iterator haEnd = helpfulActions.end();
            
            for (; haItr != haEnd; ++haItr) {
                if (haItr->second == Planner::E_AT) {
                    cout << "Timed initial literal action " << haItr->divisionID << "\n";
                } else {
                    cout << *(haItr->first) << ", ";
                    if (haItr->second == Planner::E_AT_START) cout << "start\n";
                    if (haItr->second == Planner::E_AT_END) cout << "end\n";
                    if (haItr->second == Planner::E_OVER_ALL) cout << "middle point " << haItr->divisionID << "\n";
                }
            }
            
        }
        
        list<ActionSegment> unsortedList;
        unsortedList.swap(helpfulActions);

        list<ActionSegment>::iterator rlItr = unsortedList.begin();
        const list<ActionSegment>::iterator rlEnd = unsortedList.end();

        for (; rlItr != rlEnd; ++rlItr) {
            //const int thisIOp = rlItr->first;
            if (RPGBuilder::getNonAbstractedTILVec().empty() || ( nextTIL < Private::tilCount && rlItr->second != Planner::E_AT ) ) {
                const double w = (rlItr->second == Planner::E_AT_START ? Private::earliestDeadlineRelevancyStart[rlItr->first->getID()] : Private::earliestDeadlineRelevancyEnd[rlItr->first->getID()]).toDouble();

                list<ActionSegment>::iterator haItr = helpfulActions.begin();
                const list<ActionSegment>::iterator haEnd = helpfulActions.end();
                list<double>::iterator wItr = haWeights.begin();

                for (; haItr != haEnd && (*wItr) < w; ++haItr, ++wItr) ;

                helpfulActions.insert(haItr, *rlItr);
                haWeights.insert(wItr, w);
                if (w == DBL_MAX) {
//                  cout << thisID << " " << "inf\n";
                } else {
//                  cout << thisID << " " << w << "\n";
                }


            } else {
                helpfulActions.push_back(*rlItr);
                haWeights.push_back(DBL_MAX);
            }
        }


    }

    if (evaluateDebug || Globals::globalVerbosity & 1048576) {
        cout << "Relaxed plan for state:\n";
        list<pair<double, list<ActionSegment> > >::iterator rpItr = relaxedPlan.begin();
        const list<pair<double, list<ActionSegment> > >::iterator rpEnd = relaxedPlan.end();

        for (; rpItr != rpEnd; ++rpItr) {
            cout << "\t" << rpItr->first << ":\n";
            list<ActionSegment>::iterator rlItr = rpItr->second.begin();
            const list<ActionSegment>::iterator rlEnd = rpItr->second.end();

            for (; rlItr != rlEnd; ++rlItr) {
                if (rlItr->first) {
                    cout << "\t\t" << *(rlItr->first);
                    if (rlItr->second == Planner::E_AT_END) {
                        cout << ", end\n";
                    } else {
                        cout << ", start\n";
                    }
                } else {
                    cout << "\t\tTIL " << rlItr->divisionID << " @ " << RPGBuilder::getNonAbstractedTILVec()[rlItr->divisionID]->duration << endl;
                }
            }


        }
    }


    if (evaluateDebug || Globals::globalVerbosity & 1048576) {

        cout << "Helpful actions:\n";

        list<ActionSegment>::iterator haItr = helpfulActions.begin();
        const list<ActionSegment>::iterator haEnd = helpfulActions.end();

        for (; haItr != haEnd; ++haItr) {
            if (haItr->second == Planner::E_AT) {
                cout << "Timed initial literal action " << haItr->divisionID << "\n";
            } else {
                cout << *(haItr->first) << ", ";
                if (haItr->second == Planner::E_AT_START) cout << "start\n";
                if (haItr->second == Planner::E_AT_END) cout << "end\n";
                if (haItr->second == Planner::E_OVER_ALL) cout << "middle point " << haItr->divisionID << "\n";
            }
        }


    }

//     double definiteWithinCost = 0.0;
//     
//     if (theState.statusOfTemporalPreferences
// ) {
//      
//         // post-process to mark within preferences as unreachable
//         
//         PreferenceStatusArray & psa = (*(theState.statusOfTemporalPreferences
// ));
//         
//         const list<Literal*> & goals = RPGBuilder::getLiteralGoals();        
//         const vector<map<EpsilonResolutionTimestamp, int> > & softDeadlines = RPGBuilder::getLiteralGoalSoftDeadlines();
//                 
//         const int gSize = softDeadlines.size();
//     
//         list<Literal*>::const_iterator gItr = goals.begin();
//         
//         for (int gID = 0; gID < gSize; ++gID, ++gItr) {
//         
//             if (softDeadlines[gID].empty()) {
//                 // no soft deadlines involving this goal
//                 continue;
//             }
//             
//             if (psa[softDeadlines[gID].rbegin()->second] != AutomatonPosition::satisfied) {
//                 // the final soft deadline on this goal is either eternally broken or satisfied
//                 continue;
//             }
//             
//             const int fID = (*gItr)->getStateID();
// 
//             if (theState.first.find(fID) != theState.first.end()) {
//                 continue;
//             }
//             
//             EpsilonResolutionTimestamp acIn = d->getEarliestAchievedAt(fID);
//                       
//             map<EpsilonResolutionTimestamp, int>::const_iterator costItr = softDeadlines[gID].begin();
//             const map<EpsilonResolutionTimestamp, int>::const_iterator costEnd = softDeadlines[gID].end();
//             
//             for (; costItr != costEnd && acIn >= costItr->first; ++costItr) {
//                 
//                 if (!(psa[costItr->second] == AutomatonPosition::satisfied) ) {
//                     
//                     assert(psa[costItr->second] == AutomatonPosition::unreachable || psa[costItr->second] == AutomatonPosition::eternallysatisfied);
//                     continue;
//                 }
//                 
//                 const RPGBuilder::Constraint & currPref = RPGBuilder::getPreferences()[costItr->second];
//                 
//                 if (evaluateDebug) {
//                     cout << "\t\tUpdating state as in RPG, fact " << *(*gItr) << " didn't appear until " << acIn << ", so at time " << costItr->first << ", violated preference " << currPref.name << ", cost " << currPref.cost << endl;
//                 }            
//                 
//                 psa.getCost() += currPref.cost;
//                 psa[costItr->second] = AutomatonPosition::unreachable;
//                 
//             }
//         }
//         
//         definiteWithinCost += psa.getCost();
//     }
    
    if (RPGBuilder::getMetric()) {
        
        if (RPGBuilder::getMetric()->minimise ? payload->rpgGoalPrefViolation > reachablePreferenceCost
                                              : payload->rpgGoalPrefViolation < reachablePreferenceCost) {
        
            if (prefDebug) {
                cout << "Minimum violation cost to goal " << payload->rpgGoalPrefViolation << endl;
            }
            
            list<int> punreachable;
            
            const int pCount = payload->optimisticPrefStatus.size();
            
            for (int p = 0; p < pCount; ++p) {
                if (!canBeSatisfied(theState.preferenceStatus[p])) continue;
                if (!isSatisfied(payload->optimisticPrefStatus[p])) {
                    punreachable.push_back(p);
                    if (prefDebug) {
                        cout << "Preference " << RPGBuilder::getPreferences()[p].name << " (" << p << ") was never reached\n";
                        
                        NNF_Flat * const f = payload->initialUnsatisfiedPreferenceConditions[p][0];
                        assert(!f->isSatisfied());
                        
                        const NNF_Flat::Cell * const cells = f->getCells();
                        const bool * cellIsAnd = f->cellIsAnAnd();
                        const int cellCount = f->getCellCount();
                        const int * parentIDs = f->getParentIDs();
                        
                        if (cellIsAnd[0]) {
                            bool oneWasFalse = false;
                            
                            if (RPGBuilder::getPreferences()[p].cons == E_WITHIN) {
                                if (payload->optimisticPrefStatus[p] == AutomatonPosition::unreachable) {
                                    cout << " #t Not satisfied in time\n";
                                    oneWasFalse = true;
                                }
                            }
                            
                            for (int cc = 0; cc < cellCount; ++cc) {
                                if (!cells[cc].isCell()) continue;
                                if (parentIDs[cc] != 0) continue;
                                
                                if (cells[cc].lit) {
                                    const int fID = cells[cc].lit->getStateID();
                                    if (cells[cc].polarity) {
                                        if (d->achieverDetails[fID].empty()) {
                                            oneWasFalse = true;
                                            cout << " - Don't have supporting fact " << *(cells[cc].lit) << endl;
                                        } else {
                                            cout << " + Have supporting fact " << *(cells[cc].lit) << endl;
                                        }
                                    } else {
                                        if ((*d->negativeAchievedInLayer)[fID].isUndefined()) {
                                            oneWasFalse = true;
                                            cout << " - Don't have supporting fact ¬" << *(cells[cc].lit) << endl;
                                        } else {
                                            cout << " + Have supporting fact ¬" << *(cells[cc].lit) << endl;
                                        }
                                    }
                                } else {
                                    const int fID = cells[cc].num;
                                    if (cells[cc].polarity) {                                    
                                        if ((*d->numericAchievedInLayer)[fID].isUndefined()) {
                                            oneWasFalse = true;
                                            cout << " - Don't have supporting numeric " << RPGBuilder::getNumericPreTable()[fID] << endl;
                                        }
                                    } else {
                                        //if ((*negativeNumericAchievedInLayer)[fID] < 0.0) {
                                            oneWasFalse = true;
                                        //    cout << " - Don't have supporting numeric ¬" << RPGBuilder::getNumericPrecs()[fID] << endl;
                                        //}
                                    }
                                }
                            }
                            
                            assert(oneWasFalse);
                            
                        }
                        
                        
                    }
                }
            }
            
            if (!punreachable.empty()) {
                if (PreferenceHandler::markUnreachables(theState, punreachable) == DBL_MAX) {
                    // unsatisfied :constraints
                    return new EvaluationInfo(-1,0.0,false);
                }
            }
                                
        }
    }
        
    if (RPGBuilder::getMetric() && Globals::optimiseSolutionQuality) {
        if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
                        
            double admissibleCost = 0.0;
            
            if (RPGHeuristic::alwaysExpandFully && Globals::optimiseSolutionQuality && !d->currentCosts.empty()) {
                admissibleCost = calculatedAdmissibleCostThroughFullExpansion;
                //cout << "Heuristic admissible cost = " << admissibleCost << endl;
            } else {
                
                admissibleCost = payload->rpgGoalPrefViolation/* + definiteWithinCost*/ + RPGBuilder::getMetric()->constant;
                        
                const int pneCount = RPGBuilder::getPNECount();
                list<int>::const_iterator vItr = RPGBuilder::getMetric()->variables.begin();
                const list<int>::const_iterator vEnd = RPGBuilder::getMetric()->variables.end();
                
                list<double>::const_iterator wItr = RPGBuilder::getMetric()->weights.begin();
                const list<double>::const_iterator wEnd = RPGBuilder::getMetric()->weights.end();
                
                for (; wItr != wEnd; ++wItr, ++vItr) {
                    if (*vItr < 0) {
                        if (*wItr < 0.0) {
                            // Would need upper-bound on makespan
                            return new EvaluationInfo(h,std::numeric_limits< double >::signaling_NaN(),realGoalsSatisfied);
                        } else {
                            admissibleCost += finalPlanMakespanEstimate * *wItr;
                        }
                    } else if (*vItr < pneCount) {
                        const double value = payload->startState.secondMin[*vItr];
                        admissibleCost += value * *wItr;
                    } else {
                        const double value = -payload->startState.secondMax[*vItr];
                        admissibleCost += value * *wItr;
                    }        
                }
                
                //cout << "Normal admissible cost = " << admissibleCost << endl;
            
            }
            
            return new EvaluationInfo(h,admissibleCost,realGoalsSatisfied);
            
        } else {        
            return new EvaluationInfo(h,std::numeric_limits< double >::signaling_NaN(),realGoalsSatisfied);
        }
    }
    
    return new EvaluationInfo(h,payload->rpgGoalPrefViolation/* + definiteWithinCost*/,realGoalsSatisfied);
    
};

EpsilonResolutionTimestamp RPGHeuristic::Private::earliestTILForAction(const unsigned int & i, const bool & isStart)
{

    assert(i >= 0);
    assert(i < actionsToEndPreconditions->size());
    EpsilonResolutionTimestamp toReturn(EpsilonResolutionTimestamp::infinite());

    list<Literal*> & inspect = (isStart ? (*actionsToProcessedStartPreconditions)[i] : (*actionsToEndPreconditions)[i]);
    list<Literal*>::iterator insItr = inspect.begin();
    const list<Literal*>::iterator insEnd = inspect.end();

//  cout << "\t\tRequires precs:\n";
    for (; insItr != insEnd; ++insItr) {
//      cout << "\t\t\t" << *(*insItr);
        assert(*insItr);
        const EpsilonResolutionTimestamp & thisD = deadlineAtTime[(*insItr)->getStateID()];
        if (toReturn > thisD) toReturn = thisD;
        if (thisD == EpsilonResolutionTimestamp::infinite()) {
//          cout << ", which is never a deadline\n";
        } else {
//          cout << ", which is a deadline at " << thisD << "\n";
        }
    }

    return toReturn;

};

EpsilonResolutionTimestamp RPGHeuristic::earliestTILForAction(const int & i, const bool & isStart)
{

    return d->earliestTILForAction(i, isStart);

};

bool RPGHeuristic::Private::applyPropositionalEffects(Private::BuildingPayload * const payload,
                                                      const int & currAct, const Planner::time_spec & currTS, const ActionViolationData & prefCosts,
                                                      const bool & openEnd, const EpsilonResolutionTimestamp & nlTime)//, MaxDependentInfo & POtime)
{
    static const bool updateDebug = Globals::globalVerbosity & 64 || evaluateDebug;

    {
        const list<Literal*> & addEffects = (currTS == Planner::E_AT
                                                ? RPGBuilder::getNonAbstractedTILVec()[currAct]->addEffects
                                                : (currTS == Planner::E_AT_START ? RPGBuilder::getStartPropositionAdds()[currAct] : RPGBuilder::getEndPropositionAdds()[currAct]));

        list<Literal*>::const_iterator addEffItr = addEffects.begin();
        const list<Literal*>::const_iterator addEffEnd = addEffects.end();

        for (; addEffItr != addEffEnd; ++addEffItr) {
            const int currEff = (*addEffItr)->getStateID();
            const CostedAchieverDetails::AchieverProposalResult applyResult = proposeNewAchiever(currEff, currAct, currTS, prefCosts, openEnd, nlTime);
            
            switch (applyResult) {
                case CostedAchieverDetails::not_added: {
                    if (updateDebug) cout << "\t\tFact " << currEff << ", " << *(*addEffItr) << ", was already achieved\n";
                    break;
                }
                case CostedAchieverDetails::replaced_existing_achiever: {            
                    // fact is repeated, now with lower cost
                    if (RPGHeuristic::printRPGAsDot) {
                        payload->dot.addActionToFactEdge(currAct, currTS, currEff);
                    }
                    if (updateDebug) cout << "\t\tFact " << currEff << ", " << *(*addEffItr) << ", now achieved at " << nlTime << " with lower cost\n";
                    payload->factLayers[nlTime].firstRepeated.insert(currEff);
                    break;
                }
                case CostedAchieverDetails::first_achiever: {
                    // fact is properly new
                    if (RPGHeuristic::printRPGAsDot) {
                        payload->dot.addFactNode(nlTime.toDouble(), currEff);
                        payload->dot.addActionToFactEdge(currAct, currTS, currEff);
                    }
                                                                
                                                                
                    payload->factLayers[nlTime].first.push_back(currEff);
                    //earliestPropositionPOTimes[currEff] = POtime.get();
                    if (updateDebug) cout << "\t\tFact " << currEff << ", " << *(*addEffItr) << ", is new in " << nlTime << "\n";
                    if (goals.find(currEff) != gsEnd) {
                        --(payload->unsatisfiedGoals);
                        if (payload->unsatisfiedGoals == payload->fakeGoalCount && payload->unappearedEnds == 0) {
                            
                            // either have met everything, or only have soft-goals left
                            if (payload->admissibleMakespanEstimate < nlTime) {
                                payload->admissibleMakespanEstimate = nlTime;
                            }
                            
                            if (payload->unsatisfiedGoals == 0) {      
                                // can return true (terminate expansion) if there are no outstanding fake goals
                                return true;
                            }
                        }

                    }
                    break;
                }
                case CostedAchieverDetails::same_time_as_first_achiever: {
                    // another achiever at the same time as the prior best achiever, but this one is cheaper
                    if (updateDebug) cout << "\t\tFact " << currEff << ", " << *(*addEffItr) << ", achieved at " << nlTime << " - no later than before, but now with lower cost\n";
                    if (RPGHeuristic::printRPGAsDot) {
                        payload->dot.addActionToFactEdge(currAct, currTS, currEff);
                    }
                    break;
                }
            }
        }
    }
    {
        const list<Literal*> & delEffects = (currTS == Planner::E_AT
                                                ? RPGBuilder::getNonAbstractedTILVec()[currAct]->delEffects
                                                : (currTS == Planner::E_AT_START ? RPGBuilder::getStartPropositionDeletes()[currAct] : RPGBuilder::getEndPropositionDeletes()[currAct]));

        list<Literal*>::const_iterator delEffItr = delEffects.begin();
        const list<Literal*>::const_iterator delEffEnd = delEffects.end();

                                                
        for (; delEffItr != delEffEnd; ++delEffItr) {
            const int currEff = (*delEffItr)->getStateID();
        
            EpsilonResolutionTimestamp & currAIL = (*negativeAchievedInLayer)[currEff];
            if (currAIL.isUndefined()) {                            
                if (updateDebug) cout << "\t\tNegative fact " << currEff << " is new\n";
                currAIL = nlTime;
                (*negativeAchievedBy)[currEff] = pair<int, Planner::time_spec>(currAct, currTS);
                payload->factLayers[nlTime].negativeLiterals.push_back(currEff);
            }  
            
        }
    }
    
    return false;
}

bool RPGHeuristic::Private::checkPreconditionsAreSatisfied(const int & currAct, const Planner::time_spec & ts, const EpsilonResolutionTimestamp & layer)
{

    {
        const list<Literal*> & precList = (ts == Planner::E_AT_START
                                           ? (*actionsToProcessedStartPreconditions)[currAct]
                                           : (*actionsToEndPreconditions)[currAct]
                                          );


        list<Literal*>::const_iterator pItr = precList.begin();
        const list<Literal*>::const_iterator pEnd = precList.end();


        for (; pItr != pEnd; ++pItr) {
            #ifdef POPF3ANALYSIS
            assert(!achieverDetails[(*pItr)->getStateID()].empty());
            assert(achieverDetails[(*pItr)->getStateID()].front().getLayer() <= layer);
            assert(achieverDetails[(*pItr)->getStateID()].front().getAchiever() != make_pair(currAct, ts));
            if (evaluateDebug) cout << "\t\t\t\tPrecondition " << *(*pItr) << " first became true at " << achieverDetails[(*pItr)->getStateID()].front().getLayer() << "\n";
            #else
            assert((*achievedInLayer)[(*pItr)->getStateID()] != -1.0);
            assert((*achievedInLayer)[(*pItr)->getStateID()] <= layer);
            assert((*achievedBy)[(*pItr)->getStateID()] != make_pair(currAct, ts));
            if (evaluateDebug) cout << "\t\t\t\tPrecondition " << *(*pItr) << " became true at " << (*achievedInLayer)[(*pItr)->getStateID()] << "\n";
            #endif
        }
    }

    {
        const list<int> & precList = (ts == Planner::E_AT_START
                                      ? (*actionsToProcessedStartNumericPreconditions)[currAct]
                                      : (*actionsToNumericEndPreconditions)[currAct]
                                     );

        list<int>::const_iterator pItr = precList.begin();
        const list<int>::const_iterator pEnd = precList.end();


        for (; pItr != pEnd; ++pItr) {
            assert(!(*numericAchievedInLayer)[(*pItr)].isUndefined());
            assert((*numericAchievedInLayer)[(*pItr)] <= layer);
            ActionFluentModification * const ac = (*numericAchievedBy)[(*pItr)];
            if (ac) {
                assert(!(ac->act == currAct && ac->ts == ts));
            }
            if (evaluateDebug) cout << "\t\t\t\tNumeric precondition " << (*pItr) << " became true at " << (*numericAchievedInLayer)[(*pItr)] << "\n";
        }
    }

    return true;
}

bool RPGHeuristic::Private::applyNumericEffects(Private::BuildingPayload * const payload,
                                                const int & currAct, const Planner::time_spec & currTS, const EpsilonResolutionTimestamp & nlTime,
                                                const int & limitTo)
{
    
    const int actualLimit = (limitTo != -1 ? limitTo : RPGBuilder::howManyTimesOptimistic(currAct, payload->startState));
    
    if (actualLimit == 0) {
        if (evaluateDebug) {
            cout << "\t\tNot applying numeric effects: are not interesting\n";
        }
        return false;
    }
    
    assert(actualLimit > 0);
    
    ActionAndHowManyTimes details(currAct, currTS,
                                  actualLimit,
                                  payload->actionDurations[currAct].first, payload->actionDurations[currAct].second);
    
    {
        // first, instantaneous numeric effects
        const list<int> & numericEffects = (currTS == Planner::E_AT_START ? (*actionsToRPGNumericStartEffects)[currAct]
                                                                      : (*actionsToRPGNumericEndEffects)[currAct]  );
        
        list<int>::const_iterator numEffItr = numericEffects.begin();
        const list<int>::const_iterator numEffEnd = numericEffects.end();
        
        for (; numEffItr != numEffEnd; ++numEffItr) {
            payload->fluentLayers.recordInstantaneousNumericEffect(details, nlTime, *numEffItr);
        }
        
        
    }

    map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(currAct);

    if (iceItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {
        list<RPGBuilder::IntegralContinuousEffect>::const_iterator ceItr = iceItr->second.begin();
        const list<RPGBuilder::IntegralContinuousEffect>::const_iterator ceEnd = iceItr->second.end();
        
        for (; ceItr != ceEnd; ++ceItr) {
            if (ceItr->getTS() == currTS) {
                list<int> numericEffects;
                EpsilonResolutionTimestamp now(nlTime);
                --now;
                if (currTS == Planner::E_AT_START) {
                    ceItr->getRelaxedStartEffects(numericEffects, now.toDouble());
                } else {
                    ceItr->getRelaxedEndEffects(numericEffects, now.toDouble());
                }
                
                
                if (evaluateDebug) {
                    cout << "Applying a bunch of ICE outcomes\n";
                }
                list<int>::const_iterator numEffItr = numericEffects.begin();
                const list<int>::const_iterator numEffEnd = numericEffects.end();
                
                for (; numEffItr != numEffEnd; ++numEffItr) {
                    payload->fluentLayers.recordInstantaneousNumericEffect(details, nlTime, *numEffItr);
                }
            }
        }
    }
    
    if (currTS == Planner::E_AT_START) {
        // any continuous effects?
        
        // first, any that have been integrated
        if (!integratedCTSEffectChange[currAct].empty()) {            
            list<double>::const_iterator contChangeItr = integratedCTSEffectChange[currAct].begin();
            const list<double>::const_iterator contChangeEnd = integratedCTSEffectChange[currAct].end();
            
            list<int>::const_iterator contChangeVar = integratedCTSEffectVar[currAct].begin();
            
            for (; contChangeItr != contChangeEnd; ++contChangeItr, ++contChangeVar) {
                payload->fluentLayers.recordIntegratedNumericEffect(details, nlTime, make_pair(*contChangeVar, *contChangeItr));
            }
        }
        
        if (!gradientCTSEffectChange[currAct].empty()) {

            list<double>::const_iterator contChangeItr = gradientCTSEffectChange[currAct].begin();
            const list<double>::const_iterator contChangeEnd = gradientCTSEffectChange[currAct].end();
            
            list<int>::const_iterator contChangeVar = gradientCTSEffectVar[currAct].begin();
            
            for (; contChangeItr != contChangeEnd; ++contChangeItr, ++contChangeVar) {
                payload->fluentLayers.recordGradientNumericEffect(details, nlTime, make_pair(*contChangeVar, *contChangeItr), payload->factLayers);

            }
            
        }
    }
    
    return false;
}
   

bool RPGHeuristic::Private::updateActionsForNewLiteralFact(Private::BuildingPayload * const payload,
                                                           const int & toPropagate, const EpsilonResolutionTimestamp & factLayerTime,
                                                           const bool & decrementRemainingUnsatisfiedPreconditionCounters)
{
    
    vector<int> & startPreconditionCounts = payload->startPreconditionCounts;
    vector<int> & endPreconditionCounts = payload->endPreconditionCounts;
    vector<int> & numericStartPreconditionCounts = payload->numericStartPreconditionCounts;
    vector<int> & numericEndPreconditionCounts = payload->numericEndPreconditionCounts;
    map<EpsilonResolutionTimestamp, list<pair<int,bool> > > & endActionsAtTime = payload->endActionsAtTime;
    vector<EpsilonResolutionTimestamp> & startActionSchedule = payload->startActionSchedule;
    vector<EpsilonResolutionTimestamp> & endActionSchedule = payload->endActionSchedule;
    vector<EpsilonResolutionTimestamp> & openEndActionSchedule = payload->openEndActionSchedule;
    const map<int, set<int> > & startedActions = payload->startedActions;
    int & unsatisfiedGoals = payload->unsatisfiedGoals;
    int & unappearedEnds = payload->unappearedEnds;
    map<int, set<int> > & insistUponEnds = payload->insistUponEnds;
    map<int, int> & forbiddenStart = payload->forbiddenStart;
    map<int, int> & forbiddenEnd = payload->forbiddenEnd;


    const EpsilonResolutionTimestamp nlTime = factLayerTime + EpsilonResolutionTimestamp::epsilon();
    const bool updateDebug = Globals::globalVerbosity & 64;
    const bool preconditionless = (toPropagate < 0);
    list<pair<int, Planner::time_spec> > & dependents = ((toPropagate == -1) ? (*preconditionlessActions) : ((toPropagate == -2) ? (noLongerForbidden) : (*processedPreconditionsToActions)[toPropagate]));

    if (evaluateDebug) {
        if (toPropagate == -1) {
            cout << "*Special case: preconditionless actions\n";
        } else if (toPropagate == -2) {
            cout << "*Special case: actions that are no longer forbidden\n";
        }
    }

    list<pair<int, Planner::time_spec> >::iterator depItr = dependents.begin();
    const list<pair<int, Planner::time_spec> >::iterator depEnd = dependents.end();

    if (updateDebug) cout << "\tAffects " << dependents.size() << " actions\n";

    for (; depItr != depEnd; ++depItr) {
        const int currAct = depItr->first;
        const bool startAct = (depItr->second == Planner::E_AT_START);
        assert(depItr->second != Planner::E_OVER_ALL);
        if (updateDebug) {
            cout << "\tAffects " << currAct;
            cout.flush();
        }
        assert(currAct >= 0 && currAct < RPGBuilder::getStartPropositionalPreconditions().size());
        assert(RPGBuilder::rogueActions[currAct] == RPGBuilder::OT_NORMAL_ACTION);
        if (updateDebug) cout << ", " << (startAct ? "start" : "end") << " " << *(RPGBuilder::getInstantiatedOp(currAct)) << "\n";
        if (startAct) {
            int & spc = startPreconditionCounts[currAct];
            if (!preconditionless && decrementRemainingUnsatisfiedPreconditionCounters) --spc;
            if ((!spc && !numericStartPreconditionCounts[currAct]) && forbiddenStart.find(currAct) == forbiddenStart.end() && nlTime < latestStartAllowed[currAct]) {
                
                if (startShouldBeDelayed(currAct, factLayerTime, payload)) {
                    continue;
                }
                
                assert(!RPGBuilder::rogueActions[currAct]);
                if (updateDebug) {
                    cout << "\tStart of action " << currAct << " is now applicable: " << startPreconditionCounts[currAct] << "/" << numericStartPreconditionCounts[currAct];
                    if (preconditionless) cout << ", considered preconditionless";
                    cout << "\n";
                }

                if (RPGHeuristic::printRPGAsDot) {
                    payload->dot.addActionNode(factLayerTime.toDouble(), depItr->first, depItr->second);
                }

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

                if (expandFully) earliestStartAllowed[currAct] = factLayerTime;

                if (decrementRemainingUnsatisfiedPreconditionCounters) {
                    startActionSchedule[currAct] = factLayerTime;
                    computeDynamicCost(currAct, Planner::E_AT_START, factLayerTime);
                }

                ActionViolationData & costData = payload->startActionCosts[currAct];
                
                costData.canBeApplied = true;
                
                addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
                addEffectCost(costData, currAct, depItr->second, payload);
                
                

                //MAKESTARTMDI(POtime, currAct);

                if (updateDebug) {
                    cout << "\t\ti) Applying propositional effects in " << nlTime << "\n";
                }
                if (applyPropositionalEffects(payload, currAct, Planner::E_AT_START, costData, false, nlTime/*, POtime*/)) {
                    return true;
                }

                if (updateDebug) {
                    cout << "\t\tii) Applying numeric effects\n";
                }
                if (applyNumericEffects(payload, currAct, Planner::E_AT_START, nlTime, -1)) return true;


                {
                    static pair<EpsilonResolutionTimestamp, list<pair<int,bool> > > defaultEntry(EpsilonResolutionTimestamp::undefined(), list<pair<int,bool> >());
                    
                    defaultEntry.first = factLayerTime + EpsilonResolutionTimestamp(payload->actionDurations[currAct].first,true);
                 
                    if (decrementRemainingUnsatisfiedPreconditionCounters) {
                        endActionSchedule[currAct] = defaultEntry.first;
                    }

                    if (!endPreconditionCounts[currAct] && !numericEndPreconditionCounts[currAct]) {
                        if (updateDebug) {
                            if (decrementRemainingUnsatisfiedPreconditionCounters) {
                                cout << "\t\tiii) End of action can be put at a fact layer sufficiently far in future (" << defaultEntry.first << "\n";
                            } else {
                                cout << "\t\tiii) End of action can be repeated at a fact layer sufficiently far in future (" << defaultEntry.first << "\n";
                            }
                        }

                        endActionsAtTime.insert(defaultEntry).first->second.push_back(make_pair(currAct, decrementRemainingUnsatisfiedPreconditionCounters) );
                    }
                }

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

            } else {
                if (updateDebug) cout << "\tStart of action " << currAct << " now only has " << startPreconditionCounts[currAct] << " unsatisfied propositional preconditions and " << numericStartPreconditionCounts[currAct] << " numeric\n";
            }
        } else {
            int & epc = endPreconditionCounts[currAct];
            if (!preconditionless && decrementRemainingUnsatisfiedPreconditionCounters) --epc;
            if ((!epc && !numericEndPreconditionCounts[currAct]) && forbiddenEnd.find(currAct) == forbiddenEnd.end() && nlTime < latestEndAllowed[currAct]) {
                if (RPGBuilder::rogueActions[currAct]) {
                    cout << "Critical Error: Trying to apply end of action " << currAct << ", " << *(RPGBuilder::getInstantiatedOp(currAct)) << ", which is invalid or irrelevant\n";
                    if (&dependents == preconditionlessActions) {
                        cout << "\tFound it on the list of preconditionless actions\n";
                    } else {
                        cout << "\tFound it on the list of actions depending on " << RPGBuilder::getLiteral(toPropagate) << "\n";
                    }
                    assert(!RPGBuilder::rogueActions[currAct]);
                }
                                if (updateDebug) cout << "\tEnd of action " << currAct << ", " << *(RPGBuilder::getInstantiatedOp(currAct)) << ", is now applicable\n";


                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

                bool insistOnThisEnd = (insistUponEnds.find(currAct) != insistUponEnds.end());
                
                if (decrementRemainingUnsatisfiedPreconditionCounters) {
                
                    if (expandFully) earliestEndAllowed[currAct] = factLayerTime;

                    computeDynamicCost(currAct, Planner::E_AT_END, factLayerTime);
                    
                    if (insistOnThisEnd) {
                        if (updateDebug) cout << "\tEnd is insisted upon, had " << unappearedEnds << " remaining\n";
                        if (factLayerTime - openEndActionSchedule[currAct] >= EpsilonResolutionTimestamp::zero()) {
                            payload->markEndAppeared(currAct, factLayerTime);                            
                            if (!unappearedEnds && unsatisfiedGoals == payload->fakeGoalCount) {
                                
                                if (payload->admissibleMakespanEstimate < factLayerTime) {
                                    payload->admissibleMakespanEstimate = factLayerTime;
                                }
                                
                                if (unsatisfiedGoals == 0) {
                                    return true;                                
                                }
                            }
                            
                            if (updateDebug) cout << "\tNow down to " << unappearedEnds << "\n";
                        } else {
                            if (updateDebug) cout << "\tOpen end cannot appear quite yet\n";
                            insistOnThisEnd = false;
                            endActionsAtTime[openEndActionSchedule[currAct]].push_back(make_pair(-1 - currAct, decrementRemainingUnsatisfiedPreconditionCounters));
                            /*--unappearedEnds; // has still appeared, insofar as plan extraction will happily pick this up at a later layer.
                            if (!unappearedEnds && unsatisfiedGoals == payload->fakeGoalCount) {
                                
                                if (payload->admissibleMakespanEstimate < openEndActionSchedule[currAct]) {
                                    payload->admissibleMakespanEstimate = openEndActionSchedule[currAct];
                                }
                                                                
                                if (unsatisfiedGoals == 0) {
                                    return true;                                
                                }
                            }*/
                            if (updateDebug) cout << "\tNow down to " << unappearedEnds << "\n";
                        }
                    }
                }

                bool calculatedCostYet = false;


                for (int epPass = 0; epPass < 2; ++epPass) {
                    bool doLoop = false;
                    bool limitToOnce = false;
                    if (!epPass) {
                        doLoop = insistOnThisEnd;
                        limitToOnce = true;
                    } else {
                        if (!startPreconditionCounts[currAct] && !numericStartPreconditionCounts[currAct] && !startActionSchedule[currAct].isUndefined()) {
                            const EpsilonResolutionTimestamp & enforcedEnd = endActionSchedule[currAct];
                            if (factLayerTime - enforcedEnd >= EpsilonResolutionTimestamp::zero()) {
                                if (decrementRemainingUnsatisfiedPreconditionCounters) {
                                    endActionSchedule[currAct] = factLayerTime;
                                }
                                doLoop = true;
                                if (updateDebug) {
                                    cout << "\t\tDoing the update loop because " << factLayerTime << " >= " << enforcedEnd << endl;
                                }
                                
                            } else {
                                endActionsAtTime[enforcedEnd].push_back(make_pair(currAct,decrementRemainingUnsatisfiedPreconditionCounters));
                                if (updateDebug) {
                                    cout << "\t\tNot doing the update loop because " << factLayerTime << " < " << enforcedEnd << endl;
                                }
                                
                            }
                        }
                    }

                    if (doLoop) {
                        
                        if (!calculatedCostYet) {
                            calculatedCostYet = true;
                            
                            ActionViolationData & costData = payload->endActionCosts[currAct];
                
                            costData.canBeApplied = true;
                            
                            addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
                            addEffectCost(costData, currAct, depItr->second, payload);
                            
                        }
                        
                        if (updateDebug) {
                            if (limitToOnce) {
                                cout << "\tStarted before RPG\n";
                            } else {
                                cout << "\tStart is sufficiently earlier\n";
                            }
                        }

                        if (RPGHeuristic::printRPGAsDot) {
                            if (epPass == 0) {
                                payload->dot.addNeededEnd(factLayerTime.toDouble(), depItr->first);
                            } else {
                                payload->dot.addActionNode(factLayerTime.toDouble(), depItr->first, depItr->second);
                            }
                        }

                        //MAKEENDMDI(POtime, (limitToOnce ? payload->earliestStartOf[currAct] : 0.0), RPGBuilder::getOpMinDuration(currAct, 0), currAct);

                        if (applyPropositionalEffects(payload, currAct, Planner::E_AT_END, payload->endActionCosts[currAct], limitToOnce, nlTime/*, POtime*/)) return true;

                        if (limitToOnce) {
                            const map<int, set<int> >::const_iterator saItr = startedActions.find(currAct);
                            if (saItr != startedActions.end()) {
                                if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, saItr->second.size())) return true;
                            }
                        } else {
                            if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, -1)) return true;
                        }


                    }

                }

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));


            } else {
                if (updateDebug) {
                    if (endPreconditionCounts[currAct] == 1) {
                        cout << "\tEnd of action " << currAct << " at " << factLayerTime << " now only has " << numericEndPreconditionCounts[currAct] << " unsatisfied numeric conditions, and 1 unsatisfied literal condition:";
                        list<Literal*>::const_iterator litItr = RPGBuilder::getEndPropositionalPreconditions()[currAct].begin();
                        const list<Literal*>::const_iterator litEnd = RPGBuilder::getEndPropositionalPreconditions()[currAct].end();
                        
                        int matches = 0;
                        int slack = 0;
                        for (; litItr != litEnd; ++litItr) {
                            if (achieverDetails[(*litItr)->getStateID()].empty()) {                                
                                cout << " missing{" << *(*litItr) << "}";
                                ++matches;
                            } else {   
                                if (achieverDetails[(*litItr)->getStateID()].front().getLayer() == factLayerTime) {
                                    cout << " now{" << *(*litItr) << "@" << achieverDetails[(*litItr)->getStateID()].front().getLayer() << "}";
                                    ++slack;
                                } else if (achieverDetails[(*litItr)->getStateID()].front().getLayer() > factLayerTime) {
                                    cout << " later{" << *(*litItr) << "@" << achieverDetails[(*litItr)->getStateID()].front().getLayer() << "}";
                                    ++matches;
                                } else {
                                     cout << " past{" << *(*litItr) << "@" << achieverDetails[(*litItr)->getStateID()].front().getLayer() << "}";
                                }
                            }
                        }
                        cout.flush();
                        assert(matches <= 1);
                        assert(matches + slack >= 1);
                        cout << "\n";
                    } else {
                        cout << "\tEnd of action " << currAct << " now only has " << numericEndPreconditionCounts[currAct] << " unsatisfied numeric conditions, and " << endPreconditionCounts[currAct] << " unsatisfied literal conditions\n";
                    }
                }
            }
        }
    }

    return false;

};

bool RPGHeuristic::Private::updateActionsForNewNumericFact(Private::BuildingPayload * const payload, const int & toPropagate, const EpsilonResolutionTimestamp & factLayerTime)
{

    vector<int> & startPreconditionCounts = payload->startPreconditionCounts;
    vector<int> & endPreconditionCounts = payload->endPreconditionCounts;
    vector<int> & numericStartPreconditionCounts = payload->numericStartPreconditionCounts;
    vector<int> & numericEndPreconditionCounts = payload->numericEndPreconditionCounts;
    map<EpsilonResolutionTimestamp, list<pair<int,bool> > > & endActionsAtTime = payload->endActionsAtTime;
    vector<EpsilonResolutionTimestamp> & startActionSchedule = payload->startActionSchedule;
    vector<EpsilonResolutionTimestamp> & endActionSchedule = payload->endActionSchedule;
    vector<EpsilonResolutionTimestamp> & openEndActionSchedule = payload->openEndActionSchedule;
    const map<int, set<int> > & startedActions = payload->startedActions;

    int & unsatisfiedGoals = payload->unsatisfiedGoals;
    int & unappearedEnds = payload->unappearedEnds;
    map<int, set<int> > & insistUponEnds = payload->insistUponEnds;
    map<int, int> & forbiddenStart = payload->forbiddenStart;
    map<int, int> & forbiddenEnd = payload->forbiddenEnd;


    const EpsilonResolutionTimestamp nlTime = factLayerTime + EpsilonResolutionTimestamp::epsilon();
    const bool updateDebug = Globals::globalVerbosity & 64;

    static bool initDummy = false;
    list<pair<int, Planner::time_spec> > dummyList;
    if (!initDummy) {
        dummyList.push_back(pair<int, Planner::time_spec>(-1, Planner::E_AT_END));
        initDummy = true;
    }

    list<pair<int, Planner::time_spec> > & dependents = ((toPropagate >= 0) ? (*processedNumericPreconditionsToActions)[toPropagate] : dummyList);

    list<pair<int, Planner::time_spec> >::iterator depItr = dependents.begin();
    const list<pair<int, Planner::time_spec> >::iterator depEnd = dependents.end();

    if (updateDebug && (toPropagate >= 0)) cout << "\tAffects " << dependents.size() << " actions\n";

    for (; depItr != depEnd; ++depItr) {
        const int currAct = ((toPropagate >= 0) ? depItr->first : (-1 - toPropagate));
        const bool startAct = ((toPropagate >= 0) ? (depItr->second == Planner::E_AT_START) : false);
        assert(depItr->second != Planner::E_OVER_ALL);
        if (updateDebug) cout << "\tAffects " << currAct << ", " << (startAct ? "start" : "end") << " " << *(RPGBuilder::getInstantiatedOp(currAct)) << "\n";
        if (startAct) {

            if (!(--numericStartPreconditionCounts[currAct]) && !startPreconditionCounts[currAct] && forbiddenStart.find(currAct) == forbiddenStart.end() && nlTime < latestStartAllowed[currAct]) {
                assert(!RPGBuilder::rogueActions[currAct]);
                if (updateDebug) cout << "\tStart of action " << currAct << " is now applicable\n";

                if (startShouldBeDelayed(currAct, factLayerTime, payload)) {
                    continue;
                }

                
                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

                if (RPGHeuristic::printRPGAsDot) {
                    payload->dot.addActionNode(factLayerTime.toDouble(), depItr->first, depItr->second);
                }
                
                
                if (expandFully) earliestStartAllowed[currAct] = factLayerTime;

                startActionSchedule[currAct] = factLayerTime;
                computeDynamicCost(currAct, Planner::E_AT_START, factLayerTime);
                
                //MAKESTARTMDI(POtime, currAct);

                ActionViolationData & costData = payload->startActionCosts[currAct];
                
                costData.canBeApplied = true;
                
                addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
                addEffectCost(costData, currAct, depItr->second, payload);
                
                if (applyPropositionalEffects(payload, currAct, Planner::E_AT_START, costData, false, nlTime/*, POtime*/)) return true;

                if (applyNumericEffects(payload, currAct, Planner::E_AT_START, nlTime, -1)) return true;


                {
                    const EpsilonResolutionTimestamp endTime = factLayerTime + EpsilonResolutionTimestamp(payload->actionDurations[currAct].first,true);

                    endActionSchedule[currAct] = endTime;

                    if (!endPreconditionCounts[currAct] && !numericEndPreconditionCounts[currAct]) {
                        if (updateDebug) cout << "\t\tEnd of action can be put at fact layer sufficiently far in future (" << endTime << ")\n";

                        endActionsAtTime[endTime].push_back(make_pair(currAct,true));
                    }
                }

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

            } else {
                if (updateDebug) cout << "\tStart of action " << currAct << " now only has " << startPreconditionCounts[currAct] << " unsatisfied propositional preconditions\n";
            }
        } else {
            if (toPropagate >= 0) --numericEndPreconditionCounts[currAct];
            if (!numericEndPreconditionCounts[currAct] && !endPreconditionCounts[currAct] && forbiddenEnd.find(currAct) == forbiddenEnd.end() && nlTime < latestEndAllowed[currAct]) {
                assert(!RPGBuilder::rogueActions[currAct]);
                if (updateDebug) cout << "\tEnd of action " << currAct << " is now applicable\n";

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

                
                if (expandFully) earliestEndAllowed[currAct] = factLayerTime;

                computeDynamicCost(currAct, Planner::E_AT_END, factLayerTime);
                
                bool insistOnThisEnd = (insistUponEnds.find(currAct) != insistUponEnds.end());
                if (insistOnThisEnd) {
                    if (factLayerTime - openEndActionSchedule[currAct] >= EpsilonResolutionTimestamp::zero()) {                        
                        payload->markEndAppeared(currAct, factLayerTime);
                        if (unappearedEnds == 0 && unsatisfiedGoals == payload->fakeGoalCount) {
                            if (payload->admissibleMakespanEstimate < factLayerTime) {
                                payload->admissibleMakespanEstimate = factLayerTime;
                            }
                            
                            if (unsatisfiedGoals == 0) {
                                return true;                                
                            }
                        }                        
                        if (updateDebug) cout << "\tNow down to " << unappearedEnds << "\n";
                    } else {
                        if (updateDebug) cout << "\tOpen end cannot appear quite yet\n";
                        insistOnThisEnd = false;
                        endActionsAtTime[openEndActionSchedule[currAct]].push_back(make_pair(-1 - currAct,true));
                        /*--unappearedEnds;
                        if (unappearedEnds == 0 && unsatisfiedGoals == payload->fakeGoalCount) {
                            if (payload->admissibleMakespanEstimate < openEndActionSchedule[currAct]) {
                                payload->admissibleMakespanEstimate = openEndActionSchedule[currAct];
                            }
                                                        
                            if (unsatisfiedGoals == 0) {
                                return true;                                
                            }
                        }*/ 
                        if (updateDebug) cout << "\tNow down to " << unappearedEnds << "\n";
                    }
                }

                bool calculatedCostYet = false;


                for (int epPass = 0; epPass < 2; ++epPass) {
                    bool doLoop = false;
                    bool limitToOnce = false;
                    if (!epPass) {
                        doLoop = insistOnThisEnd;
                        limitToOnce = true;
                    } else {
                        if (!startPreconditionCounts[currAct] && !numericStartPreconditionCounts[currAct] && !startActionSchedule[currAct].isUndefined()) {
                            const EpsilonResolutionTimestamp & enforcedEnd = endActionSchedule[currAct];
                            if (factLayerTime - enforcedEnd >= EpsilonResolutionTimestamp::zero()) {
                                endActionSchedule[currAct] = factLayerTime;
                                doLoop = true;
                                if (updateDebug) {
                                    cout << "\t\tDoing the update loop because " << factLayerTime << " >= " << enforcedEnd << endl;
                                }
                            } else {
                                endActionsAtTime[enforcedEnd].push_back(make_pair(currAct,true));
                                if (updateDebug) {
                                    cout << "\t\tNot doing the update loop because " << factLayerTime << " < " << enforcedEnd << endl;
                                }
                            }
                        }
                    }

                    if (doLoop) {

                        if (!calculatedCostYet) {
                            calculatedCostYet = true;
                            
                            ActionViolationData & costData = payload->endActionCosts[currAct];
                
                            costData.canBeApplied = true;
                            
                            addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
                            addEffectCost(costData, currAct, depItr->second, payload);
                            
                        }
                        
                        if (updateDebug) {
                            if (limitToOnce) {
                                cout << "\tStarted before RPG\n";
                            } else {
                                cout << "\tStart is sufficiently earlier\n";
                            }
                        }
                        
                        if (RPGHeuristic::printRPGAsDot) {
                            if (epPass == 0) {
                                payload->dot.addNeededEnd(factLayerTime.toDouble(), depItr->first);
                            } else {
                                payload->dot.addActionNode(factLayerTime.toDouble(), depItr->first, depItr->second);
                            }
                        }
                                                                
                                                                                
                        
                        //MAKEENDMDI(POtime, (limitToOnce ? payload->earliestStartOf[currAct] : 0.0), RPGBuilder::getOpMinDuration(currAct, 0), currAct);
                        
                        if (applyPropositionalEffects(payload, currAct, Planner::E_AT_END, payload->endActionCosts[currAct], limitToOnce, nlTime/*, POtime*/)) return true;
                        
                        
                        if (limitToOnce) {
                            const map<int, set<int> >::const_iterator saItr = startedActions.find(currAct);
                            if (saItr != startedActions.end()) {
                                if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, saItr->second.size())) return true;
                            }
                        } else {
                            if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, -1)) return true;
                        }
                        


                    }

                }

                //assert(checkPreconditionsAreSatisfied(depItr->first, depItr->second, nlTime));

            } else {

                if (updateDebug) {
                    cout << "\tEnd of action " << currAct;
                    cout << " now only has " << endPreconditionCounts[currAct] << " unsatisfied preconditions\n";
                }
            }
        }
    }

    return false;

};

bool RPGHeuristic::Private::applyEndEffectNow(Private::BuildingPayload * const payload,
                                              const int & currAct, const bool & openEnd, const EpsilonResolutionTimestamp & factLayerTime,
                                              const bool & isActuallyNew)
{


    const map<int, set<int> > & startedActions = payload->startedActions;


    const EpsilonResolutionTimestamp nlTime = factLayerTime + EpsilonResolutionTimestamp::epsilon();
    const bool updateDebug = Globals::globalVerbosity & 64;

    computeDynamicCost(currAct, Planner::E_AT_END, factLayerTime);
    
    if (updateDebug) cout << "\tEnd of action " << currAct << " is now applicable\n";

    //assert(checkPreconditionsAreSatisfied(currAct, Planner::E_AT_END, nlTime));

    if (RPGHeuristic::printRPGAsDot) {
        if (openEnd) {
            payload->dot.addNeededEnd(factLayerTime.toDouble(), currAct);
        } else {
            payload->dot.addActionNode(factLayerTime.toDouble(), currAct, Planner::E_AT_END);
        }
    }
    
    if (expandFully) earliestEndAllowed[currAct] = factLayerTime;

    ActionViolationData & costData = payload->endActionCosts[currAct];

    costData.canBeApplied = true;
    
    addPreconditionCost(costData, currAct, Planner::E_AT_END, factLayerTime, payload);
    addEffectCost(costData, currAct, Planner::E_AT_END, payload);

    //MAKEENDMDI(POtime, (openEnd ? payload->earliestStartOf[currAct] : 0.0), RPGBuilder::getOpMinDuration(currAct, 0), currAct);

    if (applyPropositionalEffects(payload, currAct, Planner::E_AT_END, costData, openEnd, nlTime/*, POtime*/)) return true;


    if (openEnd) {
        const map<int, set<int> >::const_iterator saItr = startedActions.find(currAct);
        if (saItr != startedActions.end()) {
            if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, saItr->second.size())) return true;
        }
    } else {
        if (applyNumericEffects(payload, currAct, Planner::E_AT_END, nlTime, -1)) return true;
    }

    
    //assert(checkPreconditionsAreSatisfied(currAct, Planner::E_AT_END, nlTime));

    return false;

};

bool RPGHeuristic::Private::startShouldBeDelayed(const int & currAct, const EpsilonResolutionTimestamp & factLayerTime, BuildingPayload * const payload)
{
    
    static const bool shortCircuit = !TemporalAnalysis::isAnythingTILManipulated();
    
    if (shortCircuit) {
        return false;
    }
    
    static const bool debug = (Globals::globalVerbosity & 16);
    
    pair<double,double> startBounds(factLayerTime.toDouble(), TemporalAnalysis::getActionTSBounds()[currAct][0].second);
    pair<double,double> endBounds(factLayerTime.toDouble() + payload->actionDurations[currAct].first, TemporalAnalysis::getActionTSBounds()[currAct][1].second);
    
    bool keep = true;
    
    TemporalAnalysis::reboundSingleAction(currAct, payload->actionDurations, keep, startBounds, endBounds);
    
    if (!keep) {        
        if (debug) {
            cout << COLOUR_light_red << "Not actually getting start of " << *(RPGBuilder::getInstantiatedOp(currAct)) << " as it can't appear here due to temporal constraints\n" << COLOUR_default;
        }
        return true;
    }
    
    EpsilonResolutionTimestamp rounded(startBounds.first, true);
    if (rounded <= factLayerTime) {
        return false;
    }
        
    payload->factLayers[rounded].startDelayedUntilNow.insert(currAct);
    if (debug) {
        cout << COLOUR_light_red << "Delayed start of " << *(RPGBuilder::getInstantiatedOp(currAct)) << " to " << rounded << " rather than " << factLayerTime << " due to temporal constraints\n" << COLOUR_default;
    }
    
    return true;
}

bool RPGHeuristic::Private::revisitActs(BuildingPayload * payload, const EpsilonResolutionTimestamp & factLayerTime, const list<pair<int, Planner::time_spec> > & actsToVisit) {
    
    if (actsToVisit.empty()) {
        return false;
    }
    
    EpsilonResolutionTimestamp nlTime(factLayerTime);
    ++nlTime;
    
    list<pair<int,Planner::time_spec> >::const_iterator depItr = actsToVisit.begin();
    const list<pair<int, Planner::time_spec> >::const_iterator depEnd = actsToVisit.end();
    
    for (; depItr != depEnd; ++depItr) {
        const int currAct = depItr->first;
        if (depItr->second == Planner::E_AT_START) {
            
            ActionViolationData & costData = payload->startActionCosts[currAct];
            
            costData.canBeApplied = true;
            
            addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
            addEffectCost(costData, currAct, depItr->second, payload);
            
            

            //MAKESTARTMDI(POtime, currAct);

            if (applyPropositionalEffects(payload, currAct, Planner::E_AT_START, costData, false, nlTime/*, POtime*/)) return true;

            {
                static pair<EpsilonResolutionTimestamp, list<pair<int,bool> > > defaultEntry(EpsilonResolutionTimestamp::undefined(), list<pair<int,bool> >());
                
                defaultEntry.first = factLayerTime + EpsilonResolutionTimestamp(payload->actionDurations[currAct].first,true);
             
                if (!payload->endPreconditionCounts[currAct] && !payload->numericEndPreconditionCounts[currAct]) {
                    payload->endActionsAtTime.insert(defaultEntry).first->second.push_back(make_pair(currAct, false) );
                }
            }

            
        } else if (depItr->second == Planner::E_AT_END) {
                        
            bool insistOnThisEnd = (payload->insistUponEnds.find(currAct) != payload->insistUponEnds.end());
            bool calculatedCostYet = false;
            
            for (int epPass = 0; epPass < 2; ++epPass) {
                bool doLoop = false;
                bool limitToOnce = false;
                
                if (!epPass) {
                    doLoop = insistOnThisEnd;
                    limitToOnce = true;
                } else {
                    if (!payload->startPreconditionCounts[currAct] && !payload->numericStartPreconditionCounts[currAct] && !payload->startActionSchedule[currAct].isUndefined()) {
                        const EpsilonResolutionTimestamp & enforcedEnd = payload->endActionSchedule[currAct];
                        if (factLayerTime - enforcedEnd >= EpsilonResolutionTimestamp::zero()) {
                            doLoop = true;
                        }
                    }
                }

                if (doLoop) {
                    
                    if (!calculatedCostYet) {
                        calculatedCostYet = true;
                        
                        ActionViolationData & costData = payload->endActionCosts[currAct];
            
                        costData.canBeApplied = true;
                        
                        addPreconditionCost(costData, currAct, depItr->second, factLayerTime, payload);
                        addEffectCost(costData, currAct, depItr->second, payload);
                        
                    }
                    
                    //MAKEENDMDI(POtime, (limitToOnce ? payload->earliestStartOf[currAct] : 0.0), RPGBuilder::getOpMinDuration(currAct, 0), currAct);

                    if (applyPropositionalEffects(payload, currAct, Planner::E_AT_END, payload->endActionCosts[currAct], limitToOnce, nlTime/*, POtime*/)) return true;
                    
                }

            }
        } else {
            assert(depItr->second == Planner::E_AT);
            
            
            ActionViolationData & costData = payload->tilCosts[depItr->first];
                    
            costData.canBeApplied = true;
            
            addPreconditionCost(costData, depItr->first, Planner::E_AT, EpsilonResolutionTimestamp::undefined(), payload);
            addEffectCost(costData, depItr->first, Planner::E_AT, payload);

            if (applyPropositionalEffects(payload, depItr->first, depItr->second, costData, false, nlTime/*, POtime*/)) return true;

            
        }
            
    }
    
    return false;
    
}

bool RPGHeuristic::Private::updatePreferencesForFact(BuildingPayload * const payload,
                                                     const int& fID, const bool& isALiteral, const bool & polarity,
                                                     const bool & isActuallyNew,
                                                     const Planner::EpsilonResolutionTimestamp & factLayerTime)
{

    if (!isActuallyNew) {
        // TODO: is this right?
        return false;
    }
    
    assert(isALiteral ? (polarity ? (size_t) fID < preconditionsToPrefs->size() : (size_t) fID < negativePreconditionsToPrefs->size())
                      : (polarity && (size_t) fID < numericPreconditionsToPrefs->size()));
    
    const list<LiteralCellDependency<pair<int,bool> > > & dependents
        = (isALiteral ? (polarity ? (*preconditionsToPrefs)[fID] : (*negativePreconditionsToPrefs)[fID])
                      : (*numericPreconditionsToPrefs)[fID]
          );

    list<pair<int,int> > nowCostFreeToAdd;
    
    set<pair<int, Planner::time_spec> > actsVisited;
    list<pair<int, Planner::time_spec> > actsToVisit;
    
    static const int taskPrefCount = RPGBuilder::getTaskPrefCount();
    
    if (evaluateDebug) {
        cout << "\tNumber of preferences depending on this: " << dependents.size() << endl;
    }
    
    {
        list<LiteralCellDependency<pair<int,bool> > >::const_iterator depItr = dependents.begin();
        const list<LiteralCellDependency<pair<int,bool> > >::const_iterator depEnd = dependents.end();
        
        for (; depItr != depEnd; ++depItr) {
            
            NNF_Flat* const toUpdate = payload->initialUnsatisfiedPreferenceConditions[depItr->dest.first][depItr->dest.second ? 1 : 0];
            
            if (!toUpdate) continue;
            
            if (toUpdate->isSatisfied()) continue;
            
            if (depItr->dest.first < taskPrefCount) {
                
                if (payload->optimisticPrefStatus[depItr->dest.first] == AutomatonPosition::unreachable) {
                    continue;
                }
                
                const RPGBuilder::Constraint & currPref = RPGBuilder::getPreferences()[depItr->dest.first];
                if (currPref.cons == VAL::E_WITHIN && currPref.deadline < factLayerTime.toDouble()) {
                    if (Globals::globalVerbosity & 32768) {
                        cout << "\t" << COLOUR_light_green;
                        
                        if (isALiteral) {
                            cout << "Literal fact ";
                            if (!polarity) cout << "¬";
                            cout << *(RPGBuilder::getLiteral(fID)) << " ";
                        } else {
                            cout << "Numeric fact " << RPGBuilder::getNumericPreTable()[fID];
                        }
                        
                        cout << "was relevant to within preference " << currPref.name << ":" << depItr->dest.first << ", but " << factLayerTime << " is too late for " << currPref.deadline << COLOUR_default << endl;
                    }
                                

                    continue;
                }
            }
            
            if (Globals::globalVerbosity & 32768) {
                cout << "\t" << COLOUR_light_green;
                
                if (isALiteral) {
                    cout << "Literal fact ";
                    if (!polarity) cout << "¬";
                    cout << *(RPGBuilder::getLiteral(fID)) << " ";
                } else {
                    cout << "Numeric fact " << RPGBuilder::getNumericPreTable()[fID];
                }
                
                cout << "is relevant to preference " << RPGBuilder::getPreferences()[depItr->dest.first].name << ":" << depItr->dest.first << COLOUR_default << endl;
            }
                        
            
            toUpdate->satisfy(depItr->index);
            
            if (depItr->dest.first < taskPrefCount) {
                
                if (toUpdate->isSatisfied()) {
                    
                    if (Globals::globalVerbosity & 32768) {
                        if (depItr->dest.second) {
                            cout << "\t\t" << COLOUR_light_red << "Preference trigger now satisfied\n" << COLOUR_default;
                        } else {
                            cout << "\t\t" << COLOUR_light_red << "Preference goal now satisfied\n" << COLOUR_default;
                        }
                    }
                    
                    payload->preferencePartTrueAtLayer[depItr->dest.first][depItr->dest.second ? 1 : 0] = factLayerTime;
                    
                    const AutomatonPosition::Position oldPosn = payload->optimisticPrefStatus[depItr->dest.first];
                                
                    PreferenceHandler::updateCostsAndPreferenceStatus(payload->startState, depItr->dest, payload->optimisticPrefStatus,
                                                                       payload->prefCostOfAddingFact, payload->prefCostOfChangingNumberB,
                                                                       nowCostFreeToAdd);
                    
                    const AutomatonPosition::Position newPosn = payload->optimisticPrefStatus[depItr->dest.first];
                    
                    if (Globals::globalVerbosity & 32768) {
                        cout << "\t\t" << COLOUR_light_red << "Preference status was " << positionName[oldPosn] << ", now " << positionName[newPosn] << COLOUR_default << endl;
                    }
                    
                    if (oldPosn == AutomatonPosition::unsatisfied || oldPosn == AutomatonPosition::triggered) {
                        
                        if (isSatisfied(newPosn)) {
                            payload->rpgGoalPrefViolation -= RPGBuilder::getPreferences()[depItr->dest.first].cost;
                                         
                            if (Globals::globalVerbosity & 32768) {
                                cout << "\t\t" << COLOUR_light_red << "Subtracted " << RPGBuilder::getPreferences()[depItr->dest.first].cost << " from cost of reaching goal" << COLOUR_default << endl;
                            }   
                            if (RPGBuilder::getMetric()) {    
                                if (RPGBuilder::getMetric()->minimise) {
                                    if (payload->rpgGoalPrefViolation < 0.0000001) {
                                        payload->rpgGoalPrefViolation = 0.0;
                                    }
                                } else {
                                    if (payload->rpgGoalPrefViolation > -0.0000001) {
                                        payload->rpgGoalPrefViolation = 0.0;
                                    }
                                }
                            }
                        }
                    }

                }
                
            } else {
                
                if (toUpdate->isSatisfied()) {
                    if (Globals::globalVerbosity & 32768) {
                        cout << "\t\t" << COLOUR_light_blue << "Precondition preference now satisfied, at time " << factLayerTime << "\n" << COLOUR_default;
                    }
                    payload->preferencePartTrueAtLayer[depItr->dest.first][depItr->dest.second ? 1 : 0] = factLayerTime;
                    
                    const pair<int,Planner::time_spec> & currAct = RPGBuilder::getPreferences()[depItr->dest.first].attachedToOperator;
                    
                    if (Globals::globalVerbosity & 32768) {
                        cout << "Applies to action " << *(RPGBuilder::getInstantiatedOp(currAct.first));
                        if (currAct.second == Planner::E_AT_END) {
                            cout << ", end\n";
                        } else {
                            cout << ", start\n";
                        }
                    }
                    
                    ActionViolationData & actCost = (currAct.second == Planner::E_AT_START ? payload->startActionCosts[currAct.first] : payload->endActionCosts[currAct.first]);
                    
                    bool canAppearHere = actCost.canBeApplied;
                                    
                    if (actCost.canBeApplied) {
                        
                        if (currAct.second == Planner::E_AT_START) {
                            
                            canAppearHere = ((!payload->startPreconditionCounts[currAct.first] && !payload->numericStartPreconditionCounts[currAct.first])
                                               && payload->forbiddenStart.find(currAct.first) == payload->forbiddenStart.end()
                                               && factLayerTime < latestStartAllowed[currAct.first]);
                            
                        } else if (currAct.second == Planner::E_AT_END) {
                            
                            canAppearHere = ((!payload->endPreconditionCounts[currAct.first] && !payload->numericEndPreconditionCounts[currAct.first])
                                               && payload->forbiddenEnd.find(currAct.first) == payload->forbiddenEnd.end()
                                               && factLayerTime < latestEndAllowed[currAct.first]);
                            
                        } else {
                            cerr << "Fatal internal error: precondition preference not at the start or end of an action\n";
                            exit(1);
                        }
                        
                    }
                    
                    if (canAppearHere) {
                        
                        
                        
                        const set<int>::iterator pmvItr = actCost.preconditionsMeanViolating.find(depItr->dest.first);
                        assert(pmvItr != actCost.preconditionsMeanViolating.end());
                        
                        const double costDelta = RPGBuilder::getPreferences()[depItr->dest.first].cost;
                        
                        actCost.preconditionsMeanViolating.erase(pmvItr);
                        actCost.overallViolations.erase(depItr->dest.first);
                        actCost.overallViolationCost -= costDelta;
                        actCost.precViolationCost -= costDelta;

                        if (actsVisited.insert(currAct).second) {
                            if (Globals::globalVerbosity & 32768) {
                                cout << "\t\t" << COLOUR_yellow << " - Revisiting " << *(RPGBuilder::getInstantiatedOp(currAct.first));
                                if (currAct.second == Planner::E_AT_END) {
                                    cout << ", end";                                
                                } else {
                                    cout << ", start";
                                }
                                cout << ", as it's now " << costDelta << " cheaper\n" << COLOUR_default;
                            }
                            actsToVisit.push_back(currAct);
                        }
                        
                        
                    }
                    
                    payload->preferencePartsToSatisfyBeforeAction[currAct].push_back(depItr->dest);                    
                    
                }
                
            }
        }
        
    }
    
    EpsilonResolutionTimestamp nlTime = factLayerTime;
    ++nlTime;
    
    if (!nowCostFreeToAdd.empty()) {
        list<pair<int,int> > & toUpdate = payload->factLayers[nlTime].preferencePairedWithFactNowFreeToAdd;
        
        toUpdate.insert(toUpdate.end(), nowCostFreeToAdd.begin(), nowCostFreeToAdd.end());
    }
        
    return revisitActs(payload, factLayerTime, actsToVisit);
    
}

bool RPGHeuristic::Private::updateForPreferencesInBetterPositions(BuildingPayload * const payload,
                                                                  const list<pair<int, int> > & preferencePairedWithFactNowFreeToAdd,
                                                                  const EpsilonResolutionTimestamp & factLayerTime)
{
    set<pair<int, Planner::time_spec> > actsVisited;
    list<pair<int, Planner::time_spec> > actsToVisit;

    
    list<pair<int, int> >::const_iterator cfItr = preferencePairedWithFactNowFreeToAdd.begin();
    const list<pair<int,int> >::const_iterator cfEnd  =preferencePairedWithFactNowFreeToAdd.end();
    
    for (; cfItr != cfEnd; ++cfItr) {        
        const map<int, set<pair<int, Planner::time_spec> > >::iterator reduceCostItr = payload->preferenceWouldBeViolatedByAction.find(cfItr->first);
        if (reduceCostItr == payload->preferenceWouldBeViolatedByAction.end()) {
            if (Globals::globalVerbosity & 32768) {
                cout << COLOUR_light_blue "\tNo actions have costs associated with " << RPGBuilder::getPreferences()[cfItr->first].name << ":" << cfItr->first << COLOUR_default << endl;
            }            
            continue;
        }
        
        const double costDelta = prefCosts[cfItr->first];
        
        set<pair<int, Planner::time_spec> >::const_iterator actItr = reduceCostItr->second.begin();
        const set<pair<int, Planner::time_spec> >::const_iterator actEnd = reduceCostItr->second.end();
        
        for (; actItr != actEnd; ++actItr) {
            const int currAct = actItr->first;
            
            ActionViolationData & actCost = (actItr->second == Planner::E_AT
                                              ? (payload->tilCosts[currAct])                                              
                                              : (actItr->second == Planner::E_AT_START ? payload->startActionCosts[currAct] : payload->endActionCosts[currAct]));
            
            actCost.effectsMeanViolating.erase(cfItr->first);
            
            if (cfItr->second != -1) {
                payload->preferencePartsToSatisfyBeforeAction[*actItr].push_back(make_pair(cfItr->first, (cfItr->second == 1)));
            }
            
            bool canAppearHere = actCost.canBeApplied;
                                    
            if (actCost.canBeApplied) {
                
                if (actItr->second == Planner::E_AT_START) {
                    
                    canAppearHere = ((!payload->startPreconditionCounts[currAct] && !payload->numericStartPreconditionCounts[currAct])
                                       && payload->forbiddenStart.find(currAct) == payload->forbiddenStart.end()
                                       && factLayerTime < latestStartAllowed[currAct]);
                    
                } else if (actItr->second == Planner::E_AT_END) {
                    
                    canAppearHere = ((!payload->endPreconditionCounts[currAct] && !payload->numericEndPreconditionCounts[currAct])
                                       && payload->forbiddenEnd.find(currAct) == payload->forbiddenEnd.end()
                                       && factLayerTime < latestEndAllowed[currAct]);
                    
                } else if (actItr->second == Planner::E_AT) {
                    if (currAct < payload->startState.nextTIL) {
                        canAppearHere = false;
                    } else {                    
                        if (RPGBuilder::modifiedRPG) {
                            // TIL only appears once, in the right place
                            canAppearHere = false;                        
                        } else {                    
                            const EpsilonResolutionTimestamp tilTS = EpsilonResolutionTimestamp(tilTimes[currAct], false) - payload->stateTS;
                            if (tilTS <= factLayerTime) { // if the latest point at which the TIL can appear is before now
                                canAppearHere = false;
                            }
                        }
                    }
                }
                
            }
            
            if (canAppearHere) {
                                
                if (actCost.preconditionsMeanViolating.find(cfItr->first) == actCost.preconditionsMeanViolating.end()) {                                
                    actCost.overallViolations.erase(cfItr->first);
                    actCost.overallViolationCost -= costDelta;
                    actCost.effViolationCost -= costDelta;

                    if (Globals::globalVerbosity & 32768) {
                        cout << "Reducing the recorded cost of ";
                        ActionSegment::printIntTSPair(*actItr);                        
                        cout << " to " << actCost.overallViolationCost << endl;
                    }
                    
                    
                    if (actsVisited.insert(*actItr).second) {
                        if (Globals::globalVerbosity & 32768) {
                            cout << "\t\t" << COLOUR_yellow << " - Revisiting ";
                            ActionSegment::printIntTSPair(*actItr);                        
                            cout << ", as it's now " << costDelta << " cheaper\n" << COLOUR_default;
                        }
                        actsToVisit.push_back(*actItr);
                    }

                } else {
                    if (Globals::globalVerbosity & 32768) {
                        assert(actItr->second != Planner::E_AT);
                        cout <<  "\t\tApplying ";
                        ActionSegment::printIntTSPair(*actItr);
                        cout << " would still violate the preference, due to its preconditions\n";
                    }
                                    
                }
            } else {
                if (Globals::globalVerbosity & 32768) {
                    cout <<  "\t\tWhen ";
                    ActionSegment::printIntTSPair(*actItr);
                    cout << " becomes applicable, it will no longer violate the preference\n";
                }
                
            }
        }
        
    }
    
    return revisitActs(payload, factLayerTime, actsToVisit);
}

#ifdef POPF3ANALYSIS

void printVec(const vector<double> & costVec) {
    const int cSize = costVec.size();
    
    cout << "[";
    for (int i = 0; i < cSize; ++i) {
        if (i) cout << ", ";
        if (costVec[i] == DBL_MAX) {
            cout << "inf";
        } else if (costVec[i] == -DBL_MAX) {
            cout << "-inf";
        } else {
            cout << costVec[i];
        }
    }
    cout << "]";
}

void RPGHeuristic::Private::updateAdditiveCosts(BuildingPayload * const payload, const int & ci, const EpsilonResolutionTimestamp & deadline, const int & updateForGoal, double & costToUpdate)
{

    if (updateForGoal == -1) {
        return;
    }

    const map<int, list<int> > & igc = NumericAnalysis::getIndependentGoalCosts()[updateForGoal];
    
    if (igc.empty()) {
        return;
    }

    const map<int, list<int> >::const_iterator igcItr = igc.find(ci);
    
    if (igcItr == igc.end()) {
        return;
    }

    static const int localDebug = 0;
    
    static const string UAC("\tupdateAdditiveCosts(): ");

    // if we get this far, we have independent goal costs - iterate over achievers,
    // finding which exist, and add the smallest of those to the additive cost
    
    double costUpdate = 0.0;
    bool achieverYet = false;
    
    list<int>::const_iterator achievedByItr = igcItr->second.begin();
    const list<int>::const_iterator achievedByEnd = igcItr->second.end();

    
    for (double localCost; achievedByItr != achievedByEnd; ++achievedByItr) {
        if (payload->startActionSchedule[*achievedByItr].isUndefined()) {
            
            // don't use an achiever if its start hasn't appeared yet
            continue;
        }
        
        if (!RPGBuilder::getRPGDEs(*achievedByItr).empty()
            && payload->endActionSchedule[*achievedByItr].isUndefined()
            && payload->openEndActionSchedule[*achievedByItr].isUndefined()) {
            
            // for durative actions, don't use an achiever if its end hasn't appeared yet
            continue;
        }
        
        if (payload->startActionSchedule[*achievedByItr] > deadline) {
            // don't use achievers that start too late
            continue;
        }
        
        
        
        {
            const list<Literal*> & startAdds = RPGBuilder::getStartPropositionAdds()[*achievedByItr];
            list<Literal*>::const_iterator addItr = startAdds.begin();
            const  list<Literal*>::const_iterator addEnd = startAdds.end();
            for (; addItr != addEnd; ++addItr) {
                if (*addItr == literalGoalVector[updateForGoal]) {
                    break;
                }
            }
            
            if (addItr == addEnd) {
                // here, it means it wasn't added by the start of the action
                
                if (payload->endActionSchedule[*achievedByItr] <= deadline) {
                    
                } else {
                    
                    if (payload->startState.startedActions.find(*achievedByItr) == payload->startState.startedActions.end() 
                        || payload->openEndActionSchedule[*achievedByItr] > deadline) {
                        
                        // don't use achievers that end too late
                        
                        continue;
                    }
                }
                                        
            }
        }
        
        
        localCost = startEffectsOnResourceLimits[*achievedByItr][ci]
                    + endEffectsOnResourceLimits[*achievedByItr][ci]
                    + dynamicStartEffectsOnResourceLimits[*achievedByItr][ci]
                    + dynamicEndEffectsOnResourceLimits[*achievedByItr][ci];
        
        if (localCost == 0.0) {
            // have a cost-free achiever - assume we'd use it
            return;
        }
        
        if (achieverYet) {
            if (localCost > 0.0) {
                if (localCost < costUpdate) {
                    costUpdate = localCost;
                }
            } else {
                if (localCost > costUpdate) {
                    costUpdate = localCost;
                }                                
            } 
        
        } else {
            costUpdate = localCost;
            achieverYet = true;
        } 
    
    }
    
    if (localDebug) {
        cout << COLOUR_yellow << UAC << "- Additive cost of goal " << *(literalGoalVector[updateForGoal]) << " on limit " << ci << " = " << costUpdate << COLOUR_default << endl;
    }
    
    costToUpdate += costUpdate;
}

void RPGHeuristic::Private::calculateGoalCost(BuildingPayload * const payload, double * calculatedCost)
{
    
    static const int localDebug = (Globals::globalVerbosity & 16 ? 1 : 0);
    
    static const string CGC("calculateGoalCost(): ");
    
    if (!calculatedCost) {
        if (!payload->tooExpensive) {
            if (localDebug & 1) {
                cout << COLOUR_light_green << CGC << "Cost threshold known to be okay\n" << COLOUR_default;
            }
            return;
        }
        
        if (!NumericAnalysis::areThereAnyIndependentGoalCosts() && RPGBuilder::getPreferences().empty()) {
            if (localDebug & 1) {
                cout << COLOUR_light_green << CGC << "No independent goal costs, so costs known to be okay\n" << COLOUR_default;
            }
            
            payload->tooExpensive = false;
            return;
        }
    }
    
    if (localDebug) {
        cout << COLOUR_light_magenta << CGC << COLOUR_default << endl;
    }
    
    
    const int costCount = currentCosts.size();
        
    assert(costCount); // or there shouldn't be independent goal costs
    
    const bool addTheMaxCosts = RPGHeuristic::addTheMaxCosts;
    
    vector<double> maxCosts(costCount, 0.0);
    vector<double> additiveCosts(costCount, 0.0);
    vector<int> mostExpensiveGID(costCount, -1);
    
    const int lgc = literalGoalVector.size();
    
    int fID;

    const vector<NumericAnalysis::NumericLimitDescriptor> & limits = NumericAnalysis::getGoalNumericUsageLimits();

    
    const list<double> & literalGoalDeadlines = RPGBuilder::getLiteralGoalDeadlines();
    list<double>::const_iterator deadlineItr = literalGoalDeadlines.begin();
    
    
    for (int gID = 0; gID < lgc; ++gID, ++deadlineItr) {
        
        if (!literalGoalVector[gID]) {
            // static goal
            continue;
        }
        
        fID = literalGoalVector[gID]->getStateID();

        if (payload->startState.first.find(fID) != payload->startState.first.end()) {
            if (localDebug & 2) {
                cout << COLOUR_light_blue << CGC << "goal fact" << *(literalGoalVector[gID]) << " is already true" << endl << COLOUR_default;
            }
            // true in the state being evaluated
            continue;
        }
        

                
                
        
        const list<CostedAchieverDetails> & achievers = achieverDetails[fID];        
        assert(!achievers.empty());
            
        list<CostedAchieverDetails>::const_reverse_iterator accItr = achievers.rbegin();
        const list<CostedAchieverDetails>::const_reverse_iterator accEnd = achievers.rend();
        
        EpsilonResolutionTimestamp roundedDeadline(EpsilonResolutionTimestamp::infinite());
        if (*deadlineItr != DBL_MAX) {
            roundedDeadline = EpsilonResolutionTimestamp(*deadlineItr,true);
        }
        
        for (; accItr != accEnd && accItr->getLayer() > roundedDeadline; ++accItr) ;
        
        if (accItr == accEnd) {
            // in this case, we don't have an early enough achiever, give up for now
            return;
        }
                    
        
        const CostedAchieverDetails & achiever = *accItr;

        
        
        for (int ci = 0; ci < costCount; ++ci) {
            
            if (limits[ci].optimisationLimit && addTheMaxCosts) {
                if (achiever.costs[ci] > 0.0) {
                    if (mostExpensiveGID[ci] == -1) {                        
                        maxCosts[ci] = currentCosts[ci];   
                        mostExpensiveGID[ci] = INT_MAX;
                    }
                    
                    maxCosts[ci] += achiever.costs[ci] - currentCosts[ci];
                    
                    if (localDebug & 2) {
                        cout << COLOUR_light_blue << CGC << "goal fact" << *(literalGoalVector[gID]) << ": is ";
                        cout << " adding to the costs on ";
                        cout << ci << ", " << achiever.costs[ci] - currentCosts[ci] << "; total is now " << maxCosts[ci] << endl << COLOUR_default;
                    }
                    
                } else if (achiever.costs[ci] < 0.0) {
                    if (mostExpensiveGID[ci] == -1) {                        
                        maxCosts[ci] = currentCosts[ci];   
                        mostExpensiveGID[ci] = INT_MAX;
                    }
                    
                    maxCosts[ci] += (achiever.costs[ci] - currentCosts[ci]);
                    if (localDebug & 2) {
                        cout << COLOUR_light_blue << CGC << "goal fact" << *(literalGoalVector[gID]) << ": is ";
                        cout << " adding to the costs on ";
                        cout << ci << ", " << achiever.costs[ci] - currentCosts[ci] << "; total is now " << maxCosts[ci] << endl << COLOUR_default;
                    }
                   
                }
            } else {
            
                if (achiever.costs[ci] > 0.0) {
                    if (mostExpensiveGID[ci] == -1 || maxCosts[ci] < achiever.costs[ci]) {
                        if (localDebug & 2) {
                            cout << COLOUR_light_blue << CGC << "goal fact" << *(literalGoalVector[gID]) << ": is ";
                            if (mostExpensiveGID[ci] == -1) {
                                cout << " the first max on ";
                            } else {
                                cout << " the new max on ";
                            }                        
                            cout << ci << ", " << achiever.costs[ci] << endl << COLOUR_default;
                        }
                        updateAdditiveCosts(payload, ci, roundedDeadline, mostExpensiveGID[ci], additiveCosts[ci]);
                        maxCosts[ci] = achiever.costs[ci];
                        mostExpensiveGID[ci] = gID;
                        
                        
                    } else {
                        updateAdditiveCosts(payload, ci, roundedDeadline, gID, additiveCosts[ci]);
                    }
                } else if (achiever.costs[ci] < 0.0) {
                    if (mostExpensiveGID[ci] == -1 || maxCosts[ci] > achiever.costs[ci]) {
                        if (localDebug & 2) {
                            cout << COLOUR_light_blue << CGC << "goal fact" << *(literalGoalVector[gID]) << ": is ";
                            if (mostExpensiveGID[ci] == -1) {
                                cout << " the first max on ";
                            } else {
                                cout << " the new max on ";
                            }                        
                            cout << ci << ", " << achiever.costs[ci] << endl << COLOUR_default;
                        }
                                            
                                            
                        updateAdditiveCosts(payload, ci, roundedDeadline, mostExpensiveGID[ci], additiveCosts[ci]);
                        maxCosts[ci] = achiever.costs[ci];
                        mostExpensiveGID[ci] = gID;
                        
                    } else {
                        updateAdditiveCosts(payload, ci, roundedDeadline, gID, additiveCosts[ci]);
                    }
                }
            }
        }
        
    }

    
    double localCost, limitToUse;
    
    for (int ci = 0; ci < costCount; ++ci) {

        localCost = additiveCosts[ci] + maxCosts[ci];

        limitToUse = limits[ci].limit;
        
        if (limits[ci].optimisationLimit && (Globals::bestSolutionQuality > -DBL_MAX || calculatedCost)) {
            if (Globals::bestSolutionQuality + 0.001 > limitToUse) {
                limitToUse = Globals::bestSolutionQuality + 0.001;
            }
            if (localDebug & 1) {
                cout << COLOUR_light_blue << CGC << "Optimisation limit, direct effect on limit is " << localCost << ", split into " << additiveCosts[ci] << " additive costs, and " << maxCosts[ci] << " max costs\n";                
            }
            
            if (RPGBuilder::getMetric()->minimise) {
                localCost -= RPGBuilder::getMetric()->constant;
                if (metricWeightOfMakespan != 0.0) {
                    localCost -= payload->admissibleMakespanEstimate.toDouble() * metricWeightOfMakespan;
                }
            } else {
                localCost += RPGBuilder::getMetric()->constant;
                if (metricWeightOfMakespan != 0.0) {
                    localCost += payload->admissibleMakespanEstimate.toDouble() * metricWeightOfMakespan;
                }
            }
            
            if (localDebug & 1) {
                if (RPGBuilder::getMetric()->constant != 0.0) {
                    cout << ", constant of " << RPGBuilder::getMetric()->constant;
                }
                if (metricWeightOfMakespan != 0.0) {
                    cout << ", makespan of " << payload->admissibleMakespanEstimate;
                    if (metricWeightOfMakespan != 1.0) {
                        cout << ", weight " << metricWeightOfMakespan;
                    }
                }
            }
            
            if (!RPGBuilder::getPreferences().empty()) {
                if (RPGBuilder::getMetric()->minimise) {
                    localCost -= PreferenceHandler::getCurrentCost(payload->startState.prefPreconditionViolations, payload->optimisticPrefStatus);
                } else {
                    localCost += PreferenceHandler::getCurrentCost(payload->startState.prefPreconditionViolations, payload->optimisticPrefStatus);
                }
                if (localDebug & 1) {
                    cout << ", with preferences is " << localCost << ", " << PreferenceHandler::getCurrentViolations(payload->optimisticPrefStatus) << endl;
                }
            }
            if (localDebug & 1) {
                cout << COLOUR_default << endl;
            }
            //localCost += payload->withinCosts;         
                        
            if (calculatedCost) {
                if (RPGBuilder::getMetric()->minimise) {
                    *calculatedCost = (localCost == 0.0 ? 0.0 : -localCost);
                } else {
                    *calculatedCost = localCost;
                }
            }
        }

//         if (localCost == 0.0) {
//             if (localDebug & 1) {
//                 cout << COLOUR_light_blue << CGC << "final effect on limit " << ci << " is zero: ignoring it\n" << COLOUR_default;
//             }
//             
//             // can use none of this resource
//             continue;
//         }
//         

        if (limitToUse > -DBL_MAX) {
                                                                                                    
            if (localCost > 0.0) {
                switch (limits[ci].op) {
                    case E_GREATER:
                    {
                        if (localCost <= limitToUse) {
                            if (localDebug & 1) {
                                cout << COLOUR_light_red << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so too expensive\n" << COLOUR_default;
                            }
                            
                            return;
                        }
                        break;
                    }
                    case E_GREATEQ:
                    {
                        if (localCost < limitToUse) {
                            if (localDebug & 1) {
                                cout << COLOUR_light_red << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so too expensive\n" << COLOUR_default;
                            }
                            
                            return;
                        }
                        break;                    
                    }                                
                    default:
                    {
                        cerr << "Internal error: limits should be defined in terms of > or >=\n";
                        exit(1);
                    }
                }
                if (localDebug & 1) {
                    cout << COLOUR_light_green << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so okay\n" << COLOUR_default;
                }
                                                            
            } else if (localCost < 0.0) {
                switch (limits[ci].op) {
                    case E_GREATER:
                    {
                        if (localCost <= limitToUse) {
                            if (localDebug & 1) {
                                cout << COLOUR_light_red << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so too expensive\n" << COLOUR_default;
                            }
                            
                            return;
                        }
                        break;
                    }
                    case E_GREATEQ:
                    {
                        if (localCost < limitToUse) {
                            if (localDebug & 1) {
                                cout << COLOUR_light_red << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so too expensive\n" << COLOUR_default;
                            }
                            
                            return;
                        }
                        break;                    
                    }                                
                    default:
                    {
                        cerr << "Internal error: limits should be defined in terms of > or >=\n";
                        exit(1);
                    }
                }
                if (localDebug & 1) {
                    cout << COLOUR_light_green << CGC << "final effect on limit " << ci << " is " << localCost << ", limit is " << limitToUse << ", so okay\n" << COLOUR_default;
                }
            } 
        }
    
        
    }

    
    // if the for loop didn't 'return' us out of here, the cost limits are okay
    
    if (localDebug & 1) {
        cout << COLOUR_light_red << CGC << "success: RP is cheap enough\n" << COLOUR_default;
    }
                                    
    payload->tooExpensive = false;
    
}
#endif


void RPGHeuristic::findApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions)
{
    d->findApplicableActions(theState, stateTime, applicableActions);
}

bool negativesAreOkay(const list<Literal*> & checkFor, const StateFacts & checkIn)
{

    list<Literal*>::const_iterator cfItr = checkFor.begin();
    const list<Literal*>::const_iterator cfEnd = checkFor.end();

    for (; cfItr != cfEnd; ++cfItr) {
        if (checkIn.find((*cfItr)->getStateID()) != checkIn.end()) return false;
    }

    return true;
}

void RPGHeuristic::Private::findApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions)
{

    static const bool debug = (Globals::globalVerbosity & 16);


    static const set<int> emptyIntSet;


    vector<int> startPreconditionCounts(*initialUnsatisfiedProcessedStartPreconditions);
    vector<int> endPreconditionCounts(*initialUnsatisfiedEndPreconditions);

    list<ActionSegment> toFilter;

    for (int pass = 0; pass < 2; ++pass) {
        list<pair<int, Planner::time_spec> > & dependents = (pass ? *onlyNumericPreconditionActions : *preconditionlessActions);

        if (debug) {
            if (pass) {
                cout << "Considering the " << dependents.size() << " actions with only numeric preconditions\n";
            } else {
                cout << "Considering the " << dependents.size() << " propositionally preconditionless actions\n";
            }
        }


        list<pair<int, Planner::time_spec> >::iterator depItr = dependents.begin();
        const list<pair<int, Planner::time_spec> >::iterator depEnd = dependents.end();

        for (; depItr != depEnd; ++depItr) {
            const int currAct = depItr->first;
            const Planner::time_spec startOrEnd = depItr->second;

            if (!negativesAreOkay((startOrEnd == Planner::E_AT_START
                                   ? RPGBuilder::getProcessedStartNegativePropositionalPreconditions()[currAct]
                                   : RPGBuilder::getEndNegativePropositionalPreconditions()[currAct]) ,
                                  theState.first)) {
                continue;
            }

            ActionSegment candidate(getOp(currAct), startOrEnd, -1, emptyIntSet);
            const bool nonMutex = RPGBuilder::stepNeedsToHaveFinished(candidate, theState, candidate.needToFinish);

            if (nonMutex) {
                toFilter.push_back(candidate);
                if (debug) {
                    cout << *(getOp(currAct));
                    if (startOrEnd == Planner::E_AT_START) {
                        cout << " start is a propositional candidate\n";
                    } else {
                        cout << " end is a propositional candidate\n";
                    }
                }
            } else {
                if (debug) {
                    cout << *(getOp(currAct));
                    if (startOrEnd == Planner::E_AT_START) {
                        cout << " start breaks a propositional invariant\n";
                    } else {
                        cout << " end breaks a propositional invariant\n";
                    }
                }
            }

        }
    }

    {
        StateFacts::const_iterator stateItr = theState.first.begin();
        const StateFacts::const_iterator stateEnd = theState.first.end();

        for (; stateItr != stateEnd; ++stateItr) {

            if (debug) {
                cout << "Considering what benefits from " << *(RPGBuilder::getLiteral(FACTA(stateItr))) << " being true\n";                
            }
            
            list<pair<int, Planner::time_spec> > & dependents = (*processedPreconditionsToActions)[FACTA(stateItr)];

            list<pair<int, Planner::time_spec> >::const_iterator depItr = dependents.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator depEnd = dependents.end();

            for (; depItr != depEnd; ++depItr) {
                const int currAct = depItr->first;
                const Planner::time_spec startOrEnd = depItr->second;
                int & toManipulate = (startOrEnd == Planner::E_AT_START ? startPreconditionCounts[currAct] : endPreconditionCounts[currAct]);

                if (!(--toManipulate)) {

                    if (negativesAreOkay((startOrEnd == Planner::E_AT_START
                                          ? RPGBuilder::getProcessedStartNegativePropositionalPreconditions()[currAct]
                                          : RPGBuilder::getEndNegativePropositionalPreconditions()[currAct]) ,
                                         theState.first)) {
                        ActionSegment candidate(getOp(currAct), startOrEnd, -1, emptyIntSet);
                        const bool nonMutex = RPGBuilder::stepNeedsToHaveFinished(candidate, theState, candidate.needToFinish);

                        if (nonMutex) {
                            if (debug) {
                                cout << "Based on propositions, " << candidate << " is a candidate\n";
                            }
                            toFilter.push_back(candidate);
                        }
                    }
                }
            }
        }

    }


    list<ActionSegment>::iterator fItr = toFilter.begin();
    const list<ActionSegment>::iterator fEnd = toFilter.end();

    for (; fItr != fEnd; ++fItr) {
        /*const pair<int, Planner::time_spec> currAct = *fItr;
        list<RPGBuilder::NumericPrecondition> & currList = (*actionsToNumericPreconditions)[currAct->first];
        bool isApplicable = true;
        list<RPGBuilder::NumericPrecondition>::iterator npItr = currList.begin();
        const list<RPGBuilder::NumericPrecondition>::iterator npEnd = currList.end();

        for (; npItr != npEnd; ++npItr) {
        if (!npItr->isSatisfied(theState.second)) {
        isApplicable = false;
        break;
        }
        }
        if (isApplicable) {
        applicableActions.push_back(currAct);
        }*/

        bool isApplicable = true;

        if (fItr->second == Planner::E_AT_START) {
            isApplicable = TemporalAnalysis::okayToStart(fItr->first->getID(), stateTime);
        } else if (fItr->second == Planner::E_AT_END) {
            isApplicable = TemporalAnalysis::okayToEnd(fItr->first->getID(), stateTime);
        }

        if (debug && !isApplicable) {
            cout << "Not okay to apply " << *fItr << ", according to temporal analysis\n";
        }

        vector<list<int> > * const toQuery = (fItr->second == Planner::E_AT_START ? actionsToProcessedStartNumericPreconditions : actionsToNumericEndPreconditions);
        if (isApplicable) {

            list<int> & nprecs = (*toQuery)[fItr->first->getID()];

            list<int>::iterator npItr = nprecs.begin();
            const list<int>::iterator npEnd = nprecs.end();

            for (; npItr != npEnd; ++npItr) {

                if (!((*rpgNumericPreconditions)[*npItr]).isSatisfiedWCalculate(theState.secondMin, theState.secondMax)) {
                    if (debug) cout << (*rpgNumericPreconditions)[*npItr] << " isn't satisfied, so " << *(fItr->first) << " isn't applicable\n";
                    isApplicable = false;
                    break;
                }

            }

        }

        /*        if (isApplicable && false) { //HACK
                    vector<list<int> > * const checkEffects = (fItr->second == Planner::E_AT_START ? actionsToRPGNumericStartEffects : actionsToRPGNumericEndEffects);

                    {

                        list<int> & neffs = (*checkEffects)[fItr->first->getID()];

                        list<int>::iterator neItr = neffs.begin();
                        const list<int>::iterator neEnd = neffs.end();

                        for (; neItr != neEnd; ++neItr) {

                            if (theState.fluentInvariants.find(((*rpgNumericEffects)[*neItr]).fluentIndex) != theState.fluentInvariants.end()) {
                                isApplicable = false;
                                break;
                            }

                        }


                    }

                }*/

        if (isApplicable) {


            map<int, set<int> >::const_iterator saOneItr = theState.startedActions.find(fItr->first->getID());
            if (fItr->second == Planner::E_AT_START) {
                if (!RPGBuilder::noSelfOverlaps || saOneItr == theState.startedActions.end()) {
                    if (RPGBuilder::isInteresting(fItr->first->getID(), theState.first, theState.startedActions)) {
                        applicableActions.push_back(*fItr);
                    } else {
                        if (debug) {
                            cout << "Not okay to apply " << *fItr << ", as it would not be interesting to do so\n";
                        }                                                            
                    }
                } else {
                    if (debug) {
                        cout << "Not okay to apply " << *fItr << ", as it is currently executing and the planner has been asked to forbid self-overlapping actions\n";
                    }                                    
                }
            } else {
                if (saOneItr != theState.startedActions.end()) {
                    applicableActions.push_back(*fItr);                    
                } else {
                    if (debug) {
                        cout << "Not okay to apply " << *fItr << ", as it hasn't been started\n";
                    }                    
                }
            }
        }
    }

    /*{
        map<int, map<int,int> >::iterator saItr = theState.startedActions.begin();
        const map<int, map<int,int> >::iterator saEnd = theState.startedActions.end();
        for (; saItr != saEnd; ++saItr) {
            RPGBuilder::LinearEffects * const lEffs = RPGBuilder::getLinearDiscretisation()[saItr->first];
            if (lEffs) {
                const int lLim = lEffs->divisions - 1;
                map<int,int>::iterator saOneItr = saItr->second.begin();
                const map<int,int>::iterator saOneEnd = saItr->second.end();

                for (; saOneItr != saOneEnd && saOneItr->first < lLim; ++saOneItr) {
                    applicableActions.push_back(ActionSegment(getOp(saItr->first), VAL::E_OVER_ALL, saOneItr->first, emptyIntList));
                }
            }
        }
    }*/

    {

        const int nextTIL = theState.nextTIL;
        static vector<RPGBuilder::FakeTILAction*> & tilActs = RPGBuilder::getNonAbstractedTILVec();

        if (nextTIL < tilActs.size()) {

            ActionSegment candidate(0, Planner::E_AT, nextTIL, emptyIntSet);

            const bool isApplicable = RPGBuilder::stepNeedsToHaveFinished(candidate, theState, candidate.needToFinish);

            if (isApplicable) {
                //cout << "TIL " << i << " is applicable\n";
                applicableActions.push_back(candidate);
            }
        }

    }

};


bool RPGHeuristic::testApplicability(const MinimalState & theState, const double & stateTime, const ActionSegment & actID, bool fail, bool ignoreDeletes)
{
    return d->testApplicability(theState, stateTime, actID, fail, ignoreDeletes);
}

bool RPGHeuristic::Private::testApplicability(const MinimalState & theState, const double & stateTime, const ActionSegment & actID, const bool & fail, const bool & ignoreDeletes)
{

    if (actID.second == Planner::E_AT_START) {

        if (RPGBuilder::noSelfOverlaps) {

            if (fail) {
                assert(theState.startedActions.find(actID.first->getID()) == theState.startedActions.end());
            } else {
                if (theState.startedActions.find(actID.first->getID()) != theState.startedActions.end()) return false;
            }
        }


        if (fail) {
            assert(TemporalAnalysis::okayToStart(actID.first->getID(), stateTime));
        } else {
            if (!TemporalAnalysis::okayToStart(actID.first->getID(), stateTime)) return false;
        }

        {
            set<int> ntf;
            const bool passesPropositional = RPGBuilder::stepNeedsToHaveFinished(actID, theState, ntf);
            if (!passesPropositional) {
                if (fail) {
                    assert(false);
                } else {
                    return false;
                }
            }
        }

        if (!negativesAreOkay(RPGBuilder::getProcessedStartNegativePropositionalPreconditions()[actID.first->getID()],
                              theState.first)) {
            if (fail) {
                assert(false);
            } else {
                return false;
            }
        }


        if (!ignoreDeletes) {

            list<int> & checkFor = (*actionsToProcessedStartNumericPreconditions)[actID.first->getID()];
            list<int>::iterator fItr = checkFor.begin();
            const list<int>::iterator fEnd = checkFor.end();

            for (; fItr != fEnd; ++fItr) {

                if (!((*rpgNumericPreconditions)[*fItr]).isSatisfiedWCalculate(theState.secondMin, theState.secondMax)) {
                    if (fail) {
                        cerr << "Fatal internal error: precondition " << (*rpgNumericPreconditions)[*fItr] << " not satisfied\n";
                        assert(false);
                    } else {
                        return false;
                    }
                }

            }
        }



    } else if (actID.second == Planner::E_AT_END) {


        if (fail) {
            assert(TemporalAnalysis::okayToEnd(actID.first->getID(), stateTime));
        } else {
            if (!TemporalAnalysis::okayToEnd(actID.first->getID(), stateTime)) return false;
        }


        {
            set<int> ntf;
            const bool passesPropositional = RPGBuilder::stepNeedsToHaveFinished(actID, theState, ntf);
            if (!passesPropositional) {
                if (fail) {
                    assert(false);
                } else {
                    return false;
                }
            }
        }

        if (!negativesAreOkay(RPGBuilder::getEndNegativePropositionalPreconditions()[actID.first->getID()],
                              theState.first)) {
            if (fail) {
                assert(false);
            } else {
                return false;
            }
        }


        if (!ignoreDeletes) {

            list<int> & checkFor = (*actionsToNumericEndPreconditions)[actID.first->getID()];
            list<int>::iterator fItr = checkFor.begin();
            const list<int>::iterator fEnd = checkFor.end();



            for (; fItr != fEnd; ++fItr) {

                if (!((*rpgNumericPreconditions)[*fItr]).isSatisfiedWCalculate(theState.secondMin, theState.secondMax)) {
                    if (fail) {
                        assert(false);
                    } else {
                        return false;
                    }
                }

            }
        }


    } else if (actID.second != Planner::E_AT) {
        assert(false);

    } else { // til action

        const int & nextTIL = theState.nextTIL;

        if (fail) {
            if (actID.divisionID < nextTIL) {
                cout << "Trying to apply " << actID.divisionID << ", but next one is " << nextTIL << "\n";
            }
            assert(actID.divisionID >= nextTIL);
        } else {
            if (actID.divisionID < nextTIL) return false;
        }

        static vector<RPGBuilder::FakeTILAction*> & tilActs = RPGBuilder::getNonAbstractedTILVec();
        static const vector<RPGBuilder::FakeTILAction*>::iterator tilEnd = tilActs.end();

        int i = 0;

        static const set<int> emptyIntSet;

        for (; i <= actID.divisionID; ++i) {
            #ifndef NDEBUG
            if (i == tilActs.size()) {
                cout << "Error: " << i << " TILs in the domain, but trying to access the one with index " << i << "\n";
                exit(1);
            }
            #endif

            ActionSegment candidate(actID.first, Planner::E_AT, i, emptyIntSet);

            const bool passesPropositional = RPGBuilder::stepNeedsToHaveFinished(candidate, theState, candidate.needToFinish);
            if (!passesPropositional) {
                if (fail) {
                    assert(false);
                } else {
                    return false;
                }
            }

        }


    }

    return true;


}
void RPGHeuristic::filterApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions)
{
    return d->filterApplicableActions(theState, stateTime, applicableActions);
}

void RPGHeuristic::Private::filterApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions)
{


    const bool filterDebug = false;

    if (filterDebug) cout << "Filtering applicable actions\n";

    list<ActionSegment> toFilter(applicableActions);

    list<ActionSegment> toNumericFilter;

    applicableActions.clear();

    if (filterDebug) cout << "Input consists of " << toFilter.size() << " actions\n";

    list<ActionSegment>::iterator tfItr = toFilter.begin();
    const list<ActionSegment>::iterator tfEnd = toFilter.end();

    /*for (; fItr != fEnd; ++fItr) {
    const int currAct = *fItr;
    list<RPGBuilder::NumericPrecondition> & currList = (*actionsToNumericPreconditions)[currAct];
    bool isApplicable = true;
    list<RPGBuilder::NumericPrecondition>::iterator npItr = currList.begin();
    const list<RPGBuilder::NumericPrecondition>::iterator npEnd = currList.end();

    for (; npItr != npEnd; ++npItr) {
    if (!npItr->isSatisfied(theState.second)) {
    isApplicable = false;
    break;
    }
    }
    if (isApplicable) {
    applicableActions.push_back(currAct);
    }
    }*/

    for (; tfItr != tfEnd; ++tfItr) {


        bool isApplicable = true;

        if (tfItr->second == Planner::E_AT_START) {

            if (!RPGBuilder::noSelfOverlaps || theState.startedActions.find(tfItr->first->getID()) == theState.startedActions.end()) {

                if (filterDebug) cout << "Considering start of " << *(tfItr->first) << "\n";

                isApplicable = RPGBuilder::isInteresting(tfItr->first->getID(), theState.first, theState.startedActions);
                
                if (isApplicable) isApplicable = TemporalAnalysis::okayToStart(tfItr->first->getID(), stateTime);

                if (isApplicable) isApplicable = RPGBuilder::stepNeedsToHaveFinished(*tfItr, theState, tfItr->needToFinish);

                if (isApplicable) isApplicable = negativesAreOkay(RPGBuilder::getProcessedStartNegativePropositionalPreconditions()[tfItr->first->getID()], theState.first);

            } else {
                isApplicable = false;
            }

        } else if (tfItr->second == Planner::E_AT_END) {
            const map<int, set<int> >::const_iterator saItr = theState.startedActions.find(tfItr->first->getID());
            if (saItr != theState.startedActions.end() && TemporalAnalysis::okayToEnd(tfItr->first->getID(), stateTime)) {
                isApplicable = RPGBuilder::stepNeedsToHaveFinished(*tfItr, theState, tfItr->needToFinish);
            } else {
                isApplicable = false;
            }
            if (isApplicable) isApplicable = negativesAreOkay(RPGBuilder::getEndNegativePropositionalPreconditions()[tfItr->first->getID()], theState.first);

        } else if (tfItr->second != Planner::E_AT) {

            assert(false);
        } else if (tfItr->second == Planner::E_AT) { // TIL action

            static const set<int> emptyIntSet;

            const int nextTIL = theState.nextTIL;

            if (tfItr->divisionID >= nextTIL) {

                bool safe = true;

                for (int i = nextTIL; safe && i <= tfItr->divisionID; ++i) {

                    ActionSegment candidate(tfItr->first, Planner::E_AT, i, emptyIntSet);

                    safe = RPGBuilder::stepNeedsToHaveFinished(candidate, theState, tfItr->needToFinish);

                }

                if (safe) {
                    applicableActions.push_back(*tfItr);
                    // skip straight to the destination list - no numeric interactions,
                    // as these are timed literals, not timed fluents
                }

            }
            isApplicable = false;
        } else {
            isApplicable = false;
        }

        if (isApplicable) {
            toNumericFilter.push_back(*tfItr);
        }
    }



    list<ActionSegment>::iterator tnfItr = toNumericFilter.begin();
    const list<ActionSegment>::iterator tnfEnd = toNumericFilter.end();

    for (; tnfItr != tnfEnd; ++tnfItr) {
        bool isApplicable = true;

        if (filterDebug) cout << "Considering numerically " << *(tnfItr->first) << "\n";

        vector<list<int> > * const toQuery = (tnfItr->second == Planner::E_AT_START ? actionsToProcessedStartNumericPreconditions : actionsToNumericEndPreconditions);
        {

            list<int> & nprecs = (*toQuery)[tnfItr->first->getID()];

            list<int>::iterator npItr = nprecs.begin();
            const list<int>::iterator npEnd = nprecs.end();

            for (; npItr != npEnd; ++npItr) {

                if (!((*rpgNumericPreconditions)[*npItr]).isSatisfiedWCalculate(theState.secondMin, theState.secondMax)) {
                    isApplicable = false;
                    break;
                } else {
                    if (filterDebug) cout << "\t" << (*rpgNumericPreconditions)[*npItr] << "satisfied\n";
                }

            }

        }

        if (isApplicable) {
            applicableActions.push_back(*tnfItr);
        }
    }


};


list<instantiatedOp*> * RPGHeuristic::makePlan(list<int> & steps)
{

    list<instantiatedOp*> * toReturn = new list<instantiatedOp*>();

    list<int>::iterator sItr = steps.begin();
    const list<int>::iterator sEnd = steps.end();
    cout << "\n";
    for (; sItr != sEnd; ++sItr) {
        toReturn->push_back(RPGBuilder::getInstantiatedOp(*sItr));
    }

    return toReturn;
}

instantiatedOp* RPGHeuristic::getOp(const int & i)
{

    return RPGBuilder::getInstantiatedOp(i);

};


list<Literal*> & RPGHeuristic::getDeleteEffects(const int & i, const Planner::time_spec & t)
{
    if (t == Planner::E_AT_START) {
        return (*(d->actionsToStartNegativeEffects))[i];
    } else {
        return (*(d->actionsToEndNegativeEffects))[i];
    }
}

list<Literal*> & RPGHeuristic::getAddEffects(const int & i, const Planner::time_spec & t)
{
    if (t == Planner::E_AT_START) {
        return (*(d->actionsToStartEffects))[i];
    } else {
        return (*(d->actionsToEndEffects))[i];
    }
};

list<Literal*> & RPGHeuristic::getPreconditions(const int & i, const Planner::time_spec & t)
{
    if (t == Planner::E_AT_START) {
        return (*(d->actionsToStartPreconditions))[i];
    } else {
        return (*(d->actionsToEndPreconditions))[i];
    }
};


list<int> & RPGHeuristic::getNumericEffects(const int & i, const Planner::time_spec & t)
{
    if (t == Planner::E_AT_START) {
        return (*(d->actionsToRPGNumericStartEffects))[i];
    } else {
        return (*(d->actionsToRPGNumericEndEffects))[i];
    }

};

list<Literal*> & RPGHeuristic::getInvariants(const int & i)
{
    return (*(d->actionsToInvariants))[i];
}

RPGBuilder::RPGNumericEffect & RPGHeuristic::getRPGNE(const int & i)
{
    return (*(d->rpgNumericEffects))[i];
};


bool RPGHeuristic::printRPGAsDot = false;
bool RPGHeuristic::blindSearch = false;
bool RPGHeuristic::makeCTSEffectsInstantaneous = false;    
bool RPGHeuristic::ignoreNumbers = false;
bool RPGHeuristic::estimateCosts = true;    


void RPGHeuristic::setGuidance(const char * config)
{
    const string asString(config);
    
    if (asString == "blind") {
        blindSearch = true;                
    } else if (asString == "nonumbers") {
        ignoreNumbers = true;
    } else if (asString == "makectsinstantaneous") {
        makeCTSEffectsInstantaneous = true;
    } else {
        cerr << "Possible options for the -g parameter are:\n";
        cerr << "\t-gblind                - use blind search (0 heuristic for goal states, otherwise 1)\n";
        cerr << "\t-gnonumbers            - ignore numeric preconditions and effects\n";
        cerr << "\t-gmakectsinstantaneous - make continuous effects instantaneous (as in the Colin IJCAI paper)\n";
        exit(1);
    }
}
    


};
