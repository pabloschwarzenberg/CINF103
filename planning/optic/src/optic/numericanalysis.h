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

#ifndef NUMERICANALYSIS_H
#define NUMERICANALYSIS_H

#include <ptree.h>

#include <vector>
using std::vector;

#include <cfloat>
#include <utility>

using std::make_pair;

#include "globals.h"
#include "RPGBuilder.h"

namespace Planner {

struct VarOpConst {
    int var;
    VAL::comparison_op op;
    double constant;        
    
    VarOpConst(const int & varIn, const double & bound, const VAL::comparison_op & isUpper);

    VarOpConst(const RPGBuilder::RPGNumericPrecondition & rnp, bool & success);
    bool implies(const VarOpConst & other) const;
    bool isMutexWith(const VarOpConst & other) const;
    bool overlaps(const VarOpConst & other) const;
    bool operator >(const VarOpConst & other) const;
    void tighten(const VarOpConst & other);
};

extern ostream & operator<<(ostream & o, const VarOpConst & masterPre);

class NumericAnalysis
{
    public:
        /** @brief Enum denoting the identified dominance constraint on a given task variable.        
        *   - <code>E_NODOMINANCE</code> denotes that no dominance constraint has been identified
        *   - <code>E_IRRELEVANT</code> denotes that the task variable never appears as a precondition of
        *     an action, or within one of the goals.
        *   - <code>E_METRICTRACKING<code> denotes that the task variable never appears as a precondition - only in the 
        *     task metric.
        *   - <code>E_SMALLERISBETTER</code> denotes that smaller values of the variable are preferable to larger values
        *     (e.g. all preconditions are of the form <code>(<= v c)</code>, and <code>v</code> can only be increased).
        *   - <code>E_BIGGERISBETTER</code> denotes that smaller values of the variable are preferable to larger values
        *     (e.g. all preconditions are of the form <code>(>= v c)</code>, and <code>v</code> can only be decreased). 
        */
        enum dominance_constraint { E_NODOMINANCE, E_IRRELEVANT, E_METRICTRACKING, E_SMALLERISBETTER, E_BIGGERISBETTER};
        
        /** @brief Enum denoting whether the effects on a variable are order-independent.
        *
        * - <code>E_ORDER_DEPENDENT</code> denotes that the order of the effects could matter
        * - <code>E_ORDER_INDEPENDENT_AT_END</code> denotes that if no actions are executing, the order
        *   of the effects does not matter
        * - <code>E_ORDER_INDEPENDENT</code> denotes that the order of the effects does not matter
        *
        *  For now, order-independence is determined by one of two simple rules.  First, if all the
        *  effects are only increases or decreases by fixed, constant values, then the effects on
        *  a variable are <code>E_ORDER_INDEPENDENT</code>.  Or, if all the other effects are
        *  increases or decreases by a continuous linear effect/duration dependent effect
        *  of actions for which the duration is bounded by fixed, constant values, then the
        *  variable can be classed as <code>E_ORDER_INDEPENDENT_AT_END</code>.  
        */
        enum order_independence { E_ORDER_DEPENDENT, E_ORDER_INDEPENDENT_AT_END, E_ORDER_INDEPENDENT };
        
        #ifdef POPF3ANALYSIS
        /** @brief Struct used to define limits on one-way variable usage, according to the goals.
         *
         * This struct is used to hold the output from <code>NumericAnalysis::findGoalNumericUsageLimits()</code>.
         * The limit is defined on the given variable according to <code>op</code>:
         * - if <code>op = VAL::E_GREATER</code>, then the limit is <code>var > limit</code>, i.e. <code>var</code> must
         *   not be decreased to this point or the relevant goal is unreachable.
         * - if <code>op = VAL::E_GREATEQ</code>, then the limit is <code>var >= limit</code>, i.e. <code>var</code> must
         *   not be decreased beyond this point or the relevant goal is unreachable.
         */
        struct NumericLimitDescriptor {
            /** @brief The variables upon which the limit is defined. */
            map<int,double> var;
            
            /** @brief The operator used when setting the limit. */
            VAL::comparison_op op;
            
            /** @brief The limit on the variable. */
            double limit;
            
            /** @brief If <code>true</code>, the limit is due to the plan metric. */
            bool optimisationLimit;

            NumericLimitDescriptor() {
            }
            
            NumericLimitDescriptor(const int & v, const double & w, const VAL::comparison_op & cOp, const double & lim);
            
            NumericLimitDescriptor(const vector<int> & v, const vector<double> & w, const int & size, const VAL::comparison_op & cOp, const double & lim);
            
            NumericLimitDescriptor(const vector<int> & v, const vector<double> & w, const int & size);
            
            bool operator<(const NumericLimitDescriptor & other) const {
                return (var < other.var);
            }
        };
        
        struct EffectDeterminedByTime {
            // effect on var = m * current timestamp + c
            int y;
            double c;
            double m;
            
            EffectDeterminedByTime(const int & yIn, const double & cIn, const double & mIn)
                : y(yIn), c(cIn), m(mIn) {
            }
        };
        
        struct CostAtTime {
            
            EpsilonResolutionTimestamp start;
            EpsilonResolutionTimestamp end;
            
            list<EffectDeterminedByTime*> limitCosts;
            list<EffectDeterminedByTime*> varCosts;
            
            CostAtTime(const EpsilonResolutionTimestamp & sIn, const EpsilonResolutionTimestamp & eIn)
                : start(sIn), end(eIn) {                
            }

        };
        
        /** @brief Whether a variable is only in at start conditions.
         *
         * If entry <code>i</code> is <code>true</code>, then variable <code>i</code> is only in
         * <code>at start</code> conditions.
         */
        static vector<bool> onlyAtStartConditionsOnVariable;
        #endif

        friend class MaskedVariableBounds;
        
        class MaskedVariableBounds {
            private:
                
                pair<double,double> durationBounds;
                map<int, pair<double,double> > mask;
                
            public:
                
                MaskedVariableBounds() : durationBounds(0.001, DBL_MAX) {
                };
                
                void tightenUpper(const int & v, const double & u) {
                    if (v == -3) {
                        if (durationBounds.second > u) {
                            durationBounds.second = u;
                        }
                    } else {
                        const map<int, pair<double,double> >::iterator mItr = mask.insert(make_pair(v, NumericAnalysis::masterVariableBounds[v])).first;
                        if (mItr->second.second > u) {
                            mItr->second.second = u;
                        }
                    }
                }
                
                void tightenLower(const int & v, const double & u) {
                    if (v == -3) {
                        if (durationBounds.first < u) {
                            durationBounds.first = u;
                        }
                    } else {
                        const map<int, pair<double,double> >::iterator mItr = mask.insert(make_pair(v, NumericAnalysis::masterVariableBounds[v])).first;
                        if (mItr->second.first < u) {
                            mItr->second.first = u;
                        }
                    }
                }
                
                const pair<double,double> & operator[](const int & i) const {
                    if (i == -3) {
                        return durationBounds;
                    }
                    const map<int, pair<double,double> >::const_iterator mItr = mask.find(i);
                    if (mItr == mask.end()) {
                        return NumericAnalysis::masterVariableBounds[i];
                    }
                    return mItr->second;
                }
                
                void applyPreToBounds(const RPGBuilder::RPGNumericPrecondition & currPre);
        };
        

        
    protected:
        /** @brief Dominance constraints on each task variable.
         * 
         *  These are defined in the order in which they
         *  occur when iterating from <code>Inst::instantiatedOp::pnesBegin()</code> to
         *  <code>Inst::instantiatedOp::pnesEnd()</code>.
         */
        static vector<dominance_constraint> dominanceConstraints;
        
        /** @brief For each task variable, this defines whether the effects on that variable are order-independent. */
        static vector<order_independence> allEffectsAreOrderIndependent;
        
        /** @brief Bounds on the value of each PNE. */
        static vector<pair<double,double> > masterVariableBounds;
        
        static void checkConditionalNumericEffectsAreOnlyOnMetricTrackingVariables();
        
        #ifdef POPF3ANALYSIS        
        /** @brief Ascertain whether it is only ever better for preconditions to have bigger/smaller values of a given fact.
         *
         *  This function is used internally by <code>findDominanceConstraintsAndMetricTrackingVariables()<code>.
         *
         *  @param varID  Variable ID to analyse to find if bigger/better values are preferable
         *  @param numericPreconditionsThatAreInCondEffs  A map from numeric preconditions to which actions' conditional effects they are in
         * 
         *  @retval <code>E_BIGGERISBETTER</code>   Bigger values of the variable are preferable
         *  @retval <code>E_SMALLERISBETTER</code>  Smaller values of the variable are preferable
         *  @retval <code>E_NODOMINANCE</code>      Neither bigger nor smaller values are clearly preferable
         */ 
        static dominance_constraint preconditionDominanceInOneDirection(const int & varID, const map<int,list<int> > & numericPreconditionsThatAreInCondEffs);

        /** @brief Ascertain whether a numeric precondition only supports change the other way
         * 
         *  This captures the modelling idiom that replenishing a resource needs it to be non-full,
         *  which otherwise gives the impression that having less of the resouce might be better;
         *  whereas it's not if:
         *   i) the only actions with a 'less is better' precondition then increase it
         *  ii) there's no gap between what they want it to be less than and what they replace it to
         *      (e.g. < 95, but then assign 100, would make it beneficial to get to below 95).
         * 
         *  Note that this works for both directions (> and <) - it looks at what the precondition
         *  is suggesting.
         * 
         *  @param preID  The precondition ID to look at the dependents of
         *  @retval <code>true</code>  'Not full' only supports it being replenished
         *  @retval <code>false</code>  Cannot prove this: less might be better.
         */ 
        static bool requiringNotFullOnlySupportsReplenishment(const int & preID);            
        
        static bool couldIncreaseVariable(const RPGBuilder::RPGNumericEffect & eff, const MaskedVariableBounds & bounds);
        static bool couldDecreaseVariable(const RPGBuilder::RPGNumericEffect & eff, const MaskedVariableBounds & bounds);
        
        /** @brief Find if one conditional outcome could be worse than another.
         *
         * This is pessimistic: it returns <code>true</code> if there's any conceivable way that <code>a</code> could be worse than <code>b</code>.
         * 
         * @param a  One conditional outcome
         * @param b  The other outcome
         * @retval <code>true</code> if <code>a</code> could, pessimistically, be worse than <code>b</code>
         * @retval <code>false</code> if <code>a</code> cannot ever be worse than <code>b</code>
         */
        static bool couldBeWorseThan(const RPGBuilder::ConditionalEffect * a, const RPGBuilder::ConditionalEffect * b, const MaskedVariableBounds & bounds);
        
        /** @brief Ascertain whether a numeric precondition only supports worse options than others available
         * 
         * In some cases, a numeric precondition being satisfied is only to ensure a preferable option wasn't
         * available.  For instance, with a cost function encoded as two sections, the first option may need
         * <code>(<= x 100)</code>, and the second section <code>(> x 100)</code>.  If the first option has
         * lower cost (greater reward) then having a smaller x is preferable; so even though there is a precondition
         * making it look like having a larger value of x enables something, it only enables an inferior option.
         * 
         *  @param preID  The precondition ID to look at the dependents of
         *  @retval <code>true</code>  The precondition only supports an option inferior to what would be available were it violated.
         *  @retval <code>false</code>  Cannot prove this: precondition might be good to have satisfied.
         */
        static bool preconditionOnlySupportsWorseMetricThanOtherOptions(const int & preID, const map<int,list<int> > & numericPreconditionsThatAreInCondEffs);
        
        /** @brief Ascertain whether any dominance is broken by effects.
         * 
         * This function is used internally by <code>findDominanceConstraintsAndMetricTrackingVariables()<code>.
         * If a variable is only in preconditions of the form <code>p {>=,>} c</code>, it not necessarily always be preferable
         * for it to be smaller if there is an effect <code>q -= p</code> on a variable which, according to the preconditions,
         * is better to be bigger.  This function considers how the effects might change the dominance rules determined from
         * just the preconditions.  @see preconditionDominanceInOneDirection
         * 
         * @param workingDominanceConstraints  The dominance constraints to be updated based on the effects
         */
        static void considerConflictingDominanceThroughEffects(vector<dominance_constraint> & workingDominanceConstraints);
        
        /** @brief Update dominance constraints according to a duration-dependent effect.
         *
         * This function is used internally by <code>considerConflictingDominanceThroughEffects()</code>.
         * If a variable causes an action's duration to increase, and that action has a continuous effect/duration-dependent
         * effect on another variable, then this affects the dominance constraints:
         * - if the effect is on a variable for which bigger values are preferred:
         *   - if the effect is positive-weighted, bigger durations are preferred; otherwise,
         *   - if the effect is negative-weighted, smaller durations are preferred.
         * - if the effect is on a variable for which smaller values are preferred:
         *   - if the effect is positive-weighted, smaller durations are preferred; otherwise,
         *   - if the effect is negative-weighted, durations durations are preferred.
         * - if the effect is on a variable for which neither smaller nor bigger values are clearly preferable, then
         *   there is no clear preference for the duration.
         * 
         * In all cases, the preference for the duration is used update the dominance constraints on the variables
         * affecting the duration:
         * - if increasing a variable causes the duration to increase/decrease, and that is not what would be preferred,
         *   then bigger values of that variable can no longer be considered better;
         * - if decreasing a variable causes the duration to increase/decrease, and that is not what would be preferred,
         *   then smaller values of that variable can no longer be considered better.
         * 
         * @param v  The variable upon which the effect is acting
         * @param w  The weight of the effect (i.e. positive or negative)
         * @param durVar  The variable affecting the duration
         * @param asIncreasedCausesDurationToDecrease  If <code>true</code>, increasing the variable's value causes the duration
         *                                             of the effect to increase; otherwise, it causes it to decrease.
         * @param workingDominanceConstraints          The current dominance constraints, to be updated as above.
         */
        static void updateForDurationDependence(const int & v, const double & w,
                                                const int & durVar, const bool & asIncreasedCausesDurationToDecrease,
                                                vector<dominance_constraint> & workingDominanceConstraints);
        
                                                
        static void considerCostsOfLiteralGoalsReachedByGoalOnlyOperators();
                                        
        static bool safeForMetricLimit(const RPGBuilder::RPGNumericEffect & currEff,
                                       const MaskedVariableBounds & variableBounds,
                                       const double & weightsecond);
        
        static void seeIfInducesALimit(const NumericLimitDescriptor & hypothesisedLimit,
                                       const map<int, list<int> > & numericEffectsThatAreInConditionalEffects,
                                       map<NumericLimitDescriptor,bool> & upperBounds);                                       
        
        /** @brief Vector to store results of <code>NumericAnalysis::findGoalNumericUsageLimits()</code>. */
        static vector<NumericLimitDescriptor> goalNumericUsageLimits;
                                               
        /** @brief Map (keys are goal indices) to store results of <code>NumericAnalysis::considerCostsOfLiteralGoalsReachedByGoalOnlyOperators()</code>. */
        static vector<map<int, list<int> > > goalHasIndependentCostOnLimit;
        
        static bool thereAreIndependentGoalCosts;
        
        /** @brief Result of the analysis to determine whether the metric is monotonically worsening. */
        static bool metricIsMonotonicallyWorsening;
        
        static vector<list<CostAtTime*>* > timeDependentStartCosts;
        static vector<list<CostAtTime*>* > timeDependentEndCosts;
        
        static vector<int> timeDependentRewardFacts;
        static map<int,int> factToTDRArrayIndex;
        static vector<set<int> > timeDependentRewardFactsDueToGoal;
        
        #endif
        
        static vector<double> maximumPositiveGradientOnVariable;
        static vector<double> maximumNegativeGradientOnVariable;

        static vector<bool> variableOnlyIncreasesByGradients;
        static vector<bool> variableOnlyDecreasesByGradients;

        /** @brief Ticker variables. Keys: var ID, Values: associated net gradient. */
        static map<int,double> tickerVariables;
        
        /** @brief For each metric var, whether it is better bigger, solely from a metric point of view */
        static map<int,bool> metricVarIsBetterBigger;
                
        static map<int,set<int> > factsThatDefineAndFixVariables;
        static map<int,set<int> > variablesFixedAndDefinedByFact;
        
        static vector<bool> whetherEffectCanBeMovedToStart;
        
        static map<int, list<pair<int, Planner::time_spec> > > numericEffectsThatAreInConditionalEffects;
    public:                
        #ifdef POPF3ANALYSIS
        static bool doGoalLimitAnalysis;
        #endif

        static bool readBounds;
        
        /** @brief Use static analysis to find the maximum gradients that can act on a variable
         *
         * This is currently calculated by looping over the actions that have a continuous effect on v,
         * and adding their contribution the maximum positive/negative gradient (for increase/decrease effects,
         * respectively) of v.  If an action can self-overlap arbitrarily many times, this causes
         * the gradient to become infinite.
         */
        static void findMaximumGradients();

        
        static const vector<double> & getMaximumPositiveGradientOnVariable() {
            return maximumPositiveGradientOnVariable;
        }
        
        static const vector<double> & getMaximumNegativeGradientOnVariable() {
            return maximumNegativeGradientOnVariable;
        }
        
        static const vector<bool> & getWhetherVariableOnlyIncreaseByGradients() {
            return variableOnlyIncreasesByGradients;
        }
        
        static const vector<bool> & getWhetherVariableOnlyDecreaseByGradients() {
            return variableOnlyDecreasesByGradients;
        }   
        
        
        /** @brief Use static analysis to identify the dominance constraints on the task numeric variables.  
         * 
         *  Each variable is given one of the values from
         *  <code>NumericAnalysis::dominance_constraint</code>.  To obtain the results of this analysis,
         *  use <code>getDominanceConstraints()</code>.
         */
        static void findDominanceConstraintsAndMetricTrackingVariables();
        
        /** @brief Use static analysis to identify the variables for which all effects are order-independent.
         *
         *  The effects on a variable are order-independent if the effects can be 
         *  interleaved arbitrarily without affecting the final change on the 
         *  variable.  To obtain the results of this analysis, use
         *  <code>getDataOnWhichVariablesHaveOrderIndependentEffects()</code>.
         */
        static void findWhichVariablesHaveOrderIndependentEffects();
        
        #ifdef POPF3ANALYSIS
        /** @brief Find which variables have prescribed usage limits in the goal.
         *
         *  This function identifies cases where the numeric goals impose limits on the usage of some
         *  variable in solutions.  Such limits arise in one of two cases:
         *  - <code>v {<=,<} c</code>, where <code>v</code> can only ever be increased;
         *  - <code>v {>=,>} c</code>, where <code>v</code> can only ever be decreased.
         *
         *  In both cases <code>v</code> must have a defined initial value.
         *
         *  To obtain the results of this analysis, call <code>getGoalNumericUsageLimits()</code>.
         */
        static void findGoalNumericUsageLimits();
        
        /** @brief Return the results of the analysis to find usage limits on numeric variables.
        *
        *  @return A const reference to <code>NumericAnalysis::goalNumericUsageLimits</code>,
        *          where each entry is a <code>NumericAnalysis::NumericLimitDescriptor</code> detailing
        *          a limit on a numeric variable according to the goals.
        */        
        static const vector<NumericLimitDescriptor> & getGoalNumericUsageLimits() {
            return goalNumericUsageLimits;
        }
        
        /** @brief Return the results of the analysis to find which literal goals have direct-achivement costs independent of the rest of the problem. */
        static const vector<map<int, list<int> > > & getIndependentGoalCosts() {
            return goalHasIndependentCostOnLimit;
        }
        
        static const bool & areThereAnyIndependentGoalCosts() {
            return thereAreIndependentGoalCosts;
        }
        
        /** @brief Find which variables are only in at start preconditions. */
        static void findWhichVariablesAreOnlyInAtStarts();
        
        /** @brief Return the results of the analysis to find variables only in at-start preconditions. */
        static const vector<bool> & getWhichVariablesAreOnlyInStartPreconditions() {
            return onlyAtStartConditionsOnVariable;
        };
        
        /** @brief Find bounds on variables. */
        static void findVariableBounds();
        
        static const vector<pair<double,double> > & getVariableBounds() {
            return masterVariableBounds;
        }
        
        static void findWhetherTheMetricIsMonotonicallyWorsening();
        
        static const bool & theMetricIsMonotonicallyWorsening() {
            return metricIsMonotonicallyWorsening;
        }
        
        /** @brief Find which variables are only ever linearly modified by processes */
        static void findVariablesThatAreTickers();
        
        /** @brief Find actions who have better reward/lower cost if executed sooner */
        static void findEarlierIsBetterTimeDependentRewards();
        
        static const vector<list<CostAtTime*>* > & getTimeDependentStartCosts() {
            return timeDependentStartCosts;
        }
        
        static const vector<list<CostAtTime*>* > & getTimeDependentEndCosts() {
            return timeDependentEndCosts;
        }
        
        static const vector<int> & getFactsInTimeDependentRewards() {
            return timeDependentRewardFacts;
        }
        
        static const vector<set<int> > & getTimeDependentRewardFactsDueToGoal() {
            return timeDependentRewardFactsDueToGoal;
        }
        
        static const map<int,int> & getFactToTDRArrayIndex() {
            return factToTDRArrayIndex;
        }
        
        static double bestAdditionalRewardFromHere(const MinimalState & s);
        
        /** @brief Return the results of the analysis to find whether variables are only ever linearly modified by processes.
         * 
         * @see NumericAnalysis::findVariablesThatAreTickers
         * @return A map from <code>PNE::getStateID()</code> values to doubles, denoting the continuous effect on that due to processes.
         */
        static const map<int,double> & getVariablesThatAreTickers() {
            return tickerVariables;
        }
        
        #endif
        
        /**
         *  Return the results of the analysis to determine which variables have only order-independent
         *  effects, as performed by <code>findWhichVariablesHaveOrderIndependentEffects()</code>.
         *
         *  @return A const reference to <code>NumericAnalysis::allEffectsAreOrderIndependent</code>,
         *          where the entries denote whether the corresponding variable's
         *          effects are order-independent.
         */        
        static const vector<order_independence> & getDataOnWhichVariablesHaveOrderIndependentEffects() {
            return allEffectsAreOrderIndependent;
        }
        
        
        /**
         *  Return the results of the analysis to determine dominance constraints on variables, as
         *  performed by <code>findDominanceConstraintsAndMetricTrackingVariables()</code>
         *
         *  @return A const reference to <code>NumericAnalysis::dominanceConstraints</code>, the vector of dominance
         *          constraints on each task variable.
         *
         */        
        static const vector<dominance_constraint> & getDominanceConstraints() {
            return dominanceConstraints;
        }
        
        static void findFactsThatDefineAndFixVariables();

        static const map<int,set<int> > & getFactsThatDefineAndFixVariables() {
            return factsThatDefineAndFixVariables;
        }
        
        static const map<int,set<int> > & getVariablesFixedAndDefinedByFact() {
            return variablesFixedAndDefinedByFact;
        }
        
        static void findEndEffectsSafeToMoveToTheStart();
        
        static const vector<bool> & effectCanBeMovedToStart() {
            return whetherEffectCanBeMovedToStart;
        }
        
        static void findOrphanedNumericEffects();
        
        static void identifyIntegralVariablesAndUpdatePreconditions();
        
        static const map<int, list<pair<int, Planner::time_spec> > > & getNumericEffectsThatAreInConditionalEffects() {
            return numericEffectsThatAreInConditionalEffects;
        }
};

};

#endif // NUMERICANALYSIS_H
