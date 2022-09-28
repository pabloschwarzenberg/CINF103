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

#ifndef __RPGBUILDER
#define __RPGBUILDER

#include <vector>
#include <list>
#include <set>
#include <map>
#include <limits>

using std::vector;
using std::list;
using std::set;
using std::map;

#include "minimalstate.h"

#include "instantiation.h"

#include "ptree.h"

#include <assert.h>
#include <values.h>
#include <math.h>
#include <string.h>

using namespace Inst;

namespace Planner
{

class RPGHeuristic;
class StartEvent;

struct EpsilonComp {

    bool operator()(const double & a, const double & b) const {
        if (fabs(b - a) < 0.0005) return false;
        return (a < b);
    }

};

class MinimalState;


struct ActionFluentModification {

    int act;
    Planner::time_spec ts;
    bool openEnd;
    double change;
    int howManyTimes;
    bool assignment;

    ActionFluentModification(const int & a, const Planner::time_spec & startOrEnd, const bool & oe, const double & incr, const int & shots, const bool & ass)
            : act(a), ts(startOrEnd), openEnd(oe), change(incr), howManyTimes(shots), assignment(ass) {};

};

struct InvData;
class TemporalAnalysis;

class PreferenceData;
class NNFUtils;
class PreferenceHandler;
class PreferenceFSA;


class RPGBuilder
{

    friend class TemporalAnalysis;
    
public:
    enum math_op {
        NE_ADD, NE_SUBTRACT, NE_MULTIPLY, NE_DIVIDE, NE_CONSTANT, NE_FLUENT, NE_VIOLATION
        #ifdef STOCHASTICDURATIONS
        , NE_STOCHASTIC_DURATION_TERM
        #endif
    };

    enum op_type {
        OT_NORMAL_ACTION=0, OT_INVALID_ACTION=1, OT_PROCESS=2
    };

    
    /** Description of the pointless effect an action has on a fact. */
    enum pointless_effect { PE_ADDED=1, PE_DELETED=2, PE_DELETED_THEN_ADDED=3 };
    
    static bool doSkipAnalysis;

    struct Operand {
        math_op numericOp;
        int fluentValue;
        double constantValue;
        string isviolated;
        #ifdef STOCHASTICDURATIONS
        PNE* durationVar;
        Operand(PNE * p) : numericOp(NE_STOCHASTIC_DURATION_TERM), fluentValue(-1), constantValue(NAN), durationVar(p) {};
        #endif
        Operand(const math_op & o) : numericOp(o), fluentValue(-1), constantValue(NAN) {};
        Operand(const int & f) : numericOp(NE_FLUENT), fluentValue(f), constantValue(NAN) {};
        Operand(const double & c) : numericOp(NE_CONSTANT), fluentValue(-1), constantValue(c) {};
        Operand(const string & s) : numericOp(NE_VIOLATION), fluentValue(-1), constantValue(NAN), isviolated(s) {};
    };

    static double calculateRHS(const list<Operand> & formula, vector<double> & fluents);
    static pair<double, bool> constRHS(const list<Operand> & formula);
    
    class Constraint {
        
        public:            
            friend class PreferenceFSA;
            friend class PreferenceHandler;
            
            #ifndef NDEBUG
            list<Literal*> debug_goal;
            list<Literal*> debug_trigger;
            
            list<pair<int,int> > debug_goalRPGNum;
            list<pair<int,int> > debug_triggerRPGNum;
            #endif
        public:
            
            string name;
            
            VAL::constraint_sort cons;
            
            VAL::FastEnvironment * fe;
            
            VAL::goal * parsed_goal;
            VAL::goal * parsed_trigger;
            
            PreferenceData * d;
            
            double cost;
            bool neverTrue;
            
            pair<int,Planner::time_spec> attachedToOperator;
      
            double deadline;
            double from;
            
            Constraint() : parsed_goal(0), parsed_trigger(0), d(0), cost(0.0), neverTrue(false), attachedToOperator(make_pair(-1, Planner::E_AT)), deadline(0.0), from(0.0) {};
            Constraint(const string & n) : name(n), parsed_goal(0), parsed_trigger(0), d(0), cost(0.0), neverTrue(false), attachedToOperator(make_pair(-1,Planner::E_AT)), deadline(0.0), from(0.0) {};
            
    };
    
    class NumericEffect
    {

    public:

        int fluentIndex;
        VAL::assign_op op; // how to update given fluent index (add to it, assign to it, etc.)
        list<Operand> formula; // formula in postfix notation
        NumericEffect(const VAL::assign_op & opIn, const int & fIn, VAL::expression * formulaIn, VAL::FastEnvironment * f, VAL::TypeChecker * t = 0);
        double applyEffect(vector<double> & fluents) const;
        void display(ostream & o) const;
    };

    class NumericPrecondition
    {

    public:
        VAL::comparison_op op; // how to compare given fluent index to calculated RHS
        list<Operand> LHSformula; // formula for LHS in postfix notation
        list<Operand> RHSformula; // formula for RHS postfix notation
        bool valid;
        bool polarity; // false = it needs to be negated
        NumericPrecondition(const VAL::comparison_op & opIn, VAL::expression * LHSformulaIn, VAL::expression * RHSformulaIn, VAL::FastEnvironment * f, VAL::TypeChecker * t = 0, const bool polarity=true);
        bool isSatisfied(vector<double> & fluents) const;
        void display(ostream & o) const;

        double evaluateRHS(vector<double> & fluentTable) const;
        pair<double, bool> constRHS() const;
    };

    class ArtificialVariable
    {

    public:
        int ID;
        int size;
        vector<double> weights;
        vector<int> fluents;
        double constant;

        double maxNeed;

        bool desirable;
        bool undesirable;
        
        ArtificialVariable() : ID(-1), size(0), constant(0.0), maxNeed(-DBL_MAX), desirable(false), undesirable(false) {};
        ArtificialVariable(const int & id, const int & s, const vector<double> & w, const vector<int> & f, const double & d, const double & maxIn, const bool & des, const bool & undes)
         : ID(id), size(s), weights(w), fluents(f), constant(d), maxNeed(maxIn), desirable(des), undesirable(undes) {};

        double evaluate(const vector<double> & fluentTable) {
            double toReturn = constant;
            for (int i = 0; i < size; ++i) {
                if (fluents[i] < 0) {
                    return std::numeric_limits<double>::signaling_NaN();
                }
                toReturn += weights[i] * fluentTable[fluents[i]];
            }
            return toReturn;
        };

        double evaluateGradient(const vector<double> & fluentTable) {
            double toReturn = 0.0;
            for (int i = 0; i < size; ++i) {
                if (fluents[i] < 0) {
                    return std::numeric_limits<double>::signaling_NaN();
                }
                toReturn += weights[i] * fluentTable[fluents[i]];
            }
            return toReturn;
        };
        
        double evaluateWCalculate(const vector<double> & fluentTable, const int & pneCount);
        double evaluateWCalculate(const vector<double> & minFluentTable, const vector<double> & maxFluentTable, const int & pneCount) const;

        bool operator <(const ArtificialVariable & v) const;
        void display(ostream & o) const;

        void updateMax(const double & m) {
            if (m > maxNeed) maxNeed = m;
        }
    };

    class RPGNumericPrecondition
    {

    public:
        int ID;
        bool desirable;
        bool undesirable;

        int LHSVariable;
        double LHSConstant;

        VAL::comparison_op op;

        int RHSVariable;
        double RHSConstant;

        RPGNumericPrecondition() : ID(-1), desirable(false), undesirable(false), LHSVariable(-1), LHSConstant(0.0), op(VAL::E_GREATEQ), RHSVariable(-1), RHSConstant(0.0) {};
        RPGNumericPrecondition(const int & i, const bool & d, const bool & ud, const int & lv, const double & lw, const VAL::comparison_op & o, const double & rw)
            : ID(i), desirable(d), undesirable(ud),  LHSVariable(lv), LHSConstant(lw), op(o), RHSVariable(-1), RHSConstant(rw) {
            
                assert(op == VAL::E_GREATER || op == VAL::E_GREATEQ);
        };

        bool isSatisfied(const vector<double> & maxFluents) const {            
            if (LHSVariable < 0) return false;
            
            const double lv = maxFluents[LHSVariable];
            if (lv == std::numeric_limits<double>::signaling_NaN()) return false;
            
            if (op == VAL::E_GREATER) {                
                return (lv > RHSConstant);
            } else {
                return (lv >= RHSConstant);
            }
        };

        bool isSatisfiedWCalculate(const vector<double> & maxFluents) const;
        bool isSatisfiedWCalculate(const vector<double> & minFluents, const vector<double> & maxFluents) const;
        bool canBeUnsatisfiedWCalculate(const vector<double> & minFluents, const vector<double> & maxFluents) const;
        
        bool operator <(const RPGNumericPrecondition & r) const;

        void display(ostream & o) const;

    };

    static void markRPGNumericPreconditionDesirable(const int & i);
    static void markRPGNumericPreconditionUndesirable(const int & i);
    
    class RPGNumericEffect
    {
    public:
        int ID;

        int fluentIndex;

        bool isAssignment; // if it's an assignmentOp - assume it's a += otherwise

        vector<double> weights;
        vector<int> variables;

        double constant;

        int size;

        bool canEverHappen;
        
        RPGNumericEffect() : ID(-1), fluentIndex(-1), isAssignment(false), constant(NAN), size(-1), canEverHappen(true) {};

        RPGNumericEffect(const int & idIn, const int & fluent, const bool & ass,
                         const vector<double> & weightsIn, const vector<int> & vars, const int & s,
                         const double & con) :
                ID(idIn), fluentIndex(fluent), isAssignment(ass),
                weights(weightsIn), variables(vars), constant(con), size(s), canEverHappen(true) {};

        double evaluate(const vector<double> & maxFluents, const double & minDur, const double & maxDur) const {            
            double toReturn = constant;
            for (int i = 0; i < size; ++i) {
                if (variables[i] >= 0) {
                    const double val = maxFluents[variables[i]];
                    if (val == DBL_MAX) return DBL_MAX;
                    if (val == -DBL_MAX) return -DBL_MAX;
                    toReturn += weights[i] * val;
                } else if (variables[i] == -3) {
                    double lw = weights[i];
                    double toUse = maxDur;
                    if (lw < 0) {
                        lw *= -1.0;
                        toUse = -minDur;
                    }
                    if (toUse == DBL_MAX) return DBL_MAX;
                    if (toUse == -DBL_MAX) return -DBL_MAX;
                    toReturn += lw * toUse;
                } else if (variables[i] == -19) {
                    double lw = weights[i];
                    double toUse = (minDur == 0.0 ? 0.0 : -minDur);
                    #ifndef NDEBUG
                    if (lw < 0) {                        
                        static bool printedMessage = false;
                        if (printedMessage == false) {
                            std::cerr << "Warning: negative weight attached to negative duration term - is this intentional?\n";
                            printedMessage = true;
                        }
                    }
                    #endif
                    if (lw < 0) {
                        lw *= -1.0;
                        toUse = maxDur;
                    }
                    if (toUse == DBL_MAX) return DBL_MAX;
                    if (toUse == -DBL_MAX) return -DBL_MAX;
                    toReturn += lw * toUse;
                } else {
                    std::cerr << "Error: asked to evaluate formula containing term with fluent ID " << variables[i] << ", which doesn't represent either a non-static fluent or the duration term -3 or -19\n";
                    assert(false);
                }
            }
            return toReturn;
        };

        double evaluateMin(const vector<double> & maxFluents, const double & minDur, const double & maxDur) const {            
            static const int pneCount = RPGBuilder::getPNECount();
            double toReturn = constant;
            for (int i = 0; i < size; ++i) {
                if (variables[i] >= pneCount) {
                    const double val = maxFluents[variables[i] - pneCount];
                    if (val == DBL_MAX) return -DBL_MAX;
                    if (val == -DBL_MAX) return DBL_MAX;
                    toReturn -= weights[i] * val;                                        
                } else if (variables[i] >= 0) {
                    const double val = maxFluents[variables[i] + pneCount];
                    if (val == DBL_MAX) return -DBL_MAX;
                    if (val == -DBL_MAX) return DBL_MAX;
                    toReturn -= weights[i] * val;
                } else if (variables[i] == -3) {
                    double lw = weights[i];
                    double toUse = minDur;
                    if (lw < 0) {
                        lw *= -1.0;
                        toUse = -maxDur;
                    }
                    if (toUse == DBL_MAX) return -DBL_MAX;
                    if (toUse == -DBL_MAX) return DBL_MAX;
                    toReturn -= lw * toUse;
                } else if (variables[i] == -19) {
                    double lw = weights[i];
                    double toUse = -maxDur;
                    #ifndef NDEBUG
                    if (lw < 0) {                        
                        static bool printedMessage = false;
                        if (printedMessage == false) {
                            std::cerr << "Warning: negative weight attached to negative duration term - is this intentional?\n";
                            printedMessage = true;
                        }
                    }
                    #endif
                    if (lw < 0) {
                        lw *= -1.0;
                        toUse = -minDur;
                    }
                    if (toUse == DBL_MAX) return -DBL_MAX;
                    if (toUse == -DBL_MAX) return DBL_MAX;
                    toReturn -= lw * toUse;
                } else {
                    std::cerr << "Error: asked to evaluate formula containing term with fluent ID " << variables[i] << ", which doesn't represent either a non-static fluent or the duration term -3 or -19\n";
                    assert(false);
                }
            }
            return toReturn;
        };

        pair<double, double> applyEffectMinMax(const vector<double> & minFluents, const vector<double> & maxFluents, const double & minDur, const double & maxDur);

        bool operator <(const RPGNumericEffect & e) const;

        void display(ostream & o) const;


    };

    /** @brief A class defining a single duration constraint, in LNF. */
    class DurationExpr
    {

    public:
        /** @brief The weights of the variables in the duration expression */
        vector<double> weights;
        
        #ifdef STOCHASTICDURATIONS
        /** @brief The IDs of the variables in the duration expression.
         *
         *  The first of each pair, if not equal to -1, is an index into the state vector of variables.
         *  Otherwise, the second entry is used.
         */
        vector<pair<int, PNE*> > variables;
        #else
        /** @brief The IDs of the variables in the duration expression.  @see RPGBuilder::getPNE */
        vector<int> variables;
        #endif
        
        /** The comparison operator for this duration expression.  Is one of:
         *  - <code>VAL::E_GREATEQ</code> for <code>(>= ?duration ...)</code>
         *  - <code>VAL::E_GREATER</code> for <code>(> ?duration ...)</code>
         *  - <code>VAL::E_EQUALS</code> for <code>(= ?duration ...)</code>
         *  - <code>VAL::E_LESS</code> for <code>(< ?duration ...)</code>
         *  - <code>VAL::E_LESSEQ</code> for <code>(<= ?duration ...)</code>
         */
        VAL::comparison_op op;

        /** @brief The constant term for the duration expression */
        double constant;

        DurationExpr() : weights(), variables(), constant(0.0) {};
        
        /** @brief Create a duration expression, with unknown operator and empty weights and variables.
         *
         * @param d  The constant term for the duration expression
         */
        DurationExpr(const double & d) : weights(0), variables(0), constant(d) {} ;


        /**
         * Evaluate the minimum possible value that satisfies this duration expression,
         * given the provided lower- and upper-bounds on the values of the task numeric
         * variables.
         *
         * @param minVars  Minimum values of the task variables
         * @param maxVars  Maximum values of the task variables
         * 
         * @return  The lowest permissible duration, according to this duration expression.
         */
        double minOf(const vector<double> & minVars, const vector<double> & maxVars);
        
        /**
         * Evaluate the maximum possible value that satisfies this duration expression,
         * given the provided lower- and upper-bounds on the values of the task numeric
         * variables.
         *
         * @param minVars  Minimum values of the task variables
         * @param maxVars  Maximum values of the task variables
         * 
         * @return  The greatest permissible duration, according to this duration expression.
         */
        double maxOf(const vector<double> & minVars, const vector<double> & maxVars);
    };

    /** @brief A class containing all the duration constraints imposed on an action. */
    class RPGDuration
    {

    public:
        /** The fixed durations of the action, those of the form <code>(= ?duration ...)</code> */
        list<DurationExpr *> fixed;

        /** The minimum durations of the action, those of the form <code>(>= ?duration ...)</code> or <code>(> ?duration ...)</code> */        
        list<DurationExpr *> min;
        
        /** The maximum durations of the action, those of the form <code>(<= ?duration ...)</code> or <code>(< ?duration ...)</code> */        
        list<DurationExpr *> max;

//      LPDuration() : fixed(0), min(0), max(0) {};
        RPGDuration(list<DurationExpr *> & eq, list<DurationExpr *> & low, list<DurationExpr *> & high)
                : fixed(eq), min(low), max(high) {};

        /**
         * Return one of the lists of durations contained in the object.
         * 
         * @param i  Which list of durations to return:
         *           - 0 returns the <code>fixed</code> duration expressions;
         *           - 1 returns the <code>min</code> duration expressions;
         *           - 2 returns the <code>max</code> duration expressions.
         *
         * @return  The requested list of duration expressions.
         */
        const list<DurationExpr *> & operator[](const int & i) const {
            switch (i) {
                case 0: {
                    return fixed;
                }
                case 1: {
                    return min;
                }
                case 2: {
                    return max;
                }
            }
            std::cerr << "Fatal internal error: duration expression index should be in the range 0 to 2, inclusive\n";
            exit(1);
        }
    };


    /**
     *  Class to represent the 'action' whose application corresponds to a timed initial literal.
     */
    class FakeTILAction
    {

    public:
        /** The time-stamp of the timed initial literal */
        const double duration;

        /** The facts added at the specified time */
        list<Literal* > addEffects;

       
        list<Literal* > abstractedAddEffects;
                
        /** The facts deleted at the specified time */
        list<Literal* > delEffects;

        list<Literal* > abstractedDelEffects;
        /**
         *   Add the specified add and delete effects to the timed initial literal action.  Is used when
         *   multiple TILs are found at a given time-stamp.
         *
         *   @param adds  Add effects to include in this TIL action
         *   @param dels  Delete effects to include in this TIL action
         */
        void mergeIn(const LiteralSet & adds, const LiteralSet & dels) {

            {
                LiteralSet::iterator lsItr = adds.begin();
                const LiteralSet::iterator lsEnd = adds.end();

                for (; lsItr != lsEnd; ++lsItr) {
                    addEffects.push_back(*lsItr);
                }
            }

            {
                LiteralSet::iterator lsItr = dels.begin();
                const LiteralSet::iterator lsEnd = dels.end();

                for (; lsItr != lsEnd; ++lsItr) {
                    delEffects.push_back(*lsItr);
                }
            }
        }

        /**
         *   Constructor for an action corresponding to a Timed Initial Literal.
         *
         *   @param dur  The time at which the timed initial occurs
         *   @param adds The facts added at time <code>dur</code>
         *   @param dels The facts deleted at time <code>dur</code>
         */
        FakeTILAction(const double & dur, const LiteralSet & adds, const LiteralSet & dels)
                : duration(dur) {
            mergeIn(adds, dels);
        }

    };




    class KShotFormula
    {

    public:
        KShotFormula() {};
        virtual int getLimit(const MinimalState & s) const = 0;
        virtual int getOptimisticLimit(const MinimalState & s) const = 0;
        virtual ~KShotFormula() {};
    };

    class UnlimitedKShotFormula : public KShotFormula
    {

    public:
        UnlimitedKShotFormula() : KShotFormula() {};
        virtual int getLimit(const MinimalState &) const {
            return INT_MAX;
        };
        virtual int getOptimisticLimit(const MinimalState &) const {
            return INT_MAX;
        };
    };

    class OneShotKShotFormula : public KShotFormula
    {

    private:
        list<int> watchedLiterals;
    public:
        OneShotKShotFormula(list<int> & toWatch) : KShotFormula(), watchedLiterals(toWatch) {};
        virtual int getLimit(const MinimalState & s) const;
        virtual int getOptimisticLimit(const MinimalState & s) const;
    };

    struct ShotCalculator {

        int variable;
        double greaterThan;
        double decreaseBy;

        ShotCalculator(const int & v, const double & g, const double & d) : variable(v), greaterThan(g), decreaseBy(d) {};
    };

    class KShotKShotFormula : public KShotFormula
    {

    private:
        list<ShotCalculator> formulae;
    public:
        KShotKShotFormula(list<ShotCalculator> & c) : KShotFormula(), formulae(c) {};
        virtual int getLimit(const MinimalState & s) const;
        virtual int getOptimisticLimit(const MinimalState & s) const;
    };

    /** A class defining the linear continuous effects of an action */
    class LinearEffects
    {

    public:
        /**
         * A single linear continuous numeric effect expression.  The gradient of the
         * effect is stored in LNF.
         */
        struct EffectExpression {
            /** The weights for the variables in the LNF expression of the gradient. */
            vector<double> weights;
            
            /** The variables in the LNF expression of the gradient. */
            vector<int> variables;

            /** The constant term of the LNF expression of the gradient. */
            double constant;

            /**
             * Constructor for a constant-gradient linear continuous effect
             *
             * @param g  The gradient of the effect
             */
            EffectExpression(const double & g) : weights(0), variables(0), constant(g) {};
        };

//      vector<double> durations;

        /** The IDs of the variables upon which this action has continuous effects.  @see RPGBuilder::getPNE */
        vector<int> vars;
        
        /**
         * The effects themselves. Each entry is a vector describing the effect upon the corresponding
         * variable in <code>vars</code>.  For now, at most one such vector exists, but in the future
         * this may change if support for piecewise-linear effects is added.
         */        
        vector<vector<EffectExpression> > effects;

//      double totalDuration;

        /**
         *  The number of divisions for the continuous numeric effects of the action.  At present this
         *  is always 1, i.e. the gradients of the effects remain fixed across the execution of the
         *  action, but this may change if support for piecewise-linear effects is added.
         */
        int divisions;

    };

    class Metric
    {

    public:
        bool minimise;

        list<double> weights;
        list<int> variables;
        double constant;

        Metric(const bool & m) : minimise(m), constant(0.0) {};

    };

    static Metric * theMetric;
    static set<int> metricVars;


    /** @brief Remove obvious duplicates from a list of constraints
     * 
     * This is used in preprocessing to eliminate duplicate constraints.  For each set of identical constraints,
     * one is kept, with its name set to the concatenation of all the constraints it represents, separated by spaces.
     * The <code>outputNameMap</code> maps all the exemplars to this, so it subsequently accrues their sum cost.
     * 
     * @param input  The list of constraints
     * @param outputNameMap  Return-by-reference: a mapping from constraint names to the IDs in the output vector
     * @param output         Return-by-reference: list of constraints without duplicates.
     */
    static void eliminateDuplicateConstraints(const list<RPGBuilder::Constraint> & input,
                                              map<string,list<int> > & outputNameMap,
                                              vector<RPGBuilder::Constraint> & output,
//                                               map<int, Literal*> * noteWithinPreferences = 0,
                                              VAL::TypeChecker * t = 0);
    
    /**
     *  Class to represent a conditional effect.  The class is capable of storing more fields than can
     *  currently be used by the planner - currently, only conditional effects upon metric tracking
     *  variables are supported, conditional on either propositions controlled exclusively by
     *  timed initial literals, or on numeric values.
     */
    class ConditionalEffect
    {

    private:

        /**
         * Propositional preconditions on the conditional effect.  Each entry is pair: the first
         * entry denotes the fact that must hold, the second denotes the time at which it must
         * hold (either <code>VAL::E_AT_START</code>, <code>VAL::E_OVER_ALL</code> or <code>VAL::E_AT_END</code>.
         * For now, the literal must be controlled exclusively by timed initial literals.
         */
        list<pair<Literal*, Planner::time_spec> > propositionalConditions;

        /**
         * Numeric preconditions on the conditional effect.  Each entry is pair: the first
         * entry denotes an entry in <code>RPGBuilder::rpgNumericPreconditions</code>; the second denotes the time at which it must
         * hold (either <code>VAL::E_AT_START</code>, <code>VAL::E_OVER_ALL</code> or <code>VAL::E_AT_END</code>.
         */
        list<pair<int, Planner::time_spec> > numericPreconditions;

        /**
         * Conditional numeric effects.  For now, these must act exclusively on metric tracking variables.
         * Each entry is pair: the first is an index in <code>RPGBuilder::rpgNumericEffects</code>; the second denotes the time at which
         * it occurs (either <code>VAL::E_AT_START</code> or <code>VAL::E_AT_END</code>).
         */
        list<pair<int, Planner::time_spec> > numericEffects;

        /** Conditional propositional add effects.  For now, must be empty. */
        list<pair<Literal*, Planner::time_spec> > propositionalAddEffects;
        /** Conditional propositional delete effects.  For now, must be empty. */
        list<pair<Literal*, Planner::time_spec> > propositionalDeleteEffects;

    public:
        ConditionalEffect() {
        }

        void addCondition(Literal * const l, const Planner::time_spec & t, const int &
#ifndef NDEBUG
                                                                                   actID
#endif                          
        ) {
            assert(t == Planner::E_AT_START || RPGBuilder::actionIsDurative(actID));
            propositionalConditions.push_back(make_pair(l, t));
        }

        void addCondition(const int & p, const Planner::time_spec & t, const int &
#ifndef NDEBUG
                                                                               actID
#endif                          
        ) {
            assert(t == Planner::E_AT_START || RPGBuilder::actionIsDurative(actID));
            numericPreconditions.push_back(make_pair(p, t));
        }

        void addNumericEffect(const int & p, const Planner::time_spec & t, const int &
#ifndef NDEBUG
                                                                                   actID
#endif                          
        ) {
            assert(t == Planner::E_AT_START || RPGBuilder::actionIsDurative(actID));
            numericEffects.push_back(make_pair(p, t));
        }

        void addAddEffect(Literal * const l, const Planner::time_spec & t) {
            propositionalAddEffects.push_back(make_pair(l, t));
        }

        void addDeleteEffect(Literal * const l, const Planner::time_spec & t) {
            propositionalDeleteEffects.push_back(make_pair(l, t));
        }

        const list<pair<Literal*, Planner::time_spec> > & getPropositionalConditions() const {
            return propositionalConditions;
        }

        const list<pair<int, Planner::time_spec> > & getNumericPreconditions() const {
            return numericPreconditions;
        }

        list<pair<int, Planner::time_spec> > & getEditableNumericEffects() {
            return numericEffects;
        }

        const list<pair<int, Planner::time_spec> > & getNumericEffects() const {
            return numericEffects;
        }

        const list<pair<Literal*, Planner::time_spec> > & getPropositionalAddEffects() const {
            return propositionalAddEffects;
        }

        const list<pair<Literal*, Planner::time_spec> > & getPropositionalDeleteEffects() const {
            return propositionalDeleteEffects;
        }

        void makeNonTemporal();

    };

    
    class IntegralContinuousEffect {
        
    private:

        int parentAction;
        
        int minimalOutcome;
        int outcomes;
        
        int leftPrecondition;
        Planner::time_spec leftPreconditionTS;
        double leftPreconditionDifference;
        
        int rightPrecondition;
        double rightPreconditionDifference;
        
        list<pair<int,double> > leftStartEffectsWithDifference;
        list<pair<int,double> > leftEndEffectsWithDifference;

        vector<list<int> > startEffectsForOutcome;
        vector<list<int> > endEffectsForOutcome;
        
        list<int> relaxedStartEffects; // the left- and right-most outcome for each start effect
        list<int> relaxedEndEffects;   // the left- and right-most outcome for each end effect

        bool calculateRelaxedOutcomes;
                
    public:
        
        IntegralContinuousEffect(const int & act, const int & oc,
                                 const int & lp, const Planner::time_spec & ts, const double & lpd,
                                 const int & rp, const double & rpd)
            : parentAction(act), minimalOutcome(0), outcomes(oc),
              leftPrecondition(lp), leftPreconditionTS(ts), leftPreconditionDifference(lpd),
              rightPrecondition(rp), rightPreconditionDifference(rpd),
              startEffectsForOutcome(outcomes + 1),
              endEffectsForOutcome(outcomes + 1) {        
        }
        
        void addStartEffectsForOutcome(const int & i, const list<int> & effs) {
            startEffectsForOutcome[i] = effs;
        }
        
        void addEndEffectsForOutcome(const int & i, const list<int> & effs) {
            endEffectsForOutcome[i] = effs;
        }
        
        void addStartEffect(const int & eff, const double & diff, const int & rightEff) {
            leftStartEffectsWithDifference.push_back(make_pair(eff,diff));
            relaxedStartEffects.push_back(eff);
            relaxedStartEffects.push_back(rightEff);
        }
        
        void addEndEffect(const int & eff, const double & diff, const int & rightEff) {
            leftEndEffectsWithDifference.push_back(make_pair(eff,diff));
            relaxedEndEffects.push_back(eff);
            relaxedEndEffects.push_back(rightEff);
        }                        
        
        bool satisfied(const Planner::time_spec & ts, const vector<double> & min, const vector<double> & max,
                       const double & minDur, const double & maxDur, pair<int,int> & outcomeBracket) const;
        
        const list<pair<int,double> > & getLeftStartEffects() const {
            return leftStartEffectsWithDifference;
        }
        
        const list<pair<int,double> > & getLeftEndEffects() const {
            return leftEndEffectsWithDifference;
        }

        void workOutSuitablePreconditionRelaxation();
        
        void getRelaxedStartEffects(list<int> & writeTo, const double & currLayer) const;
        
        void getRelaxedEndEffects(list<int> & writeTo, const double & currLayer) const;
        
        const Planner::time_spec & getTS() const {
            return leftPreconditionTS;
        }
        
        const int & getLeftPrecondition() const {
            return leftPrecondition;
        }
        
        const double & getLeftPreconditionDifference() const {
            return leftPreconditionDifference;
        }
        
        const int & getRightPrecondition() const {
            return rightPrecondition;
        }
        
        const double & getRightPreconditionDifference() const {
            return rightPreconditionDifference;
        }
        
        const int & getIntegerLB() const {
            return minimalOutcome;
        }
        
        const int & getIntegerUB() const {
            return outcomes;
        }
    };
    
    class NoDuplicatePair
    {

    protected:

        list<Literal*> * first;
        LiteralSet * second;

    public:

        NoDuplicatePair()
                : first((list<Literal*>*)0), second((LiteralSet*)0) {
        }

        NoDuplicatePair(list<Literal*> * const listIn, LiteralSet* const setIn)
                : first(listIn), second(setIn) {
        }

        void push_back(Literal* const toAdd) {
            if (second->insert(toAdd).second) {
                first->push_back(toAdd);
            }
        }

        Literal* back() const {
            return first->back();
        }

        bool operator!() const {
            return (!first);
        }

        bool empty() const {
            if (!first) return true;
            return (first->empty());
        }

        template<typename T>
        void insert(T itr, const T & itrEnd) {
            for (; itr != itrEnd; ++itr) {
                push_back(*itr);
            }
        };
    };


    class ProtoConditionalEffect
    {

    public:

        list<Literal*> startPrec;
        LiteralSet startPrecSet;
        list<Literal*> inv;
        LiteralSet invSet;
        list<Literal*> endPrec;
        LiteralSet endPrecSet;

        list<Literal*> startNegPrec;
        LiteralSet startNegPrecSet;
        list<Literal*> negInv;
        LiteralSet negInvSet;
        list<Literal*> endNegPrec;
        LiteralSet endNegPrecSet;


        list<RPGBuilder::NumericPrecondition> startPrecNumeric;
        list<RPGBuilder::NumericPrecondition> invNumeric;
        list<RPGBuilder::NumericPrecondition> endPrecNumeric;

        list<Literal*> startAddEff;
        LiteralSet startAddEffSet;
        list<Literal*> startDelEff;
        LiteralSet startDelEffSet;
        list<RPGBuilder::NumericEffect> startNumericEff;

        list<Literal*> endAddEff;
        LiteralSet endAddEffSet;
        list<Literal*> endDelEff;
        LiteralSet endDelEffSet;
        list<RPGBuilder::NumericEffect> endNumericEff;

        set<int> startNumericEffsOnVar;
        set<int> endNumericEffsOnVar;
    };

    struct Guarded {
        set<int> guardedConditionVars;
        set<int> guardedEffectVars;
    };
   
    
protected:

    friend class NNFUtils;
    friend class PreferenceHandler;
    

    static bool RPGdebug;
    static bool problemIsNotTemporal;
// static vector<list<pair<int, double> > > actionsToNegativeNumericEffects;
// static vector<list<pair<int, double> > > negativeNumericEffectsToActions;

    static vector<vector<int> > actionsToStartPreferences;
    static vector<vector<int> > actionsToEndPreferences;
    
    /** @brief Number of constraints + number of preferences */
    static int taskPrefCount;
    
    /** @brief Number of constraints */
    static int taskConstraintCount;
    
    
    static int preconditionPrefCount;
    
    
    static vector<list<pair<int, Planner::time_spec> > > preconditionsToActions;
    static vector<list<pair<int, Planner::time_spec> > > negativePreconditionsToActions;

    static list<pair<int, Planner::time_spec> > preconditionlessActions;
    static list<pair<int, Planner::time_spec> > onlyNumericPreconditionActions;

    static vector<list<Literal*> > actionsToStartPreconditions;
    static vector<list<Literal*> > actionsToInvariants;
    static vector<list<Literal*> > actionsToEndPreconditions;

    static vector<list<Literal*> > actionsToStartNegativePreconditions;
    static vector<list<Literal*> > actionsToNegativeInvariants;
    static vector<list<Literal*> > actionsToEndNegativePreconditions;


    static vector<LiteralSet> actionsToEndOneShots;

    static vector<list<Literal*> > actionsToStartEffects;
    static vector<list<Literal*> > actionsToStartNegativeEffects;
    static vector<list<Literal*> > actionsToEndEffects;
    static vector<list<Literal*> > actionsToEndNegativeEffects;

    static vector<list<pair<int, Planner::time_spec> > > effectsToActions;
    static vector<list<pair<int, Planner::time_spec> > > negativeEffectsToActions;

    static vector<double> actionsToMinDurations;
    static vector<double> actionsToMaxDurations;
    static vector<list<NumericPrecondition*> > fixedDurationExpressions;
    static vector<list<NumericPrecondition*> > minDurationExpressions;
    static vector<list<NumericPrecondition*> > maxDurationExpressions;

    // one for each instantiated action; within that - one for each point along the action, minus the last
    // entry [a][0] specifies duration between a0 and a1
    static vector<vector<RPGDuration*> > rpgDurationExpressions;
    static vector<double> nonTemporalDuration;


    static vector<LinearEffects*> linearDiscretisation;

    static vector<list<ProtoConditionalEffect*> > actionsToRawConditionalEffects;

    static vector<list<NumericPrecondition> > actionsToStartNumericPreconditions;
    static vector<list<NumericPrecondition> > actionsToNumericInvariants;
    static vector<list<NumericPrecondition> > actionsToEndNumericPreconditions;

    static vector<list<NumericEffect> > actionsToStartNumericEffects;
    static vector<list<NumericEffect> > actionsToEndNumericEffects;

    static vector<list<int> > actionsToRPGNumericStartPreconditions;
    static vector<list<int> > actionsToRPGNumericInvariants;
    static vector<list<int> > actionsToRPGNumericEndPreconditions;

    static vector<list<int> > actionsToRPGNumericStartEffects;
    static vector<list<int> > actionsToRPGNumericEndEffects;

    static vector<list<ConditionalEffect> > actionsToConditionalEffects;

    static map<int, list<IntegralContinuousEffect> > actionsToIntegralConditionalEffects;
// static vector<list<pair<int, double> > > numericPreconditionsToActions;
// static vector<list<pair<int, double> > > actionsToNumericPreconditions;

    static vector<int> initialUnsatisfiedStartPreconditions;
    static vector<int> initialUnsatisfiedInvariants;
    static vector<int> initialUnsatisfiedEndPreconditions;

    static vector<EpsilonResolutionTimestamp> achievedInLayer;
    static vector<EpsilonResolutionTimestamp> achievedInLayerReset;
    static vector<pair<int, Planner::time_spec> > achievedBy;
    static vector<pair<int, Planner::time_spec> > achievedByReset;

    static vector<EpsilonResolutionTimestamp> negativeAchievedInLayer;
    static vector<EpsilonResolutionTimestamp> negativeAchievedInLayerReset;
    static vector<pair<int, Planner::time_spec> > negativeAchievedBy;
    static vector<pair<int, Planner::time_spec> > negativeAchievedByReset;

    static vector<EpsilonResolutionTimestamp> numericAchievedInLayer;
    static vector<EpsilonResolutionTimestamp> numericAchievedInLayerReset;
    static vector<ActionFluentModification*> numericAchievedBy;
    static vector<ActionFluentModification*> numericAchievedByReset;

    static vector<EpsilonResolutionTimestamp> negativeNumericAchievedInLayer;
    static vector<EpsilonResolutionTimestamp> negativeNumericAchievedInLayerReset;
    static vector<ActionFluentModification*> negativeNumericAchievedBy;
    static vector<ActionFluentModification*> negativeNumericAchievedByReset;
    
    
// static vector<int> increasedInLayer;
// static vector<pair<int, double> > increasedBy;
// static vector<pair<int, double> > increasedReset;

    static vector<instantiatedOp*> instantiatedOps;

    static vector<Literal*> literals;
    static vector<PNE*> pnes;
    static vector<pair<bool, bool> > globalStaticLiterals;

    static vector<vector<Literal*> > propositionGroups;
    static vector<vector<int> > literalToPropositionGroupID;
    
    static vector<RPGNumericPrecondition> rpgNumericPreconditions;
    static vector<RPGNumericEffect> rpgNumericEffects;
    static vector<list<pair<int, Planner::time_spec> > > rpgNumericEffectsToActions;
    static vector<list<pair<int, Planner::time_spec> > > rpgNumericPreconditionsToActions;

    static vector<ArtificialVariable> rpgArtificialVariables;
    static vector<list<int> > rpgVariableDependencies;

    static vector<list<int> > rpgArtificialVariablesToPreconditions;
    static vector<list<int> > rpgNegativeVariablesToPreconditions;
    static vector<list<int> > rpgPositiveVariablesToPreconditions;

    static vector<int> initialUnsatisfiedNumericStartPreconditions;
    static vector<int> initialUnsatisfiedNumericInvariants;
    static vector<int> initialUnsatisfiedNumericEndPreconditions;

    static vector<list<pair<int, Planner::time_spec> > > processedPreconditionsToActions;
    static vector<list<pair<int, Planner::time_spec> > > processedNegativePreconditionsToActions;
    static vector<list<Literal*> > actionsToProcessedStartPreconditions;
    static vector<list<Literal*> > actionsToProcessedStartNegativePreconditions;
    static vector<int> initialUnsatisfiedProcessedStartPreconditions;
    static vector<list<int> > realVariablesToRPGEffects;

    static vector<list<pair<int, Planner::time_spec> > > processedRPGNumericPreconditionsToActions;

    static vector<list<NumericPrecondition> > actionsToProcessedStartNumericPreconditions;

    /** @brief The literal goals. */
    static list<Literal*> literalGoals;
    
    /** @brief Hard deadlines on literal goals.
     * 
     * Each entry is the hard deadline associated with the corresponding goal in <code>literalGoals<code>.
     */
    static list<double> literalGoalDeadlines;
    
    /** @brief Soft deadlines on literals
     * 
     * The map is from a fact, to the within preferences that depend upon it.
     */
    static map<int, list<int> > factRelevantToWithinPreferences;
    
    static map<int, list<int> > negativeFactRelevantToWithinPreferences;
    
    
    /** @brief A map from literal state IDs to their goal index.
     *
     *
     * This can be used, for instance, to find the soft deadlines associated with a goal:
     * use this map to turn a literal into an index, and then consult <code>literalGoalSoftDeadlines<code>
     * to find the soft deadlines on the goal with that index.
     */
    static map<int, int> literalsToGoalIndex;
    
    static list<NumericPrecondition> numericGoals;
    static list<double> numericGoalDeadlines;
    static list<pair<int, int> > numericRPGGoals;
    static list<double> rpgNumericGoalDeadlines;

    static vector<Constraint> preferences;
    //static map<int, Literal*> preferencesThatAreSoftDeadlines;
    static map<string, list<int> > prefNameToID;
    static map<string,int> prefNameToNumberOfTimesDefinitelyViolated;
    static double permanentPreferenceViolations;
    
    //static vector<Constraint> constraints;

    static vector<list<int> > actionsToProcessedStartRPGNumericPreconditions;
    static vector<int> initialUnsatisfiedProcessedStartNumericPreconditions;

    static vector<list<int> > mentionedInFluentInvariants;

    static list<FakeTILAction> timedInitialLiterals;
    static vector<FakeTILAction*> normalTimedInitialLiteralsVector;

    static bool definedNonAbstractedTILs;
    static vector<FakeTILAction*> nonAbstractedTimedInitialLiteralsVector;
    
    static list<FakeTILAction> optimisationTimedInitialLiterals;
    static vector<FakeTILAction*> optimisationTimedInitialLiteralsVector;

    static vector<FakeTILAction*> allTimedInitialLiteralsVector;
    
    static map<int, set<int> > tilsThatAddFact;
    static map<int, set<int> > tilsThatDeleteFact;

    static vector<KShotFormula*> kShotFormulae;
    static vector<bool> selfMutexes;
    static vector<bool> oneShotLiterals;

    static vector<double> maxNeeded;
    static vector<bool> definedValueInInitialState;
    
    /** @brief Semaphore facts and the PNEs they guard.
     *
     * @see <code>RPGBuilder::findSemaphoreFacts</code>.
     */
    static map<int, Guarded> semaphoreFacts;
    
    /** @brief  A map from action IDs to a fact that renders it uninteresting to apply. */
    static map<int, int> uninterestingnessCriteria;
    
    /** @brief  The IDs of concurrent redundant actions. */
    static set<int> concurrentRedundantActions;
    
    /** Facts which are manipulated by effects, but never appear in preconditions/the goal. */
    static LiteralSet factsWithOnlyPointlessEffects;
    
    /** The pointless start effects of each action. */
    static map<int, map<Literal*, pointless_effect, LiteralLT> > pointlessStartEffects;
    
    /** The pointless start effects of each action. */
    static map<int, map<Literal*, pointless_effect, LiteralLT> > pointlessEndEffects;
    
    /** The pointless start effects of each action. */
    static map<int, map<Literal*, pointless_effect, LiteralLT> > pointlessTILEffects;
    
    struct BuildingNumericPreconditionData {
        
        set<ArtificialVariable> artificialVariableSet;
        map<RPGNumericPrecondition, list<pair<int, Planner::time_spec> > > rpgNumericPreconditionSet;        
        const int negOffset;
        const int offset;
        int precCount;
        int avCount;
        vector<double> localMaxNeed;
        
        set<int> desirable;
        set<int> undesirable;
        
        BuildingNumericPreconditionData() : negOffset(pnes.size()),offset(negOffset * 2), precCount(0), avCount(offset),localMaxNeed(offset, -DBL_MAX) {};            
        
    };
    
    static void buildRPGNumericPreconditions();
    static void buildRPGNumericEffects();
    static void detectConditionalEffectsThatEncodeIntegralOutcomes();
// static void simplify(pair<list<double>, list<int> > & s);
// static void makeOneSided(pair<list<double>, list<int> > & LHSvariable, pair<list<double>, list<int> > & RHSvariable, const int & negOffset);
// static void makeWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result);
    static bool processPrecondition(RPGBuilder::BuildingNumericPreconditionData & commonData,
                                    NumericPrecondition & currPre,
                                    list<int> & conjunctiveList,
                                    list<int> & disjunctiveList,
                                    const int & i, const Planner::time_spec & passTimeSpec);
    
    static bool processPreconditions(RPGBuilder::BuildingNumericPreconditionData & commonData,
                                     list<NumericPrecondition> & currPreList, list<int> & destList,
                                     int & toIncrement,
                                     const int & i, const Planner::time_spec & passTimeSpec);

    static void buildDurations(vector<list<NumericPrecondition*> > & d, vector<list<NumericPrecondition*> > & e, vector<list<NumericPrecondition*> > & f);

    /** @brief Infer additional start preconditions, due to numeric invariants.
     *
     *  Each numeric invariants (<code>over all</code> conditions) leads to a numeric start precondition in one of two ways:
     *  - if it refers to variables that are not affected by the actions start effects or continuous numeric effects, then it is
     *    copied as-is to be a start numeric precondition
     *  - otherwise, the invariant is regressed through the actions' start effects (and an epsilon amount of its continuous numeric)
     *    effects, and this new constraint added as a start precondition.
     *
     *  @param  pre        The numeric invariant
     *  @param  startEffs  The action's start numeric effects
     *  @param  ctsEffs    The action's continuous numeric effects
     *  @param  commondata  Comomon data used when building up extra preconditions (shared across many actions)
     *  @param  preResult   After the function, this holds the new numeric precondition formed.  It is a pair, where:
     *                      - the first entry is a pointer to the precondition itself
     *                      - the second entry is true if the precondition was new (i.e. never seen before on any action)
     *  @param  avResult    After the function, this holds the artificial variable that was created for the new precondition.  It is a pair, where:
     *                      - the first entry is a pointer to the artificial variable itself (or <code>0</code> if one was needed, i.e. the invariant
     *                        only referred to a single variable)
     *                      - the second entry is true if the artificial variable was new (i.e. never seen before in any other precondition)
     */
    static bool pushInvariantBackThroughStartEffects(const RPGNumericPrecondition & pre, list<int> & startEffs, LinearEffects * ctsEffs,
                                                     InvData & commonData, pair<const RPGNumericPrecondition *, bool> & preResult, pair<ArtificialVariable *, bool> & avResult);

    static void handleNumericInvariants();
    static void findSelfMutexes();
    static void oneShotInferForTILs();
    static void kshotInferForAction(const int & i, MinimalState & refState, LiteralSet & maybeOneShotLiteral, vector<double> & initialFluents, const int & fluentCount);
    static void doSomeUsefulMetricRPGInference();
    static void separateOptimisationTILs();
    
    /** @brief Find concurrent redundant actions
     *
     * A concurrent redundant action is one where there is no benefit to self-overlapping it
     * See 'Admissible Makespan Estimates for PDDL2.1 Temporal Planning', 
     * by Patrik Haslum:
     *
     * http://ie.technion.ac.il/~dcarmel/heuristics-icaps09/hdip05-haslum.pdf
     */
    static void findConcurrentRedundantActions();
    
    /** @brief Identify some conditions under which the application of an action is uninteresting
     *
     * This function looks at facts which cannot be deleted.  If an actions only useful effect is to
     * add such a fact (i.e. all other facts are deletes or numerically undesirable) then once the
     * fact is true (or once the action has started) it's not interesting to start it again.
     */
    static void findUninterestingnessCriteria();
    static DurationExpr * buildDE(NumericPrecondition * d);
    static list<DurationExpr *> buildDEList(list<NumericPrecondition *> & d);
    /** @brief Remove the (linear) continuous effects from the given list, returning them. */
    static LinearEffects * buildLE(list<NumericEffect> & effList, const string & whereEffectsAreFrom);

    static bool considerAndFilter(LiteralSet & initialState, LiteralSet & revisit, const int & operatorID);
    static void postFilterUnreachableActions();
    static void buildMetric(VAL::metric_spec*);

    /** @brief Find facts that act as semaphores in durative domains.
     *
     *  A semaphore fact is one whose role within the planning domain is to force non-concurrency of
     *  certain actions, e.g. all the actions involving a piece of equipment.  For a fact p to be a 
     *  semaphore:
     *
     *  - it must be true in the initial state
     *  - instantaneous actions requiring p must delete it then add it again
     *  - (at start (p)) is coupled with an effect (at start (not (p))) and one of either (at end (p)) or (at start (p))
     *  - (at end (p)) is coupled with an effect (at end (not (p))) and another (at end (p)).
     *  - there is no condition (over all (p))
     *
     *  They can also be goals, the rationale being that 'goals being satisfied' is an infinitely long action
     *  at the end of a plan, requiring the semaphore before it can be applied, i.e. requiring no actions
     *  to be executing (as follows from the PDDL semantics).
     *
     *  To make semaphore facts useful, the fluents they 'guard' are noted by this.  A semaphore fact guards a
     *  fluent if, to refer to the value of that fluent, one must also have the requisite semaphore fact.
     */
    static void findSemaphoreFacts();
    
    /** Initialise the look-up tables for conditional effects.
     *
     *  Visit the conditional effects noted during action instantiation, and
     *  make ConditionalEffect objects to represent each of them.  For now,
     *  the function also calls <code>postmortem_noADL</code> if there are
     *  any conditional propositional effects, or preconditions on facts that
     *  aren't exclusively controlled by timed initial literals.
     *  @see ConditionalEffect
     */
    static void buildThePropositionalBitOfConditionalEffects();

    /** Identify whih facts are static. */
    static void getBasicStaticInformationFromTIM();
    static void findStaticLiterals();
    
    /** Remove pointless effects on literals that are never in preconditions.
     *
     *  If a literal is never a precondition (or a goal), then effects
     *  on it are pointless, and can be ignored without affecting completeness.
     *  The main benefit of this analysis is then that more actions become
     *  compression-safe, as they have no pointless end-delete effects.
     */
    static void removePointlessEffects();
    
    static void pruneStaticPreconditions(list<Literal*> & toPrune, int & toDec);
    static void pruneStaticPreconditions();

    class CommonRegressionData;

    static void postFilterIrrelevantActions();
    static void pruneIrrelevant(const int & operatorID);

    static RPGHeuristic * globalHeuristic;

public:


    static const pair<bool, bool> & isStatic(Literal* l);

    static void simplify(pair<list<double>, list<int> > & s);
    static void makeOneSided(pair<list<double>, list<int> > & LHSvariable, pair<list<double>, list<int> > & RHSvariable, const int & negOffset);
    
    #ifdef STOCHASTICDURATIONS
    static void simplify(pair<list<double>, list<pair<int,PNE*> > > & s);
    static void makeDurationWeightedSum(list<Operand> & formula, pair<list<double>, list<pair<int,PNE*> > > & result);
    static void makeWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result);
    #else
    static void makeDurationWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result);
    static void makeWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result);
    #endif

    static const vector<double> & getNonTemporalDurationToPrint() {
        return nonTemporalDuration;
    }
    
    static const vector<FakeTILAction*> & getAllTimedInitialLiterals() {
        return allTimedInitialLiteralsVector;
    }
    
    static vector<list<NumericPrecondition*> > & getFixedDEs() {
        return fixedDurationExpressions;
    }
    
    static vector<list<NumericPrecondition*> > & getMinDEs() {
        return minDurationExpressions;
    }
    
    static vector<list<NumericPrecondition*> > & getMaxDEs() {
        return maxDurationExpressions;
    }
    
    static vector<RPGDuration*> & getRPGDEs(const int & a) {
        return rpgDurationExpressions[a];
    }
    
    static vector<LinearEffects*> & getLinearDiscretisation() {
        return linearDiscretisation;
    }

    static vector<list<int> > & getStartPreNumerics() {
        return actionsToRPGNumericStartPreconditions;
    }
    
    static vector<list<int> > & getInvariantNumerics() {
        return actionsToRPGNumericInvariants;
    }
    
    static vector<list<int> > & getEndPreNumerics() {
        return actionsToRPGNumericEndPreconditions;
    }

    static vector<list<int> > & getStartEffNumerics() {
        return actionsToRPGNumericStartEffects;
    }
    
    static vector<list<int> > & getEndEffNumerics() {
        return actionsToRPGNumericEndEffects;
    }

    static vector<list<ConditionalEffect> > & getEditableActionsToConditionalEffects() {
        return actionsToConditionalEffects;
    }

    static const vector<list<ConditionalEffect> > & getActionsToConditionalEffects() {
        return actionsToConditionalEffects;
    }
    
    static const map<int, list<IntegralContinuousEffect> > & getActionsToIntegralConditionalEffects() {
        return actionsToIntegralConditionalEffects;
    }
    
    static vector<list<Literal*> > & getStartPropositionAdds() {
        return actionsToStartEffects;
    }
    
    static vector<list<Literal*> > & getStartPropositionDeletes() {
        return actionsToStartNegativeEffects;
    }

    static vector<list<Literal*> > & getEndPropositionAdds() {
        return actionsToEndEffects;
    };
    static vector<list<Literal*> > & getEndPropositionDeletes() {
        return actionsToEndNegativeEffects;
    };

    static vector<list<Literal*> > & getProcessedStartPropositionalPreconditions() {
        return actionsToProcessedStartPreconditions;
    };
    static vector<list<Literal*> > & getStartPropositionalPreconditions() {
        return actionsToStartPreconditions;
    };
    static vector<list<Literal*> > & getStartNegativePropositionalPreconditions() {
        return actionsToStartNegativePreconditions;
    };
    static vector<list<int> > & getProcessedStartRPGNumericPreconditions() {
        return actionsToProcessedStartRPGNumericPreconditions;
    }
    
    static vector<list<Literal*> > & getInvariantPropositionalPreconditions() {
        return actionsToInvariants;
    };
    static vector<list<Literal*> > & getInvariantNegativePropositionalPreconditions() {
        return actionsToNegativeInvariants;
    };
    static vector<list<Literal*> > & getEndPropositionalPreconditions() {
        return actionsToEndPreconditions;
    };
    static vector<list<Literal*> > & getEndNegativePropositionalPreconditions() {
        return actionsToEndNegativePreconditions;
    };
    static vector<list<int> > & getEndRPGNumericPreconditions() {
        return actionsToRPGNumericEndPreconditions;
    }
    
    static vector<list<Literal*> > & getProcessedStartNegativePropositionalPreconditions() {
        return actionsToProcessedStartNegativePreconditions;
    };

    /** @return A reference to <code>rpgNumericPreconditions</code>, the preconditions used in the problem, in LNF. */
    static vector<RPGNumericPrecondition> & getNumericPreTable() {
        return rpgNumericPreconditions;
    }
    
    /** @return A reference to <code>rpgNumericEffects</code>, the effects used in the problem, in LNF. */
    static vector<RPGNumericEffect> & getNumericEff() {
        return rpgNumericEffects;
    }
    
    /** @return a reference to <code>rpgNumericEffectsToActions</code>: for each numeric effect, which actions have it. */
    static const vector<list<pair<int, Planner::time_spec> > > & getRpgNumericEffectsToActions() {
        return rpgNumericEffectsToActions;
    }

    /** @return a reference to <code>rpgNumericPreconditionsToActions</code>: for each numeric precondition, which actions have it. */
    static const vector<list<pair<int, Planner::time_spec> > > & getRawRpgNumericPreconditionsToActions() {
        return rpgNumericPreconditionsToActions;
    }
    
    /** @return a reference to <code>processedRPGNumericPreconditionsToActions</code>: for each numeric precondition, after pushing invariants through start effects, which actions have it. */
    static const vector<list<pair<int, Planner::time_spec> > > & getProcessedRPGNumericPreconditionsToActions() {
        return processedRPGNumericPreconditionsToActions;
    }
            

    /**
     * @return A const reference to <code>rpgArtificialVariables</code>, the artificial variables built
     *         so that multi-variable preconditions and can be written in terms of a single 'artificial'
     *         variable.
     */
    static const vector<ArtificialVariable> & getArtificialVariableTable() {
        return rpgArtificialVariables;
    }
    
    /**
     * @return A const reference to <code>maxNeeded</code>, the maximum amount of each variable needed
     *         to satisfy the preconditions.
     */
    static const vector<double> & getMaxNeeded() {
        return maxNeeded;
    }
    
    /** @brief For each variable, whether it has an initial-state value. */
    static const vector<bool> & getWhetherDefinedValueInInitialState() {
        return definedValueInInitialState;
    }
    
    /**
     * @see <code>RPGBuilder::findSemaphoreFacts</code>.
     *
     * @return A const reference to <code>semaphoreFacts</code>.
     */
    static const map<int, Guarded> & getSemaphoreFacts() {
        return semaphoreFacts;
    }
    
    static vector<list<pair<int, Planner::time_spec> > > & getPresToActions() {
        return processedPreconditionsToActions;
    }
    
    static vector<list<pair<int, Planner::time_spec> > > & getRawPresToActions() {
        return preconditionsToActions;
    };

    static vector<list<pair<int, Planner::time_spec> > > & getRawNumericPresToActions() {
        return rpgNumericPreconditionsToActions;
    }
    
    static const vector<Constraint> & getPreferences() {
        return preferences;
    }
    
    static vector<Constraint> & getEditablePreferences() {
        return preferences;
    }
            
    
//     static const map<int,Literal*> & getPreferencesThatAreSoftDeadlines() {
//         return preferencesThatAreSoftDeadlines;
//     }
    
    static const vector<op_type> & rogueActions;
    static vector<op_type> realRogueActions;
    static bool sortedExpansion;
    static bool fullFFHelpfulActions;
    static bool modifiedRPG;
    static bool noSelfOverlaps;
    static bool doTemporalAnalysis;
    
    static void initialise();

    static bool nonTemporalProblem() {
        return problemIsNotTemporal;
    };

    static bool actionIsDurative(const int & i) {
        return (!fixedDurationExpressions[i].empty() || !minDurationExpressions[i].empty() || !maxDurationExpressions[i].empty());
    }
    
    static list<Literal*> & getLiteralGoals() {
        return literalGoals;
    };
    
    static const list<double> & getLiteralGoalDeadlines() {
        return literalGoalDeadlines;
    }

    static const map<int,int> & getLiteralsToGoalIndex() {
        return literalsToGoalIndex;
    }

    static const map<int, list<int> > & getFactsRelevantToWithinPreferences() {
        return factRelevantToWithinPreferences;
    }

    #ifdef POPF3ANALYSIS
    static void updateGoalDeadlines(const double & d) {
        {
            list<double>::iterator ldItr = literalGoalDeadlines.begin();
            const list<double>::iterator ldEnd = literalGoalDeadlines.end();
            
            for (; ldItr != ldEnd; ++ldItr) {
                if (*ldItr > d) {
                    *ldItr = d;
                }
            }
        }
        {
            list<double>::iterator ldItr = numericGoalDeadlines.begin();
            const list<double>::iterator ldEnd = numericGoalDeadlines.end();
            
            for (; ldItr != ldEnd; ++ldItr) {
                if (*ldItr > d) {
                    *ldItr = d;
                }
            }
        }
        cout << "\n * All goal deadlines now no later than " << d << std::endl;
    }
    #endif

    static RPGHeuristic * generateRPGHeuristic();
    static RPGHeuristic * getHeuristic() {
        if (!globalHeuristic) {
            globalHeuristic = RPGBuilder::generateRPGHeuristic();                
        }
        return globalHeuristic;
    }
    static void getInitialState(LiteralSet & initialState, vector<double> & initialFluents);
    static void getNonStaticInitialState(LiteralSet & initialState, vector<double> & initialFluents);
    static instantiatedOp* getInstantiatedOp(const int & i) {
        return instantiatedOps[i];
    };
    static Literal* getLiteral(const int & i) {
        return literals[i];
    };
    /*static list<FakeTILAction> & getTILs() {
        return timedInitialLiterals;
    };*/
    static void boostMinDuration(const int & actID, const double & minDur) {
        assert(minDur > actionsToMinDurations[actID]);
        actionsToMinDurations[actID] = minDur;
    }
    static void boostMaxDuration(const int & actID, const double & maxDur) {
        assert(maxDur < actionsToMaxDurations[actID]);
        actionsToMaxDurations[actID] = maxDur;
    }
    static list<pair<int, Planner::time_spec> > & getEffectsToActions(const int & i) {
        return effectsToActions[i];
    };
    static const vector<list<pair<int, Planner::time_spec> > > & getEffectsToActions() {
        return effectsToActions;
    };
    static const vector<list<pair<int, Planner::time_spec> > > & getNegativeEffectsToActions() {
        return negativeEffectsToActions;
    };
    
    static vector<FakeTILAction*> & getNormalTILVec() {
        return normalTimedInitialLiteralsVector;
    };

    static vector<FakeTILAction*> & getNonAbstractedTILVec() {
        assert(definedNonAbstractedTILs);
        return nonAbstractedTimedInitialLiteralsVector;
    }
    
    static void getEffects(instantiatedOp* op, const bool & start, list<Literal*> & add, list<Literal*> & del, list<NumericEffect> & numeric);
    static void getPrecInv(instantiatedOp* op, const bool & start, list<Literal*> & precs, list<Literal*> & inv, list<NumericPrecondition> & numericPrec, list<NumericPrecondition> & numericInv);
    // static void getCollapsedAction(instantiatedOp* op, list<Literal*> & pre, list<Literal*> & add, list<Literal*> & del, list<NumericPrecondition> & numericPre, list<NumericEffect> & numericEff);

    static Metric * getMetric() {
        return theMetric;
    }
    
//     static const vector<bool> * getFactHasBeenSeenForWithinSoftDeadline() {
//         return factHasBeenSeenForWithinSoftDeadline;
//     }
    
    static list<int> & getMentioned(const int & i) {
        return mentionedInFluentInvariants[i];
    };

    static bool stepNeedsToHaveFinished(const ActionSegment & act, const MinimalState & s, set<int> & dest);

    static double getOpMinDuration(instantiatedOp* op, const int & div);
    static double getOpMinDuration(const int & op, const int & div);

    static double getOpMaxDuration(instantiatedOp* op, const int & div);
    static double getOpMaxDuration(const int & op, const int & div);

    static pair<double, double> getOpDuration(instantiatedOp* op, const int & div, const vector<double> & minFluents, const vector<double> & maxFluents);
    static pair<double, double> getOpDuration(const int & op, const int & div, const vector<double> & minFluents, const vector<double> & maxFluents);

    static PNE* getPNE(const int & i) {
        assert(i >= 0);
        assert(i < (int) pnes.size());
        return pnes[i];
    };
    static int getPNECount() {
        return pnes.size();
    };
    static int getAVCount() {
        return rpgArtificialVariables.size();
    };
    static ArtificialVariable & getArtificialVariable(const int & i) {
        return rpgArtificialVariables[i - (2 * getPNECount())];
    };

    static list<int> & getVariableDependencies(const int & i) {
        return rpgVariableDependencies[i];
    };
    static list<int> & affectsRPGNumericPreconditions(int i) {

        static const int off = getPNECount();
        if (i < off) {
            return rpgPositiveVariablesToPreconditions[i];
        };
        i -= off;
        if (i < off) {
            return rpgNegativeVariablesToPreconditions[i];
        }
        i -= off;
        return rpgArtificialVariablesToPreconditions[i];

    }


    static int howManyTimes(const int & actID, const MinimalState & e) {
        return kShotFormulae[actID]->getLimit(e);
    };
    static int howManyTimesOptimistic(const int & actID, const MinimalState & e) {
        return kShotFormulae[actID]->getOptimisticLimit(e);
    };
    static bool literalIsOneShot(const int & lID) {
        return oneShotLiterals[lID];
    };
    static bool isSelfMutex(const int & actID) {
        return selfMutexes[actID];
    };
    static list<pair<int, int> > & getNumericRPGGoals() {
        return numericRPGGoals;
    };
    static list<double> & getNumericRPGGoalDeadlines() {
        return rpgNumericGoalDeadlines;
    };
    static list<NumericPrecondition> & getNumericGoals() {
        return numericGoals;
    };

    /** @brief Find whether applying an action in the given state is concievably worthwhile
     *
     * @see <code>RPGBuilder::findUninterestingnessCriteria</code> and <code>RPGBuilder::findConcurrentRedundantActions</code>
     *
     * @param act   The ID of the action to apply (an index into <code>RPGBuilder::instantiatedOps</code>
     * @param facts  The facts in the current state
     * @param started The actions that have been started in the current state
     * @retval <code>true</code>  The action might be useful to apply
     * @retval <code>false</code> The action is definitely not useful to apply
     */
    static bool isInteresting(const int & act, const StateFacts & facts, const map<int, set<int> > & started);
    
    static LiteralSet & getEndOneShots(const int & i) {
        return actionsToEndOneShots[i];
    };
    
    static const vector<vector<Literal*> > & getPropositionGroups() {
        return propositionGroups;
    }
    
    static const vector<vector<int> > & getLiteralToPropositionGroupID() {
        return literalToPropositionGroupID;
    }
    
    static const int & getTaskPrefCount() {
        return taskPrefCount;
    }
        
    static const int & getPreconditionPrefCount() {
        return preconditionPrefCount;
    }
                
    static const map<string,int> & getPermanentViolationDetails()
    {
        return prefNameToNumberOfTimesDefinitelyViolated;
    }
    static const double & getPermanentViolationCost()
    {
        return permanentPreferenceViolations;
    }
    static const vector<vector<int> > & getStartPreferences()
    {
        return actionsToStartPreferences;
    }
    static const vector<vector<int> > & getEndPreferences()
    {
        return actionsToEndPreferences;
    }
};

extern EpsilonResolutionTimestamp earliestPointForNumericPrecondition(const RPGBuilder::RPGNumericPrecondition & p,
                                                                      const vector<double> * earliestNumericPOTimes);

extern EpsilonResolutionTimestamp earliestPointForNumericPrecondition(const RPGBuilder::RPGNumericPrecondition & p,
                                                                      const MinimalState & s,
                                                                      const vector<double> & stepTimes);

class RPGHeuristic
{

private:
    class Private;

    Private * const d;

    struct ActionViolationData {
        set<int> preconditionsMeanViolating;
        double precViolationCost;
        
        set<int> effectsMeanViolating;
        double effViolationCost;
        
        set<int> overallViolations;
        double overallViolationCost;
        
        bool canBeApplied;
        
        ActionViolationData()
            : precViolationCost(-1.0), effViolationCost(-1.0), overallViolationCost(-1.0), canBeApplied(false)
        {
        }
        
        inline bool isCostFree() const {
            return (overallViolationCost < 0.00001);
        }
    };
    
public:

    /** @brief If set to true, the heuristic returns a value of 1 for goal states, or 0 otherwise. */
    static bool blindSearch;
    
    /** @brief If set to true, the RPG ignores numeric preconditions and effects. */
    static bool ignoreNumbers;
    
    /** @brief If set to true, the RPG integrates continuous effects, so they occur in full at the start of the action. */
    static bool makeCTSEffectsInstantaneous;
    
    /** @brief If set to true, use SAPA-esque RPG costs.*/
    static bool estimateCosts;
    
    /** @brief Configure the heuristic guidance provided by the RPG heuristic.
     *
     *  The heuristic configuration is determined according to the
     *  given string (usually passed with the prefix '-g' on the command line).
     *
     *  @param config  Configuration name to use
     */
    static void setGuidance(const char * config);
    
    static set<int> emptyIntList;

    /** @brief Number of states evaluated during search. */
    static unsigned int statesEvaluated;
    
    /** @brief If set to true, print RPGs in DOT format. */
    static bool printRPGAsDot;
    
    /** @brief If set to true, helpful actions are ordered according to the deadline to which they are relevant, soonest first. */
    static bool orderByDeadlineRelevance;
    
    /** @brief If set to true, the TRPG is always expanded fully, thereby guaranteeing cost estimates are admissible. */
    static bool alwaysExpandFully;
    
    static bool addTheMaxCosts;
    
    RPGHeuristic(const bool & b,
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
                 list<pair<int, Planner::time_spec> > * onpa);

    ~RPGHeuristic();

    static vector<EpsilonResolutionTimestamp> & getEarliestForStarts();
    static vector<EpsilonResolutionTimestamp> & getEarliestForEnds();


    #ifdef POPF3ANALYSIS
    /** @brief Call this when Globals::bestSolutionQuality is better. */
    void metricHasChanged();
    #endif
    
    class EvaluationInfo {
        
    private:
            
        int hValue;
    public:
        
        double admissibleReachablePrefCost;
        bool goalState;
        

        EvaluationInfo()
        : hValue(-1), admissibleReachablePrefCost(DBL_MAX), goalState(false)
        {
            //cout << "Created evaluation info at " << this << ", with the default constructor\n";
        }
        
        EvaluationInfo(const int & a, const double & b, const bool & c)
        : hValue(a), admissibleReachablePrefCost(b), goalState(c)
        {
            //cout << "Created evaluation info at " << this << ", with h = " << hValue << std::endl;
        }
        
        EvaluationInfo(const EvaluationInfo & e)
        : hValue(e.hValue), admissibleReachablePrefCost(e.admissibleReachablePrefCost), goalState(e.goalState)
        {
            //cout << "Created evaluation info at " << this << "< by copying " << &e << ", with h = " << hValue << std::endl;
        }
        
        EvaluationInfo & operator=(const EvaluationInfo & e)        
        {
            //cout << "Input to assignment: " << &e << ", h = " << e.hValue << std::endl;
            hValue = e.hValue;
            admissibleReachablePrefCost = e.admissibleReachablePrefCost;
            goalState = e.goalState;
            //cout << "Updated evaluation info at " << this << "by assignment, with h = " << hValue << std::endl;
            return *this;
        }
        
        const int & getH() const {
            return hValue;
        }
        
        void incrementH(const int & i) {
            hValue += i;
        }
        
        
        
    };
    
    EvaluationInfo* getRelaxedPlan(MinimalState & theState, const list<StartEvent> * startEventQueue,
                                  const vector<double> & minTimestamps, const double & stateTS, const double & currentCost,
                                  const vector<double> & extrapolatedMin, const vector<double> & extrapolatedMax, const vector<double> & timeAtWhichStateVariableBoundsHold,
                                  list<ActionSegment> & helpfulActions, list<pair<double, list<ActionSegment> > > & relaxedPlan,
                                  double & finalPlanMakespanEstimate, map<double, list<pair<int, int> > > * justApplied = 0, double tilFrom = 0.001)  __attribute__((warn_unused_result));

    void findApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions);
    void filterApplicableActions(const MinimalState & theState, const double & stateTime, list<ActionSegment> & applicableActions);

    bool testApplicability(const MinimalState & theState, const double & stateTime, const ActionSegment & actID, bool fail = false, bool ignoreDeletes = false);

    list<Literal*> & getDeleteEffects(const int & i, const Planner::time_spec & t);
    list<Literal*> & getAddEffects(const int & i, const Planner::time_spec & t);
    list<Literal*> & getPreconditions(const int & i, const Planner::time_spec & t);
    list<Literal*> & getInvariants(const int & i);

    list<int> & getNumericEffects(const int & i, const Planner::time_spec & t);
    RPGBuilder::RPGNumericEffect & getRPGNE(const int & i);

    list<instantiatedOp*> * makePlan(list<int> & steps);

    instantiatedOp* getOp(const int & i);
    EpsilonResolutionTimestamp earliestTILForAction(const int & i, const bool & isStart);

    static EpsilonResolutionTimestamp & getDeadlineRelevancyStart(const int & i);

    static EpsilonResolutionTimestamp & getDeadlineRelevancyEnd(const int & i);


    void doFullExpansion(MinimalState & refState, const list<FFEvent> & dummyPlanSize);

};

ostream & operator <<(ostream & o, const RPGBuilder::NumericPrecondition & p);
ostream & operator <<(ostream & o, const RPGBuilder::NumericEffect & p);

ostream & operator <<(ostream & o, const RPGBuilder::RPGNumericPrecondition & p);
ostream & operator <<(ostream & o, const RPGBuilder::ArtificialVariable & p);
ostream & operator <<(ostream & o, const RPGBuilder::RPGNumericEffect & p);

enum whereAreWe { PARSE_UNKNOWN, PARSE_PRECONDITION, PARSE_EFFECT, PARSE_DURATION, PARSE_GOAL, PARSE_INITIAL, PARSE_CONDITIONALEFFECT, PARSE_CONTINUOUSEFFECT, PARSE_METRIC, PARSE_DERIVATION_RULE, PARSE_CONSTRAINTS };

extern whereAreWe WhereAreWeNow;

void validatePNE(PNE * c);
void validateLiteral(Literal * l);

void postmortem_noNestedWhens();
void postmortem_noADL();
void postmortem_invalidMetric();
void postmortem_nonLinearCTS(const string & actName, const string & worksOutAs);
void postmortem_noQuadratic(const string & theOp);
void postmortem_noTimeSpecifierOnAPropPrecondition(const string & actname, const string & effect);
void postmortem_twoSimulataneousNumericEffectsOnTheSameVariable(const string & actname, const string & varname);
void postmortem_fixedAndNotTimeSpecifiers(const string & actname, const bool & multipleEquals);
void postmortem_noTimeSpecifierOnAPropEffect(const string & actname, const string & effect);
void postmortem_noTimeSpecifierOnInstantNumericEffect(const string & actname, const string & effect, const string & suggested, const bool & isAssign);
void postmortem_wrongNumberOfFluentArguments(const string & actname, const bool & haveActName, const whereAreWe & w, const string & predname, const string & lit, const int & givenArgs, const set<int> & realargs);
void postmortem_wrongNumberOfPredicateArguments(const string & actname, const bool & haveActName, const whereAreWe & w, const string & predname, const string & lit, const int & givenargs, const set<int> & realargs);
void postmortem_mathsError(const string & description, const string & help, const whereAreWe & w);
void postmortem_noConstraints(const bool unsupportedPref = false, const char * n = 0);
void postmortem_isViolatedNotExist(const string & s);
void postmortem_fatalConstraint(const string & whichOne);
void postmortem_processesMustHaveNoConditions(const string & actName);
void postmortem_invalidGoal(const string & s);
void postmortem_unsatisfiableConstraint();

};



#endif
// kate: indent-mode cstyle; space-indent on; indent-width 4; replace-tabs on;
