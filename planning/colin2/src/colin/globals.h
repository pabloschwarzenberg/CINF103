/************************************************************************
 * Copyright 2012; Planning, Agents and Intelligent Systems Group,
 * Department of Informatics,
 * King's College, London, UK
 * http://www.inf.kcl.ac.uk/staff/andrew/planning/
 *
 * Amanda Coles, Andrew Coles, Maria Fox, Derek Long - COLIN
 * Stephen Cresswell - PDDL Parser
 *
 * This file is part of COLIN.
 *
 * COLIN is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * COLIN is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with COLIN.  If not, see <http://www.gnu.org/licenses/>.
 *
 ************************************************************************/

#ifndef __GLOBALS
#define __GLOBALS

#ifndef NDEBUG
#define ENABLE_DEBUGGING_HOOKS 1
#endif

#include <instantiation.h>
#include <cmath>
#include <climits>
#include <cfloat>

#ifndef POPF3ANALYSIS
//#define POPF3ANALYSIS
#endif

using Inst::Literal;
using Inst::instantiatedOp;

namespace Planner
{

struct LiteralLT {

    bool operator()(const Literal* const & a, const Literal* const & b) const {
        return (a->getGlobalID() < b->getGlobalID());
    }

};

typedef map<int, bool> StepAndEpsilon;

typedef set<Literal*, LiteralLT> LiteralSet;


/** @brief Class describing a snap-action. */
class ActionSegment
{

public:
    /** @brief The number of TIL events in the problem, used for bounds checking. */
    static int tilLimit;

    /** @brief The root action of the snap-action (or <code>0</code> if a TIL). */
    instantiatedOp* first;
    
    /** @brief The time-specifier of the snap-action.
     * 
     * This takes one of three values:
     * - <code>VAL::E_AT_START</code> for start snap-actions, or instantaneous actions
     * - <code>VAL::E_AT_END</code> for end snap-actions
     * - <code>VAL::E_AT</code> for TIL actions
     */
    VAL::time_spec second;
    
    /** @brief The index of the TIL event (an index into <code>RPGBuilder::allTimedInitialLiteralsVector</code>. */
    int divisionID;

    /** @brief Step IDs of actions that must have finished prior to this one.  Deprecated. */
    set<int> needToFinish;

    ActionSegment()
        : first(0), second(VAL::E_OVER_ALL), divisionID(-1)
    {
    }
    
    ActionSegment(instantiatedOp* const f, const VAL::time_spec & s, const int & d, const set<int> & n)
        : first(f), second(s), divisionID(d), needToFinish(n)
    {
        assert(second != VAL::E_AT || divisionID <= tilLimit);
    }

    ActionSegment(const ActionSegment & o)
        : first(o.first), second(o.second), divisionID(o.divisionID), needToFinish(o.needToFinish)
    {
    }

    virtual ~ActionSegment()
    {
    }
    
};

extern ostream & operator <<(ostream & o, const ActionSegment & s);


class EpsilonResolutionTimestamp {
    
protected:
    long timestampTimesOneThousand;

    EpsilonResolutionTimestamp(const long & l) : timestampTimesOneThousand(l) {        
    }

    EpsilonResolutionTimestamp() : timestampTimesOneThousand(-LONG_MAX) {        
    }
    
public:
        
    EpsilonResolutionTimestamp(const double & d, const bool & roundDown)
        : timestampTimesOneThousand(roundDown ? d * 1000 : ceil(d * 1000)) { 
        assert(d != DBL_MAX);
        assert(d != -DBL_MAX);
    }
    
    EpsilonResolutionTimestamp(const EpsilonResolutionTimestamp & other)
        : timestampTimesOneThousand(other.timestampTimesOneThousand) {        
    }
    
    EpsilonResolutionTimestamp & operator=(const EpsilonResolutionTimestamp & other) {
        timestampTimesOneThousand = other.timestampTimesOneThousand;
        return *this;
    }
    
    bool operator<(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand < other.timestampTimesOneThousand);
    }

    bool operator<=(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand <= other.timestampTimesOneThousand);
    }
    
    bool operator==(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand == other.timestampTimesOneThousand);
    }

    bool operator>=(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand >= other.timestampTimesOneThousand);
    }

    bool operator>(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand > other.timestampTimesOneThousand);
    }
    
    bool operator!=(const EpsilonResolutionTimestamp & other) const {
        return (timestampTimesOneThousand != other.timestampTimesOneThousand);
    }
    
    void operator +=(const EpsilonResolutionTimestamp & other) {
        timestampTimesOneThousand += other.timestampTimesOneThousand;
    }
    
    void operator -=(const EpsilonResolutionTimestamp & other) {
        timestampTimesOneThousand -= other.timestampTimesOneThousand;
    }
    
    bool isEpsilonAhead(const EpsilonResolutionTimestamp & other) const {
        return ((timestampTimesOneThousand - other.timestampTimesOneThousand) == 1);        
    }
    
    bool isZero() const {
        return (timestampTimesOneThousand == 0);
    }
    
    double toDouble() const {
        return (timestampTimesOneThousand / 1000.0);
    }
    
    bool isUndefined() const {
        return (timestampTimesOneThousand == -1000);
    }
    
    static const EpsilonResolutionTimestamp & epsilon() {
        static const EpsilonResolutionTimestamp toReturn(1);
        
        return toReturn;
    }
    
    static const EpsilonResolutionTimestamp & infinite() {
        static const EpsilonResolutionTimestamp toReturn(LONG_MAX);
        
        return toReturn;
    }         
    
    static const EpsilonResolutionTimestamp & zero() {
        static const EpsilonResolutionTimestamp toReturn(0);
        
        return toReturn;
    }
    
    static const EpsilonResolutionTimestamp & undefined() {
        static const EpsilonResolutionTimestamp toReturn(-1000);
        
        return toReturn;
    }
    
    void write(ostream & o) const{
        long beforeDot = timestampTimesOneThousand / 1000;
        long afterDot = timestampTimesOneThousand % 1000;
        o << beforeDot << ".";
        if (afterDot < 100) {
            o << "0";
        }            
        if (afterDot < 10) {
            o << "0";
        }
        o << afterDot;
    }
    
    void operator++() {
        assert(timestampTimesOneThousand >= 0);
        ++timestampTimesOneThousand;
    }
    
    void operator--() {
        assert(timestampTimesOneThousand >= 1);
        --timestampTimesOneThousand;
    }
};

extern EpsilonResolutionTimestamp operator-(const EpsilonResolutionTimestamp & a, const EpsilonResolutionTimestamp & b);

extern EpsilonResolutionTimestamp operator-(const EpsilonResolutionTimestamp & a);

extern EpsilonResolutionTimestamp operator+(const EpsilonResolutionTimestamp & a, const EpsilonResolutionTimestamp & b);

extern ostream & operator<<(ostream & o, const EpsilonResolutionTimestamp & t);
    

/** @brief Class containing global variables. */
class Globals
{

public:

    /** @brief Global verbosity flag.
     * 
     *  This is a bit-mask, where each bit corresponds to whether
     *  debugging output should be provided for a certain part of the code.
     *  
     *  - 1: provide basic information about how search is progressing
     *  - 2: when expanding a state, print the plan that reached that state
     *  - 16: provide (lots of) information about action grounding
     *  - 64: provite (lots of) information from the RPG heuristic
     *  - 4096: provide information about the STP constraints used within the incremental Bellman-Ford implementation
     *  - 8192: provide debugging information about trivial cycle checking (if doing totally ordered search)
     *  - 65536: print out a list of all ground action names, fact names, and variable names
     *  - 131072: print out information about the action pruning performed in the preprocessor
     *  - 1048576: provide information about the ordering constraints added to the partial order when applying an action
     */
    static const int & globalVerbosity;
    
    #define EPSILON 0.001
    
    static int writeableVerbosity;
    
    /** @brief Debugging flag - triple-check the plan scheduling during search.
     * 
     *  If set to true (pass the <code>-D</code> flag at the command line), the plan is scheduled using
     *  three techniques, at every state: the LP, the incremental Bellman-Ford, and Floyd-Walshall.  Additionally, the
     *  latter is ran each time an edge is added to the incremental Bellman-Ford algorithm to check the incremental updates
     *  are correct.
     *
     *  @see LPScheduler
     */
    static bool paranoidScheduling;

    /** @brief Enable profiling mode for scheduling.
     * 
     *  If set to true (pass the <code>-P</code> flag at the command line), the plan is scheduled using
     *  both the LP and incremental Bellman-Ford, without the two being integrated.  The profile data produced by
     *  gprof can then be used to ascertain the comparative performance of the two approaches:
     *  - Time taken for the STP is <code>LPScheduler::prime()</code> + <code>ParentData::spawnChildData()</code>
     *  - Time taken for the LP is <code>LPScheduler::LPScheduler()</code> - <code>ParentData::spawnChildData()</code>
     *    (as the latter is called from within the LP scheduler constructor, but needs to be discounted as in profiling
     *     mode the two are not integrated.)
     *
     *  @see LPScheduler
     */
    static bool profileScheduling;

    /** @brief True if only testing for relaxed plan, false otherwise.
     */
    static bool rpOnly;

    #ifdef ENABLE_DEBUGGING_HOOKS

    /** @brief A vector of which actions definitely must be kept, i.e. not pruned in preprocessing.
     * 
     *  This vector is only present for debugging purposes.  To populate the vector:
     *  - use the <code>-H</code> command line flag
     *  - provide a plan filename after the domain and problem filenames
     *  Then, the <code>instantiatedOp</code>s used in the plan will have their entries in this vector
     *  set to true.
     */
    static vector<bool> actionHasToBeKept;
    
    /** @brief An exemplar plan for the current problem, to be read in for debugging purposes.
     * 
     *  @see actionHasToBeKept
     */
    static const char * planFilename;
    
    /** @brief Indices of the remaining actions in the solution plan given.
     *
     *  This set is only present for debugging purposes.  When evaluating a state reached
     *  during the plan passed to the planner, the indices remaining actions
     */
    static list<ActionSegment> remainingActionsInPlan;

    /** @brief Read in <code>planFilename</code> and note that its actions must not be pruned in preprocessing.
     *
     *  @see actionHasToBeKept
     */
    static void markThatActionsInPlanHaveToBeKept();
    
    /** @brief Note that the action with the specified ID has been pruned, due to the given reason.
     * 
     *  This will lead to an assertion failure if the action must not be pruned.
     *
     *  @param i         The action index that has been eliminated
     *  @param synopsis  A short reason for why the action was eliminated.  This is printed if the pruning is known to be in error.
     *
     *  @see actionHasToBeKept
     */
    static void eliminatedAction(const int & i, const char * synopsis);
    #endif
    
    #ifdef POPF3ANALYSIS
    /** @brief  If <code>true</code>, carry on seearching after first plan found. */
    static bool optimiseSolutionQuality;
  
    /** @brief  Quality of the best solution found so far. */
    static double bestSolutionQuality;
    #endif
    
    /** @brief  If <code>true</code>, search is totally ordered. */
    static bool totalOrder;
};

};

#endif
