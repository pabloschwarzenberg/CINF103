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

#ifndef FFEVENT_H
#define FFEVENT_H

#include <ptree.h>

namespace Inst {
    class instantiatedOp;
};

using Inst::instantiatedOp;

#include "globals.h"

#include <set>
using std::set;

namespace Planner {

#ifdef STOCHASTICDURATIONS
class StochasticTimestampData;
#endif

struct StartEvent {
    int actID;
    int divisionsApplied;
    int stepID;
    double advancingDuration;
    double minDuration;
    double maxDuration;
    double elapsed;
    double minAdvance;
//  ScheduleNode* compulsaryEnd;
    bool terminated;
    bool ignore;
    int fanIn;
    set<int> endComesBefore;
    set<int> endComesBeforePair;

    set<int> endComesAfter;
    set<int> endComesAfterPair;


    inline set<int> & getEndComesBefore() {
        return endComesBefore;
    };
    inline set<int> & getEndComesAfter() {
        return endComesAfter;
    };
    inline set<int> & getEndComesAfterPair() {
        return endComesAfterPair;
    };
    inline set<int> & getEndComesBeforePair() {
        return endComesBeforePair;
    };


    double lpMinTimestamp;
    double lpMaxTimestamp;


    StartEvent(const int & a, const int & da, const int & s, const double & mind, const double & maxd, const double &e) : actID(a), divisionsApplied(da), stepID(s), advancingDuration(mind), minDuration(mind), maxDuration(maxd), elapsed(e), minAdvance(DBL_MAX), terminated(false), ignore(false), fanIn(0), lpMinTimestamp(0.0), lpMaxTimestamp(DBL_MAX) {};

    bool operator ==(const StartEvent & e) const {
        return (actID == e.actID &&
                divisionsApplied == e.divisionsApplied &&
                stepID == e.stepID &&
                fabs(minDuration - e.minDuration) < 0.0005 &&
                fabs(maxDuration - e.maxDuration) < 0.0005 &&
                fabs(elapsed - e.elapsed) < 0.0005 &&
                fabs(advancingDuration - e.advancingDuration) < 0.0005 &&
//          compulsaryEnd == e.compulsaryEnd &&
                terminated == e.terminated &&
                fanIn == e.fanIn &&
                endComesBefore == e.endComesBefore);
    }

    void endMustComeAfter(const int & i) {
        assert(i >= 0); endComesAfter.insert(i);
    }
    void endMustComeAfterPair(const int & i) {
        assert(i >= 0); endComesAfterPair.insert(i);
    }

    void actionHasFinished(const int & i) {
        assert(i >= 0); endComesAfter.erase(i);
    }

};

class FFEvent
{

public:

    static int tilLimit;

    instantiatedOp* action;
    
    /** @brief Time-specifier of the action
     *
     * This is one of a number of values:
     * - <code>Planner::E_AT_START</code> if <code>action</code> is the start of an action, or an instantaneous action
     * - <code>Planner::E_AT_END</code> if <code>action</code> is the start of an action
     * - <code>Planner::E_AT</code> for a timed-initial literal, where <code>divisionID</code> is the index into <code>RPGBuilder::timedInitialLiteralsVector</code>
     * - <code>Planner::E_CONTINUOUS</code> for dummy events inserted to collate the facts relevant to the status of non-temporal preferences.
     * - <code>Planner::E_DUMMY_TEMPORAL_TRIGGER</code> for dummy events inserted to collate the facts relevant to the trigger of a temporal preference, with preference ID <code>divisionID</code>
     * - <code>Planner::E_DUMMY_TEMPORAL_GOAL</code> for dummy events inserted to collate the facts relevant to the goal of a temporal preference, with preference ID <code>divisionID</code>
     * - <code>Planner::E_DUMMY_PREFERENCE_PRECONDITION</code> for dummy events inserted to hold soft temporal constraints to meet preference preconditions.
     */
    Planner::time_spec time_spec;
    double minDuration;
    double maxDuration;
    int pairWithStep;
//  ScheduleNode* wait;

    /** @brief For end actions, if they've been applied yet; for dummy steps, whether to add their temporal constraints.
     *
     * This serves two purposes:
     * - If <code>time_spec</code> is <code>Planner::E_AT_END</code>, then if this variable holds the value <code>true</code>, the end of the action has been applied.  Otherwise, it's a placeholder.
     * - If this is a dummy event, then if this variable holds the value <code>true</code>, the temporal constraints are safe to add (or must always be added) to the STP/LP.
     */
    bool getEffects;
    double lpTimestamp;
    double lpMinTimestamp;
    double lpMaxTimestamp;
    
    /** @brief For TILs, the index of the TIL; for dummy steps, the index of the relevant preference. */
    int divisionID;
    set<int> needToFinish;
    
    #ifdef STOCHASTICDURATIONS
    StochasticTimestampData * stochasticTimestamp;
    #endif
    
    FFEvent(instantiatedOp* a, const double & dMin, const double & dMax);
    FFEvent(instantiatedOp* a, const int & pw, const double & dMin, const double & dMax);
    FFEvent(instantiatedOp* a, const int & s, const int & pw, const double & dMin, const double & dMax);
    FFEvent(const int & t);

    virtual ~FFEvent();
    
    virtual void passInMinMax(const double & a, const double & b) {
        lpMinTimestamp = a;
        lpMaxTimestamp = b;
    }

    FFEvent(const FFEvent & f);
//  FFEvent(ScheduleNode* s, const bool & b);
    FFEvent();
    FFEvent & operator=(const FFEvent & f);
    bool operator==(const FFEvent & f) const {
        if (time_spec == Planner::E_AT_END && pairWithStep != f.pairWithStep) return false;
        return (action == f.action && time_spec == f.time_spec && minDuration == f.minDuration && maxDuration == f.maxDuration && pairWithStep == f.pairWithStep && getEffects == f.getEffects && divisionID == f.divisionID);
    }

    bool isDummyStep() const {
        return (time_spec == Planner::E_CONTINUOUS
                || time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE || time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE
                || time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_FALSE || time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE
                || time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION);
    }

    static void printPlan(const list<FFEvent> & toPrint);
        
    static const FFEvent & getDummyStep() {
        static FFEvent toReturn;
        toReturn.time_spec = Planner::E_CONTINUOUS;
        toReturn.getEffects = false;
        
        return toReturn;
    }
    

};

};

#endif
