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

#ifndef FFEVENT_H
#define FFEVENT_H

#include <limits>

#include <ptree.h>

namespace Inst {
    class instantiatedOp;
};

using Inst::instantiatedOp;

#include <set>
using std::set;

namespace Planner {

#ifdef STOCHASTICDURATIONS
class StochasticTimestampData;
#endif


class FFEvent
{

public:

    static int tilLimit;

    instantiatedOp* action;
    VAL::time_spec time_spec;
    double minDuration;
    double maxDuration;
    int pairWithStep;
//  ScheduleNode* wait;
    bool getEffects;
    double lpTimestamp;
    double lpMinTimestamp;
    double lpMaxTimestamp;
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
        if (time_spec != VAL::E_AT_START && pairWithStep != f.pairWithStep) return false;
        return (action == f.action && time_spec == f.time_spec && minDuration == f.minDuration && maxDuration == f.maxDuration && pairWithStep == f.pairWithStep && getEffects == f.getEffects && divisionID == f.divisionID);
    }

    static void printPlan(const list<FFEvent> & toPrint, int statesEvaluated = 0, double quality = std::numeric_limits<double>::quiet_NaN(), ostream& out = std::cout);
};

};

#endif
