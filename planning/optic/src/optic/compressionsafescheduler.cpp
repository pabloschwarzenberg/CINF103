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

#include "compressionsafescheduler.h"
#include "temporalconstraints.h"
#include "RPGBuilder.h"
#include "temporalanalysis.h"

namespace Planner {

bool CompressionSafeScheduler::safeToUseThis = false;
    
bool CompressionSafeScheduler::canUseThisScheduler()
{

    safeToUseThis = true;
    
    const int actCount = RPGBuilder::rogueActions.size();
    
    for (int a = 0; a < actCount; ++a) {
        if (RPGBuilder::rogueActions[a]) {
            continue;
        }
        
        if (!TemporalAnalysis::canSkipToEnd(a)) {
            safeToUseThis = false;
            return false;
        };
                
    }
    
    return true;
}

    
void CompressionSafeScheduler::assignTimestamps(const MinimalState & s,
                                                         list<FFEvent> & header,
                                                         list<FFEvent> & now)
{

    if (!safeToUseThis) {
        std::cerr << "Fatal internal error - attempting to use the simple compression-safe scheduler on a problem that needs at least the STP solver\n";
        assert(safeToUseThis);
        exit(1);
    }
    
    const int planSize = header.size() + now.size();
    
    vector<FFEvent*> planAsAVector(planSize);
    vector<int> fanIn(planSize, 0);
    vector<list<int> > fanOut(planSize);
    list<int> visit;
    
    {
        int i = 0;
        const map<int,bool> * stepsBefore;
        for (int pass = 0; pass < 2; ++pass) {
            list<FFEvent> & currList = (pass ? now : header);
            list<FFEvent>::iterator clItr = currList.begin();
            const list<FFEvent>::iterator clEnd = currList.end();
            
            for (; clItr != clEnd; ++clItr, ++i) {
                planAsAVector[i] = &(*clItr);
                stepsBefore = s.temporalConstraints->stepsBefore(i);
                fanIn[i] = (stepsBefore ? stepsBefore->size() : 0);
                if (!fanIn[i]) {
                    visit.push_back(i);                
                } else {
                    map<int,bool>::const_iterator sbItr = stepsBefore->begin();
                    const map<int,bool>::const_iterator sbEnd = stepsBefore->end();
                    
                    for (; sbItr != sbEnd; ++sbItr) {
                        fanOut[sbItr->first].push_back(i);
                    }
                }
            }
        }
    }
    
    int i;
    const map<int,bool> * stepsBefore;
    while (!visit.empty()) {
        i = visit.front();
        visit.pop_front();
        
        double & currTS = planAsAVector[i]->lpTimestamp;
        
        stepsBefore = s.temporalConstraints->stepsBefore(i);
        
        if (stepsBefore) {
            map<int,bool>::const_iterator sbItr = stepsBefore->begin();
            const map<int,bool>::const_iterator sbEnd = stepsBefore->end();
            
            for (double prevTS; sbItr != sbEnd; ++sbItr) {
                prevTS = planAsAVector[sbItr->first]->lpTimestamp;
                if (sbItr->second) {
                    prevTS += 0.001;
                }
                if (prevTS > currTS) {
                    currTS = prevTS;
                }
            }
            
            if (planAsAVector[i]->time_spec == Planner::E_AT_END) {
                const int & pairedWith = planAsAVector[i]->pairWithStep;
                const double minDurationSinceStart = planAsAVector[pairedWith]->lpTimestamp + planAsAVector[pairedWith]->minDuration;
                if (minDurationSinceStart > currTS) {
                    currTS = minDurationSinceStart;
                }
            }
            
        } else {
            currTS = 0.0;
        }
        
        planAsAVector[i]->lpMinTimestamp = currTS;
        planAsAVector[i]->lpMaxTimestamp = DBL_MAX;
        
        list<int>::const_iterator foItr = fanOut[i].begin();
        const list<int>::const_iterator foEnd = fanOut[i].end();
        
        for (; foItr != foEnd; ++foItr) {
            if (!(--fanIn[*foItr])) {
                visit.push_back(*foItr);
            }
        }
        
    }
    
}



};