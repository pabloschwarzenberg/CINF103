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

#ifndef STOCHASTICDURATIONS_H
#define STOCHASTICDURATIONS_H

#include "FFEvent.h"
#include "minimalstate.h"

#include <vector>
#include <string>
#include <utility>

using std::string;
using std::vector;
using std::pair;

namespace Planner {
    
/** @brief  A small amount of data about a given timestamp, based on a sequence of stochastic predecessors. */
class StochasticTimestampData {
  
protected:
    StochasticTimestampData() {
    }
    
public:
    
    /** @brief  Destructor - actual implementation left to subclasses. */
    virtual ~StochasticTimestampData() {
    }
    
    /** @brief  Return a copy of the object. */
    virtual StochasticTimestampData * clone() const = 0;
    
    /** @brief  Return a timestamp for use when computing the heuristic. */
    virtual double getTimestampForRPGHeuristic() const = 0;
};

/** @brief  Class to manage stochastic durations. */
class StochasticDurations
{

protected:
    StochasticDurations();

    double evaluateActionDurationAtPercentile(const int & act);

public:
    
    /** @brief  Add any book-keeping data to the initial state. */
    virtual void prepareTheInitialState(MinimalState & initialState) = 0;
    
    /** @brief  Update the stochastic timestamp data of the most recent step in a plan.
     * 
     * @param newState The state reached during search
     * @param plan     The header of the plan (plan to the parent of the state)
     * @param newStep  The new step to be added to the plan (leading from the parent state
     *                 to the new state)
     * @param newStepPairedWith  If the new step is the start of a compression-safe action, this should be
     *                           the plan step with which the new step is paired.     
     * @param stepID   The index of the new step in the plan
     * @param reachedAllTheGoals   Return-by-reference, set to <code>true</code> if this was considered to
     *                             be a goal state.
     * @retval <code>true</code>   If the timestamp was updated successfully
     * @retval <code>false</code>  If the distribution of the latest timestamp exceeded the conditions
     *                             imposed on solutions.   
     */
    virtual bool updateTimestampsOfNewPlanStep(const MinimalState & prevState, MinimalState & newState,
                                               list<FFEvent> & header, FFEvent * const newStep,
                                               FFEvent * const newStepPairedWith, const int & stepID,
                                               bool & reachedAllTheGoals) = 0;


};

extern StochasticDurations * durationManager;
extern void setDurationManager(const string & name);
extern void setSolutionDeadlineTimeToLatestGoal();
extern double solutionDeadlineTime;
extern double solutionDeadlinePercentage;

class PDF {
    
protected:
    
    double expectedValue;
    
    PDF() {
    }
    
public:
    inline const double & getExpectedValue() const {
        return expectedValue;
    }
            
    virtual double getValueAtPercentile() = 0;                        
    virtual double sample() = 0;
};


extern vector<PDF*> PDFsForVariable;
extern void initialiseDistributions();

};

#endif // STOCHASTICDURATIONS_H
