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

#ifndef TOTALORDERTRANSFORMER_H
#define TOTALORDERTRANSFORMER_H

#include "minimalstate.h"

namespace Planner
{

class TemporalConstraints;

/**
 *   A class wrapping up the functionality of applying an action to a state, where
 *  the actions are constrained to occur in a strict total-order.  This follows,
 *  for example, the behaviour of CRIKEY and COLIN.
 *  @see StateTransformer, PartialOrderTransformer
 */
class TotalOrderTransformer : public StateTransformer
{

public:
    TotalOrderTransformer() {
    }

    virtual ~TotalOrderTransformer() {
    }

    /**
     *  Returns the index of the most recent step in the plan - the step which, due to the total order constraints,
     *  must precede the ends of all actions that have started but not yet finished.
     *
     *  @param  cons  The temporal constraints from which to extract the index of the appropriate step.
     *  @return       If the plan is empty, -1; otherwise, the index of the step most recently added.
     *
     *  @see TemporalConstraints
     */
    virtual int stepThatMustPrecedeUnfinishedActions(const TemporalConstraints * const cons) const;
    
    /**
     *  Return the upper bound on the time-stamp of the next snap-action applied, after the
     *  specified number of TILs have been applied.  As the plan must follow a total order, all
     *  actions before the next TIL can come no later than then.
     *
     *  @param tilIndexApplied  How many TILs have been applied
     *  @return  The upper bound of the time-stamp of the next action applied
     */
    virtual double latestTimePointOfActionsStartedHere(const int & tilIndexApplied) const;
        
    

    virtual TemporalConstraints * cloneTemporalConstraints(const TemporalConstraints * const, const int extendBy = 0);
    virtual TemporalConstraints * emptyTemporalConstraints();
    virtual MinimalState * applyAction(MinimalState & s, vector<double> & minTimestamps, const ActionSegment & a, const bool & inPlace, const double & minDur, const double & maxDur);

};

}

#endif              // TOTALORDERTRANSFORMER_H
