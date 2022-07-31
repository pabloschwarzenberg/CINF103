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


#ifndef PARTIALORDERTRANSFORMER_H
#define PARTIALORDERTRANSFORMER_H

#include "minimalstate.h"

namespace Planner
{

class TemporalConstraints;

class PartialOrderTransformer : public StateTransformer
{

public:
    PartialOrderTransformer() {
    }

    virtual ~PartialOrderTransformer() {
    }

    virtual TemporalConstraints * cloneTemporalConstraints(const TemporalConstraints * const, const int extendBy = 0);
    virtual TemporalConstraints * emptyTemporalConstraints();
    virtual MinimalState * applyAction(MinimalState & s, const vector<double> & minTimestamps,
                                       const ActionSegment & a, const bool & inPlace, const double & minDur, const double & maxDur);
    #ifdef POPF3ANALYSIS
    virtual void updateWhenEndOfActionIs(MinimalState & s, const int & actID, const int & stepID, const double & newTS);
    #endif

};

}

#endif              // PARTIALORDERTRANSFORMER_H
