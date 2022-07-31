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

#include "totalordertransformer.h"
#include "temporalconstraints.h"
#include "RPGBuilder.h"

using Inst::Literal;

namespace Planner
{

TemporalConstraints * TotalOrderTransformer::cloneTemporalConstraints(const TemporalConstraints * const other, const int extendBy)
{
    return t.cloneTemporalConstraints(other, extendBy);
}

TemporalConstraints * TotalOrderTransformer::emptyTemporalConstraints()
{
    return t.emptyTemporalConstraints();
}

int TotalOrderTransformer::stepThatMustPrecedeUnfinishedActions(const TemporalConstraints * const cons) const
{
    return cons->getMostRecentStep();
}

double TotalOrderTransformer::latestTimePointOfActionsStartedHere(const int & i) const
{
    static const int tilCount = RPGBuilder::getNonAbstractedTILVec().size();
    
    if (i < tilCount) {
        return (RPGBuilder::getNonAbstractedTILVec()[i]->duration);
    } else {
        return DBL_MAX;
    }
}


MinimalState * TotalOrderTransformer::applyAction(MinimalState & theStateHidden, vector<double> & minTimestamps, list<pair<int, FFEvent> > & newDummySteps, bool & constraintsSatisfied, const ActionSegment & a, const bool & inPlace,
        const double & minDur, const double & maxDur)
{
    const int previousMostRecent = theStateHidden.temporalConstraints->getMostRecentStep();

    MinimalState * toReturn = t.applyAction(theStateHidden, minTimestamps, newDummySteps, constraintsSatisfied,  a, inPlace, minDur, maxDur);

    if (previousMostRecent != -1) { // if this isn't the first step in the plan
        const int newMostRecent = toReturn->temporalConstraints->getMostRecentStep();
        toReturn->temporalConstraints->addOrdering(previousMostRecent, newMostRecent, true); // then impose the total ordering constraint
        if (Globals::globalVerbosity & 4096) {
            cout << "TO constraint: " << previousMostRecent << " comes before " << newMostRecent << std::endl;
        }
    } else {
        if (Globals::globalVerbosity & 4096) {
            const int newMostRecent = toReturn->temporalConstraints->getMostRecentStep();
            cout << "No TO constraint for step " << newMostRecent << std::endl;
        }
    }

    return toReturn;
};

#ifdef POPF3ANALYSIS
void TotalOrderTransformer::updateWhenEndOfActionIs(MinimalState & s, const int & actID, const int & stepID, const double & newTS)
{
    t.updateWhenEndOfActionIs(s,actID,stepID,newTS);
}
#endif


};
