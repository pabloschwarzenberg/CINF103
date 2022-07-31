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

#ifndef CHOOSEPRECONDITIONS_H
#define CHOOSEPRECONDITIONS_H

#include "RPGBuilder.h"

#include "minimalstate.h"

#include <vector>
#include <utility>

using std::vector;
using std::pair;


namespace Planner {

class NNFNode;

namespace NNFPreconditionChooser {
    
    struct Supporters {
        int pref;
        bool meetsTheTrigger;
        bool satisfyIt;
        
        set<int> propositions;
        set<int> negativePropositions;
        set<int> numerics;
        
        Supporters(const int & p, const bool & t)
        : pref(p), meetsTheTrigger(t), satisfyIt(true) {
        }
    };
    
    extern pair<bool,double> satisfyNNFEarly(MinimalState & s, const vector<double> & minTimestamps, NNFNode* toVisit,
                                             Supporters & chosen);          

    extern bool collectNNFDependencies(MinimalState & s, NNFNode* toVisit, Supporters & chosen);          

};

};

#endif // CHOOSEPRECONDITIONS_H
