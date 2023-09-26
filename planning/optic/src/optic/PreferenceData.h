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

#ifndef PREFERENCEDATA_H
#define PREFERENCEDATA_H

#include <utility>
using std::make_pair;

namespace Planner {
    
class NNFNode;
class NNF_Flat;



class PreferenceData {
    
public:
    
    enum { GoalIdx = 0, TriggerIdx = 1};
    
    friend class PreferenceHandler;
    friend class PreferenceFSA;
    
    
    vector<pair<NNFNode*, bool> > nodes;
    vector<NNF_Flat*> flattened;
    
    vector<list<int> > conditionLiterals;
    vector<list<int> > conditionNegativeLiterals;
    vector<list<int> > conditionNums;
    
    PreferenceData()
    : nodes(2, make_pair((NNFNode*)0, false)), flattened(2,(NNF_Flat*)0),
              conditionLiterals(2), conditionNegativeLiterals(2),
                        conditionNums(2)
                        {        
                        }
                                                        
};

};

#endif