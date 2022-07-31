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

#include "colintotalordertransformer.h"
#include "temporalconstraints.h"
#include "RPGBuilder.h"
#include "temporalanalysis.h"

#include "colours.h"

using Inst::Literal;
using std::cerr;
using std::endl;

namespace Planner
{

bool applyDebug = false;
    
TemporalConstraints * TotalOrderTransformer::cloneTemporalConstraints(const TemporalConstraints * const other, const int extendBy)
{
    return new TemporalConstraints(*other, extendBy);
}

TemporalConstraints * TotalOrderTransformer::emptyTemporalConstraints()
{
    return new TemporalConstraints();
}

int TotalOrderTransformer::stepThatMustPrecedeUnfinishedActions(const TemporalConstraints * const cons) const
{
    return cons->getMostRecentStep();
}

double TotalOrderTransformer::latestTimePointOfActionsStartedHere(const int & i) const
{
    static const int tilCount = RPGBuilder::getTILVec().size();
    
    if (tilCount >= i) return DBL_MAX;
    return (RPGBuilder::getTILVec()[i]->duration);
}


static unsigned int oldStepCount;

void TOTHelper_updateForInstantaneousEffects(MinimalState & theState, const unsigned int & stepID, list<Literal*> & delEffs, list<Literal*> & addEffs)
{
    {
        list<Literal*>::iterator effItr = delEffs.begin();
        const list<Literal*>::iterator effEnd = delEffs.end();

        for (; effItr != effEnd; ++effItr) {
            const int litID = (*effItr)->getStateID();
            
            {
                const StateBFacts::iterator stateItr = theState.firstAnnotations.find(litID);
                if (stateItr != theState.firstAnnotations.end()) {
                    for (int pass = 0; pass < 2; ++pass) {
                        set<int> & actionEndPoints = (pass ? stateItr->second.second : stateItr->second.first);
                        
                        if (!actionEndPoints.empty()) {
                            
                            if (applyDebug) {
                                if (pass) {
                                    cout << "\t" << *(*effItr) << " was an invariant of some compression-safe actions, but has now been deleted\n";
                                } else {
                                    cout << "\t" << *(*effItr) << " was a pending end-effect of compression-safe actions, but has now been deleted\n";
                                }
                            }
                            
                            set<int>::const_iterator epItr = actionEndPoints.begin();
                            const set<int>::const_iterator epEnd = actionEndPoints.end();
                            
                            for (; epItr != epEnd; ++epItr) {
                                if (*epItr != stepID) {
                                    theState.temporalConstraints->addOrdering(*epItr, stepID, true);
                                    if (pass == 0) {
                                        stateItr->second.second.erase(*epItr);
                                    }
                                    StateBFacts::iterator cuItr = theState.firstAnnotations.begin();
                                    while (cuItr != stateItr) {
                                        cuItr->second.first.erase(*epItr);
                                        cuItr->second.second.erase(*epItr);
                                        if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                                            const StateBFacts::iterator cuDel = cuItr++;
                                            theState.firstAnnotations.erase(cuDel);
                                        } else {
                                            ++cuItr;
                                        }
                                    }
                                    
                                    cuItr = stateItr;
                                    ++cuItr;
                                    while (cuItr != theState.firstAnnotations.end()) {
                                        cuItr->second.first.erase(*epItr);
                                        cuItr->second.second.erase(*epItr);
                                        if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                                            const StateBFacts::iterator cuDel = cuItr++;
                                            theState.firstAnnotations.erase(cuDel);
                                        } else {
                                            ++cuItr;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    
                    theState.firstAnnotations.erase(stateItr);
                }                                
            }
            
            theState.first.erase(litID);
            
        }
    }

    {
        list<Literal*>::iterator effItr = addEffs.begin();
        const list<Literal*>::iterator effEnd = addEffs.end();

        for (; effItr != effEnd; ++effItr) {
            const int litID = (*effItr)->getStateID();
            theState.first.insert(litID);
            {
                const StateBFacts::iterator stateItr = theState.firstAnnotations.find(litID);
                if (stateItr != theState.firstAnnotations.end()) {
                    set<int> & actionEndPoints = stateItr->second.first;
                    
                    if (!actionEndPoints.empty()) {
                        
                        if (applyDebug) {
                            cout << "\t" << *(*effItr) << " was a pending end-effect of compression-safe actions, but has now been added\n";
                        }
                        
                        set<int>::const_iterator epItr = actionEndPoints.begin();
                        const set<int>::const_iterator epEnd = actionEndPoints.end();
                        
                        for (; epItr != epEnd; ++epItr) {
                            if (*epItr != stepID) {
                                theState.temporalConstraints->addOrdering(*epItr, stepID, true);
                                stateItr->second.second.erase(*epItr);                               
                                
                                StateBFacts::iterator cuItr = theState.firstAnnotations.begin();
                                while (cuItr != stateItr) {
                                    cuItr->second.first.erase(*epItr);
                                    cuItr->second.second.erase(*epItr);
                                    if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                                        const StateBFacts::iterator cuDel = cuItr++;
                                        theState.firstAnnotations.erase(cuDel);
                                    } else {
                                        ++cuItr;
                                    }
                                }
                                
                                cuItr = stateItr;
                                ++cuItr;
                                while (cuItr != theState.firstAnnotations.end()) {
                                    cuItr->second.first.erase(*epItr);
                                    cuItr->second.second.erase(*epItr);
                                    if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                                        const StateBFacts::iterator cuDel = cuItr++;
                                        theState.firstAnnotations.erase(cuDel);
                                    } else {
                                        ++cuItr;
                                    }
                                }
                            }
                        }
                    }
                    actionEndPoints.clear();
                    if (stateItr->second.second.empty()) {
                        theState.firstAnnotations.erase(stateItr);
                    }
                }
            }
        }
    }
}

void TOTHelper_meetPreconditions(MinimalState & theState, const int & stepID, const list<Literal*> & reservePositive)
{

    if (applyDebug) {
        cout << "\tPreconditions requested at " << stepID << endl;
    }


    const list<Literal*> & reserve = reservePositive;

    list<Literal*>::const_iterator precItr = reserve.begin();
    const list<Literal*>::const_iterator precEnd = reserve.end();

    for (; precItr != precEnd; ++precItr) {
        const int litID = (*precItr)->getStateID();
        #ifndef NDEBUG
        StateFacts::iterator stateItr = theState.first.find(litID);

        if (stateItr == theState.first.end()) {
            cerr << "Fatal internal error: applying an action whose preconditions aren't met\n";
            exit(1);
        }
        #endif
        
        
            
        StateBFacts::iterator stateBItr = theState.firstAnnotations.find(litID); 
        if (stateBItr != theState.firstAnnotations.end()) {
            
            
            set<int>::const_iterator epItr = stateBItr->second.first.begin();             
            const set<int>::const_iterator epEnd = stateBItr->second.first.end();
            
            for (; epItr != epEnd; ++epItr) {
                if (*epItr != stepID) {
                    theState.temporalConstraints->addOrdering(*epItr, stepID, true);
                    stateBItr->second.second.erase(*epItr);
                    
                    StateBFacts::iterator cuItr = theState.firstAnnotations.begin();
                    while (cuItr != stateBItr) {
                        cuItr->second.first.erase(*epItr);
                        cuItr->second.second.erase(*epItr);
                        if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                            const StateBFacts::iterator cuDel = cuItr++;
                            theState.firstAnnotations.erase(cuDel);
                        } else {
                            ++cuItr;
                        }
                    }
                    
                    cuItr = stateBItr;
                    ++cuItr;
                    while (cuItr != theState.firstAnnotations.end()) {
                        cuItr->second.first.erase(*epItr);
                        cuItr->second.second.erase(*epItr);
                        if (cuItr->second.first.empty() && cuItr->second.second.empty()) {
                            const StateBFacts::iterator cuDel = cuItr++;
                            theState.firstAnnotations.erase(cuDel);
                        } else {
                            ++cuItr;
                        }
                    }
                }
            }
            
            if (stateBItr->second.second.empty()) {
                theState.firstAnnotations.erase(stateBItr);
            }         
        }
    }        
}

void TOTHelper_applyNumericEffects(MinimalState & theState, const list<int> & numEffs, const double & minDur, const double & maxDur)
{

    list<int>::const_iterator effItr = numEffs.begin();
    const list<int>::const_iterator effEnd = numEffs.end();

    list<pair<int, pair<double, double> > > updated;

    for (; effItr != effEnd; ++effItr) {
        RPGBuilder::RPGNumericEffect & rpgEff = RPGBuilder::getNumericEff()[*effItr];
        updated.push_back(pair<int, pair<double, double> >(rpgEff.fluentIndex, rpgEff.applyEffectMinMax(theState.secondMin, theState.secondMax, minDur, maxDur)));
    }

    list<pair<int, pair<double, double> > >::iterator updItr = updated.begin();
    const list<pair<int, pair<double, double> > >::iterator updEnd = updated.end();

    for (; updItr != updEnd; ++updItr) {
        theState.secondMin[updItr->first] = updItr->second.first;
        theState.secondMax[updItr->first] = updItr->second.second;
    }
    
}



MinimalState * TotalOrderTransformer::applyAction(MinimalState & theStateHidden, vector<double> & minTimestamps, const ActionSegment & a, const bool & inPlace,
        const double & minDur, const double & maxDur)
{
    const int previousMostRecent = theStateHidden.temporalConstraints->getMostRecentStep();

    applyDebug = Globals::globalVerbosity & 1048576;

    unsigned int extensionNeeded = 0;

    if (applyDebug) {
        oldStepCount = theStateHidden.temporalConstraints->size();
        cout << "Applying action.  Previously had space for constraints on " << oldStepCount << " steps\n";
        assert(oldStepCount == theStateHidden.planLength);
    }


    if (a.first) {
        if (a.second == VAL::E_AT_START) {
            ++extensionNeeded;
            const int actID = a.first->getID();

            if (!RPGBuilder::getRPGDEs(actID).empty()) {
                ++extensionNeeded; // isn't a non-temporal action
                if (applyDebug) cout << "Temporal record extension of two needed - starting " << *(a.first) << "\n";
            } else {
                if (applyDebug) cout << "Temporal record extension of one needed - applying an instantaneous action, " << *(a.first) << "\n";
            }
        } else {
            if (applyDebug) cout << "Temporal record extension of zero needed - is the end of " << *(a.first) << "\n";
        }
    } else {
        extensionNeeded = (a.divisionID - theStateHidden.nextTIL) + 1;
        if (applyDebug) {
            cout << "Temporal record extension of " << extensionNeeded << " needed - applying TIL " << a.divisionID;
            if (a.divisionID != theStateHidden.nextTIL) {
                cout << "; next one would be " << theStateHidden.nextTIL;
            }
            cout << "\n";
        }
    }
    MinimalState * const workOn = (inPlace ? &theStateHidden : new MinimalState(theStateHidden, extensionNeeded));

    if (inPlace && extensionNeeded) {
        theStateHidden.temporalConstraints->extend(extensionNeeded);
    }

    if (applyDebug) {
        const unsigned int newStepCount = workOn->temporalConstraints->size();
        cout << "Now have space for constraints on " << newStepCount << " steps\n";
        assert(newStepCount - oldStepCount == extensionNeeded);
    }

    if (!a.first) { // applying a TIL
        static vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getTILVec();
        
        for (; workOn->nextTIL <= a.divisionID; ++(workOn->nextTIL)) {
            
            TOTHelper_updateForInstantaneousEffects(*workOn,  workOn->planLength, tilVec[workOn->nextTIL]->delEffects, tilVec[workOn->nextTIL]->addEffects);
            ++workOn->planLength;
        }                
        
        workOn->temporalConstraints->setMostRecentStep(workOn->planLength - 1);
         
        if (previousMostRecent != -1) {
            const int newMostRecent = workOn->temporalConstraints->getMostRecentStep();
            workOn->temporalConstraints->addOrdering(previousMostRecent, newMostRecent, true); // then impose the total ordering constraint
            if (Globals::globalVerbosity & 4096) {
                cout << "TO constraint: " << previousMostRecent << " comes before " << newMostRecent << std::endl;
            }
        }
            
        return workOn;
    }

    const int actID = a.first->getID();

    if (a.second == VAL::E_AT_START) {

        if (RPGBuilder::getRPGDEs(actID).empty()) { // non-temporal action
            list<Literal*> & pres = RPGBuilder::getStartPropositionalPreconditions()[actID];
            
            TOTHelper_meetPreconditions(*workOn, workOn->planLength, pres);

            list<Literal*> & delEffs = RPGBuilder::getStartPropositionDeletes()[actID];
            list<Literal*> & addEffs = RPGBuilder::getStartPropositionAdds()[actID];

            TOTHelper_updateForInstantaneousEffects(*workOn, workOn->planLength, delEffs, addEffs);

            TOTHelper_applyNumericEffects(*workOn, RPGBuilder::getStartEffNumerics()[actID], minDur, maxDur);
            
            workOn->temporalConstraints->setMostRecentStep(workOn->planLength);

            ++workOn->planLength;

            if (previousMostRecent != -1) {
                const int newMostRecent = workOn->temporalConstraints->getMostRecentStep();
                workOn->temporalConstraints->addOrdering(previousMostRecent, newMostRecent, true); // then impose the total ordering constraint
                if (Globals::globalVerbosity & 4096) {
                    cout << "TO constraint: " << previousMostRecent << " comes before " << newMostRecent << std::endl;
                }
            }

            return workOn;
        }
        
        const bool skip = (TemporalAnalysis::canSkipToEnd(actID) ? SAFETOSKIP : UNSAFETOSKIP);
        
        workOn->temporalConstraints->setMostRecentStep(workOn->planLength);
        
        const int startStepID = workOn->planLength++;
        const int endStepID = workOn->planLength++;
        
        if (applyDebug) {
            assert(workOn->planLength == workOn->temporalConstraints->size());
            cout << "New step IDs: " << startStepID << "," << endStepID << "\n";
        }
        
        workOn->temporalConstraints->addOrdering(startStepID, endStepID, false);
        
        {
            if (applyDebug) cout << " * Requesting start preconditions\n";
            list<Literal*> & pres = RPGBuilder::getProcessedStartPropositionalPreconditions()[actID];
            TOTHelper_meetPreconditions(*workOn, startStepID, pres);
        }
        
        {
            
            list<Literal*> & delEffs = RPGBuilder::getStartPropositionDeletes()[actID];
            list<Literal*> & addEffs = RPGBuilder::getStartPropositionAdds()[actID];
            
            if (applyDebug) cout << " * Applying start effects.  Start adds: " << addEffs.size() << ", Start deletes: " << delEffs.size() << "\n";                        
                        
            TOTHelper_updateForInstantaneousEffects(*workOn, startStepID, delEffs, addEffs);
        }
        
        TOTHelper_applyNumericEffects(*workOn, RPGBuilder::getStartEffNumerics()[actID], minDur, maxDur);
        
        if (skip == SAFETOSKIP) {
            
            if (applyDebug) cout << " * Requesting invariants for compression-safe action\n";
            
            list<Literal*> & pres = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
            
            list<Literal*>::const_iterator pItr = pres.begin();
            const list<Literal*>::const_iterator pEnd = pres.end();
            
            for (; pItr != pEnd; ++pItr) {
                if (applyDebug) {
                    cout << "   - " << *(*pItr) << endl;
                }
                workOn->firstAnnotations[(*pItr)->getStateID()].second.insert(endStepID); // associate the end of this action with an invariant on this fact
            }
            
            {
                
                list<Literal*> & delEffs = RPGBuilder::getEndPropositionDeletes()[actID];
            
                list<Literal*>::const_iterator effItr = delEffs.begin();
                const list<Literal*>::const_iterator effEnd = delEffs.end();
                
                for (; effItr != effEnd; ++effItr) {
                    workOn->first.erase((*effItr)->getStateID());
                    workOn->firstAnnotations.erase((*effItr)->getStateID());
                }

            
            }

            
            list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];
            
            if (applyDebug) cout << " * Recording pending effects of a compression-safe action\n";
            
            list<Literal*>::const_iterator effItr = addEffs.begin();
            const list<Literal*>::const_iterator effEnd = addEffs.end();
            
            for (; effItr != effEnd; ++effItr) {
                if (!workOn->first.insert((*effItr)->getStateID()).second) {
                    //cout << COLOUR_light_red << "Warning: compression-safe action end-adds a fact that is already true\n";
                    
                }
                workOn->firstAnnotations[(*effItr)->getStateID()].first.insert(endStepID); // associate the end of this action with an effect on this fact
                if (applyDebug) {
                    cout << "   - " << *(*effItr) << endl;
                }
                
            }
            
            ++(workOn->actionsExecuting);
            
        } else {

            {
                if (applyDebug) cout << " * Non-compression-safe action - recording invariants\n";
                
                list<Literal*> & pres = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
                
                list<Literal*>::const_iterator pItr = pres.begin();
                const list<Literal*>::const_iterator pEnd = pres.end();
                
                for (; pItr != pEnd; ++pItr) {
                    ++(workOn->invariants.insert(make_pair((*pItr)->getStateID(),0)).first->second);
                    
                }
            }

            
            workOn->startedActions[actID].insert(endStepID);
            ++(workOn->actionsExecuting);
        }
        
        if (previousMostRecent != -1) {
            const int newMostRecent = workOn->temporalConstraints->getMostRecentStep();
            workOn->temporalConstraints->addOrdering(previousMostRecent, newMostRecent, true); // then impose the total ordering constraint
            if (Globals::globalVerbosity & 4096) {
                cout << "TO constraint: " << previousMostRecent << " comes before " << newMostRecent << std::endl;
            }
        }
        
        return workOn;
    }

    
    // otherwise, we're ending a non-compression-safe action
    
    map<int, set<int> >::iterator saItr = workOn->startedActions.find(actID);
    
    assert(saItr != workOn->startedActions.end());
    
    set<int>::iterator endItr = saItr->second.begin();
    
    const int endStepID = *endItr;
    //const int startStepID = endStepID - 1;
    saItr->second.erase(endItr);
    if (saItr->second.empty()) workOn->startedActions.erase(saItr);
    
    --(workOn->actionsExecuting);
    
    workOn->temporalConstraints->setMostRecentStep(endStepID);

    {
        if (applyDebug) cout << " * De-registering invariants\n";
        
        list<Literal*> & pres = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
        
        list<Literal*>::const_iterator pItr = pres.begin();
        const list<Literal*>::const_iterator pEnd = pres.end();
        
        for (; pItr != pEnd; ++pItr) {
            map<int,int>::iterator invItr = workOn->invariants.find((*pItr)->getStateID());
            assert(invItr != workOn->invariants.end());
            if (!(--(invItr->second))) {
                workOn->invariants.erase(invItr);
            }
        }
    }

    {
        if (applyDebug) cout << " * Requesting end preconditions\n";
        list<Literal*> & pres = RPGBuilder::getEndPropositionalPreconditions()[actID];
        TOTHelper_meetPreconditions(*workOn, endStepID, pres);
    }
   
      
    {
        if (applyDebug) cout << " * Recording end effects\n";
        list<Literal*> & delEffs = RPGBuilder::getEndPropositionDeletes()[actID];
        list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];

        TOTHelper_updateForInstantaneousEffects(*workOn, endStepID, delEffs, addEffs);
    }
    
    TOTHelper_applyNumericEffects(*workOn, RPGBuilder::getEndEffNumerics()[actID], minDur, maxDur);
    


    if (previousMostRecent != -1) {
        const int newMostRecent = workOn->temporalConstraints->getMostRecentStep();
        workOn->temporalConstraints->addOrdering(previousMostRecent, newMostRecent, true); // then impose the total ordering constraint
        if (Globals::globalVerbosity & 4096) {
            cout << "TO constraint: " << previousMostRecent << " comes before " << newMostRecent << std::endl;
        }
    }

    return workOn;
};



};
