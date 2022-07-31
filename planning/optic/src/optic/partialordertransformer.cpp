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

#include "partialordertransformer.h"
#include "temporalconstraints.h"
#include "numericanalysis.h"
#include "temporalanalysis.h"

#include "colours.h"

#include "RPGBuilder.h"
#include "PreferenceHandler.h"
#include "PreferenceData.h"

#include "globals.h"

using Inst::Literal;
using std::endl;
using std::cerr;

static bool applyDebug;

namespace Planner
{

TemporalConstraints * PartialOrderTransformer::cloneTemporalConstraints(const TemporalConstraints * const other, const int extendBy)
{
    return new TemporalConstraints(*other, extendBy);
}

TemporalConstraints * PartialOrderTransformer::emptyTemporalConstraints()
{
    return new TemporalConstraints();
}

typedef pair<set<pair<StepAndBeforeOrAfter,double> >, set<StepAndBeforeOrAfter> > GoalFalseTrueAfterStep;

double POTHelper_getTimeOfStep(MinimalState & theState, const vector<double> & minTimestamps, const int & stepID, const double & tsOfThisStep) {
    double timeNow = (tsOfThisStep >= 0.0 ? tsOfThisStep : 0.0);
            
    const map<int,bool> * const beforeNow = theState.temporalConstraints->stepsBefore(stepID);
    
    if (beforeNow) {
        double localT;
        map<int,bool>::const_iterator bnItr = beforeNow->begin();
        const map<int,bool>::const_iterator bnEnd = beforeNow->end();
        
        for (; bnItr != bnEnd; ++bnItr) {
            localT = minTimestamps[bnItr->first];
            if (bnItr->second) {
                localT += 0.001;
            }
            if (localT > timeNow) {
                timeNow = localT;
            }
        }
    }
    
    return timeNow;
}

struct LocalNNFData {
    NNF_Flat* first;
    vector<double> second;

    vector<int> outstandingPreconditionsForSingleAdderForCell;
    vector<double> minForCell;
    
    LocalNNFData(NNF_Flat * const f, const int & capacity)
        : first(f), second(capacity,0.0)
    {
    }
};


void POTHelper_updateWithinCosts(MinimalState & theState,
                                 const map<int,GoalFalseTrueAfterStep> & earliestGoalPointNow,
                                 const vector<double> & minTimestamps)
{
    
    static const bool debug = (Globals::globalVerbosity & 1048576);
    
    if (earliestGoalPointNow.empty()) {
        return;
    }
    
    // PreferenceStatusArray & psa = (*(theState.statusOfTemporalPreferences));
    
    bool costChanged = false;
            
    map<int,GoalFalseTrueAfterStep>::const_iterator nowItr = earliestGoalPointNow.begin();
    const map<int,GoalFalseTrueAfterStep>::const_iterator nowEnd = earliestGoalPointNow.end();
    
    for (; nowItr != nowEnd; ++nowItr) {
        
        if (theState.preferenceStatus[nowItr->first] != AutomatonPosition::unsatisfied) {
            continue;
        }
        
        if (debug) {
            cout << "First appearance of unsatisfied within preference " << nowItr->first << ", " << RPGBuilder::getPreferences()[nowItr->first].name << ", has been delayed:\n";
        }
                
        EpsilonResolutionTimestamp falseTS(EpsilonResolutionTimestamp::undefined());
        
        {
            bool first = true;
            set<pair<StepAndBeforeOrAfter,double> >::const_iterator tItr = nowItr->second.first.begin();
            const set<pair<StepAndBeforeOrAfter,double> >::const_iterator tEnd = nowItr->second.first.end();
            
            for (; tItr != tEnd; ++tItr) {
                if (first) {
                    falseTS = EpsilonResolutionTimestamp(minTimestamps[tItr->first.stepID] + (tItr->first.beforeOrAfter == StepAndBeforeOrAfter::AFTER ? EPSILON : 0.0) + tItr->second,true);
                    first = false;
                } else {
                    const EpsilonResolutionTimestamp currTS(minTimestamps[tItr->first.stepID] + (tItr->first.beforeOrAfter == StepAndBeforeOrAfter::AFTER ? EPSILON : 0.0) + tItr->second,true);
                    if (currTS > falseTS) {
                        falseTS = currTS;
                    }
                }
            }
            
        }

        EpsilonResolutionTimestamp trueTS(EpsilonResolutionTimestamp::undefined());
        
        {
            bool first = true;
            set<StepAndBeforeOrAfter>::const_iterator tItr = nowItr->second.second.begin();
            const set<StepAndBeforeOrAfter>::const_iterator tEnd = nowItr->second.second.end();
            
            for (; tItr != tEnd; ++tItr) {
                if (first) {
                    trueTS = EpsilonResolutionTimestamp(minTimestamps[tItr->stepID] + (tItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER ? EPSILON : 0.0),true);
                    first = false;
                } else {
                    const EpsilonResolutionTimestamp currTS(minTimestamps[tItr->stepID] + (tItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER ? EPSILON : 0.0),true);
                    if (currTS < trueTS) {
                        trueTS = currTS;
                    }
                }
            }
        }

        
        if (debug) {
            if (!falseTS.isUndefined()) {
                cout << "\tNow cannot be true until after " << falseTS << endl;
            }
            if (!trueTS.isUndefined()) {
                cout << "\tBecomes true after " << trueTS << endl;
            }                
        }
                
        
        if (!falseTS.isUndefined()) {
        
            #ifndef NDEBUG
            if (!trueTS.isUndefined()) {
                assert(falseTS <= trueTS);
            }
            #endif
            
            
            if (falseTS >= EpsilonResolutionTimestamp(RPGBuilder::getPreferences()[nowItr->first].deadline, true)) {
                if (debug) {
                    cout << "\t\tAt time " << falseTS << ": exceeded deadline on preference " << RPGBuilder::getPreferences()[nowItr->first].name << ", cost " << RPGBuilder::getPreferences()[nowItr->first].cost << endl;
                }  
                
                theState.preferenceStatus[nowItr->first] = AutomatonPosition::unreachable;
                
                costChanged = true;
                
            }
        }
        
//         if (!trueTS.isUndefined()) {
//             map<EpsilonResolutionTimestamp, int>::const_iterator costItr = costs.begin();
//             const map<EpsilonResolutionTimestamp, int>::const_iterator costEnd = costs.end();
//             
//             for (; costItr != costEnd && costItr->first <= trueTS; ++costItr) {
//                 
//                 if (!(psa[costItr->second] == AutomatonPosition::satisfied) ) {
//                     
//                     assert(psa[costItr->second] == AutomatonPosition::unreachable || psa[costItr->second] == AutomatonPosition::eternallysatisfied);
//                     continue;
//                 }
//                 
//                 const RPGBuilder::Constraint & currPref = RPGBuilder::getPreferences()[costItr->second];
//                 
//                 if (debug) {
//                     cout << "\t\tAt time " << costItr->first << ": violated preference " << currPref.name << ", cost " << currPref.cost << endl;
//                 }            
//                 
//                 psa.getCost() += currPref.cost;
//                 psa[costItr->second] = AutomatonPosition::unreachable;
//                 
//                 costChanged = true;         
//             }
//             
//             for (; costItr != costEnd; ++costItr) {
//                 
//                 if (!(psa[costItr->second] == AutomatonPosition::satisfied) ) {
//                     
//                     assert(psa[costItr->second] == AutomatonPosition::unreachable || psa[costItr->second] == AutomatonPosition::eternallysatisfied);
//                     continue;
//                 }
//                 
//                 psa[costItr->second] = AutomatonPosition::eternallysatisfied;
//                 
//                 if (debug) {
//                     const RPGBuilder::Constraint & currPref = RPGBuilder::getPreferences()[costItr->second];                
//                     cout << "\t\tAt time " << costItr->first << ": eternally met preference " << currPref.name << ", cost " << currPref.cost << endl;
//                 }            
//             }
//         }
        
    }
    if (debug && costChanged) {
        cout << "\tCost of state is now " << theState.calculateCost() << endl;
    }
}


void POTHelper_updateForInstantaneousEffects(MinimalState & theState,
                                             const StepAndBeforeOrAfter & stepBA, list<Literal*> & delEffs, list<Literal*> & addEffs,
                                             set<int> & newlyAdded, set<int> & newlyDeleted,
                                             map<int,GoalFalseTrueAfterStep> & earliestGoalPointNow)
{
    const unsigned int stepID = stepBA.stepID;
    {
        list<Literal*>::iterator effItr = delEffs.begin();
        const list<Literal*>::iterator effEnd = delEffs.end();

        for (; effItr != effEnd; ++effItr) {
            const int litID = (*effItr)->getStateID();    
            if (TemporalAnalysis::getFactIsAbstract()[litID]) {
                continue;
            }
            bool matchedFirst = false;
            {
                const StateFacts::iterator stateItr = theState.first.find(litID);
                if (stateItr != theState.first.end()) {

                    newlyDeleted.insert(litID);
                    
                    assert(theState.retired.find(litID) == theState.retired.end());

                    {
                        const map<StepAndBeforeOrAfter, bool> & invAfter = stateItr->second.deletableFrom;
                        map<StepAndBeforeOrAfter, bool>::const_iterator iamItr = invAfter.begin();
                        const map<StepAndBeforeOrAfter, bool>::const_iterator iamEnd = invAfter.end();
                        for (; iamItr != iamEnd; ++iamItr) {
                            const StepAndBeforeOrAfter * const iaItr = &(iamItr->first);
                            if (iaItr->beforeOrAfter == StepAndBeforeOrAfter::BEFORE && iaItr->stepID == 0) {
                                continue;
                            }
                            if (iaItr->stepID != stepID) {
                                theState.temporalConstraints->addOrdering(iaItr->stepID, stepID, (iaItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                            }
                        }
                    }
                    {
                        const StepAndBeforeOrAfter addedAt = stateItr->second.availableFrom;
                        if (addedAt.stepID > 0 || addedAt.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                            theState.temporalConstraints->addOrdering(addedAt.stepID, stepID, (addedAt.beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                        }
                        
                        /*if (TemporalAnalysis::goalSoftDeadlinesHaveMonotonicallyWorseningCosts()) {
                            const map<int,int> & factToGoalID = RPGBuilder::getLiteralsToGoalIndex();
                            const map<int,int>::const_iterator gItr = factToGoalID.find(litID);
                            if (gItr != factToGoalID.end() && !((*theState.factHasBeenSeenForWithinSoftDeadline)[gItr->second])) {
                                const map<EpsilonResolutionTimestamp, RPGBuilder::SoftDeadline> & softDeadlines = RPGBuilder::getLiteralGoalSoftDeadlines()[gItr->second];
                                if (!softDeadlines.empty()) {                                    
                                    earliestGoalPointWas[gItr->second].insert(addedAt);
                                    earliestGoalPointNow[gItr->second].insert(stepBA);
                                }
                            }
                        }*/
                    }

                    PropositionAnnotation & toUpdate = theState.retired.insert(*stateItr).first->second;
                    toUpdate.markAsDeleted(stepBA);
                    theState.first.erase(stateItr);

                    if (applyDebug) {
                        cout << "\t" << *(*effItr) << " was true, but has now been deleted\n";
                    }

                    matchedFirst = true;
                }
            }

            if (!matchedFirst) {
                const pair<StateFacts::iterator, bool> stateItrPair = theState.retired.insert(make_pair(litID, PropositionAnnotation(false)));
                const StateFacts::iterator & stateItr = stateItrPair.first;
                if (!stateItrPair.second) {

                    {
                        const map<StepAndBeforeOrAfter, bool> & invAfter = stateItr->second.deletableFrom;
                        map<StepAndBeforeOrAfter, bool>::const_iterator iamItr = invAfter.begin();
                        const map<StepAndBeforeOrAfter, bool>::const_iterator iamEnd = invAfter.end();
                        for (; iamItr != iamEnd; ++iamItr) {
                            const StepAndBeforeOrAfter * const iaItr = &(iamItr->first);
                            if (iaItr->beforeOrAfter == StepAndBeforeOrAfter::BEFORE && iaItr->stepID == 0) {
                                continue;
                            }
                            if (iaItr->stepID != stepID) {
                                theState.temporalConstraints->addOrdering(iaItr->stepID, stepID, (iaItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                            }
                        }
                    }
                    {
                        const StepAndBeforeOrAfter deletedAt = stateItr->second.negativeAvailableFrom;
                        assert(!deletedAt.never());
                        if (!(deletedAt.beforeOrAfter == StepAndBeforeOrAfter::BEFORE && deletedAt.stepID == 0)) {
                            theState.temporalConstraints->addOrdering(deletedAt.stepID, stepID, (deletedAt.beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                        }
                        
                        /*if (TemporalAnalysis::goalSoftDeadlinesHaveMonotonicallyWorseningCosts()) {
                            const map<int,int> & factToGoalID = RPGBuilder::getLiteralsToGoalIndex();
                            const map<int,int>::const_iterator gItr = factToGoalID.find(litID);
                            if (gItr != factToGoalID.end()) {
                                const map<EpsilonResolutionTimestamp, RPGBuilder::SoftDeadline> & softDeadlines = RPGBuilder::getLiteralGoalSoftDeadlines()[gItr->second];
                                if (!softDeadlines.empty()) {                                    
                                    earliestGoalPointWas[gItr->second].insert(deletedAt);
                                    earliestGoalPointNow[gItr->second].insert(stepBA);
                                }
                            }
                        }*/
                    }

                    stateItr->second.markAsDeleted(stepBA);

                    if (applyDebug) {
                        cout << "\t" << *(*effItr) << " was previously deleted, and has been deleted again\n";
                    }
                } else {

                    stateItr->second.markAsDeleted(stepBA);

                    if (applyDebug) {
                        cout << "\t" << *(*effItr) << " was false initially, and has just been deleted\n";
                    }

                }
            }
        }
    }

    {
        list<Literal*>::iterator effItr = addEffs.begin();
        const list<Literal*>::iterator effEnd = addEffs.end();

        const PropositionAnnotation afterNow(stepID);

        for (; effItr != effEnd; ++effItr) {
            const int litID = (*effItr)->getStateID();
            if (TemporalAnalysis::getFactIsAbstract()[litID]) {
                continue;
            }
            newlyDeleted.erase(litID);            
            bool previouslyDeleted = false;

            {
                const StateFacts::iterator stateItr = theState.retired.find(litID);
                if (stateItr != theState.retired.end()) {
                    assert(theState.first.find(litID) == theState.first.end());
                    previouslyDeleted = true;
                    {
                        const StepAndBeforeOrAfter deletedAt = stateItr->second.negativeAvailableFrom;
                        assert(!deletedAt.never());

                        if (deletedAt.beforeOrAfter != StepAndBeforeOrAfter::BEFORE) {
                            
                            // BEFORE only happens with 'BEFORE step 0', i.e. negative initially
                        
                            if (deletedAt.stepID != stepID) {
                                theState.temporalConstraints->addOrdering(deletedAt.stepID, stepID, (deletedAt.beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                            }
                            if (applyDebug) {
                                cout << "\t" << *(*effItr) << " had previously been deleted " << deletedAt << endl;
                            }
                            
                        } else {
                            
                            if (applyDebug) {
                                cout << "\t" << *(*effItr) << " was false initially, but then referred to negatively in some ADL\n";
                            }
                            
                        }
                        
                        {
                            const map<StepAndBeforeOrAfter, bool> & invAfter = stateItr->second.addableFrom;
                            map<StepAndBeforeOrAfter, bool>::const_iterator iamItr = invAfter.begin();
                            const map<StepAndBeforeOrAfter, bool>::const_iterator iamEnd = invAfter.end();
                            for (; iamItr != iamEnd; ++iamItr) {
                                const StepAndBeforeOrAfter * const iaItr = &(iamItr->first);
                                if (iaItr->stepID != stepID) {
                                    theState.temporalConstraints->addOrdering(iaItr->stepID, stepID, (iaItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                                }
                            }
                        }

                        /*if (TemporalAnalysis::goalSoftDeadlinesHaveMonotonicallyWorseningCosts()) {
                            const map<int,int> & factToGoalID = RPGBuilder::getLiteralsToGoalIndex();
                            const map<int,int>::const_iterator gItr = factToGoalID.find(litID);
                            if (gItr != factToGoalID.end() && !((*theState.factHasBeenSeenForWithinSoftDeadline)[gItr->second])) {
                                (*theState.factHasBeenSeenForWithinSoftDeadline)[gItr->second] = true;
                                const map<EpsilonResolutionTimestamp, RPGBuilder::SoftDeadline> & softDeadlines = RPGBuilder::getLiteralGoalSoftDeadlines()[gItr->second];
                                if (!softDeadlines.empty()) {                                    
                                    earliestGoalPointNow[gItr->second].insert(stepBA);
                                    earliestGoalPointWas[gItr->second].insert(deletedAt);
                                }
                            }
                        }*/
                    }

                    PropositionAnnotation & toUpdate = theState.first.insert(*stateItr).first->second;
                    toUpdate.markAsAdded(stepBA);
                    theState.retired.erase(stateItr);

                    if (applyDebug) {
                        cout << ", and is now available from " << stepBA << "\n";
                    }
                    
                    newlyAdded.insert(litID);

                }

            }

            if (!previouslyDeleted) {
                const pair<StateFacts::iterator, bool> stateItrPair = theState.first.insert(make_pair(litID, afterNow));

                if (!stateItrPair.second) { // if we haven't just added it (i.e. it was there already)
                    
                    if (stateItrPair.first->second.availableFrom.stepID || stateItrPair.first->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                        if (applyDebug) {
                            cout << "\t" << *(*effItr) << " used to be available from step " << stateItrPair.first->second.availableFrom.stepID << ", adding ordering constraint\n";
                        }
                        theState.temporalConstraints->addOrdering(stateItrPair.first->second.availableFrom.stepID, stepID, false);
                    }
                    stateItrPair.first->second.availableFrom.updateStepID(stepID); // override when it's available from
                    stateItrPair.first->second.availableFrom.updateBeforeOrAfter(StepAndBeforeOrAfter::AFTER); // ...  to after now

                } else {
                    
                    newlyAdded.insert(litID);
//                     const map<int, list<int> > & factToPrefID = RPGBuilder::getLiteralsToGoalIndex();
//                     const map<int, list<int> >::const_iterator gItr = factToPrefID.find(litID);
//                     if (gItr != factToPrefID.end()) {
//                         list<int>::const_iterator pItr = gItr->second.begin();
//                         const list<int>::const_iterator pEnd = gItr->second.end();
//                         
//                         for(; pItr != pEnd; ++pItr) {
//                             if (theState.preferenceStatus[*pItr] == AutomatonPosition::unsatisfied) {
//                                 // if the latest preference depending on this fact is still satisfied, this needs checking later on
//                                 // otherwise, it's unreachable (moot) or eternally satisfied (met earlier) so we can ignore it
//                                 earliestGoalPointNow[*pItr].second.insert(stepBA);
//                             }
//                         }
//                     }
                    
                }

                if (applyDebug) {
                    cout << "\t" << *(*effItr) << " is brand new and available from " << stepBA << "\n";
                }
            }
            
            
            
        }
    }
}

void POTHelper_updateForEndDeleteInvariantInteractions(MinimalState & theState, const StepAndBeforeOrAfter & endsAt,
        const list<Literal*> & theEffs, const bool & areAdds)
{

    const unsigned int stepID = endsAt.stepID;

    StateFacts & polarised = (areAdds ? theState.retired : theState.first);

#ifndef NDEBUG
    StateFacts & otherpolarised = (areAdds ? theState.first : theState.retired);
#endif

    list<Literal*>::const_iterator effItr = theEffs.begin();
    const list<Literal*>::const_iterator effEnd = theEffs.end();

    for (; effItr != effEnd; ++effItr) {
        if (applyDebug) {
            cout << "\tConsidering end ";
            if (areAdds) {
                cout << "effect " << *(*effItr) << endl;
            } else {
                cout << "effect (not " << *(*effItr) << ")" << endl;
            }
        }

        const int litID = (*effItr)->getStateID();
        if (TemporalAnalysis::getFactIsAbstract()[litID]) {
            if (applyDebug) {
                cout << "\t-- Abstracted, so ignoring it\n";
            }
            continue;
        }
        const StateFacts::iterator stateItr = polarised.find(litID);
        if (stateItr != polarised.end()) {

            assert(otherpolarised.find(litID) == otherpolarised.end());

            {
                const map<StepAndBeforeOrAfter, bool> & invAfter = (areAdds ? stateItr->second.addableFrom : stateItr->second.deletableFrom);
                map<StepAndBeforeOrAfter, bool>::const_iterator iamItr = invAfter.begin();
                const map<StepAndBeforeOrAfter, bool>::const_iterator iamEnd = invAfter.end();
                for (; iamItr != iamEnd; ++iamItr) {
                    const StepAndBeforeOrAfter * const iaItr = &(iamItr->first);
                    if (iaItr->stepID != stepID) {
                        if (applyDebug) {
                            cout << "\t - Soonest this effect can happen is ";
                            if (iaItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                                cout << "epsilon after";
                            } else {
                                cout << "at";
                            }
                            cout << " step " << iaItr->stepID << endl;
                        }
                        theState.temporalConstraints->addOrdering(iaItr->stepID, stepID, (iaItr->beforeOrAfter == StepAndBeforeOrAfter::AFTER));
                    }
                }
            }
            if (areAdds) {
                stateItr->second.promisedAdd.insert(stepID);
            } else {
                stateItr->second.promisedDelete.insert(stepID);
            }
        }
    }
}

void POTHelper_updateForPreconditionsInternal(MinimalState & theState, const StepAndBeforeOrAfter & startsAt,
                                              const pair<StepAndBeforeOrAfter, bool> & finishesAt,
                                              StateFacts & polarisedFacts, const int & litID, const int & pass) {
    
    StateFacts::iterator stateItr = polarisedFacts.find(litID);

    // first, we need to make sure that the proposition has been established by the time we try to use it
    // if we want it at the end of the current happening (i.e. as an invariant that is about to start), then
    // it's sufficient for the achiever to fire no later than the current stepID; otherwise,
    // if we want it at the start of the current happening (standard precondition), then
    // we need an epsilon gap if it was added at the end of the achieving happening rather than the start
    // (i.e. true, given the latter isn't valid under the PDDL semantics)

    if (stateItr != polarisedFacts.end()) {
        if (startsAt.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
            if (stateItr->second.availableFrom.stepID || stateItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                if (stateItr->second.availableFrom.stepID != startsAt.stepID) { // if it's not just that we want a fact we've just added as an invariant
                    if (applyDebug) {
                        cout << "\tWaiting until " << stateItr->second.availableFrom << " to get " << *(RPGBuilder::getLiteral(litID)) << " as an invariant\n";
                    }

                    theState.temporalConstraints->addOrdering(stateItr->second.availableFrom.stepID, startsAt.stepID, false);
                }
            }
        } else {
            if (stateItr->second.availableFrom.stepID || stateItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                if (applyDebug) {
                    cout << "\tWaiting until " << stateItr->second.availableFrom << " to get " << *(RPGBuilder::getLiteral(litID)) << " as a start/end pre\n";
                }

                theState.temporalConstraints->addOrdering(stateItr->second.availableFrom.stepID, startsAt.stepID, stateItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER);
            }
        }
    } else {
        // can only refer to non-existant facts if they're negated, and are false initially and never since made true
        assert(pass);
        
        // create a dummy state negative fact record for this fact, so we can insert the threat-resolving constraints next        
        stateItr = polarisedFacts.insert(make_pair(litID, StepAndBeforeOrAfter())).first;
    }

    // second, we now need to add the preservation constraints

    if (finishesAt.first.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
        map<StepAndBeforeOrAfter, bool> & checkInSet = (pass ? stateItr->second.addableFrom : stateItr->second.deletableFrom);
        const StepAndBeforeOrAfter tmp(StepAndBeforeOrAfter::BEFORE, finishesAt.first.stepID);
        const map<StepAndBeforeOrAfter, bool>::iterator checkItr = checkInSet.find(tmp);
        if (checkItr != checkInSet.end()) { // if we already have it as being available from 'before' this step
            // (i.e. if we had a start prec which is now an over all, or an over all which is now an at end)
            checkInSet.erase(checkItr); // remove it
        }
        checkInSet.insert(finishesAt); // because we now need to preserve it until after the step
        if (applyDebug) {
            cout << "\t" << *(RPGBuilder::getLiteral(litID)) << " now cannot be ";
            if (pass) {
                cout << "added";
            } else {
                cout << "deleted";
            }
            cout << " until " << finishesAt.first << "\n";
        }
    } else {
        map<StepAndBeforeOrAfter, bool> & checkInSet = (pass ? stateItr->second.addableFrom : stateItr->second.deletableFrom);
        const StepAndBeforeOrAfter tmp(StepAndBeforeOrAfter::AFTER, finishesAt.first.stepID);
        const map<StepAndBeforeOrAfter, bool>::iterator checkItr = checkInSet.find(tmp);
        if (checkItr == checkInSet.end()) { // if we don't have it as being preserved until after this step
            checkInSet.insert(finishesAt); // add the entry to do so
        }
        if (applyDebug) {
            cout << "\t" << *(RPGBuilder::getLiteral(litID)) << " now cannot be ";
            if (pass) {
                cout << "added";
            } else {
                cout << "deleted";
            }
            cout << " until " << finishesAt.first << "\n";
        }
        if (finishesAt.first.stepID != startsAt.stepID) {

            // check for clashes with promised deletes
            const set<int> & promised = (pass ? stateItr->second.promisedAdd : stateItr->second.promisedDelete);

            set<int>::const_iterator promItr = promised.begin();
            const set<int>::const_iterator promEnd = promised.end();

            for (; promItr != promEnd; ++promItr) {
                if (applyDebug) {
                    cout << "\t" << *(RPGBuilder::getLiteral(litID)) << " is going to be ";
                    if (pass) {
                        cout << "added";
                    } else {
                        cout << "deleted";
                    }
                    cout << " at " << *promItr << ", so forcing an ordering.\n";
                }
                theState.temporalConstraints->addOrdering(finishesAt.first.stepID, *promItr, false);
            }

        }

    }
    
}
                                      
void POTHelper_updateForPreconditions(MinimalState & theState, const StepAndBeforeOrAfter & startsAt,
                                      const pair<StepAndBeforeOrAfter, bool> & finishesAt,
                                      const list<Literal*> & reservePositive, const list<Literal*> & reserveNegative)
{

    if (applyDebug) {
        cout << "\tPreconditions requested from " << startsAt << " until " << finishesAt.first << "\n";
    }

    for (int pass = 0; pass < 2; ++pass) {
        const list<Literal*> & reserve = (pass ? reserveNegative : reservePositive);

        StateFacts & polarisedFacts = (pass ? theState.retired : theState.first);

        list<Literal*>::const_iterator precItr = reserve.begin();
        const list<Literal*>::const_iterator precEnd = reserve.end();

        for (; precItr != precEnd; ++precItr) {
            const int litID = (*precItr)->getStateID();
            if (TemporalAnalysis::getFactIsAbstract()[litID]) {
                continue;
            }
            POTHelper_updateForPreconditionsInternal(theState, startsAt, finishesAt, polarisedFacts, litID, pass);
        }
    }
}

void POTHelper_updateForPreconditions(MinimalState & theState, const StepAndBeforeOrAfter & startsAt,
                                      const pair<StepAndBeforeOrAfter, bool> & finishesAt,
                                      const set<int> & reservePositive, const set<int> & reserveNegative)
{

    if (applyDebug) {
        if (!reservePositive.empty() || !reserveNegative.empty()) {
            cout << "\tPrecondition preferences requested from " << startsAt << " until " << finishesAt.first << "\n";
        }
    }

    for (int pass = 0; pass < 2; ++pass) {
        const set<int> & reserve = (pass ? reserveNegative : reservePositive);

        StateFacts & polarisedFacts = (pass ? theState.retired : theState.first);

        set<int>::const_iterator precItr = reserve.begin();
        const set<int>::const_iterator precEnd = reserve.end();

        for (; precItr != precEnd; ++precItr) {
            const int litID = *precItr;
            if (TemporalAnalysis::getFactIsAbstract()[litID]) {
                continue;
            }
            POTHelper_updateForPreconditionsInternal(theState, startsAt, finishesAt, polarisedFacts, litID, pass);
        }
    }
}


void POTHelper_invariantsCanNowFinish(MinimalState & theState, const StepAndBeforeOrAfter & finishesAt,
                                      const list<Literal*> & reservePositive, const list<Literal*> & reserveNegative)
{

    for (int pass = 0; pass < 2; ++pass) {
        const list<Literal*> & reserve = (pass ? reserveNegative : reservePositive);
        StateFacts & polarisedFacts = (pass ? theState.retired : theState.first);

        list<Literal*>::const_iterator precItr = reserve.begin();
        const list<Literal*>::const_iterator precEnd = reserve.end();

        for (; precItr != precEnd; ++precItr) {
            if (applyDebug) {
                cout << "\tRemoving the invariant ";
                if (pass) cout << "¬";
                cout << *(*precItr) << " started at step " << finishesAt.stepID - 1 << "\n";
            }
            const int litID = (*precItr)->getStateID();
            if (TemporalAnalysis::getFactIsAbstract()[litID]) {
                continue;
            }
            StateFacts::iterator stateItr = polarisedFacts.find(litID);

            assert(stateItr != polarisedFacts.end()); // otherwise we're referring to a precondition which isn't true/false

            map<StepAndBeforeOrAfter, bool> & checkInSet = (pass ? stateItr->second.addableFrom : stateItr->second.deletableFrom);

            map<StepAndBeforeOrAfter, bool>::iterator cisItr = checkInSet.find(finishesAt);
            assert(cisItr != checkInSet.end()); // or it means it was never registered as an invariant

            cisItr->second = SAFETOSKIP;

        }
    }
}


void POTHelper_updateForNumericVariables(MinimalState & theState, const int & startsAt, const int & endsAt, const bool & forStart, const set<int> & mentioned)
{
    set<int>::iterator cvItr = mentioned.begin();
    const set<int>::iterator cvEnd = mentioned.end();

    for (; cvItr != cvEnd; ++cvItr) {
        const int var = *cvItr;

        if (var < 0) {
            // duration term
            continue;
        }
        
        if (NumericAnalysis::getDominanceConstraints()[var] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }
        
        if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[var] != NumericAnalysis::E_ORDER_DEPENDENT
            && NumericAnalysis::getDominanceConstraints()[var] == NumericAnalysis::E_METRICTRACKING) {
            continue;
        }
        
        FluentInteraction & currFI = theState.temporalConstraints->lastStepToTouchPNE[var];

        if (!forStart) {
            currFI.futureEndInteractions.erase(endsAt);
        }

        if (forStart) {
            currFI.stepsWithPreconditionsSinceTheLastEffect.insert(startsAt);
        } else {
            currFI.stepsWithPreconditionsSinceTheLastEffect.insert(endsAt);
        }
        
        
        if (currFI.lastInstantaneousEffect != -1 && currFI.lastInstantaneousEffect != startsAt && currFI.lastInstantaneousEffect != endsAt) {
            
            if (applyDebug) {
                cout << "\t\tMust come after " << currFI.lastInstantaneousEffect << ", the last instantaneous effect on " << *(RPGBuilder::getPNE(*cvItr)) << endl;
            }
            if (forStart) {
                theState.temporalConstraints->addOrdering(currFI.lastInstantaneousEffect, startsAt, true);
            } else {
                theState.temporalConstraints->addOrdering(currFI.lastInstantaneousEffect, endsAt, true);
            }
        }

        set<int>::iterator fiItr = currFI.activeCTSEffects.begin();
        const set<int>::iterator fiEnd = currFI.activeCTSEffects.end();

        for (; fiItr != fiEnd; ++fiItr) {
            if (forStart) {
                if (*fiItr - 1 != startsAt) {
                    if (applyDebug) {
                        cout << "\t\tMust come after " << *fiItr - 1 << ", the start of a CTS effect on " << *(RPGBuilder::getPNE(*cvItr)) << endl;
                    }            
                    theState.temporalConstraints->addOrdering(*fiItr - 1, startsAt, true);
                }
                if (*fiItr != endsAt) {
                    if (applyDebug) {
                        cout << "\t\tMust come before " << *fiItr  << ", the future end of a CTS effect on " << *(RPGBuilder::getPNE(*cvItr)) << endl;
                    }            
                    theState.temporalConstraints->addOrdering(startsAt, *fiItr, true);
                }
            } else {
                if (*fiItr - 1 != startsAt && *fiItr - 1 != endsAt) {
                    if (applyDebug) {
                        cout << "\t\tMust come after " << *fiItr - 1 << ", the start of a CTS effect on " << *(RPGBuilder::getPNE(*cvItr)) << endl;
                    }            
                    theState.temporalConstraints->addOrdering(*fiItr - 1, endsAt, true);
                }
                if (*fiItr  != startsAt && *fiItr != endsAt) {
                    if (applyDebug) {
                        cout << "\t\tMust come before " << *fiItr  << ", the future end of a CTS effect on " << *(RPGBuilder::getPNE(*cvItr)) << endl;
                    }            
                    theState.temporalConstraints->addOrdering(endsAt, *fiItr, true);
                }
            }
            /*if (*fiItr != startsAt + 1) {
                theState.temporalConstraints->addOrdering(*fiItr, startsAt + 1, true); // the end of an action is always at the step after it
            }*/
        }
    }
}

void POTHelper_warnForNumericVariables(MinimalState & theState, const int & endsAt, const set<int> & mentioned)
{
    set<int>::iterator cvItr = mentioned.begin();
    const set<int>::iterator cvEnd = mentioned.end();

    for (; cvItr != cvEnd; ++cvItr) {
        const int var = *cvItr;

        if (NumericAnalysis::getDominanceConstraints()[var] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }
        
        if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[var] != NumericAnalysis::E_ORDER_DEPENDENT
            && NumericAnalysis::getDominanceConstraints()[var] == NumericAnalysis::E_METRICTRACKING) {            
            continue;
        }
        
        FluentInteraction & currFI = theState.temporalConstraints->lastStepToTouchPNE[var];

        currFI.futureEndInteractions.insert(endsAt);
        
    }
}

#ifdef POPF3ANALYSIS
template<typename T>
void POTHelper_updateForNumericPreconditions(MinimalState & theState, const int & stepID, set<int> & mentioned, T & reserve, const bool mustBeSatisfied=true)
#else
template<typename T>
void POTHelper_updateForNumericPreconditions(MinimalState &, const int &, set<int> & mentioned, T & reserve, const bool mustBeSatisfied=true)
#endif
{

    static const int PNEcount = RPGBuilder::getPNECount();

    typename T::iterator precItr = reserve.begin();
    const typename T::iterator precEnd = reserve.end();

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*precItr];

        
        const int currVar = currPre.LHSVariable;

        if (currVar < 0) continue;

        if (applyDebug) {
            cout << COLOUR_light_blue << "\t\t\tLooking at reserving " << currPre << COLOUR_default << endl;
        }

        if (currVar < PNEcount) {            
            mentioned.insert(currVar);
            #ifdef POPF3ANALYSIS
            if (mustBeSatisfied) {            
                map<double, map<int,double> > & queuedEffs = theState.temporalConstraints->lastStepToTouchPNE[currVar].compressionSafeEndEffectOfStepsAtTime;
                if (!queuedEffs.empty()) {
                    double lb = theState.secondMax[currVar];
                    {
                        // first, revert all future effects                    
                        map<double, map<int,double> >::const_iterator qeItr = queuedEffs.begin();
                        const map<double, map<int,double> >::const_iterator qeEnd = queuedEffs.end();
                        for (; qeItr != qeEnd; ++qeItr) {
                            map<int,double>::const_iterator qe2Itr = qeItr->second.begin();
                            const map<int,double>::const_iterator qe2End = qeItr->second.end();
                            
                            for (; qe2Itr != qe2End; ++qe2Itr) {
                                lb -= qe2Itr->second;
                            }
                        }
                    }
                    
                    // then, if add as few as possible, forwards by timepoint, until the pre is satisfied
                    if (currPre.op == VAL::E_GREATER ? lb <= currPre.RHSConstant : lb < currPre.RHSConstant) {
                        map<double, map<int,double> >::const_iterator qeItr = queuedEffs.begin();
                        const map<double, map<int,double> >::const_iterator qeEnd = queuedEffs.end();
                        
                        bool satisfied = false;
                                            
                        for (; !satisfied; ++qeItr) {
                            
                            assert(qeItr != qeEnd);
                            
                            map<int,double>::const_iterator qe2Itr = qeItr->second.begin();
                            const map<int,double>::const_iterator qe2End = qeItr->second.end();
                            
                            for (; !satisfied && qe2Itr != qe2End; ++qe2Itr) {                            
                                
                                // make this step come after the next increase of this variable
                                theState.temporalConstraints->addOrdering(qe2Itr->first, stepID, true);
                                if (applyDebug) {
                                    cout << COLOUR_light_blue << "\t\t\tAdding ordering after " << qe2Itr->first << " to get " << qe2Itr->second << " more of " << *(RPGBuilder::getPNE(currVar)) << COLOUR_default << endl;
                                }
                                                            
                                                                                        
                                // .. and note we now have its effect
                                lb += qe2Itr->second;
                                
                                satisfied = (currPre.op == VAL::E_GREATER ? lb > currPre.RHSConstant : lb >= currPre.RHSConstant);
                            }                        
                        }
                    }
                }
            }
            #endif
        } else if (currVar < 2 * PNEcount) {
            mentioned.insert(currVar - PNEcount);
            #ifdef POPF3ANALYSIS            
            if (mustBeSatisfied) {
                map<double, map<int,double> > & queuedEffs = theState.temporalConstraints->lastStepToTouchPNE[currVar].compressionSafeEndEffectOfStepsAtTime;
                if (!queuedEffs.empty()) {
                    double ub = theState.secondMin[currVar - PNEcount];
                    double target = currPre.RHSConstant;
                    if (target != 0.0) {
                        target = -target;
                    }
                    {
                        // first, revert all future effects                    
                        map<double, map<int,double> >::const_iterator qeItr = queuedEffs.begin();
                        const map<double, map<int,double> >::const_iterator qeEnd = queuedEffs.end();
                        for (; qeItr != qeEnd; ++qeItr) {
                            map<int,double>::const_iterator qe2Itr = qeItr->second.begin();
                            const map<int,double>::const_iterator qe2End = qeItr->second.end();
                            
                            for (; qe2Itr != qe2End; ++qe2Itr) {
                                ub -= qe2Itr->second;
                            }
                        }
                    }
                    
                    // then, if add as few as possible, forwards by timepoint, until the pre is satisfied
                    if (currPre.op == VAL::E_GREATER ? ub >= target : ub > target) {
                        map<double, map<int,double> >::const_iterator qeItr = queuedEffs.begin();
                        const map<double, map<int,double> >::const_iterator qeEnd = queuedEffs.end();
                        
                        bool satisfied = false;
                                            
                        for (; !satisfied; ++qeItr) {
                            
                            assert(qeItr != qeEnd);
                            
                            map<int,double>::const_iterator qe2Itr = qeItr->second.begin();
                            const map<int,double>::const_iterator qe2End = qeItr->second.end();
                            
                            for (; !satisfied && qe2Itr != qe2End; ++qe2Itr) {                            
                                
                                // make this step come after the next increase of this variable
                                theState.temporalConstraints->addOrdering(qe2Itr->first, stepID, true);
                                
                                // .. and note we now have its effect
                                ub += qe2Itr->second;
                                
                                satisfied = (currPre.op == VAL::E_GREATER ? ub < target : ub <= target);
                            }                        
                        }
                    }
                }
            }                
            #endif
        } else {
            RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currVar);

            for (int i = 0; i < currAV.size; ++i) {
                const int lv = currAV.fluents[i];
                if (lv < PNEcount) {
                    mentioned.insert(lv);
                } else {
                    mentioned.insert(lv - PNEcount);
                }
            }
            
            #ifdef POPF3ANALYSIS
            
            if (mustBeSatisfied) {
                double lb = currAV.constant;
                bool simple = true;
                
                if (applyDebug) {
                    cout << "\t\t\t\tStarting with constant of " << lb << endl;
                }
                {
                    int v;
                    for (int s = 0; s < currAV.size; ++s) {
                        v = currAV.fluents[s];
                        if (v < 0) {
                            simple = false;
                            break;
                        } else {
                            if (v < PNEcount) {
                                if (applyDebug) {
                                    cout << "\t\t\t\tUB on " << *(RPGBuilder::getPNE(v)) << " is " << theState.secondMax[v] << ", weighted " << currAV.weights[s] << endl;
                                }    
                                lb += currAV.weights[s] * theState.secondMax[v];
                            } else {                            
                                lb -= currAV.weights[s] * theState.secondMin[v - PNEcount];
                                if (applyDebug) {
                                    cout << "\t\t\t\tLB on " << *(RPGBuilder::getPNE(v - PNEcount)) << " is " << theState.secondMin[v - PNEcount] << ", weighted -" << currAV.weights[s] << endl;
                                }    

                            }
                        } 
                    
                    }
                    
                }
                
                if (simple) {
                    
                    if (applyDebug) {
                        cout << "\t\t\tWith all queued effects, LHS is " << lb << endl;
                    }

                    vector<map<double, map<int,double> >::iterator> queuedEffItr(currAV.size);
                    vector<map<double, map<int,double> >::iterator> queuedEffEnd(currAV.size);
                    
                    int v;
                    double w;
                    for (int s = 0; s < currAV.size; ++s) {
                        v = currAV.fluents[s];
                        w = currAV.weights[s];
                        if (v >= PNEcount) {
                            v -= PNEcount;
                            w = -w;
                        }

                        map<double, map<int,double> > & currMap = theState.temporalConstraints->lastStepToTouchPNE[v].compressionSafeEndEffectOfStepsAtTime;
                        queuedEffItr[s] = currMap.begin();
                        queuedEffEnd[s] = currMap.end();
                        
                        {
                            // first, revert all future effects                    
                            map<double, map<int,double> >::const_iterator qeItr = currMap.begin();
                            const map<double, map<int,double> >::const_iterator qeEnd = currMap.end();
                            for (; qeItr != qeEnd; ++qeItr) {
                                map<int,double>::const_iterator qe2Itr = qeItr->second.begin();
                                const map<int,double>::const_iterator qe2End = qeItr->second.end();
                                
                                for (; qe2Itr != qe2End; ++qe2Itr) {
                                    lb -= qe2Itr->second * w;
                                    if (applyDebug) {
                                        cout << "\t\t\tRolling back effect on " << *(RPGBuilder::getPNE(v)) << ", LHS is now " << lb << endl;
                                    }
                                }
                            }
                        }
                    }
                    
                    if (currPre.op == VAL::E_GREATER ? lb <= currPre.RHSConstant : lb < currPre.RHSConstant) {
                        
                        bool satisfied = false;
                                            
                        while (!satisfied) {
                            
                            
                            int earliestS = -1;
                            double earliestT;
                            
                            for (int s = 0; s < currAV.size; ++s) {
                                if (queuedEffItr[s] != queuedEffEnd[s]) {
                                    if (   earliestS == -1 || earliestT > queuedEffItr[s]->first) {
                                        
                                        earliestS = s;
                                        earliestT = queuedEffItr[s]->first;
                                    }
                                }
                            }
                            
                            assert(earliestS != -1);
                            
                            const bool negativeVar = (currAV.fluents[earliestS] >= PNEcount);
                            
                            map<int,double>::const_iterator qe2Itr = queuedEffItr[earliestS]->second.begin();
                            const map<int,double>::const_iterator qe2End = queuedEffItr[earliestS]->second.end();
                            
                            for (; !satisfied && qe2Itr != qe2End; ++qe2Itr) {                            
                                
                                // make this step come after the next increase of this variable
                                theState.temporalConstraints->addOrdering(qe2Itr->first, stepID, true);
                                
                                // .. and note we now have its effect
                                
                                if (negativeVar) {
                                    lb -= qe2Itr->second * currAV.weights[earliestS];
                                } else {
                                    lb += qe2Itr->second * currAV.weights[earliestS];
                                }
                                
                                satisfied = (currPre.op == VAL::E_GREATER ? lb > currPre.RHSConstant : lb >= currPre.RHSConstant);
                            }
                            
                            if (!satisfied) {
                                ++(queuedEffItr[earliestS]);
                            }
                        }
                    }
                }
            }
            #endif
        }
        
    }
}



void POTHelper_updateForDurations(MinimalState &, const int &, set<int> & mentioned, RPGBuilder::RPGDuration & durationConstraints)
{
    
    //static const int PNEcount = RPGBuilder::getPNECount();
    
    for (int pass = 0; pass < 3; ++pass) {
        const list<RPGBuilder::DurationExpr*> & reserve = durationConstraints[pass];


        list<RPGBuilder::DurationExpr*>::const_iterator precItr = reserve.begin();
        const list<RPGBuilder::DurationExpr*>::const_iterator precEnd = reserve.end();

        for (; precItr != precEnd; ++precItr) {
            #ifdef STOCHASTICDURATIONS
            const int vc = (*precItr)->variables.size();
            for (int vi = 0; vi < vc; ++vi) {
                if ((*precItr)->variables[vi].first != -1) {
                    mentioned.insert((*precItr)->variables[vi].first);
                }
            }
            #else
            mentioned.insert((*precItr)->variables.begin(), (*precItr)->variables.end());
            #endif
        }
    }

}

void POTHelper_updateForInputsToInstantaneousNumericEffects(set<int> & mentioned, list<int> & reserve)
{

    static const int PNEcount = RPGBuilder::getPNECount();

    list<int>::iterator precItr = reserve.begin();
    const list<int>::iterator precEnd = reserve.end();

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*precItr];

        for (int i = 0; i < currEff.size; ++i) {
            const int lv = currEff.variables[i];
            if (lv < 0) continue;
            if (lv < PNEcount) {
                mentioned.insert(lv);
            } else if (lv < 2 * PNEcount) {
                mentioned.insert(lv - PNEcount);
            } else {
                RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(lv);

                for (int j = 0; j < currAV.size; ++j) {
                    const int lvtwo = currAV.fluents[j];
                    if (lvtwo < PNEcount) {
                        mentioned.insert(lvtwo);
                    } else {
                        mentioned.insert(lvtwo - PNEcount);
                    }
                }
            }
        }
        if (!currEff.isAssignment) {
            if (currEff.fluentIndex < PNEcount) {
                mentioned.insert(currEff.fluentIndex);
            } else {
                mentioned.insert(currEff.fluentIndex - PNEcount);
            }
        }
    }
}

void POTHelper_updateForOutputsFromInstantaneousNumericEffects(MinimalState & theState, const vector<double> & minTimestamps,
                                                               const ActionSegment & act,
                                                               const int & stepID, list<int> & reserve, const int & minDur, const int & maxDur,
                                                               set<int> & variablesTouched)
{

    static const int PNEcount = RPGBuilder::getPNECount();

    list<int>::iterator precItr = reserve.begin();
    const list<int>::iterator precEnd = reserve.end();

    list<pair<int, pair<double, double> > > updated;

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*precItr];

        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_IRRELEVANT) {
            if (applyDebug) {
                cout << "\tSkipping irrelevant " << currEff << ": leaving bounds at [" << theState.secondMin[currEff.fluentIndex] << "," << theState.secondMax[currEff.fluentIndex] << "]\n";
            }
            continue;
        }
        
        updated.push_back(pair<int, pair<double, double> >(currEff.fluentIndex, currEff.applyEffectMinMax(theState.secondMin, theState.secondMax, minDur, maxDur)));
                
                
        if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[currEff.fluentIndex] != NumericAnalysis::E_ORDER_DEPENDENT
            && NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_METRICTRACKING) {
            if (applyDebug) {
                cout << "\tUpdating but not inserting ordering constraints for order-independent metric-tracking " << currEff << endl;
            }
            continue;
        }                                
        
        const int localFluentIndex = (currEff.fluentIndex < PNEcount ? currEff.fluentIndex : currEff.fluentIndex - PNEcount);

        variablesTouched.insert(localFluentIndex);
        
        FluentInteraction & currFI = theState.temporalConstraints->lastStepToTouchPNE[localFluentIndex];
        
        if (applyDebug) {
            cout  << "\t\t" << currEff << ", so setting last instantaneous effect on " << *(RPGBuilder::getPNE(localFluentIndex)) << " to " << stepID << endl;
        }
        
        currFI.lastInstantaneousEffect = stepID;
        currFI.futureEndInteractions.erase(stepID);
        
        {
            const set<int> & futureSet = currFI.futureEndInteractions;
            
            set<int>::const_iterator fsItr = futureSet.begin();
            const set<int>::const_iterator fsEnd = futureSet.end();
            
            for (; fsItr != fsEnd; ++fsItr) {
                if (applyDebug) {
                    cout << "\tRequesting ordering to come before" << *fsItr << ", a future end with a pre/eff on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                }
                theState.temporalConstraints->addOrdering(stepID, *fsItr, true);
            }
        }
        
        {
            set<int> & pastSet = currFI.stepsWithPreconditionsSinceTheLastEffect;
            
            set<int>::const_iterator psItr = pastSet.begin();
            const set<int>::const_iterator psEnd = pastSet.end();
            
            for (; psItr != psEnd; ++psItr) {
                if (*psItr != stepID) {
                    if (applyDebug) {
                        cout << "\tRequesting ordering to come after" << *psItr << ", a past step with a pre/duration on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                    }
                    theState.temporalConstraints->addOrdering(*psItr, stepID, true);
                }
            }
            
            pastSet.clear();
        }
        
        {

            map<int, int> & invSet = theState.temporalConstraints->lastStepToTouchPNE[localFluentIndex].activeInvariants;

            map<int, int>::iterator isItr = invSet.begin();
            const map<int, int>::iterator isEnd = invSet.end();

            for (; isItr != isEnd; ++isItr) {
                if (stepID != isItr->second) {
                    if (applyDebug) {
                        cout << "\tRequesting ordering to come after " << isItr->second << ", the start of an invariant on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                    }
                    theState.temporalConstraints->addOrdering(isItr->second, stepID, true);
                }

                if (stepID != isItr->first) {
                    if (applyDebug) {
                        cout << "\tRequesting ordering to come after " << isItr->second << ", the end of an invariant on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                    }
                    theState.temporalConstraints->addOrdering(stepID, isItr->first, true);
                }
            }
        }

        {

            set<int> & invSet = theState.temporalConstraints->lastStepToTouchPNE[localFluentIndex].activeCTSEffects;

            set<int>::iterator isItr = invSet.begin();
            const set<int>::iterator isEnd = invSet.end();

            for (; isItr != isEnd; ++isItr) {
                if (stepID != (*isItr - 1)) {
                    theState.temporalConstraints->addOrdering(*isItr - 1, stepID, true);
                }

                if (stepID != *isItr) {
                    theState.temporalConstraints->addOrdering(stepID, *isItr, true);
                }
            }
        }

    }

    #ifdef POPF3ANALYSIS
    
    map<int,double> dynamicUpdated;
    
    if (act.first) {
        
        const list<NumericAnalysis::CostAtTime*>* const dynamicCosts
                    = (act.second == Planner::E_AT_END ? NumericAnalysis::getTimeDependentEndCosts()[act.first->getID()]
                                                       : NumericAnalysis::getTimeDependentStartCosts()[act.first->getID()]);
                    
     
        if (dynamicCosts) {
            
            if (applyDebug) {
                cout << "\tLooking at the time-dependent effects\n";
            }
            double timeNow = 0.0;
            
            const map<int,bool> * const beforeNow = theState.temporalConstraints->stepsBefore(stepID);
            
            if (beforeNow) {
                double localT;
                map<int,bool>::const_iterator bnItr = beforeNow->begin();
                const map<int,bool>::const_iterator bnEnd = beforeNow->end();
                
                for (; bnItr != bnEnd; ++bnItr) {
                    localT = minTimestamps[bnItr->first];
                    if (bnItr->second) {
                        localT += 0.001;
                    }
                    if (localT > timeNow) {
                        timeNow = localT;
                    }
                }
            }
            
            EpsilonResolutionTimestamp nowRounded(timeNow, true);
            
            list<NumericAnalysis::CostAtTime*>::const_iterator cItr = dynamicCosts->begin();
            const list<NumericAnalysis::CostAtTime*>::const_iterator cEnd = dynamicCosts->end();
            
            for (; cItr != cEnd; ++cItr) {
                if ((*cItr)->varCosts.empty()) {
                    continue;
                }
                if (nowRounded < (*cItr)->start) {
                    continue;
                }
                if (nowRounded > (*cItr)->end) {
                    continue;
                }
                list<NumericAnalysis::EffectDeterminedByTime*>::const_iterator vcItr = (*cItr)->varCosts.begin();
                const list<NumericAnalysis::EffectDeterminedByTime*>::const_iterator vcEnd = (*cItr)->varCosts.end();
                
                for (; vcItr != vcEnd; ++vcItr) {
                    
                    if (applyDebug) {
                        cout << "\t\tA time-dependent effect fires\n";
                    }

                    double & alter = dynamicUpdated.insert(make_pair((*vcItr)->y,0.0)).first->second;
                    alter += (*vcItr)->c;
                    if ((*vcItr)->m != 0.0) {
                        alter += (*vcItr)->m * timeNow;
                    }
                }
            }
        } else {
            //cout << "No dynamic costs on " << *(act.first) << endl;
        }
                    
    }
    
    list<pair<int, pair<double, double> > >::iterator updItr = updated.begin();
    const list<pair<int, pair<double, double> > >::iterator updEnd = updated.end();
    
    map<int,double>::const_iterator dynItr;
    
    for (; updItr != updEnd; ++updItr) {
        dynItr = dynamicUpdated.find(updItr->first);
        
        if (dynItr == dynamicUpdated.end()) {
            theState.secondMin[updItr->first] = updItr->second.first;
            theState.secondMax[updItr->first] = updItr->second.second;
            if (applyDebug) {
                cout << "\tAfter effects, updated " << *(RPGBuilder::getPNE(updItr->first)) << " to [" << updItr->second.first << "," << updItr->second.second << "]" << endl;
            }

        }
    }
    
    dynItr = dynamicUpdated.begin();
    map<int,double>::const_iterator dynEnd = dynamicUpdated.end();
    
    for (; dynItr != dynEnd; ++dynItr) {
        theState.secondMin[dynItr->first] += dynItr->second;
        theState.secondMax[dynItr->first] += dynItr->second;
    }
    #else

    list<pair<int, pair<double, double> > >::iterator updItr = updated.begin();
    const list<pair<int, pair<double, double> > >::iterator updEnd = updated.end();

    for (; updItr != updEnd; ++updItr) {
        theState.secondMin[updItr->first] = updItr->second.first;
        theState.secondMax[updItr->first] = updItr->second.second;
    }

    #endif
}

#ifdef POPF3ANALYSIS
void POTHelper_queueCompressionSafeInstantaneousNumericEffects(MinimalState & theState, const int & stepID, list<int> & reserve, set<int> & variablesTouchedEnd)
{

    list<int>::iterator precItr = reserve.begin();
    const list<int>::iterator precEnd = reserve.end();

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*precItr];

        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }

        variablesTouchedEnd.insert(currEff.fluentIndex);
        
        theState.secondMin[currEff.fluentIndex] += currEff.constant;
        theState.secondMax[currEff.fluentIndex] += currEff.constant;            

        if (applyDebug) {
            cout << "\t\tHas a compression safe end effect " << *(RPGBuilder::getPNE(currEff.fluentIndex));
            if (currEff.constant >= 0.0) {
                cout << " += " << currEff.constant << endl;
            } else {
                cout << " -= " << -currEff.constant << endl;
            }
        }
        
        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_METRICTRACKING) {
            FluentInteraction & currFI = theState.temporalConstraints->lastStepToTouchPNE[currEff.fluentIndex];
            currFI.compressionSafeEndEffectOfStepsAtTime[-1.0].insert(make_pair(stepID, currEff.constant));            
        }
    }

}
#endif


void POTHelper_warnForNumericEffects(MinimalState & theState, const int & stepID, list<int> & reserve, const int & minDur, const int & maxDur)
{

    static const int PNEcount = RPGBuilder::getPNECount();

    list<int>::iterator precItr = reserve.begin();
    const list<int>::iterator precEnd = reserve.end();

    list<pair<int, pair<double, double> > > updated;

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*precItr];

        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }
        
        if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[currEff.fluentIndex] != NumericAnalysis::E_ORDER_DEPENDENT
            && NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_METRICTRACKING) {
            continue;
        }                                

        const int localFluentIndex = (currEff.fluentIndex < PNEcount ? currEff.fluentIndex : currEff.fluentIndex - PNEcount);
                                                
        if (NumericAnalysis::effectCanBeMovedToStart()[*precItr]) {
            {
                const set<int> & futureSet = theState.temporalConstraints->lastStepToTouchPNE[localFluentIndex].futureEndInteractions;
                
                set<int>::const_iterator fsItr = futureSet.begin();
                const set<int>::const_iterator fsEnd = futureSet.end();
                
                for (; fsItr != fsEnd; ++fsItr) {
                    if (applyDebug) {
                        cout << "\tRequesting ordering to come before" << *fsItr << ", a future end with a pre/eff on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                    }
                    theState.temporalConstraints->addOrdering(stepID, *fsItr, true);
                }
            }
                           
        } else {
                        
            theState.temporalConstraints->lastStepToTouchPNE[localFluentIndex].futureEndInteractions.insert(stepID);
        }
        
        
        
    }

}

void POTHelper_registerContinuousNumericEffects(MinimalState & theState, const int & startStepID, const int & endStepID, RPGBuilder::LinearEffects* const effs, const bool & registerNotDeregister)
{

    if (!effs) return;

    const unsigned int lim = effs->vars.size();

    for (unsigned int v = 0; v < lim; ++v) {
        
        if (NumericAnalysis::getDominanceConstraints()[effs->vars[v]] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }
        
        if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[effs->vars[v]] != NumericAnalysis::E_ORDER_DEPENDENT
            && NumericAnalysis::getDominanceConstraints()[effs->vars[v]] == NumericAnalysis::E_METRICTRACKING) {
            continue;
        }
                
                
        
        FluentInteraction & currFI = theState.temporalConstraints->lastStepToTouchPNE[effs->vars[v]];
        if (registerNotDeregister) {
            currFI.lastInstantaneousEffect = startStepID;
            currFI.activeCTSEffects.insert(endStepID);
        } else {
            currFI.lastInstantaneousEffect = endStepID;
            currFI.activeCTSEffects.erase(endStepID);
        }

        {
            const int stepID = (registerNotDeregister ? startStepID : endStepID);

            map<int, int> & invSet = theState.temporalConstraints->lastStepToTouchPNE[effs->vars[v]].activeInvariants;

            map<int, int>::iterator isItr = invSet.begin();
            const map<int, int>::iterator isEnd = invSet.end();

            for (; isItr != isEnd; ++isItr) {
                if (stepID != isItr->second) {
                    theState.temporalConstraints->addOrdering(isItr->second, stepID, true);
                }

                if (stepID != isItr->first) {
                    theState.temporalConstraints->addOrdering(stepID, isItr->first, true);
                }
            }
            
            set<int> & pastSet = theState.temporalConstraints->lastStepToTouchPNE[effs->vars[v]].stepsWithPreconditionsSinceTheLastEffect;

            set<int>::const_iterator psItr = pastSet.begin();
            const set<int>::const_iterator psEnd = pastSet.end();
            
            for (; psItr != psEnd; ++psItr) {
                if (*psItr != stepID) {
                    if (applyDebug) {
                        cout << "\tRequesting ordering to come after" << *psItr << ", a past step with a pre/duration on " << *(RPGBuilder::getPNE(effs->vars[v])) << "\n";
                    }
                    theState.temporalConstraints->addOrdering(*psItr, stepID, true);
                }
            }
                        
            pastSet.clear();                        
        }
                
    }
}

void POTHelper_registerInvariantNumerics(MinimalState & theState, const int & startStepID, const int & endStepID, list<int> & reserve, const bool & registerNotDeregister)
{
    static const int PNEcount = RPGBuilder::getPNECount();

    if (applyDebug) {
        if (registerNotDeregister) {
            cout << "\tNumeric invariants requested from " << startStepID << " until " << endStepID << "\n";
        } else {
            cout << "\tNumeric invariants expired from " << startStepID << " until " << endStepID << "\n";
        }
    }


    list<int>::iterator precItr = reserve.begin();
    const list<int>::iterator precEnd = reserve.end();

    set<int> mentioned;

    for (; precItr != precEnd; ++precItr) {
        RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*precItr];

        if (applyDebug) {
            cout << "\t\t" << currPre << endl;
        }
        
        for (int pass = 0; pass < 2; ++pass) {

            const int currVar = (pass ? currPre.RHSVariable : currPre.LHSVariable);

            if (currVar < 0) continue;


            if (currVar < PNEcount) {
                mentioned.insert(currVar);
                if (registerNotDeregister) {
                    theState.temporalConstraints->lastStepToTouchPNE[currVar].activeInvariants.insert(make_pair(endStepID, startStepID));
                } else {
                    theState.temporalConstraints->lastStepToTouchPNE[currVar].activeInvariants.erase(endStepID);
                    theState.temporalConstraints->lastStepToTouchPNE[currVar].stepsWithPreconditionsSinceTheLastEffect.insert(endStepID);
                }
            } else if (currVar < 2 * PNEcount) {
                mentioned.insert(currVar - PNEcount);
                if (registerNotDeregister) {
                    INVARIANTINSERT(theState.temporalConstraints->lastStepToTouchPNE[currVar - PNEcount].activeInvariants, make_pair(endStepID, startStepID), theState.planLength);
                } else {
                    INVARIANTERASE(theState.temporalConstraints->lastStepToTouchPNE[currVar - PNEcount].activeInvariants, endStepID, theState.planLength);
                    theState.temporalConstraints->lastStepToTouchPNE[currVar - PNEcount].stepsWithPreconditionsSinceTheLastEffect.insert(endStepID);
                }
            } else {
                RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currVar);

                for (int i = 0; i < currAV.size; ++i) {
                    const int lv = currAV.fluents[i];
                    if (lv < PNEcount) {
                        mentioned.insert(lv);
                        if (registerNotDeregister) {
                            INVARIANTINSERT(theState.temporalConstraints->lastStepToTouchPNE[lv].activeInvariants, make_pair(endStepID, startStepID), theState.planLength);
                        } else {
                            INVARIANTERASE(theState.temporalConstraints->lastStepToTouchPNE[lv].activeInvariants, endStepID, theState.planLength);
                            theState.temporalConstraints->lastStepToTouchPNE[lv].stepsWithPreconditionsSinceTheLastEffect.insert(endStepID);
                        }
                    } else {
                        mentioned.insert(lv - PNEcount);
                        if (registerNotDeregister) {
                            INVARIANTINSERT(theState.temporalConstraints->lastStepToTouchPNE[lv-PNEcount].activeInvariants, make_pair(endStepID, startStepID), theState.planLength);
                        } else {
                            INVARIANTERASE(theState.temporalConstraints->lastStepToTouchPNE[lv-PNEcount].activeInvariants, endStepID, theState.planLength);
                            theState.temporalConstraints->lastStepToTouchPNE[lv-PNEcount].stepsWithPreconditionsSinceTheLastEffect.insert(endStepID);
                        }
                    }
                }
            }
        }
    }

    if (applyDebug) {
        cout << "\tConstraints for invariants done, updating for touching numeric variables\n";
    }

    if (registerNotDeregister) {
        POTHelper_updateForNumericVariables(theState, startStepID, endStepID, true, mentioned);
    } else {
        POTHelper_updateForNumericVariables(theState, startStepID, endStepID, false, mentioned);
    }

    if (applyDebug) {
        cout << "\tExiting update for invariants\n";
    }
}

void sanityCheck(MinimalState & workOn)
{

    if (!workOn.startedActions.empty()) return;

    {
        static const int pneCount = RPGBuilder::getPNECount();
        
        for (int pne = 0; pne < pneCount; ++pne) {
            if (workOn.temporalConstraints->lastStepToTouchPNE[pne].lastInstantaneousEffect != -1) {
                if (workOn.temporalConstraints->lastStepToTouchPNE[pne].lastInstantaneousEffect >= workOn.planLength) {
                    cerr << "Fatal error: " << *(RPGBuilder::getPNE(pne)) << " last touched by " << workOn.temporalConstraints->lastStepToTouchPNE[pne].lastInstantaneousEffect << ", which is not within a plan of length " << workOn.planLength << endl;
                    assert(workOn.temporalConstraints->lastStepToTouchPNE[pne].lastInstantaneousEffect < workOn.planLength);
                }
            }
        }
    }
    
    // for now the only check is that we don't have any hanging deletable froms if all actions have finished

    for (int pass = 0; pass < 2; ++pass) {

        StateFacts & polarised = (pass ? workOn.retired : workOn.first);

        StateFacts::iterator propItr = polarised.begin();
        const StateFacts::iterator propEnd = polarised.end();

        for (; propItr != propEnd; ++propItr) {
            if (TemporalAnalysis::getFactIsAbstract()[propItr->first]) {
                continue;
            }
            
            map<StepAndBeforeOrAfter, bool> & deletableFrom = (pass ? propItr->second.addableFrom : propItr->second.deletableFrom);
            map<StepAndBeforeOrAfter, bool>::iterator dfItr = deletableFrom.begin();
            const map<StepAndBeforeOrAfter, bool>::iterator dfEnd = deletableFrom.end();

            for (; dfItr != dfEnd; ++dfItr) {
                assert(dfItr->second == SAFETOSKIP);
            }
        }
    }

}

void POTHelper_orderDummyStepWRTDependencies(MinimalState & theState, const NNFPreconditionChooser::Supporters & support, const int & dummyStepID)
{
    
    static const int pneCount = RPGBuilder::getPNECount();
    
    {
        
        set<int>::const_iterator litItr = support.propositions.begin();
        const set<int>::const_iterator litEnd = support.propositions.end();
        
        for (; litItr != litEnd; ++litItr) {
            
            StateFacts::iterator stateItr = theState.first.find(*litItr);
            
            if (stateItr != theState.first.end()) {
                
                // so this is just like the precondition case
                // - we refer to this fact positively, and it is true
                
                if (stateItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) { // if it wasn't true in the initial state
                    theState.temporalConstraints->addOrdering(stateItr->second.availableFrom.stepID, dummyStepID, true);
                }
                stateItr->second.deletableFrom.insert(make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, dummyStepID), SAFETOSKIP));
                
            } else {
                // make sure that future adders of this fact come after now, to avoid retroactive support
                
                StateFacts::iterator retItr = theState.retired.find(*litItr);
                
                if (retItr == theState.retired.end()) {
                    // never previously deleted, so create the ability to record that adders must come after now
                    retItr = theState.retired.insert(make_pair(*litItr, StepAndBeforeOrAfter())).first;
                    retItr->second.markAsDeleted(StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, 0));
                }
                
                retItr->second.addableFrom.insert(make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, dummyStepID), SAFETOSKIP));
                
                
            }
            
        }
    }
    
    {
        
        set<int>::const_iterator litItr = support.negativePropositions.begin();
        const set<int>::const_iterator litEnd = support.negativePropositions.end();
        
        for (; litItr != litEnd; ++litItr) {
            
            StateFacts::iterator posStateItr = theState.first.find(*litItr);
              
            if (posStateItr != theState.first.end()) {
                // the fact is currently true
                // make sure future deletors come after now, to avoid retroactive support
                
                posStateItr->second.deletableFrom.insert(make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, dummyStepID), SAFETOSKIP));
                
            } else {
                
                // the fact is currently false - treat it as we would a negative precondition
        
                StateFacts::iterator retItr = theState.retired.find(*litItr);
            
                if (retItr == theState.retired.end()) {
                    // false initially, never since deleted
                    retItr = theState.retired.insert(make_pair(*litItr, StepAndBeforeOrAfter())).first;                        
                    retItr->second.markAsDeleted(StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, 0));
                }
                
                retItr->second.addableFrom.insert(make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, dummyStepID), SAFETOSKIP));
                
            }
            
        }
    }
    
    {
        
        set<int> relevantNumericVars;
        
        
        set<int>::const_iterator npItr = support.numerics.begin();
        const set<int>::const_iterator npEnd = support.numerics.end();
        
        for (; npItr != npEnd; ++npItr) {
            
            const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*npItr];
            
            if (currPre.LHSVariable < pneCount) {
                relevantNumericVars.insert(currPre.LHSVariable);
            } else if (currPre.LHSVariable < 2 * pneCount) {
                relevantNumericVars.insert(currPre.LHSVariable - pneCount);
            } else {
                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                
                for (int s = 0; s < currAV.size; ++s) {
                    if (currAV.fluents[s] < pneCount) {
                        relevantNumericVars.insert(currAV.fluents[s]);
                    } else {
                        relevantNumericVars.insert(currAV.fluents[s] - pneCount);
                    }
                }
            }
            
        }
        
        
        set<int>::const_iterator varItr = relevantNumericVars.begin();  
        const set<int>::const_iterator varEnd = relevantNumericVars.end();
        
        for (; varItr != varEnd; ++varItr) {
            
            FluentInteraction & currFI =  theState.temporalConstraints->lastStepToTouchPNE[*varItr];

            if (currFI.lastInstantaneousEffect >= 0) {
                theState.temporalConstraints->addOrdering(currFI.lastInstantaneousEffect, dummyStepID, true);
                if (applyDebug) {
                    cout << COLOUR_yellow << "To support " << *(RPGBuilder::getPNE(*varItr)) << " ordering dummy step " << dummyStepID << " after " << currFI.lastInstantaneousEffect << COLOUR_default << endl;
                }
            }
            
            currFI.stepsWithPreconditionsSinceTheLastEffect.insert(dummyStepID);
            
        }
    }

}

void POTHelper_supportPreferencePreconditions(MinimalState & theState, const int & pairWithStep, list<pair<int, FFEvent> > & newDummySteps,
                                              const list<NNFPreconditionChooser::Supporters> & chosen)
{

    
    list<NNFPreconditionChooser::Supporters>::const_iterator tcItr = chosen.begin();
    const list<NNFPreconditionChooser::Supporters>::const_iterator tcEnd = chosen.end();
    
    for (; tcItr != tcEnd; ++tcItr) {
        //const RPGBuilder::Constraint * const pref = &(RPGBuilder::getPreferences()[tcItr->pref]);
        
        assert(!tcItr->meetsTheTrigger);
        
        theState.temporalConstraints->extend(1);
        
        const int dummyStepID = theState.planLength++;
        
        newDummySteps.push_back(make_pair(dummyStepID, FFEvent::getDummyStep()));
        
        FFEvent & dummyTemporalStep = newDummySteps.back().second;
        dummyTemporalStep.time_spec = Planner::E_DUMMY_PREFERENCE_PRECONDITION;
        dummyTemporalStep.divisionID = tcItr->pref;
        dummyTemporalStep.pairWithStep = pairWithStep;
        
        
        POTHelper_orderDummyStepWRTDependencies(theState, *tcItr, dummyStepID);
        
        
    }
    
}


void POTHelper_addDummySteps(MinimalState & theState, const int & justAfterStep, list<pair<int, FFEvent> > & newDummySteps,
                             const list<NNFPreconditionChooser::Supporters> & chosen)
{
    
    list<NNFPreconditionChooser::Supporters>::const_iterator tcItr = chosen.begin();
    const list<NNFPreconditionChooser::Supporters>::const_iterator tcEnd = chosen.end();
    
    for (; tcItr != tcEnd; ++tcItr) {
        theState.temporalConstraints->extend(1);
        
        const int dummyStepID = theState.planLength++;
        
        newDummySteps.push_back(make_pair(dummyStepID, FFEvent::getDummyStep()));
        
        FFEvent & dummyTemporalStep = newDummySteps.back().second;
        if (tcItr->satisfyIt) {
            dummyTemporalStep.time_spec = (tcItr->meetsTheTrigger ? Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE : Planner::E_DUMMY_TEMPORAL_GOAL_TRUE);
        } else {
            assert(RPGBuilder::getPreferences()[tcItr->pref].cons == VAL::E_ATMOSTONCE);
            dummyTemporalStep.time_spec = (tcItr->meetsTheTrigger ? Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE : Planner::E_DUMMY_TEMPORAL_GOAL_FALSE);
        }
        dummyTemporalStep.divisionID = tcItr->pref;
        
        if (RPGBuilder::getPreferences()[tcItr->pref].cons == VAL::E_ALWAYSWITHIN && tcItr->meetsTheTrigger) {
            dummyTemporalStep.pairWithStep = justAfterStep;
        } else {        
            dummyTemporalStep.pairWithStep = -1;
        }
        
        POTHelper_orderDummyStepWRTDependencies(theState, *tcItr, dummyStepID);                

    }
    
    
}

static unsigned int oldStepCount;

MinimalState * PartialOrderTransformer::applyAction(MinimalState & theStateHidden,
                                                    vector<double> & minTimestamps,
                                                    list<pair<int, FFEvent> > & newDummySteps,
                                                    bool & constraintsSatisfied,
                                                    const ActionSegment & a, 
                                                    const bool & inPlace, const double & minDur, const double & maxDur)
{
    applyDebug = Globals::globalVerbosity & 1048576;
    constraintsSatisfied = true;
    
    unsigned int extensionNeeded = 0;

    if (applyDebug) {
        oldStepCount = theStateHidden.temporalConstraints->size();
        cout << "Applying action.  Previously had space for constraints on " << oldStepCount << " steps\n";
        assert(oldStepCount == theStateHidden.planLength);
        sanityCheck(theStateHidden);
    }


    if (a.first) {
        if (a.second == Planner::E_AT_START) {
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

    map<int,GoalFalseTrueAfterStep> goalNowAvailableFrom;
    
    
    if (inPlace && extensionNeeded) {
        theStateHidden.temporalConstraints->extend(extensionNeeded);
    }

    if (applyDebug) {
        const unsigned int newStepCount = workOn->temporalConstraints->size();
        cout << "Now have space for constraints on " << newStepCount << " steps\n";
        assert(newStepCount - oldStepCount == extensionNeeded);
    }

    if (!a.first) { // applying a TIL
        static vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNonAbstractedTILVec();

        for (; workOn->nextTIL <= a.divisionID; ++(workOn->nextTIL)) {

            set<int> newlyAdded;
            set<int> newlyDeleted;
            const set<int> variablesTouched;
            
            POTHelper_updateForInstantaneousEffects(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, workOn->planLength),
                                                    tilVec[workOn->nextTIL]->delEffects, tilVec[workOn->nextTIL]->addEffects,
                                                    newlyAdded, newlyDeleted,
                                                    goalNowAvailableFrom);
                                                    
                                                    
            minTimestamps[workOn->planLength] = tilVec[workOn->nextTIL]->duration;
            
            if (!goalNowAvailableFrom.empty()) {                                
                POTHelper_updateWithinCosts(*workOn, goalNowAvailableFrom, minTimestamps);                
                goalNowAvailableFrom.clear();
            }
                                             
            ++workOn->planLength;
            {
                list<NNFPreconditionChooser::Supporters> chosen;
                //check preferences
                constraintsSatisfied = PreferenceHandler::update(*workOn, minTimestamps, newlyAdded, newlyDeleted, variablesTouched,chosen);
                if (!constraintsSatisfied) {
                    return workOn;
                }
                //add constraints to partial order to make sure if it's a ^ b that both hold at once
                POTHelper_addDummySteps(*workOn, workOn->planLength - 1, newDummySteps, chosen);
            }
        }

        workOn->temporalConstraints->setMostRecentStep(workOn->planLength - 1);

        return workOn;
    }

    const int actID = a.first->getID();
    
    if (a.second == Planner::E_AT_START) {

        if (RPGBuilder::getRPGDEs(actID).empty()) { // non-temporal action

            {
                list<NNFPreconditionChooser::Supporters> chosenPreconditionPreferenceSupport;
                //check precondition preferences
                PreferenceHandler::aboutToApply(*workOn, a, minTimestamps, chosenPreconditionPreferenceSupport);
                POTHelper_supportPreferencePreconditions(*workOn, workOn->planLength, newDummySteps, chosenPreconditionPreferenceSupport);
            }
            
            
            set<int> newlyAdded;
            set<int> newlyDeleted;
            set<int> variablesTouched;
            
            list<Literal*> & pres = RPGBuilder::getStartPropositionalPreconditions()[actID];
            list<Literal*> & negpres = RPGBuilder::getStartNegativePropositionalPreconditions()[actID];
            POTHelper_updateForPreconditions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, workOn->planLength),
                                             make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, workOn->planLength), SAFETOSKIP),
                                             pres, negpres);
                                             
                                             
            list<Literal*> & delEffs = RPGBuilder::getStartPropositionDeletes()[actID];
            list<Literal*> & addEffs = RPGBuilder::getStartPropositionAdds()[actID];

            POTHelper_updateForInstantaneousEffects(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, workOn->planLength),
                                                    delEffs, addEffs,
                                                    newlyAdded, newlyDeleted,
                                                    goalNowAvailableFrom);

            list<pair<int,int> > minOutcomes;
            const list<RPGBuilder::IntegralContinuousEffect> * ice = 0;
            
            {
                set<int> mentioned;
                POTHelper_updateForNumericPreconditions(*workOn, workOn->planLength, mentioned, RPGBuilder::getStartPreNumerics()[actID]);
                map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator integralItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(actID);
                if (integralItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {
                    
                    list<int> fire;
                    
                    list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = integralItr->second.begin();
                    const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = integralItr->second.end();
                    
                    for (; effItr != effEnd; ++effItr) {
                        pair<int,int> mo(-1,-1);
                        if (effItr->satisfied(Planner::E_AT_START, workOn->secondMin, workOn->secondMax, minDur, maxDur, mo)) {
                            if (applyDebug) {
                                cout << "Outcomes " << mo.first << " to " << mo.second << " of " << *(RPGBuilder::getInstantiatedOp(actID)) << " could conceivably fire\n";
                            }
                            fire.push_back(effItr->getLeftPrecondition());
                        }
                        minOutcomes.push_back(mo);
                    }
                    
                    if (!fire.empty()) {
                        POTHelper_updateForNumericPreconditions(*workOn, workOn->planLength, mentioned, fire);
                        ice = &(integralItr->second);
                    }                    
                }
                
                POTHelper_updateForInputsToInstantaneousNumericEffects(mentioned, RPGBuilder::getStartEffNumerics()[actID]);

                POTHelper_updateForNumericVariables(*workOn, workOn->planLength, workOn->planLength, true, mentioned);
            }

            POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, workOn->planLength, RPGBuilder::getStartEffNumerics()[actID], minDur, maxDur, variablesTouched);

            if (ice) {
                list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = ice->begin();
                const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = ice->end();
                
                list<pair<int,int> >::const_iterator moItr = minOutcomes.begin();
                
                list<int> effs;
                map<int, pair<double,double> > effectModification;
                
                for (; effItr != effEnd; ++effItr, ++moItr) {

                    if (moItr->first != -1) {
                        const list<pair<int,double> > & seffs = effItr->getLeftStartEffects();
                        list<pair<int,double> >::const_iterator seffItr = seffs.begin();
                        const list<pair<int,double> >::const_iterator seffEnd = seffs.end();
                        
                        for (; seffItr != seffEnd; ++seffItr) {                        
                            effs.push_back(seffItr->first);
                            effectModification[RPGBuilder::getNumericEff()[seffItr->first].fluentIndex] = make_pair(moItr->first * seffItr->second, moItr->second * seffItr->second);
                        }                                                    
                    }                    
                }
                
                assert(!effs.empty());

                if (applyDebug) {
                    cout << COLOUR_light_blue << "\tAbout to apply integer-encoding conditional effects\n";
                }
                
                
                POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, workOn->planLength, effs, minDur, maxDur, variablesTouched);

                map<int, pair<double,double> >::const_iterator emItr = effectModification.begin();
                const map<int, pair<double,double> >::const_iterator emEnd = effectModification.end();
                
                for (; emItr != emEnd; ++emItr) {
                    if (emItr->second.first < emItr->second.second) {
                        if (applyDebug) {
                            cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.first << ", upper bound by " << emItr->second.second << COLOUR_default << endl;
                        }
                        workOn->secondMin[emItr->first] += emItr->second.first;
                        workOn->secondMax[emItr->first] += emItr->second.second;
                    } else {
                        if (applyDebug) {
                            cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.second << ", upper bound by " << emItr->second.first << COLOUR_default << endl;
                        }                        
                        workOn->secondMax[emItr->first] += emItr->second.first;
                        workOn->secondMin[emItr->first] += emItr->second.second;
                    }
                }
            }
            
            if (!goalNowAvailableFrom.empty() || !RPGBuilder::getPreferences().empty() || workOn->lowerBoundOnTimeDependentRewardFacts) {
                minTimestamps[workOn->planLength] = POTHelper_getTimeOfStep(*workOn, minTimestamps, workOn->planLength, 0.0);                                
            }
            
            if (!goalNowAvailableFrom.empty()) {
                POTHelper_updateWithinCosts(*workOn, goalNowAvailableFrom, minTimestamps);                
            }
            
            workOn->temporalConstraints->setMostRecentStep(workOn->planLength);

            ++workOn->planLength;
            
            {
                list<NNFPreconditionChooser::Supporters> chosen;
                //check preferences
                constraintsSatisfied = PreferenceHandler::update(*workOn, minTimestamps, newlyAdded, newlyDeleted, variablesTouched, chosen);
                if (!constraintsSatisfied) {
                    return workOn;
                }                
                //add constraints to partial order to make sure if it's a ^ b that both hold at once
                POTHelper_addDummySteps(*workOn, workOn->planLength - 1, newDummySteps, chosen);
            }
            
            if (applyDebug) sanityCheck(*workOn);

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
            list<NNFPreconditionChooser::Supporters> chosenPreconditionPreferenceSupport;
            //check precondition preferences
            PreferenceHandler::aboutToApply(*workOn, a, minTimestamps, chosenPreconditionPreferenceSupport);
            POTHelper_supportPreferencePreconditions(*workOn, startStepID, newDummySteps, chosenPreconditionPreferenceSupport);
        }
        
        
        set<int> mentioned;

        POTHelper_updateForDurations(*workOn, startStepID, mentioned, *(RPGBuilder::getRPGDEs(actID)[0]));

        list<pair<int,int> > minOutcomes;
        const list<RPGBuilder::IntegralContinuousEffect> * ice = 0;
        
        
        {
            if (applyDebug) cout << " * Requesting start preconditions\n";
            list<Literal*> & pres = RPGBuilder::getStartPropositionalPreconditions()[actID];
            list<Literal*> & negpres = RPGBuilder::getStartNegativePropositionalPreconditions()[actID];
            POTHelper_updateForPreconditions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, startStepID),
                                             make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, startStepID), SAFETOSKIP),
                                             pres, negpres);
                                             
            POTHelper_updateForNumericPreconditions(*workOn, startStepID, mentioned, RPGBuilder::getStartPreNumerics()[actID]);
            
            map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator integralItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(actID);
            if (integralItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {

                if (applyDebug) {
                    cout << "Considering integral conditional effects" << endl;
                }
                list<int> fire;
                
                list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = integralItr->second.begin();
                const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = integralItr->second.end();
                
                for (; effItr != effEnd; ++effItr) {
                    pair<int,int> mo(-1,-1);
                    if (effItr->satisfied(Planner::E_AT_START, workOn->secondMin, workOn->secondMax, minDur, maxDur, mo)) {
                        if (applyDebug) {
                            cout << "Outcomes " << mo.first << " to " << mo.second << " of " << *(RPGBuilder::getInstantiatedOp(actID)) << " could conceivably fire\n";
                        }                        
                        fire.push_back(effItr->getLeftPrecondition());
                    } else {
                        if (applyDebug) {
                            cout << "No outcomes of " << *(RPGBuilder::getInstantiatedOp(actID)) << " could conceivably fire\n";
                        }
                        
                    }
                    minOutcomes.push_back(mo);
                }
                
                if (!fire.empty()) {
                    POTHelper_updateForNumericPreconditions(*workOn, startStepID, mentioned, fire);
                    ice = &(integralItr->second);
                }                    
            }
        }

        set<int> newlyAdded;
        set<int> newlyDeleted;
        set<int> variablesTouched;
        
        {

            list<Literal*> & delEffs = RPGBuilder::getStartPropositionDeletes()[actID];
            list<Literal*> & addEffs = RPGBuilder::getStartPropositionAdds()[actID];

            if (applyDebug) cout << " * Applying start effects.  Start adds: " << addEffs.size() << ", Start deletes: " << delEffs.size() << "\n";                        
            
            POTHelper_updateForInstantaneousEffects(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, startStepID),
                                                    delEffs, addEffs,
                                                    newlyAdded, newlyDeleted,
                                                    goalNowAvailableFrom);
        }

        {
            POTHelper_updateForInputsToInstantaneousNumericEffects(mentioned, RPGBuilder::getStartEffNumerics()[actID]);
            POTHelper_updateForNumericVariables(*workOn, startStepID, endStepID, true, mentioned);

            mentioned.clear();

            POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, startStepID, RPGBuilder::getStartEffNumerics()[actID], minDur, maxDur, variablesTouched);

            if (ice) {
                list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = ice->begin();
                const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = ice->end();
                
                list<pair<int,int> >::const_iterator moItr = minOutcomes.begin();
                
                list<int> effs;
                map<int, pair<double,double> > effectModification;
                
                for (; effItr != effEnd; ++effItr, ++moItr) {

                    if (moItr->first != -1) {
                        const list<pair<int,double> > & seffs = effItr->getLeftStartEffects();
                        list<pair<int,double> >::const_iterator seffItr = seffs.begin();
                        const list<pair<int,double> >::const_iterator seffEnd = seffs.end();
                        
                        for (; seffItr != seffEnd; ++seffItr) {                        
                            effs.push_back(seffItr->first);
                            effectModification[RPGBuilder::getNumericEff()[seffItr->first].fluentIndex] = make_pair(moItr->first * seffItr->second, moItr->second * seffItr->second);
                        }                                                    
                    }                    
                }
                
                assert(!effs.empty());

                if (applyDebug) {
                    cout << COLOUR_light_blue << "\tAbout to apply integer-encoding conditional effects\n";
                }
                                                                
                POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, startStepID, effs, minDur, maxDur, variablesTouched);

                map<int, pair<double,double> >::const_iterator emItr = effectModification.begin();
                const map<int, pair<double,double> >::const_iterator emEnd = effectModification.end();
                
                for (; emItr != emEnd; ++emItr) {
                    if (emItr->second.first < emItr->second.second) {
                        if (applyDebug) {
                            cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.first << ", upper bound by " << emItr->second.second << COLOUR_default << endl;
                        }
                        workOn->secondMin[emItr->first] += emItr->second.first;
                        workOn->secondMax[emItr->first] += emItr->second.second;
                    } else {
                        if (applyDebug) {
                            cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.second << ", upper bound by " << emItr->second.first << COLOUR_default << endl;
                        }                        
                        workOn->secondMax[emItr->first] += emItr->second.first;
                        workOn->secondMin[emItr->first] += emItr->second.second;
                    }
                }
            }

            
            POTHelper_registerContinuousNumericEffects(*workOn, startStepID, endStepID, RPGBuilder::getLinearDiscretisation()[actID], true);
            
        }
        
        if (!RPGBuilder::getPreferences().empty()) {
            minTimestamps[startStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, 0.0);
            list<NNFPreconditionChooser::Supporters> chosen;
            //check preferences            
            constraintsSatisfied = PreferenceHandler::update(*workOn, minTimestamps, newlyAdded, newlyDeleted, variablesTouched, chosen);
            if (!constraintsSatisfied) {
                return workOn;
            }            
            //add constraints to partial order to make sure if it's a ^ b that both hold at once
            POTHelper_addDummySteps(*workOn, startStepID, newDummySteps, chosen);
        } else if (workOn->lowerBoundOnTimeDependentRewardFacts) {
            minTimestamps[startStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, 0.0);
        }
                
        {
            if (applyDebug) cout << " * Requesting invariants from " << startStepID << " to " << endStepID << "\n";
            list<Literal*> & pres = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
            list<Literal*> & negpres = RPGBuilder::getInvariantNegativePropositionalPreconditions()[actID];
            POTHelper_updateForPreconditions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, startStepID),
                                             make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, endStepID), skip),
                                             pres, negpres);
            POTHelper_registerInvariantNumerics(*workOn, startStepID, endStepID, RPGBuilder::getInvariantNumerics()[actID], true);
        }

        if (skip == SAFETOSKIP) {

            
            {
                list<NNFPreconditionChooser::Supporters> chosenEndPreconditionPreferenceSupport;
                ActionSegment aEnd(a);
                aEnd.second = Planner::E_AT_END;                
                PreferenceHandler::aboutToApply(*workOn, aEnd, minTimestamps, chosenEndPreconditionPreferenceSupport);
                POTHelper_supportPreferencePreconditions(*workOn, endStepID, newDummySteps, chosenEndPreconditionPreferenceSupport);
            }
            
            {
                
                if (applyDebug) cout << " * Compression-safe action - requesting end preconditions\n";
                list<Literal*> & pres = RPGBuilder::getEndPropositionalPreconditions()[actID];
                list<Literal*> & negpres = RPGBuilder::getEndNegativePropositionalPreconditions()[actID];
                POTHelper_updateForPreconditions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, endStepID),
                                                 make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID), skip),
                                                 pres, negpres);
            }
            
            set<int> newlyAddedEnd;
            set<int> newlyDeletedEnd;
            set<int> variablesTouchedEnd;
            
            {
                if (applyDebug) cout << " * Compression-safe action - recording end effects\n";

                list<Literal*> & delEffs = RPGBuilder::getEndPropositionDeletes()[actID];
                list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];

                POTHelper_updateForInstantaneousEffects(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID),
                                                        delEffs, addEffs,
                                                        newlyAddedEnd, newlyDeletedEnd,
                                                        goalNowAvailableFrom);
                
                #ifdef POPF3ANALYSIS
                POTHelper_queueCompressionSafeInstantaneousNumericEffects(*workOn, endStepID, RPGBuilder::getEndEffNumerics()[actID], variablesTouchedEnd);
                #endif
            }
            if (!RPGBuilder::getPreferences().empty()) {
                minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, minTimestamps[startStepID] + minDur);
                list<NNFPreconditionChooser::Supporters> chosen;
                //check preferences            
                constraintsSatisfied = PreferenceHandler::update(*workOn, minTimestamps, newlyAddedEnd, newlyDeletedEnd, variablesTouchedEnd, chosen);
                if (!constraintsSatisfied) {
                    return workOn;
                }                
                //add constraints to partial order to make sure if it's a ^ b that both hold at once
                POTHelper_addDummySteps(*workOn, endStepID, newDummySteps, chosen);
            } else if (workOn->lowerBoundOnTimeDependentRewardFacts) {
                minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, minTimestamps[startStepID] + minDur);
            }
            
            if (!goalNowAvailableFrom.empty()) {        
                if (RPGBuilder::getPreferences().empty() && !workOn->lowerBoundOnTimeDependentRewardFacts) {
                    // if we have preferences, these were calculated higher up
                    minTimestamps[startStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, 0.0);
                    minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, minTimestamps[startStepID] + minDur);
                }
                POTHelper_updateWithinCosts(*workOn, goalNowAvailableFrom, minTimestamps);                
            }
            
            
            ++(workOn->actionsExecuting);
        } else {
            
            {
                if (applyDebug) cout << " * Non-compression-safe action - avoiding end-delete--invariant clashes\n";

                list<Literal*> & delEffs = RPGBuilder::getEndPropositionDeletes()[actID];
                POTHelper_updateForEndDeleteInvariantInteractions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID), delEffs, false);

                list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];
                POTHelper_updateForEndDeleteInvariantInteractions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID), addEffs, true);

            }

            if (!NumericAnalysis::getVariablesFixedAndDefinedByFact().empty()) {
                const list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];
                list<Literal*>::const_iterator effItr = addEffs.begin();
                const list<Literal*>::const_iterator effEnd = addEffs.end();
                
                for (; effItr != effEnd; ++effItr) {
                    const map<int,set<int> >::const_iterator fixItr = NumericAnalysis::getVariablesFixedAndDefinedByFact().find((*effItr)->getStateID());
                    if (fixItr != NumericAnalysis::getVariablesFixedAndDefinedByFact().end()) {
                        set<int>::const_iterator vItr = fixItr->second.begin();
                        const set<int>::const_iterator vEnd = fixItr->second.end();
                        
                        for (; vItr != vEnd; ++vItr) {
                            const set<int> & futures = workOn->temporalConstraints->lastStepToTouchPNE[*vItr].futureEndInteractions;
                            set<int>::const_iterator aftItr = futures.begin();
                            const set<int>::const_iterator aftEnd = futures.end();
                            
                            for (; aftItr != aftEnd; ++aftItr) {
                                workOn->temporalConstraints->addOrdering(endStepID, *aftItr, true);
                            }
                        }
                    }
                }
            }
            
            {
                set<int> mentioned;
                
                POTHelper_updateForNumericPreconditions(*workOn, endStepID, mentioned, RPGBuilder::getEndPreNumerics()[actID], false);
                POTHelper_updateForInputsToInstantaneousNumericEffects(mentioned, RPGBuilder::getEndEffNumerics()[actID]);
                
                POTHelper_warnForNumericVariables(*workOn, endStepID, mentioned);
                
                POTHelper_warnForNumericEffects(*workOn, endStepID, RPGBuilder::getEndEffNumerics()[actID], minDur, maxDur);
                
            }
    

            workOn->startedActions[actID].insert(endStepID);
            ++(workOn->actionsExecuting);

            if (!goalNowAvailableFrom.empty()) {
                if (RPGBuilder::getPreferences().empty()) {
                    // if we have preferences, this was calculated higher up
                    minTimestamps[startStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, startStepID, 0.0);
                }
                POTHelper_updateWithinCosts(*workOn, goalNowAvailableFrom, minTimestamps);                
            }
            
            // we only need record the action as started in the non-compression safe case
            // as it end needs not be explicitly applied otherwise
        }

        if (applyDebug) sanityCheck(*workOn);

        return workOn;
    }

    // otherwise, we're ending a non-compression-safe action

    map<int, set<int> >::iterator saItr = workOn->startedActions.find(actID);

    assert(saItr != workOn->startedActions.end());

    set<int>::iterator endItr = saItr->second.begin();

    const int endStepID = *endItr;
    const int startStepID = endStepID - 1;
    saItr->second.erase(endItr);
    if (saItr->second.empty()) workOn->startedActions.erase(saItr);

    --(workOn->actionsExecuting);

    workOn->temporalConstraints->setMostRecentStep(endStepID);

    {
        if (applyDebug) cout << " * De-registering invariants\n";

        POTHelper_invariantsCanNowFinish(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, endStepID),
                                         RPGBuilder::getInvariantPropositionalPreconditions()[actID],
                                         RPGBuilder::getInvariantNegativePropositionalPreconditions()[actID]);
        POTHelper_registerInvariantNumerics(*workOn, startStepID, endStepID, RPGBuilder::getInvariantNumerics()[actID], false);
        POTHelper_registerContinuousNumericEffects(*workOn, -1, endStepID, RPGBuilder::getLinearDiscretisation()[actID], false);
    }

    {
        list<NNFPreconditionChooser::Supporters> chosenPreconditionPreferenceSupport;
        //check precondition preferences
        PreferenceHandler::aboutToApply(*workOn, a, minTimestamps, chosenPreconditionPreferenceSupport);
        POTHelper_supportPreferencePreconditions(*workOn, endStepID, newDummySteps, chosenPreconditionPreferenceSupport);
    }
    
    
    {
        if (applyDebug) cout << " * Requesting end preconditions\n";
        list<Literal*> & pres = RPGBuilder::getEndPropositionalPreconditions()[actID];
        list<Literal*> & negpres = RPGBuilder::getEndNegativePropositionalPreconditions()[actID];
        POTHelper_updateForPreconditions(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::BEFORE, endStepID),
                                         make_pair(StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID), SAFETOSKIP),
                                         pres, negpres);
                                         
    }

    set<int> newlyAdded;
    set<int> newlyDeleted;
    set<int> variablesTouched;
    
    {
        if (applyDebug) cout << " * Recording end effects\n";
        list<Literal*> & delEffs = RPGBuilder::getEndPropositionDeletes()[actID];
        list<Literal*> & addEffs = RPGBuilder::getEndPropositionAdds()[actID];

        POTHelper_updateForInstantaneousEffects(*workOn, StepAndBeforeOrAfter(StepAndBeforeOrAfter::AFTER, endStepID),
                                                delEffs, addEffs,
                                                newlyAdded, newlyDeleted,
                                                goalNowAvailableFrom);
    }

    list<pair<int,int> > minOutcomes;
    const list<RPGBuilder::IntegralContinuousEffect> * ice = 0;
    
    
    {
        set<int> mentioned;
        if (applyDebug) cout << " * Collecting inputs to end numeric preconditions\n";        
        POTHelper_updateForNumericPreconditions(*workOn, endStepID, mentioned, RPGBuilder::getEndPreNumerics()[actID]);
        
        map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator integralItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(actID);
        if (integralItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {
            
            list<int> fire;
            
            list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = integralItr->second.begin();
            const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = integralItr->second.end();
            
            for (; effItr != effEnd; ++effItr) {
                pair<int,int> mo(-1,-1);
                if (effItr->satisfied(Planner::E_AT_END, workOn->secondMin, workOn->secondMax, minDur, maxDur, mo)) {
                    if (applyDebug) {
                        cout << "Outcomes " << mo.first << " to " << mo.second << " of " << *(RPGBuilder::getInstantiatedOp(actID)) << " could conceivably fire\n";
                    }
                    fire.push_back(effItr->getLeftPrecondition());
                }
                minOutcomes.push_back(mo);
            }
            
            if (!fire.empty()) {
                POTHelper_updateForNumericPreconditions(*workOn, workOn->planLength, mentioned, fire);
                ice = &(integralItr->second);
            }                    
        }

        
        if (applyDebug) cout << " * Collecting inputs to end numeric effects\n";        
        POTHelper_updateForInputsToInstantaneousNumericEffects(mentioned, RPGBuilder::getEndEffNumerics()[actID]);
        if (applyDebug) cout << " * Ordering after needs of preconditions and effects\n";        
        POTHelper_updateForNumericVariables(*workOn, startStepID, endStepID, false, mentioned);

        POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, endStepID, RPGBuilder::getEndEffNumerics()[actID], minDur, maxDur, variablesTouched);

    }

    if (ice) {
        list<RPGBuilder::IntegralContinuousEffect>::const_iterator effItr = ice->begin();
        const list<RPGBuilder::IntegralContinuousEffect>::const_iterator effEnd = ice->end();
        
        list<pair<int,int> >::const_iterator moItr = minOutcomes.begin();
        
        list<int> effs;
        map<int, pair<double,double> > effectModification;
        
        for (; effItr != effEnd; ++effItr, ++moItr) {

            if (moItr->first != -1) {
                const list<pair<int,double> > & seffs = effItr->getLeftEndEffects();
                list<pair<int,double> >::const_iterator seffItr = seffs.begin();
                const list<pair<int,double> >::const_iterator seffEnd = seffs.end();
                
                for (; seffItr != seffEnd; ++seffItr) {                        
                    effs.push_back(seffItr->first);
                    effectModification[RPGBuilder::getNumericEff()[seffItr->first].fluentIndex] = make_pair(moItr->first * seffItr->second, moItr->second * seffItr->second);
                }                                                    
            }                    
        }
        
        assert(!effs.empty());

        if (applyDebug) {
            cout << COLOUR_light_blue << "\tAbout to apply integer-encoding conditional effects\n";
        }
        
        
        POTHelper_updateForOutputsFromInstantaneousNumericEffects(*workOn, minTimestamps, a, endStepID, effs, minDur, maxDur, variablesTouched);

        map<int, pair<double,double> >::const_iterator emItr = effectModification.begin();
        const map<int, pair<double,double> >::const_iterator emEnd = effectModification.end();
        
        for (; emItr != emEnd; ++emItr) {
            if (emItr->second.first < emItr->second.second) {
                if (applyDebug) {
                    cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.first << ", upper bound by " << emItr->second.second << COLOUR_default << endl;
                }
                workOn->secondMin[emItr->first] += emItr->second.first;
                workOn->secondMax[emItr->first] += emItr->second.second;
            } else {
                if (applyDebug) {
                    cout << COLOUR_light_blue << "\tLower bound on outcome increased by " << emItr->second.second << ", upper bound by " << emItr->second.first << COLOUR_default << endl;
                }                        
                workOn->secondMax[emItr->first] += emItr->second.first;
                workOn->secondMin[emItr->first] += emItr->second.second;
            }
        }
    }

    
    if (!RPGBuilder::getPreferences().empty()) {
        minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, endStepID, minTimestamps[startStepID] + minDur );
        list<NNFPreconditionChooser::Supporters> chosen;
        //check preferences            
        constraintsSatisfied = PreferenceHandler::update(*workOn, minTimestamps, newlyAdded, newlyDeleted, variablesTouched, chosen);
        if (!constraintsSatisfied) {
            return workOn;
        }        
        //add constraints to partial order to make sure if it's a ^ b that both hold at once
        POTHelper_addDummySteps(*workOn, endStepID, newDummySteps, chosen);
    } else if (workOn->lowerBoundOnTimeDependentRewardFacts) {
        minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, endStepID, minTimestamps[startStepID] + minDur );
    }

    if (!goalNowAvailableFrom.empty()) {                
        if (RPGBuilder::getPreferences().empty()) {
            // if we have preferences, this was calculated higher up
            minTimestamps[endStepID] = POTHelper_getTimeOfStep(*workOn, minTimestamps, endStepID, minTimestamps[startStepID] + minDur );
        }
        POTHelper_updateWithinCosts(*workOn, goalNowAvailableFrom, minTimestamps);                
    }

    if (applyDebug) sanityCheck(*workOn);

    return workOn;


};

#ifdef POPF3ANALYSIS
void PartialOrderTransformer::updateWhenEndOfActionIs(MinimalState & s, const int & actID, const int & stepID, const double & newTS)
{
    const list<int> & effList = RPGBuilder::getEndEffNumerics()[actID];
    
    list<int>::const_iterator effItr = effList.begin();
    const list<int>::const_iterator effEnd = effList.end();
    
    for (; effItr != effEnd; ++effItr) {
        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
        
        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_IRRELEVANT) {
            continue;
        }
        
        if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_METRICTRACKING) {
            map<double, map<int,double> > & currMap = s.temporalConstraints->lastStepToTouchPNE[currEff.fluentIndex].compressionSafeEndEffectOfStepsAtTime;
            map<double, map<int,double> >::iterator moveItr = currMap.find(-1.0);
            #ifdef NDEBUG
            if (moveItr == currMap.end()) {
                cerr << "Internal error: cannot find c.s. end effect on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                exit(1);
            }
            #endif
            currMap[newTS].insert(moveItr->second.begin(), moveItr->second.end());
            currMap.erase(moveItr);
        }        
    }
}
#endif

};
