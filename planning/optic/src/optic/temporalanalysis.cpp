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

//
// C++ Implementation: temporalanalysis
//
// Description:
//
//
// Author: Amanda Coles, Andrew Coles, Maria Fox, Derek Long <firstname.lastname@cis.strath.ac.uk>, (C) 2009
//
// Copyright: See COPYING file that comes with this distribution
//
//
#include "temporalanalysis.h"

#ifdef POPF3ANALYSIS
#include "numericanalysis.h"
#endif

#include "PreferenceHandler.h"

#include "FFEvent.h"
#include "temporalconstraints.h"

#include <cassert>

#include "colours.h"

using std::endl;

namespace Planner
{

vector<vector<pair<double, double> > > TemporalAnalysis::actionTSBounds;
LiteralSet TemporalAnalysis::initialState;
bool TemporalAnalysis::yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts;
bool TemporalAnalysis::abstractTILsWherePossible = false;

void TemporalAnalysis::dummyDeadlineAnalysis()
{

    const int actCount = RPGBuilder::getFixedDEs().size();
    actionTSBounds = vector<vector<pair<double, double> > >(actCount, vector<pair<double, double> >(2, pair<double, double>(0.0, DBL_MAX)));

};

map<int, list<pair<double, double> > > TemporalAnalysis::windows;

void TemporalAnalysis::processTILDeadlines()
{

    static const bool debug = (Globals::globalVerbosity & 32);
    if (debug) cout << "Performing TIL deadline analysis\n";

    const int actCount = RPGBuilder::getFixedDEs().size();

    actionTSBounds = vector<vector<pair<double, double> > >(actCount, vector<pair<double, double> >(2, pair<double, double>(0.0, DBL_MAX)));


    static const bool workingGlobally = true;
    if (!initialisedGlobalActionDurationBounds) {
        initialisedGlobalActionDurationBounds = true;
        
        globalActionDurationBounds.resize(actCount);
        
        for (int act = 0; act < actCount; ++act) {
            if (RPGBuilder::rogueActions[act]) {
                continue;
            }
            globalActionDurationBounds[act].first = RPGBuilder::getOpMinDuration(act, -1);
            globalActionDurationBounds[act].second = RPGBuilder::getOpMaxDuration(act, -1);
        }
    }
    
    
    static const list<pair<double, double> > emptyList;

    map<int, double> lastAppearance;

    map<int, bool> windowable;

    {

        vector<double> initialFluents;

        RPGBuilder::getInitialState(initialState, initialFluents);

        const vector<RPGBuilder::FakeTILAction*> & allTILs = RPGBuilder::getNormalTILVec();

        if (debug) {
            cout << "Number of TIL happenings: " << allTILs.size() << endl;            
        }
        
        map<int, double> literalAppears;
        map<int, double> literalDisappearsForGood;

        const int tilCount = allTILs.size();
        
        for (int tilID = 0; tilID < tilCount; ++tilID) {
            RPGBuilder::FakeTILAction * const tilItr = allTILs[tilID];
            
            if (debug) cout << "\tTIL " << tilID << " at " << tilItr->duration << "\n";

            {

                list<Literal*> & effs = tilItr->delEffects;

                list<Literal*>::iterator effItr = effs.begin();
                const list<Literal*>::iterator effEnd = effs.end();

                for (; effItr != effEnd; ++effItr) {
                    const int litID = (*effItr)->getStateID();
                    const pair<map<int, bool>::iterator, bool> wItr = windowable.insert(make_pair(litID, true));
                    if (wItr.second) {
                        const list<pair<int, Planner::time_spec> > & etaList = RPGBuilder::getEffectsToActions(litID);
                        list<pair<int, Planner::time_spec> >::const_iterator etItr = etaList.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator etEnd = etaList.end();

                        for (; etItr != etEnd; ++etItr) {
                            if (etItr->second != Planner::E_AT) {
                                if (debug) {
                                    if (wItr.first->second) {
                                        cout << *(*effItr) << " does not form windows, is added by:\n";
                                    }
                                }
                                wItr.first->second = false;
                                if (!debug) break;
                                if (debug) {
                                    if (etItr->second == Planner::E_AT_START) {
                                        cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " start\n";
                                    } else if (etItr->second == Planner::E_AT_END) {
                                        cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " end\n";
                                    }
                                }
                            }
                        }

                        if (debug && wItr.first->second) {
                            cout << *(*effItr) << " forms windows - only added by TILs\n";
                        }

                    }
                    if (wItr.first->second) {
                        literalDisappearsForGood.insert(pair<int, double>(litID, tilItr->duration));
                        list<pair<double, double> > & dest = windows[litID];

                        if (debug) {
                            cout << "Looking at window behaviour for " << *(*effItr);
                        }

                        const pair<map<int, double>::iterator, bool> laItr = lastAppearance.insert(make_pair(litID, DBL_MAX));
                        double & startOfWindow = laItr.first->second;

                        if (laItr.second) {
                            if (dest.empty()) {
                                if (initialState.find(*effItr) != initialState.end()) {
                                    startOfWindow = 0.0;
                                    if (debug) cout << " - true in the initial state";
                                } else {
                                    if (debug) cout << " - not true in the initial state";
                                }
                            } else {
                                if (debug) cout << " - not reappeared since last delete";
                            }
                        } else {
                            if (debug) cout << " - last appeared at " << startOfWindow;
                        }



                        if (startOfWindow != DBL_MAX) {
                            if (debug) {
                                cout << " - making a window [" << startOfWindow << "," << tilItr->duration << "]";
                            }
                            dest.push_back(make_pair(startOfWindow, tilItr->duration));
                        }

                        lastAppearance.erase(laItr.first);

                        if (debug) cout << " - done\n";
                    } else {

                    }
                }

            }

            {

                list<Literal*> & effs = tilItr->addEffects;

                list<Literal*>::iterator effItr = effs.begin();
                const list<Literal*>::iterator effEnd = effs.end();

                for (; effItr != effEnd; ++effItr) {

                    const int litID = (*effItr)->getStateID();
                    const pair<map<int, bool>::iterator, bool> wItr = windowable.insert(make_pair(litID, true));
                    if (wItr.second) {
                        const list<pair<int, Planner::time_spec> > & etaList = RPGBuilder::getEffectsToActions(litID);
                        list<pair<int, Planner::time_spec> >::const_iterator etItr = etaList.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator etEnd = etaList.end();

                        for (; etItr != etEnd; ++etItr) {
                            if (etItr->second != Planner::E_AT) {
                                if (debug) {
                                    if (wItr.first->second) {
                                        cout << *(*effItr) << " does not form windows, is added by:\n";
                                    }
                                }
                                wItr.first->second = false;
                                if (!debug) break;
                                if (debug) {
                                    if (etItr->second == Planner::E_AT_START) {
                                        cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " start\n";
                                    } else if (etItr->second == Planner::E_AT_END) {
                                        cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " end\n";
                                    }
                                }
                            }
                        }

                        if (debug && wItr.first->second) {
                            cout << *(*effItr) << " forms windows - only added by TILs\n";
                        }

                    }
                    if (wItr.first->second) {
                        literalDisappearsForGood.erase(litID);

                        const pair<map<int, double>::iterator, bool> laItr = lastAppearance.insert(make_pair(litID, 0.0));

                        if (laItr.second) {
                            double visibleFrom = tilItr->duration;
                            if (windows.find(litID) == windows.end()) { // appeared, but no time-windows defined yet
                                if (initialState.find(*effItr) != initialState.end()) visibleFrom = 0.0;
                            }
                            laItr.first->second = visibleFrom;
                        }

                        if (initialState.find(*effItr) == initialState.end() && RPGBuilder::getEffectsToActions((*effItr)->getStateID()).empty()) {
                            literalAppears.insert(pair<int, double>((*effItr)->getStateID(), tilItr->duration));
                        }
                    } else {
                        if (debug) {
                            cout << *(*effItr) << " does not form windows, can be added by:\n";
                            const list<pair<int, Planner::time_spec> > & etaList = RPGBuilder::getEffectsToActions(litID);
                            list<pair<int, Planner::time_spec> >::const_iterator etItr = etaList.begin();
                            const list<pair<int, Planner::time_spec> >::const_iterator etEnd = etaList.end();

                            for (; etItr != etEnd; ++etItr) {
                                if (etItr->second == Planner::E_AT_START) {
                                    cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " start\n";
                                } else if (etItr->second == Planner::E_AT_END) {
                                    cout << "\t" << *(RPGBuilder::getInstantiatedOp(etItr->first)) << " end\n";
                                } else if (etItr->second == Planner::E_AT) {
                                    cout << "\tTIL " << etItr->first << "\n";
                                }
                            }
                        }
                    }
                }
            }

        }

        {
            map<int, double>::iterator restrictItr = literalAppears.begin();
            const map<int, double>::iterator restrictEnd = literalAppears.end();

            for (; restrictItr != restrictEnd; ++restrictItr) {

                const double epsilonOff = restrictItr->second + EPSILON;

                list<pair<int, Planner::time_spec> > & affected = RPGBuilder::getPresToActions()[restrictItr->first];
                list<pair<int, Planner::time_spec> >::iterator affItr = affected.begin();
                const list<pair<int, Planner::time_spec> >::iterator affEnd = affected.end();

                for (; affItr != affEnd; ++affItr) {
                    if (affItr->second == Planner::E_AT_START) {
                        double & currMin = actionTSBounds[affItr->first][0].first;
                        if (epsilonOff > currMin) {
                            currMin = epsilonOff;
                            #ifdef ENABLE_DEBUGGING_HOOKS
                            if (workingGlobally) {
                                Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                            }
                            #endif

                            const double endOff = epsilonOff + globalActionDurationBounds[affItr->first].first;
                            double & endMin = actionTSBounds[affItr->first][1].first;
                            if (endOff > endMin) {
                                endMin = endOff;
                                #ifdef ENABLE_DEBUGGING_HOOKS
                                if (workingGlobally) {                                    
                                    Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                                }
                                #endif
                            }
                        }
                    } else {
                        double & currMin = actionTSBounds[affItr->first][1].first;
                        if (epsilonOff > currMin) {
                            currMin = epsilonOff;
                            #ifdef ENABLE_DEBUGGING_HOOKS
                            if (workingGlobally) {                                
                                Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                            }
                            #endif

                            const double startOff = epsilonOff - globalActionDurationBounds[affItr->first].second;
                            double & startMin = actionTSBounds[affItr->first][0].first;
                            if (startOff > startMin) {
                                startMin = startOff;
                                #ifdef ENABLE_DEBUGGING_HOOKS
                                if (workingGlobally) {                                    
                                    Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                                }
                                #endif

                            }
                        }
                    }
                }
            }
        }

        {
            map<int, double>::iterator restrictItr = literalDisappearsForGood.begin();
            const map<int, double>::iterator restrictEnd = literalDisappearsForGood.end();

            for (; restrictItr != restrictEnd; ++restrictItr) {

                if (debug) cout << *(RPGBuilder::getLiteral(restrictItr->first)) << " disappears at " << restrictItr->second << "\n";

                const double epsilonOff = restrictItr->second - EPSILON;

                list<pair<int, Planner::time_spec> > & affected = RPGBuilder::getRawPresToActions()[restrictItr->first];

                if (debug) cout << "Bounding " << affected.size() << " start/end points\n";
                list<pair<int, Planner::time_spec> >::iterator affItr = affected.begin();
                const list<pair<int, Planner::time_spec> >::iterator affEnd = affected.end();

                for (; affItr != affEnd; ++affItr) {
                    if (debug) {
                        cout << "- " << *(RPGBuilder::getInstantiatedOp(affItr->first)) << ":";
                        cout.flush();
                    }
                    if (affItr->second == Planner::E_AT_START) {
                        double & currMax = actionTSBounds[affItr->first][0].second;
                        if (epsilonOff < currMax) {
                            currMax = epsilonOff;
                            if (debug) {
                                cout << " start, max down to " << currMax << ";";
                                cout.flush();
                            }
                            #ifdef ENABLE_DEBUGGING_HOOKS
                            if (workingGlobally) {                                                                                        
                                Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                            }
                            #endif

                            const double endOff = epsilonOff +  globalActionDurationBounds[affItr->first].second;
                            double & endMax = actionTSBounds[affItr->first][1].second;
                            if (endOff < endMax) {
                                endMax = endOff;
                                if (debug) {
                                    cout << " => end max down to " << epsilonOff << "+" << globalActionDurationBounds[affItr->first].second << " = " << endMax << ";";
                                    cout.flush();
                                }
                                #ifdef ENABLE_DEBUGGING_HOOKS
                                if (workingGlobally) {                                                                                                
                                    Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                                }
                                #endif

                            }
                        }
                    } else { // invariant or at end
                        double & currMax = actionTSBounds[affItr->first][1].second;
                        if (epsilonOff < currMax) {
                            currMax = epsilonOff;
                            #ifdef ENABLE_DEBUGGING_HOOKS
                            if (workingGlobally) {                                
                                Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                            }
                            #endif
                            
                            const double startOff = epsilonOff - RPGBuilder::getOpMinDuration(affItr->first, 0);
                            double & startMax = actionTSBounds[affItr->first][0].second;
                            if (startOff < startMax) {
                                startMax = startOff;
                                #ifdef ENABLE_DEBUGGING_HOOKS
                                if (workingGlobally) {                                    
                                    Globals::checkActionBounds(affItr->first, actionTSBounds[affItr->first][0].first, actionTSBounds[affItr->first][0].second, actionTSBounds[affItr->first][1].first, actionTSBounds[affItr->first][1].second);
                                }
                                #endif

                            }
                        }
                    }
                    if (debug) {
                        cout << endl;
                    }
                }
            }
        }

        {
            map<int, double>::const_iterator laItr = lastAppearance.begin();
            const map<int, double>::const_iterator laEnd = lastAppearance.end();

            for (; laItr != laEnd; ++laItr) {
                list<pair<double, double> > & dest = windows[laItr->first];
                if (!dest.empty()) {
                    dest.push_back(make_pair(laItr->second, DBL_MAX));
                }
            }
        }
        {

            map<int, list<pair<double, double> > >::const_iterator winItr = windows.begin();
            const map<int, list<pair<double, double> > >::const_iterator winEnd = windows.end();

            for (; winItr != winEnd; ++winItr) {
                const list<pair<double, double> > & currList = winItr->second;
                if (currList.empty()) continue;

                if (debug) {
                    cout << "Windows on " << *(RPGBuilder::getLiteral(winItr->first)) << ":";
                    list<pair<double, double> >::const_iterator cwItr = currList.begin();
                    const list<pair<double, double> >::const_iterator cwEnd = currList.end();

                    for (; cwItr != cwEnd; ++cwItr) {
                        cout << " [" << cwItr->first << ",";
                        if (cwItr->second == DBL_MAX) {
                            cout << "end]";
                        } else {
                            cout << cwItr->second << "]";
                        }
                    }
                    cout << "\n";
                }
            }
        }
    }
    /*
    for (int i = 0; i < actCount; ++i) {
        if (!RPGBuilder::rogueActions[i]) {
            double & startMax = actionTSBounds[i][0].second;
            // if (startMax < DBL_MAX) cout << "Start of " << *(RPGBuilder::getInstantiatedOp(i)) << " is applicable no later than " << startMax << "\n";
        }
    }*/

};

void TemporalAnalysis::findGoalDeadlines(list<Literal*> & goals,
                                         list<double> & dest)
{
    
    list<Literal*>::iterator gItr = goals.begin();
    const list<Literal*>::iterator gEnd = goals.end();

    list<double>::iterator dItr = dest.begin();
    
    for (int gid = 0; gItr != gEnd; ++gItr, ++dItr, ++gid) {

        double goalDeadline = 0.0;

        if (initialState.find(*gItr) == initialState.end()) {
            list<pair<int, Planner::time_spec> > & eta = RPGBuilder::getEffectsToActions((*gItr)->getStateID());

            list<pair<int, Planner::time_spec> >::iterator etaItr = eta.begin();
            const list<pair<int, Planner::time_spec> >::iterator etaEnd = eta.end();

            for (; etaItr != etaEnd; ++etaItr) {

                double thisDeadline = DBL_MAX;
                
                if (etaItr->second == VAL::E_AT) {
                    thisDeadline = RPGBuilder::getNormalTILVec()[etaItr->first]->duration;
                } else if (etaItr->second == VAL::E_AT_START) {
                    thisDeadline = actionTSBounds[etaItr->first][0].second;
                } else {
                    thisDeadline = actionTSBounds[etaItr->first][1].second;
                }
                
                
                if (thisDeadline > goalDeadline) {
                    goalDeadline = thisDeadline;
                    if (goalDeadline == DBL_MAX) break;
                    goalDeadline += EPSILON;
                }
            }
        } else {
            goalDeadline = DBL_MAX;
        }
        if (goalDeadline != DBL_MAX) {
//          cout << "Deadline on goal " << *(*gItr) << ": " << goalDeadline << "\n";
        } else {
//          cout << "No deadline on goal " << *(*gItr) << "\n";
        }
        if (goalDeadline < *dItr) {
            *dItr = goalDeadline;
        }
        
    }
    
    
};

void TemporalAnalysis::findGoalSoftDeadlines(std::map< int, std::list< int > >& factRelevantToWithinPreferences,
                                             std::map< int, std::list< int > >& negativeFactRelevantToWithinPreferences)
{

    static const vector<RPGBuilder::Constraint> & preferences = RPGBuilder::getPreferences();
    const int prefCount = preferences.size();
    
    for (int pID = 0; pID < prefCount; ++pID) {
        if (preferences[pID].cons != VAL::E_WITHIN) {
            continue;                        
        }
        
        set<int> requiredPositive;
        set<int> requiredNegative;
        
        PreferenceHandler::collectAllFactsInNNF(pID, false, requiredPositive, requiredNegative);
        
        {
            set<int>::const_iterator fItr = requiredPositive.begin();
            const set<int>::const_iterator fEnd = requiredPositive.end();
            
            for (; fItr != fEnd; ++fItr) {
                factRelevantToWithinPreferences[*fItr].push_back(pID);
                {
                    const list<pair<int, Planner::time_spec> > & adders = RPGBuilder::getEffectsToActions()[*fItr];

                    if (adders.size() == 1) {
                        if (adders.front().second != Planner::E_AT) {
                            const list<Literal*> & pres = RPGBuilder::getProcessedStartPropositionalPreconditions()[adders.front().first];

                            list<Literal*>::const_iterator pItr = pres.begin();
                            const list<Literal*>::const_iterator pEnd = pres.end();

                            for (; pItr != pEnd; ++pItr) {
                                cout << "Only one action adds " << *(RPGBuilder::getLiteral(*fItr)) << " so its precondition " << *(*pItr) << " is relevant to within preferences\n";
                                factRelevantToWithinPreferences[(*pItr)->getStateID()].push_back(*fItr);
                            }
                        }
                    }
                }
            }
        }

        
        {
            set<int>::const_iterator fItr = requiredNegative.begin();
            const set<int>::const_iterator fEnd = requiredNegative.end();
            
            for (; fItr != fEnd; ++fItr) {
                negativeFactRelevantToWithinPreferences[*fItr].push_back(pID);
            }
        }
        
        
    }
    
}


// void TemporalAnalysis::findGoalSoftDeadlines(vector<map<EpsilonResolutionTimestamp, int > > & softDeadlines,
//                                              vector<bool> *& factHasBeenSeenForWithinSoftDeadline)
// {
//     
//     if (RPGBuilder::getPreferences().empty()) {
//         return;
//     }
//     
//     LiteralSet tinitialState;
//     vector<double> tinitialFluents;
//     
//     RPGBuilder::getNonStaticInitialState(tinitialState, tinitialFluents);
//         
//     const map<int, int> & factToGoalID = RPGBuilder::getLiteralsToGoalIndex();
//     
//     static const vector<RPGBuilder::Constraint> & preferences = RPGBuilder::getPreferences();
//     const map<int,Literal*> & localPreferences = RPGBuilder::getPreferencesThatAreSoftDeadlines();
//         
//     const int prefCount = preferences.size();
//     
//     bool anySoftDeadlines = false;
//     
//     {
//         map<int,Literal*>::const_iterator wpItr = localPreferences.begin();
//         const map<int,Literal*>::const_iterator wpEnd = localPreferences.end();
//         
//         for (; wpItr != wpEnd; ++wpItr) {
//             
//             const map<int,int>::const_iterator gidItr = factToGoalID.find(wpItr->second->getStateID());
//             
//             if (gidItr == factToGoalID.end()) continue;
//             
//             if (tinitialState.find(RPGBuilder::getLiteral(gidItr->first)) != tinitialState.end()) continue;
//             
//             EpsilonResolutionTimestamp ts(preferences[wpItr->first].deadline, true);
//             
//             if (!softDeadlines[gidItr->second].insert(make_pair(ts,wpItr->first)).second) {
//                 std::cerr << "Fatal error when parsing input preference: two within preferences are defined to act on the same fact, at the same time.\nMerge them into one and run the planner again.\n";
//                 exit(1);
//             }
//             
//            
//             anySoftDeadlines = true;
//         }
//     }
//             
// 
//     if (!anySoftDeadlines) {
//         yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts = false;
//         factHasBeenSeenForWithinSoftDeadline = 0;
//         return;
//     }
//             
//     const list<Literal*> & goals = RPGBuilder::getLiteralGoals();        
//     
//     yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts = true;
//     
//     const int gSize = softDeadlines.size();
//     
//     for (int gID = 0; gID < gSize; ++gID) {
//         
//         if (softDeadlines[gID].empty()) continue;
//         
//         double prevCost = 0.0;
//         
//         map<EpsilonResolutionTimestamp,int>::const_iterator sdItr = softDeadlines[gID].begin();
//         const map<EpsilonResolutionTimestamp,int>::const_iterator sdEnd = softDeadlines[gID].end();
//         
//         for (; sdItr != sdEnd; ++sdItr) {
//             const double localCost = preferences[sdItr->second].cost;
//             
//             if (localCost == 0.0) {
//                 continue;
//             }
//             
//             const double thisCost = prevCost + localCost;
//             
//             if (RPGBuilder::getMetric()->minimise) {
//                 if (prevCost > thisCost) {
//                     {
//                         cout << "Soft-deadlines on goals do not have monotonically worsening cost due to soft-deadline at " << sdItr->first << " on ";
//                         list<Literal*>::const_iterator gItr = goals.begin();
//                         for (int i = 0; i < gID; ++i, ++gItr) ;
//                         cout << *(*gItr) << endl;
//                     }
//                     yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts = false;
//                     return;
//                 }
//             } else {
//                 if (prevCost < thisCost) {
//                     {
//                         cout << "Soft-deadlines on goals do not have monotonically worsening cost due to soft-deadline at " << sdItr->first << " on ";
//                         list<Literal*>::const_iterator gItr = goals.begin();
//                         for (int i = 0; i < gID; ++i, ++gItr) ;
//                         cout << *(*gItr) << endl;
//                     }
//                     yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts = false;
//                     return;
//                 }
//             }            
//             
//             prevCost = thisCost;
//         }
//         
//     }   
//     
//     factHasBeenSeenForWithinSoftDeadline = new vector<bool>(gSize,false);
//         
//     {
//         list<Literal*>::const_iterator gItr = goals.begin();
//         const list<Literal*>::const_iterator gEnd = goals.end();
//         
//         for (int gID = 0; gItr != gEnd; ++gItr, ++gID) {
//             (*factHasBeenSeenForWithinSoftDeadline)[gID]
//                 = (tinitialState.find(*gItr) != tinitialState.end()
//                     || softDeadlines[gID].empty() );
//         }
//     }
//         
//     PreferenceStatusArray::initialise(prefCount);   
//     
//     {
//         map<int,Literal*>::const_iterator wpItr = localPreferences.begin();
//         const map<int,Literal*>::const_iterator wpEnd = localPreferences.end();
//         
//         for (; wpItr != wpEnd; ++wpItr) {
//             
//             const map<int,int>::const_iterator gidItr = factToGoalID.find(wpItr->second->getStateID());
//             
//             if (gidItr == factToGoalID.end()) continue;
//             
//             if (tinitialState.find(wpItr->second) != tinitialState.end()) {
//                 
//                 (*(PreferenceStatusArray::getGlobalInitialArray()))[wpItr->first] = AutomatonPosition::eternallysatisfied;
//                 
//             }
//         }
//     }
// }


bool TemporalAnalysis::actionIsNeverApplicable(const int & a)
{
    bool printDiagnostic = false;
    if ((actionTSBounds[a][0].first > actionTSBounds[a][0].second)) {
        if (printDiagnostic) {
            cout << "Start LB > Start UB" << endl;
        }
        return true;
    }
    if ((actionTSBounds[a][1].first > actionTSBounds[a][1].second)) {
        if (printDiagnostic) {
            cout << "End LB > End UB" << endl;
        }
        return true;
    }
    if ((actionTSBounds[a][0].first + globalActionDurationBounds[a].first) > actionTSBounds[a][1].second) {
        if (printDiagnostic) {
            cout << "Start UB + min duration > end UB" << endl;
        }
        return true;
    }
    if ((actionTSBounds[a][1].first - globalActionDurationBounds[a].second) > actionTSBounds[a][0].second) {
        if (printDiagnostic) {
            cout << "End LB - max duration > start UB" << endl;
        }
        return true;
    }

    return false;
}

void TemporalAnalysis::findActionTimestampLowerBounds()
{

    RPGHeuristic* const currRPG = RPGBuilder::getHeuristic();

    LiteralSet initialState;
    vector<double> initialFluents;

    RPGBuilder::getNonStaticInitialState(initialState, initialFluents);


    MinimalState refState;
    refState.insertFacts(initialState.begin(), initialState.end(), StepAndBeforeOrAfter());

    refState.secondMin = initialFluents;
    refState.secondMax = initialFluents;

    {
        const int pneCount = RPGBuilder::getPNECount();
        
        for (int pne = 0; pne < pneCount; ++pne) {
            if (!RPGBuilder::getWhetherDefinedValueInInitialState()[pne]) {
                refState.secondMin[pne] = DBL_MAX;
                refState.secondMax[pne] = -DBL_MAX;
            }
        }
    }
//     if (RPGBuilder::getFactHasBeenSeenForWithinSoftDeadline()) {
//         refState.statusOfTemporalPreferences = PreferenceStatusArray::getInitialArray();
//     }
    
//  refState.derivePredicates();

    list<FFEvent> dummyPlan;
    pullInAbstractTILs(refState, dummyPlan);
    
    assert(factIsAbstract.size() == RPGBuilder::getNegativeEffectsToActions().size());
    
    currRPG->doFullExpansion(refState, dummyPlan);

    static const bool workingGlobally = true;
    
    const int actCount = RPGBuilder::actionsToStartPreconditions.size();

    for (int a = 0; a < actCount; ++a) {

        if (!RPGBuilder::rogueActions[a]) {

            bool isRogue = false;
            
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (workingGlobally) {                
                if (RPGBuilder::getRPGDEs(a).empty()) {
                    Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second);
                } else {
                    Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second, actionTSBounds[a][1].first, actionTSBounds[a][1].second);
                }
            }
            #endif
            
            double earliestStart = RPGHeuristic::getEarliestForStarts()[a].toDouble();
            double earliestEnd = RPGHeuristic::getEarliestForEnds()[a].toDouble();

            if (earliestStart != DBL_MAX && earliestEnd != DBL_MAX) {
                //cout << "Initial RPG bounds " << *(getInstantiatedOp(a)) << " no earlier than " << earliestStart << " ; " << earliestEnd << "\n";
                const double maxActDur = globalActionDurationBounds[a].second;
                if (earliestStart < (earliestEnd - maxActDur) - 0.0005) {
                    earliestStart = earliestEnd - maxActDur;
//                  cout << "Maximum act duration = " << maxActDur << ", so pulling start to " << earliestStart << "\n";
                }

                TemporalAnalysis::suggestNewStartLowerBound(a, earliestStart);
                TemporalAnalysis::suggestNewEndLowerBound(a, earliestEnd);

                isRogue = TemporalAnalysis::actionIsNeverApplicable(a);

                if (isRogue) {
                    cout << "Pruning " << *(RPGBuilder::getInstantiatedOp(a)) << " - temporal contradiction: start min/max = " << actionTSBounds[a][0].first << "/" << actionTSBounds[a][0].second;
                    cout << "; end min/max = " << actionTSBounds[a][1].first << "/" << actionTSBounds[a][1].second;
                    cout << "; duration min/max = " << globalActionDurationBounds[a].first << "/" << globalActionDurationBounds[a].second << endl;
                    #ifdef ENABLE_DEBUGGING_HOOKS
                        Globals::eliminatedAction(a, "The earliest point the start could be applied was too close to the latest point at which the end could be applied");
                    #endif
                }
            } else {
                cout << "Pruning " << *(RPGBuilder::getInstantiatedOp(a)) << " - never appeared in initial RPG\n";
                #ifdef ENABLE_DEBUGGING_HOOKS
                    Globals::eliminatedAction(a, "The action never appeared in the initial RPG");
                #endif
                isRogue = true;
            }

            if (isRogue) {

                RPGBuilder::pruneIrrelevant(a);

            }
            
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (workingGlobally) {                                                        
                if (RPGBuilder::getRPGDEs(a).empty()) {
                    Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second);
                } else {
                    Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second, actionTSBounds[a][1].first, actionTSBounds[a][1].second);
                }
            }
            #endif

        }

    }
    
    recalculateDurationsFromBounds();

}



/** Determine if the list of end preconditions is a subset of the action's invariants.
 *
 *  This is a helper function for compression-safe action detection, and is used
 *  to check whether an action's end precondition list is a subset of its invariants,
 *  one of the criteria used.
 *
 *  @param endPre  The end preconditions of an action
 *  @param inv     The invariants of an action
 *  @retval <code>true</code>  The end preconditions are a subset of the invariants
 *  @retval <code>false</code>  The end preconditions are not a subset of the invariants
 */
bool firstIsSubsumedBySecond(const list<Literal*> & endPre, const list<Literal*> & inv)
{
    list<Literal*>::const_iterator pItr = endPre.begin();
    const list<Literal*>::const_iterator pEnd = endPre.end();
    
    for (; pItr != pEnd; ++pItr) {
        if (TemporalAnalysis::getFactIsAbstract()[(*pItr)->getStateID()]) {
            // ignore abstracted TIL-controlled facts
            continue;
        }
        list<Literal*>::const_iterator iItr = inv.begin();
        const list<Literal*>::const_iterator iEnd = inv.end();
        
        for (; iItr != iEnd; ++iItr) {
            if (*iItr == *pItr) break;
        }
        if (iItr == iEnd) return false;
    }
        
    return true;
}


/** @brief Make sure no actions depend on the facts in the given effects list.
 *
 *  This is a helper function for compression-safe action detection, and is used
 *  to check whether an action's end effects are only ever beneficial.  In the
 *  case of end delete effects, they must not be used as a positive precondition
 *  of any action, or as a goal.  In the case of end add effects, they must not
 *  be used as a negative precondition of an action, or as a negative goal.
 *
 *  @param effs     The end effects of an action
 *  @param affects  The lookup table from literal IDs to which snap-actions require
 *                  the fact as a precondition.  (If <code>effs</code> is the end
 *                  delete effects of an action, this should be a reference to 
 *                  <code>RPGBuilder::preconditionsToActions</code>.)
 *  @param goals    A set of goals, none of which can be made inviolate by <code>effs</code>.
 *  @param canIgnore  Any elements of <code>effects</code> that are in this set can be ignored.
 *  
 *  @retval <code>true</code>   There is no overlap between the effects list and the preconditions of actions or goals
 *  @retval <code>false</code>  The effects list can violate some preconditions and/or goals
 */
bool noOverlap(const list<Literal*> & effs, const vector<list<pair<int, Planner::time_spec> > > & affects,
               const vector<list<LiteralCellDependency<pair<int,bool> > > > * const affectsPrefs,
               const LiteralSet & goals, const LiteralSet & canIgnore)
{
    list<Literal*>::const_iterator effItr = effs.begin();
    const list<Literal*>::const_iterator effEnd = effs.end();
    
    for (; effItr != effEnd; ++effItr) {
        if (TemporalAnalysis::getFactIsAbstract()[(*effItr)->getStateID()]) {
            continue;
        }
        if (canIgnore.find(*effItr) != canIgnore.end()) {
            continue;
        }
        
        if (!affects[(*effItr)->getStateID()].empty()) {
            if (Globals::globalVerbosity & 16384) {
                cout << "Fact as precondition " << *(*effItr) << ": ";
            }
            return false;
        }
        if (goals.find(*effItr) != goals.end()) {
            if (Globals::globalVerbosity & 16384) {
                cout << "Fact as goal " << *(*effItr) << ": ";
            }
            return false;
        }
        if (affectsPrefs && !(*affectsPrefs)[(*effItr)->getStateID()].empty()) {
            if (Globals::globalVerbosity & 16384) {
                cout << "Fact affecting preferences " << *(*effItr) << ": ";
            }
            return false;
        }
    }
    
    return true;
}

bool guardInPlace(const int & v, const set<int> & definiteFacts) {
    const map<int,set<int> >::const_iterator guardItr = NumericAnalysis::getFactsThatDefineAndFixVariables().find(v);
    if (guardItr != NumericAnalysis::getFactsThatDefineAndFixVariables().end()) {
        set<int> isect;
        std::set_intersection(guardItr->second.begin(), guardItr->second.end(), definiteFacts.begin(), definiteFacts.end(), std::insert_iterator<set<int> >(isect, isect.begin()));
        
        if (!isect.empty()) {
            return true;
        }
    }
    return false;
}

bool endNumericPreconditionsOnlyReferToTime(const list<int> & pres, const set<int> & definiteFacts)
{
    static const int pneCount = RPGBuilder::getPNECount();
    
    list<int>::const_iterator preItr = pres.begin();
    const list<int>::const_iterator preEnd = pres.end();
    
    for (; preItr != preEnd; ++preItr) {
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*preItr];
        
        if (currPre.LHSVariable < 0) {
            assert(currPre.LHSVariable == -3 || currPre.LHSVariable == -19);
            // refers to duration - that's fine, as essentially it's determined at the start of the action
        } else if (currPre.LHSVariable < pneCount) {
            if (NumericAnalysis::getVariablesThatAreTickers().find(currPre.LHSVariable) != NumericAnalysis::getVariablesThatAreTickers().end()) {
                continue;
            }
            if (guardInPlace(currPre.LHSVariable, definiteFacts)) {
                continue;
            }
            return false;
        } else if (currPre.LHSVariable < 2 * pneCount) {
            if (NumericAnalysis::getVariablesThatAreTickers().find(currPre.LHSVariable - pneCount) != NumericAnalysis::getVariablesThatAreTickers().end()) {
                continue;
            }
            if (guardInPlace(currPre.LHSVariable - pneCount, definiteFacts)) {
                continue;
            }
            return false;
        } else {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
            
            for (int s = 0; s < currAV.size; ++s) {
                if (currAV.fluents[s] < 0) {
                    assert(currAV.fluents[s] == -3 || currAV.fluents[s] == -19);
                    continue;
                } else if (currAV.fluents[s] < pneCount) {
                    if (NumericAnalysis::getVariablesThatAreTickers().find(currAV.fluents[s]) != NumericAnalysis::getVariablesThatAreTickers().end()) {
                        continue;
                    }
                    if (guardInPlace(currAV.fluents[s], definiteFacts)) {
                        continue;
                    }
                    return false;
                } else {
                    if (NumericAnalysis::getVariablesThatAreTickers().find(currAV.fluents[s] - pneCount) != NumericAnalysis::getVariablesThatAreTickers().end()) {
                        continue;
                    }
                    if (guardInPlace(currAV.fluents[s] - pneCount, definiteFacts)) {
                        continue;
                    }
                    return false;
                }
            }
        }
    }
    
    return true;
}

void TemporalAnalysis::recogniseHoldThroughoutDeleteAtEndIdiom(LiteralSet & factsIdentified)
{

    const vector<list<pair<int, Planner::time_spec> > > & preconditionsToActions = RPGBuilder::getRawPresToActions();
    const vector<list<pair<int, Planner::time_spec> > > & negativeEffectsToActions = RPGBuilder::negativeEffectsToActions;
    
    const int litCount = preconditionsToActions.size();

    // First, we exclude facts that could be added by a TIL during the action and then deleted again by its end.
    // In this case, moving the end delete to the start and scrubbing the invariant is not equivalent.
    
    set<int> exclude;
        
    {
        const vector<RPGBuilder::FakeTILAction*> & TILs = RPGBuilder::getAllTimedInitialLiterals();
        
        const int tilCount = TILs.size();
        
        for (int t = 0; t < tilCount; ++t) {
            list<Literal*>::const_iterator effItr = TILs[t]->addEffects.begin();
            const list<Literal*>::const_iterator effEnd = TILs[t]->addEffects.end();
            
            for (; effItr != effEnd; ++effItr) {
                exclude.insert((*effItr)->getStateID());
            }
        }
    }
    
    const set<int>::const_iterator exEnd = exclude.end();
    set<int>::const_iterator exItr = exclude.begin();
    
    for (int lit = 0; lit < litCount; ++lit) {
        
        if (exItr != exEnd) {
            if (*exItr == lit) { // skip any facts manipulated by TILs
                ++exItr;
                if (Globals::globalVerbosity & 16384) {
                    cout << *RPGBuilder::getLiteral(lit) << ", if end-deleted, will break the action being compression safe, due to potential TIL interactions\n";
                }
                
                continue;
            }
        }
        
        vector<set<int> > startEndDelete(3);
        
        list<pair<int, Planner::time_spec> >::const_iterator eItr = negativeEffectsToActions[lit].begin();
        const list<pair<int, Planner::time_spec> >::const_iterator eEnd = negativeEffectsToActions[lit].end();
        
        for (; eItr != eEnd; ++eItr) {
            switch (eItr->second) {
                case Planner::E_AT_START:
                    startEndDelete[0].insert(eItr->first);
                    break;
                case Planner::E_AT_END:
                    startEndDelete[1].insert(eItr->first);
                    break;
                case Planner::E_AT: {
                    startEndDelete[2].insert(eItr->first);
                    break;
                }
                default:
                {
                    std::cerr << "Fatal internal error: effect should be at start or at end.\n";
                    exit(1);
                }
            }
        }
        
        if (!startEndDelete[2].empty()) {
            continue;
        }
        
        if (startEndDelete[1].empty()) {
            //never end deleted, so no concerns
            continue;
        }
        
        vector<set<int> > actionsWithFactAsAStartInvEndCondition(3);
        
        list<pair<int, Planner::time_spec> >::const_iterator pItr = preconditionsToActions[lit].begin();
        const list<pair<int, Planner::time_spec> >::const_iterator pEnd = preconditionsToActions[lit].end();
        
        for (; pItr != pEnd; ++pItr) {
            switch (pItr->second) {
                case Planner::E_AT_START:
                    actionsWithFactAsAStartInvEndCondition[0].insert(pItr->first);
                    break;
                case Planner::E_OVER_ALL:
                    actionsWithFactAsAStartInvEndCondition[1].insert(pItr->first);
                    break;
                case Planner::E_AT_END:
                    actionsWithFactAsAStartInvEndCondition[2].insert(pItr->first);
                    break;
                default:
                {
                    std::cerr << "Fatal internal error: precondition recorded for a time specifier other than at start, over all or at end.\n";
                    exit(1);
                }
            }
        }


        set<int> onlyAsEnd;
        
        std::set_difference(actionsWithFactAsAStartInvEndCondition[2].begin(), actionsWithFactAsAStartInvEndCondition[2].end(),
                            actionsWithFactAsAStartInvEndCondition[1].begin(), actionsWithFactAsAStartInvEndCondition[1].end(),
                            insert_iterator<set<int> >(onlyAsEnd, onlyAsEnd.begin()));
                            
                            
        if (!onlyAsEnd.empty()) {
            // would not be compression safe, as there's an end-only precondition
            if (Globals::globalVerbosity & 16384) {
                cout << *RPGBuilder::getLiteral(lit) << ", if end-deleted, will break the action being compression safe, as it can be required only at the end of some action\n";
            }                                        
            continue;
        }
        // Actions which only have the fact as an 'at start' precondition - these must also delete at start
        
        set<int> onlyAsAStart;
        
        std::set_difference(actionsWithFactAsAStartInvEndCondition[0].begin(), actionsWithFactAsAStartInvEndCondition[0].end(),
                            actionsWithFactAsAStartInvEndCondition[1].begin(), actionsWithFactAsAStartInvEndCondition[1].end(),
                            insert_iterator<set<int> >(onlyAsAStart, onlyAsAStart.begin()));
                                
        
        
        set<int> onlyAsStartButNotThenDeleted;
        
        std::set_difference(onlyAsAStart.begin(), onlyAsAStart.end(),
                            startEndDelete[0].begin(), startEndDelete[0].end(),
                            insert_iterator<set<int> >(onlyAsStartButNotThenDeleted, onlyAsStartButNotThenDeleted.begin()));
        
        if (!onlyAsStartButNotThenDeleted.empty()) {
            // breaks the idiom: cannot move the end delete to the start of an action if something else could
            // use it only momentarily during its execution.
            if (Globals::globalVerbosity & 16384) {
                cout << *RPGBuilder::getLiteral(lit) << ", if end-deleted, will break the action being compression safe, as it can needed at the start of an action, but isn't then deleted\n";
            }                                        
                                    
            continue;
        }
        
        set<int> overAllButNotDeletedAtEnd;
        
        std::set_difference(actionsWithFactAsAStartInvEndCondition[1].begin(), actionsWithFactAsAStartInvEndCondition[1].end(),
                            startEndDelete[1].begin(), startEndDelete[1].end(),
                            insert_iterator<set<int> >(overAllButNotDeletedAtEnd, overAllButNotDeletedAtEnd.begin()));
        
        if (!overAllButNotDeletedAtEnd.empty()) {
            // breaks the idiom: could potentially use and not delete the fact after the start but before the end of an action which 
            // will delete the fact at its end
            if (Globals::globalVerbosity & 16384) {
                cout << *RPGBuilder::getLiteral(lit) << ", if end-deleted, will break the action being compression safe, as some action " << *RPGBuilder::getInstantiatedOp(*(overAllButNotDeletedAtEnd.begin())) << " needs it as an invariant, but doesn't then delete it\n";
            }                                        
            
            continue;
        }
        
        // otherwise, we've made it - all actions with a precondition on the fact either:
        //  i) delete it straight away
        // ii) need it throughout, and then delete it at the end
        
        factsIdentified.insert(RPGBuilder::getLiteral(lit));
        
        if (Globals::globalVerbosity & 16384) {
            cout << *RPGBuilder::getLiteral(lit) << " is end-deleted, but recognised as still being compression safe\n";
        }
    }
    
}

#ifdef POPF3ANALYSIS
bool TemporalAnalysis::endNumericEffectsAreCompressionSafe(const list<int> & effects,
                                                           vector<bool> & allInteractionWithVarIsCompressionSafe)
{
    
    
    list<int>::const_iterator effItr = effects.begin();
    const list<int>::const_iterator effEnd = effects.end();
    
    for (; effItr != effEnd; ++effItr) {
        
        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
        
        // first, all current interaction with the variable has to be compression safe
        if (!allInteractionWithVarIsCompressionSafe[currEff.fluentIndex]) {
            if (Globals::globalVerbosity & 16384) {
                cout << "Interacts with non-compression safe variable " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
            }
            return false;
        }
        
        // third, the effect has to be only ever a good idea, with respect to the dominance constraints on the variable
        switch (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex]) {
            case NumericAnalysis::E_NODOMINANCE: {
                if (Globals::globalVerbosity & 16384) {
                    cout << "Interacts with variable with no dominance constraints, " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                }                
                return false;
            }
            case NumericAnalysis::E_METRICTRACKING: {
                if (Globals::globalVerbosity & 16384) {
                    cout << "Interacts with metric-tracking variable, " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                }
                break;
            }
            case NumericAnalysis::E_IRRELEVANT: {
                if (Globals::globalVerbosity & 16384) {
                    cout << "Interacts with irrelevant variable, " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                }
                break;
            }
            case NumericAnalysis::E_SMALLERISBETTER: {
                if (currEff.constant > 0.0) { // if smaller is better, and this is an increase, it's not compression safe
                    if (Globals::globalVerbosity & 16384) {
                        cout << "Has undesirable increase effect on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                    }
                    return false;
                }
                            

                break;
            }
            case NumericAnalysis::E_BIGGERISBETTER: {
                if (currEff.constant < 0.0) { // if bigger is better, and this is a decrease, it's not compression safe
                    if (Globals::globalVerbosity & 16384) {
                        cout << "Has undesirable decrease effect on " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << endl;
                    }
                    return false;                                        
                }                
                break;
            }
        }
        
    }
    // if nothing tripped the return falses above, then everything must be compression safe
    return true;

}
void TemporalAnalysis::markCompressionSafetyConditions(const int & actID, const list<int> & effects,
                                                       vector<set<int> > & actionsDependingOnVarBeingCompressionSafe)
{
    list<int>::const_iterator effItr = effects.begin();
    const list<int>::const_iterator effEnd = effects.end();
    
    for (; effItr != effEnd; ++effItr) {
        
        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
        
        actionsDependingOnVarBeingCompressionSafe[currEff.fluentIndex].insert(actID);
    }
    
}

void TemporalAnalysis::markAffectedVariablesAsNotCompressionSafe(const list<int> & effects,
                                                                 vector<bool> & allInteractionWithVarIsCompressionSafe,
                                                                 set<int> & newlyUnsafe)
{
    
    list<int>::const_iterator effItr = effects.begin();
    const list<int>::const_iterator effEnd = effects.end();
    
    for (; effItr != effEnd; ++effItr) {
        
        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
        if (allInteractionWithVarIsCompressionSafe[currEff.fluentIndex]) {
            allInteractionWithVarIsCompressionSafe[currEff.fluentIndex] = false;
            newlyUnsafe.insert(currEff.fluentIndex);
        }
    }
    
}
                                                   
#endif

vector<bool> TemporalAnalysis::startEndSkip;

struct TimeDependentLimit {
    double RHSconstant;
    double durationWeight;
    double timeWeight;
    double maxValueOfRest;

    TimeDependentLimit()
        : RHSconstant(0.0), durationWeight(0.0), timeWeight(0.0), maxValueOfRest(DBL_MAX) {
    }
    
    TimeDependentLimit(const double & rhs, const double & durWeight, const double & tWeight, const double & lhsRest)
        : RHSconstant(rhs), durationWeight(durWeight), timeWeight(tWeight), maxValueOfRest(lhsRest) {
    }
    
    double getLower(const double & minDur, const double & maxDur) const {
        if (timeWeight <= 0.0) {
            return 0.0;
        }
        
        if (durationWeight == 0.0) {
            return ((RHSconstant - maxValueOfRest) / timeWeight);
        } else if (durationWeight > 0.0) {
            return (((RHSconstant - maxValueOfRest) - durationWeight * maxDur) / timeWeight);
        } else {
            return (((RHSconstant - maxValueOfRest) - durationWeight * minDur) / timeWeight);
        }
    }
    
    double getUpper(const double & minDur, const double & maxDur) const {
        if (timeWeight >= 0.0) {
            return DBL_MAX;
        }
        
        if (durationWeight == 0.0) {
            return ((-RHSconstant + maxValueOfRest) / - timeWeight);
        } else if (durationWeight > 0.0) {
            return ((-RHSconstant + maxValueOfRest + durationWeight * maxDur) / -timeWeight);
        } else {
            return ((-RHSconstant + maxValueOfRest + durationWeight * minDur) / -timeWeight);
        }
    }
};

void TemporalAnalysis::findCompressionSafeActions()
{

    const int actCount = RPGBuilder::instantiatedOps.size();
    const int pneCount = RPGBuilder::pnes.size();

    startEndSkip.resize(actCount, false);

    if (!RPGBuilder::doSkipAnalysis) return;

    int compressionSafeActionCount = 0;
    int nonRogueCount = 0;
    
    LiteralSet goalsAsASet;
    LiteralSet negativeGoalsAsASet;
    
    goalsAsASet.insert(RPGBuilder::literalGoals.begin(), RPGBuilder::literalGoals.end());

    LiteralSet okayToDeleteAtEnd;
    LiteralSet okayToAddAtEnd;
    
    recogniseHoldThroughoutDeleteAtEndIdiom(okayToDeleteAtEnd);
    
    #ifdef POPF3ANALYSIS
    vector<bool> allInteractionWithVarIsCompressionSafe(pneCount);
    
    for (int v = 0; v < pneCount; ++v) {
        allInteractionWithVarIsCompressionSafe[v] = (   NumericAnalysis::getDominanceConstraints()[v] == NumericAnalysis::E_IRRELEVANT
                                                    ||  (    (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[v] == NumericAnalysis::E_ORDER_INDEPENDENT)
                                                          && NumericAnalysis::getWhichVariablesAreOnlyInStartPreconditions()[v])
                                                    );
    }
    
    vector<set<int> > actionsDependingOnVarBeingCompressionSafe(pneCount);
    
    #endif
    
    for (int i = 0; i < actCount; ++i) {

        if (!RPGBuilder::rogueActions[i]) {
            if (RPGBuilder::getRPGDEs(i).empty()) continue;

            ++nonRogueCount;

            set<int> factsWeDefinitelyHaveAfterTheStart;
            
            for (int pass = 0; pass < 2; ++pass) {
                const list<Literal*> * currList;
                switch (pass) {
                    case 0: {
                        currList = &(RPGBuilder::getStartPropositionalPreconditions()[i]);
                        break;
                    }
                    case 1: {
                        currList = &(RPGBuilder::getInvariantPropositionalPreconditions()[i]);
                        break;
                    }    
                }
                
                list<Literal*>::const_iterator fItr = currList->begin();
                const list<Literal*>::const_iterator fEnd = currList->end();
                
                for (; fItr != fEnd; ++fItr) {
                    if (RPGBuilder::getNegativeEffectsToActions()[(*fItr)->getStateID()].empty()) {
                        factsWeDefinitelyHaveAfterTheStart.insert((*fItr)->getStateID());
                    }
                }
            }
            
            if (Globals::globalVerbosity & 16384) {
                #ifdef POPF3ANALYSIS
                #ifdef TOTALORDERSTATES
                startEndSkip[i] = RPGBuilder::actionsToRPGNumericEndEffects[i].empty();
                #else
                startEndSkip[i] = endNumericEffectsAreCompressionSafe(RPGBuilder::actionsToRPGNumericEndEffects[i],
                                                                      allInteractionWithVarIsCompressionSafe);
                #endif
                #else
                startEndSkip[i] = RPGBuilder::actionsToRPGNumericEndEffects[i].empty();
                #endif
                
                if (!startEndSkip[i]) {
                    cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " cannot be compression safe - has unsafe end numeric effects\n";
                } else {
                    
                    startEndSkip[i] = RPGBuilder::actionsToRPGNumericInvariants[i].empty() && endNumericPreconditionsOnlyReferToTime(RPGBuilder::actionsToRPGNumericEndPreconditions[i], factsWeDefinitelyHaveAfterTheStart) && !RPGBuilder::linearDiscretisation[i];
                                  
                    if (!startEndSkip[i]) {
                        cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " cannot be compression safe - has non-start numerics\n";
                    } else {
                        startEndSkip[i] =      firstIsSubsumedBySecond(RPGBuilder::actionsToEndPreconditions[i], RPGBuilder::actionsToInvariants[i])
                                            && firstIsSubsumedBySecond(RPGBuilder::actionsToEndNegativePreconditions[i], RPGBuilder::actionsToNegativeInvariants[i]);
                        if (!startEndSkip[i]) {
                            cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " cannot be compression safe - end pres aren't subsumed by invariants\n";
                        } else {
                            startEndSkip[i] = noOverlap(RPGBuilder::actionsToEndNegativeEffects[i], RPGBuilder::preconditionsToActions, PreferenceHandler::getPreconditionsToPrefs(), goalsAsASet, okayToDeleteAtEnd);
                            if (!startEndSkip[i]) {
                                cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " cannot be compression safe - end delete effects intersect with needed preconditions\n";
                            } else {
                                startEndSkip[i] = noOverlap(RPGBuilder::actionsToEndEffects[i], RPGBuilder::negativePreconditionsToActions, PreferenceHandler::getNegativePreconditionsToPrefs(), negativeGoalsAsASet, okayToAddAtEnd);
                                if (!startEndSkip[i]) {
                                    cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " cannot be compression safe - end add effects intersect with needed negative preconditions\n";
                                }
                            }
                        }
                    }
                }
                
            } else {
                #ifdef POPF3ANALYSIS
                #ifdef TOTALORDERSTATES
                startEndSkip[i] = RPGBuilder::actionsToRPGNumericEndEffects[i].empty()
                #else
                startEndSkip[i] =     endNumericEffectsAreCompressionSafe(RPGBuilder::actionsToRPGNumericEndEffects[i], allInteractionWithVarIsCompressionSafe)
                #endif
                #else
                startEndSkip[i] =     RPGBuilder::actionsToRPGNumericEndEffects[i].empty()
                #endif
                                      && RPGBuilder::actionsToRPGNumericInvariants[i].empty()
                                      && endNumericPreconditionsOnlyReferToTime(RPGBuilder::actionsToRPGNumericEndPreconditions[i], factsWeDefinitelyHaveAfterTheStart) && !RPGBuilder::linearDiscretisation[i]
                                      && firstIsSubsumedBySecond(RPGBuilder::actionsToEndPreconditions[i], RPGBuilder::actionsToInvariants[i])
                                      && firstIsSubsumedBySecond(RPGBuilder::actionsToEndNegativePreconditions[i], RPGBuilder::actionsToNegativeInvariants[i])
                                      && noOverlap(RPGBuilder::actionsToEndNegativeEffects[i], RPGBuilder::preconditionsToActions, PreferenceHandler::getPreconditionsToPrefs(), goalsAsASet, okayToDeleteAtEnd)
                                      && noOverlap(RPGBuilder::actionsToEndEffects[i], RPGBuilder::negativePreconditionsToActions, PreferenceHandler::getNegativePreconditionsToPrefs(), negativeGoalsAsASet, okayToAddAtEnd);
            }


            if (startEndSkip[i]) {
                bool ddes = false;
                if (RPGBuilder::fixedDurationExpressions[i].empty() && false) {
                    // check for duration-dependent preconditions/effects

                    {
                        list<int> & currList = RPGBuilder::actionsToRPGNumericStartPreconditions[i];
                        list<int>::iterator clItr = currList.begin();
                        const list<int>::iterator clEnd = currList.end();

                        for (; clItr != clEnd; ++clItr) {

                            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::rpgNumericPreconditions[*clItr];
                            if (currPre.LHSVariable < -1) {
                                if (Globals::globalVerbosity & 16384) {
                                    cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " is not compression safe: it has a duration-dependent start condition " << currPre << "\n";
                                }
                                ddes = true;
                                break;
                            } else if (currPre.LHSVariable >= 2 * pneCount) {
                                RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                                for (int j = 0; j < currAV.size; ++j) {
                                    if (currAV.fluents[j] < -1) {
                                        if (Globals::globalVerbosity & 16384) {
                                            cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " is not compression safe: it has a duration-dependent start condition " << currPre << "\n";
                                        }
                                        
                                        ddes = true;
                                        break;
                                    }
                                }
                                if (ddes) break;
                            }
                        }

                    }

                    
                    if (!ddes) {
                        list<int> & currList = RPGBuilder::actionsToRPGNumericStartEffects[i];
                        list<int>::iterator clItr = currList.begin();
                        const list<int>::iterator clEnd = currList.end();

                        for (; clItr != clEnd; ++clItr) {

                            RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::rpgNumericEffects[*clItr];

                            for (int j = 0; j < currEff.size; ++j) {
                                if (currEff.variables[j] < -1) {
                                    if (Globals::globalVerbosity & 16384) {
                                        cout << "Action " << *(RPGBuilder::getInstantiatedOp(i)) << " is not compression safe: it has a duration-dependent start effect " << currEff << "\n";
                                    }
                                    
                                    ddes = true;
                                    break;
                                }
                            }
                            if (ddes) break;
                        }

                    }
                }

                startEndSkip[i] = !ddes;
                if (startEndSkip[i]) {
                    ++compressionSafeActionCount;
                    if (Globals::globalVerbosity & 16) {
                        cout << *(RPGBuilder::getInstantiatedOp(i)) << " is a candidate for start-end skipping\n";
                    }
                    
                    #ifdef POPF3ANALYSIS
                    markCompressionSafetyConditions(i, RPGBuilder::actionsToRPGNumericEndEffects[i], actionsDependingOnVarBeingCompressionSafe);
                    #endif
                } else {
                    
                    #ifdef POPF3ANALYSIS
                    
                    set<int> newNonCompressionSafeVariables;                    
                    markAffectedVariablesAsNotCompressionSafe(RPGBuilder::actionsToRPGNumericEndEffects[i], allInteractionWithVarIsCompressionSafe, newNonCompressionSafeVariables);
                    
                    while (!newNonCompressionSafeVariables.empty()) {
                        set<int> varsToUpdateFrom;
                        varsToUpdateFrom.swap(newNonCompressionSafeVariables);
                        
                        set<int>::const_iterator vItr = varsToUpdateFrom.begin();
                        const set<int>::const_iterator vEnd = varsToUpdateFrom.end();
                        
                        for (; vItr != vEnd; ++vItr) {
                            set<int>::const_iterator noncsActItr = actionsDependingOnVarBeingCompressionSafe[*vItr].begin();
                            const set<int>::const_iterator noncsActEnd = actionsDependingOnVarBeingCompressionSafe[*vItr].end();
                            
                            int reversed = 0;
                            for (; noncsActItr != noncsActEnd; ++noncsActItr) {
                                if (startEndSkip[*noncsActItr]) {
                                    startEndSkip[*noncsActItr] = false;
                                    ++reversed;
                                    markAffectedVariablesAsNotCompressionSafe(RPGBuilder::actionsToRPGNumericEndEffects[*noncsActItr], allInteractionWithVarIsCompressionSafe, newNonCompressionSafeVariables);
                                }
                            }
                            
                            if (Globals::globalVerbosity & 16) {
                                cout << "Shown that interaction with " << *(RPGBuilder::getPNE(*vItr)) << " is not compression safe, actions affected: " << reversed << endl;
                            }
                            actionsDependingOnVarBeingCompressionSafe[*vItr].clear();
                        }
                    };
                    
                    #endif
                    
                }
            }

            if (Globals::globalVerbosity & 16384) {
                if (startEndSkip[i]) {
                    cout << COLOUR_light_green << "Overall, action " << *(RPGBuilder::getInstantiatedOp(i)) << " is compression safe\n" << COLOUR_default;
                } else {
                    cout << COLOUR_light_red << "Overall, action " << *(RPGBuilder::getInstantiatedOp(i)) << " is not compression safe\n" << COLOUR_default;
                }
            }            
        }
        
    }

                

    
    #ifdef POPF3ANALYSIS    
    if (Globals::globalVerbosity & 16) {
        for (int v = 0; v < pneCount; ++v) {
            if (!actionsDependingOnVarBeingCompressionSafe[v].empty()) {
                cout << "Detecting compression-safety of interaction with " << *(RPGBuilder::getPNE(v)) << " has allowed " << actionsDependingOnVarBeingCompressionSafe[v].size() << " action(s) to be compression safe\n";
            }
        }
    }
    #endif
    
    if (nonRogueCount) {
        if (compressionSafeActionCount == nonRogueCount) {
            cout << "All the ground actions in this problem are compression-safe\n";
        } else if (compressionSafeActionCount == 0) {
            cout << "None of the ground temporal actions in this problem have been recognised as compression-safe\n";
        } else {
            const int percentage = (int)((double) compressionSafeActionCount / (double) nonRogueCount * 100.0);
            cout << percentage << "% of the ground temporal actions in this problem are compression-safe\n";
        }
    }
}

map<int, TILTimeline> TemporalAnalysis::timelineOnTILs;
map<int, list<int> > TemporalAnalysis::actionStartUsesAbstractedFact;
map<int, list<int> > TemporalAnalysis::actionOverAllUsesAbstractedFact;
map<int, list<int> > TemporalAnalysis::actionEndUsesAbstractedFact;
vector<bool> TemporalAnalysis::factIsAbstract;
bool TemporalAnalysis::anythingTILManipulated = false;

bool RPGBuilder::definedNonAbstractedTILs = false;


void TemporalAnalysis::buildTimelinesOnTILs()
{

    
    const vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNormalTILVec();
    
    if (tilVec.empty()) {
        factIsAbstract.resize(RPGBuilder::getNegativeEffectsToActions().size(), false);
        RPGBuilder::definedNonAbstractedTILs = true;
        return;
    }
    
    
    static const int lpDebug = 0;
    
                            
    LiteralSet initialFacts;
    vector<double> initialFluents;
    
    if (lpDebug & 1) {
        cout << "Building timelines on TILs: getting initial state\n";
    }
    
    RPGBuilder::getInitialState(initialFacts, initialFluents);
    
    const int tilCount = tilVec.size();
    
    RPGBuilder::nonAbstractedTimedInitialLiteralsVector.reserve(tilCount);
    
    
    for (int til = 0; til < tilCount; ++til) {
        int fID;
        
        for (int addDeletePass = 0; addDeletePass < 2; ++addDeletePass) {
            list<Literal*>::const_iterator addItr = (addDeletePass ? tilVec[til]->delEffects.begin() : tilVec[til]->addEffects.begin());
            const list<Literal*>::const_iterator addEnd = (addDeletePass ? tilVec[til]->delEffects.end() : tilVec[til]->addEffects.end());
            
            for (; addItr != addEnd; ++addItr) {
                
                fID = (*addItr)->getStateID();
                
                map<int, TILTimeline>::iterator fItr = timelineOnTILs.find(fID);
                    
                if (fItr == timelineOnTILs.end()) {
                    
                    fItr = timelineOnTILs.insert(make_pair(fID, TILTimeline())).first;

                    fItr->second.firstAdder = fItr->second.end();
                    fItr->second.firstDeletor = fItr->second.end();
                    fItr->second.lastDeletor = fItr->second.end();
                    
                    
                    if (initialFacts.find(*addItr) != initialFacts.end()) {
                        fItr->second.happenings.insert(make_pair(-EPSILON, TILTimeline::AddedOrDeleted(true)));
                    }
                    
                    set<pair<int, Planner::time_spec> > requiredBy;
                    requiredBy.insert(RPGBuilder::getRawPresToActions()[fID].begin(), RPGBuilder::getRawPresToActions()[fID].end());
                    
                    for (int pass = 0; pass < 2; ++pass) {
                        const list<pair<int, Planner::time_spec> > & affectedBy = (pass ? RPGBuilder::getNegativeEffectsToActions()[fID] : RPGBuilder::getEffectsToActions(fID));
                        
                        list<pair<int, Planner::time_spec> >::const_iterator actItr = affectedBy.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator actEnd = affectedBy.end();
                        
                        for (; actItr != actEnd; ++actItr) {

                            if (pass) {
                                requiredBy.erase(*actItr);
                            }
                            
                            if (actItr->second != Planner::E_AT) {
                                if (pass) {
                                    fItr->second.onlyEverDeletedByTILs = false;
                                } else {
                                    fItr->second.onlyEverAddedByTILs = false;
                                } 
                            
                            }
                            
                        }
                    }
                    
                    fItr->second.allReferencesToItDeleteIt = (requiredBy.empty() && abstractTILsWherePossible && fItr->second.onlyEverAddedByTILs);
                    
                }
                
                if (addDeletePass) {                    
                    fItr->second.happenings.insert(make_pair(tilVec[til]->duration, TILTimeline::AddedOrDeleted(false))).first->second.deleted = true;
                } else {
                    fItr->second.happenings.insert(make_pair(tilVec[til]->duration, TILTimeline::AddedOrDeleted(true))).first->second.added = true;
                }
                
            }
        }
        
    }

    factIsAbstract.resize(RPGBuilder::getNegativeEffectsToActions().size(),false);
            
            
    {
        map<int, TILTimeline>::iterator tilFactItr = timelineOnTILs.begin();
        const map<int, TILTimeline>::iterator tilFactEnd = timelineOnTILs.end();
        
        for (; tilFactItr != tilFactEnd; ++tilFactItr) {
            tilFactItr->second.closedEnded = !tilFactItr->second.rbegin()->second.added;
            
            if (!tilFactItr->second.closedEnded) {
                tilFactItr->second.allReferencesToItDeleteIt = false;
                cout << "[i] Not abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << "\n";
                continue;
            }
            
            if (!abstractTILsWherePossible) {
                factIsAbstract[tilFactItr->first] = false;
                continue;
            }
            
            if (tilFactItr->second.allReferencesToItDeleteIt) {
                cout << "(i) Abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << "\n";
                factIsAbstract[tilFactItr->first] = true;
                anythingTILManipulated = true;
                continue;
            }
            
            if (!tilFactItr->second.onlyEverAddedByTILs) {
                cout << "[ii] Not abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << "\n";
                continue;
            }
            
            if (!tilFactItr->second.onlyEverDeletedByTILs) {
                cout << "[iii] Not abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << "\n";
                continue;
            }

            
            double LB = DBL_MAX;
            double UB = -DBL_MAX;
            int windows = 0;
            
            TILTimeline::const_iterator tlItr = tilFactItr->second.begin();
            const TILTimeline::const_iterator tlEnd = tilFactItr->second.end();
            
            double lastDeletedAt = -1.0;
            double lastAddedAt = -1.0;
            
            for (; tlItr != tlEnd; ++tlItr) {
                if (tlItr->second.deleted) {
                    if (lastAddedAt != -1.0) {
                        if (UB < tlItr->first) {
                            UB = tlItr->first;
                        }
                        ++windows;
                    }
                    lastAddedAt = -1.0;
                    lastDeletedAt = tlItr->first;
                }
                if (tlItr->second.added) {
                    lastDeletedAt = -1.0;
                    lastAddedAt = tlItr->first + EPSILON;                        
                    if (LB > lastAddedAt) {
                        LB = lastAddedAt;
                    }
                }
            }

            assert(windows);
            
            tilFactItr->second.numberOfWindows = windows;
                        
            if (tilFactItr->second.numberOfWindows == 1) {
                cout << "(ii) Abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << ": is a single window [" << LB << "," << UB << "]\n";
            } else {
                cout << "(ii) Abstracting out TIL " << *(RPGBuilder::getLiteral(tilFactItr->first)) << ": appears in " << windows << " windows, bounded overall by [" << LB << "," << UB << "]\n";
            }
            
            factIsAbstract[tilFactItr->first] = true;
            anythingTILManipulated = true;
        }
    }
    
    int newTilID = 0;
    for (int til = 0; til < tilCount; ++til) {
        
        
        {
            list<Literal*> & originalAdds = tilVec[til]->addEffects;
            list<Literal*> & revisedAdds = tilVec[til]->abstractedAddEffects;
            
            
            list<Literal*>::iterator addItr = originalAdds.begin();
            const list<Literal*>::iterator addEnd = originalAdds.end();
            
            while (addItr != addEnd) {
                if (factIsAbstract[(*addItr)->getStateID()]) {
                    revisedAdds.push_back(*addItr);
                    const list<Literal*>::iterator addDel = addItr++;
                    originalAdds.erase(addDel);
                    assert(abstractTILsWherePossible);
                } else {
                    ++addItr;
                }
            }
        }
        
        {
            list<Literal*> & originalDels = tilVec[til]->delEffects;
            list<Literal*> & revisedDels = tilVec[til]->abstractedDelEffects;
            
            
            list<Literal*>::iterator delItr = originalDels.begin();
            const list<Literal*>::iterator delEnd = originalDels.end();
            
            while (delItr != delEnd) {
                if (factIsAbstract[(*delItr)->getStateID()]) {
                    revisedDels.push_back(*delItr);
                    const list<Literal*>::iterator delDel = delItr++;
                    originalDels.erase(delDel);
                    assert(abstractTILsWherePossible);
                } else {
                    ++delItr;
                }
            }
        }
        
        if (!tilVec[til]->addEffects.empty() || !tilVec[til]->delEffects.empty()) {
            RPGBuilder::nonAbstractedTimedInitialLiteralsVector.push_back(tilVec[til]);
            
            if (til != newTilID) {
            
                {
                    list<Literal*> & effList = RPGBuilder::nonAbstractedTimedInitialLiteralsVector.back()->addEffects;
                    
                    list<Literal*>::iterator elItr = effList.begin();
                    const list<Literal*>::iterator elEnd = effList.end();
                    
                    for (; elItr != elEnd; ++elItr) {
                        RPGBuilder::effectsToActions[(*elItr)->getStateID()].remove(make_pair(til, Planner::E_AT));
                        RPGBuilder::effectsToActions[(*elItr)->getStateID()].push_back(make_pair(newTilID, Planner::E_AT));                        
                    }
                }
                {
                    list<Literal*> & effList = RPGBuilder::nonAbstractedTimedInitialLiteralsVector.back()->delEffects;
                    
                    list<Literal*>::iterator elItr = effList.begin();
                    const list<Literal*>::iterator elEnd = effList.end();
                    
                    for (; elItr != elEnd; ++elItr) {
                        RPGBuilder::negativeEffectsToActions[(*elItr)->getStateID()].remove(make_pair(til, Planner::E_AT));
                        RPGBuilder::negativeEffectsToActions[(*elItr)->getStateID()].push_back(make_pair(newTilID, Planner::E_AT));                        
                    }
                }
                
            }
            
            ++newTilID;
        } else {
            assert(abstractTILsWherePossible);
        }
    }

    RPGBuilder::definedNonAbstractedTILs = true;

    assert(abstractTILsWherePossible || RPGBuilder::getNormalTILVec() == RPGBuilder::getNonAbstractedTILVec());
    
    map<int, TILTimeline>::const_iterator tilItr = timelineOnTILs.begin();
    const map<int, TILTimeline>::const_iterator tilEnd = timelineOnTILs.end();
    
    for (; tilItr != tilEnd; ++tilItr) {
        if (!factIsAbstract[tilItr->first]) {
            continue;
        }
        
        list<pair<int, Planner::time_spec> > & dependents = RPGBuilder::getRawPresToActions()[tilItr->first];

        assert(   (tilItr->second.onlyEverAddedByTILs && tilItr->second.allReferencesToItDeleteIt && tilItr->second.closedEnded)
               || (tilItr->second.numberOfWindows >= 1 && tilItr->second.closedEnded && tilItr->second.onlyEverAddedByTILs && tilItr->second.onlyEverDeletedByTILs));
        
        
        list<pair<int, Planner::time_spec> >::const_iterator depItr = dependents.begin();
        const list<pair<int, Planner::time_spec> >::const_iterator depEnd = dependents.end();
        
        for (; depItr != depEnd; ++depItr) {
            if (depItr->second == Planner::E_AT_START) {
                actionStartUsesAbstractedFact[depItr->first].push_back(tilItr->first);
            } else if (depItr->second == Planner::E_OVER_ALL) {
                actionOverAllUsesAbstractedFact[depItr->first].push_back(tilItr->first);
            } else {
                assert(depItr->second == Planner::E_AT_END);
                actionEndUsesAbstractedFact[depItr->first].push_back(tilItr->first);
            }
        }
            
        
        RPGBuilder::effectsToActions[tilItr->first].clear();
        RPGBuilder::negativeEffectsToActions[tilItr->first].clear();
    }
    
    map<int, TILTimeline>::iterator tilFactItr = timelineOnTILs.begin();
    const map<int, TILTimeline>::iterator tilFactEnd = timelineOnTILs.end();
    
    for (; tilFactItr != tilFactEnd; ++tilFactItr) {

        if (lpDebug & 1) {
            cout << "Bounds on " << *(RPGBuilder::getLiteral(tilFactItr->first)) << ":";
            cout.flush();
        }
        
        TILTimeline::const_iterator itr = tilFactItr->second.begin();
        const TILTimeline::const_iterator itrEnd = tilFactItr->second.end();
        
        for (; itr != itrEnd; ++itr) {
            
            if (itr->second.added && tilFactItr->second.firstAdder == tilFactItr->second.end()) {
                tilFactItr->second.firstAdder = itr;
                if (lpDebug & 1) {
                    cout << " first added at " << itr->first << ";";
                    cout.flush();
                }
            } else {
                if (lpDebug & 1) {
                    cout << " another add at " << itr->first << ";";
                    cout.flush();
                }
            } 
        
            
            if (itr->second.deleted) {
                if (tilFactItr->second.firstDeletor == tilFactItr->second.end()) {
                    tilFactItr->second.firstDeletor = itr;
                }
                
                tilFactItr->second.lastDeletor = itr;
            }
            
        }
        
        if (lpDebug & 1) {
            if (tilFactItr->second.lastDeletor == tilFactItr->second.end()) {
                cout << " never deleted\n";
            } else {
                cout << " deleted at " << tilFactItr->second.lastDeletor->first << endl;
            }
        }
    }
}

bool TemporalAnalysis::initialisedGlobalActionDurationBounds = false;
vector<pair<double,double> > TemporalAnalysis::globalActionDurationBounds;

void TemporalAnalysis::reboundActionsGivenTILTimelines()
{
    
    static const int lpDebug = 0;

    assert(initialisedGlobalActionDurationBounds);
    

    
    const int actCount = RPGBuilder::getStartPropositionalPreconditions().size();
    static const int pneCount = RPGBuilder::getPNECount();
    const vector<pair<double,double> > & varBounds = NumericAnalysis::getVariableBounds();
    const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
    
    list<int> pruneAction;
    
    static const bool workingGlobally = true;
    
    const vector<RPGBuilder::RPGNumericPrecondition> & numPreTable = RPGBuilder::getNumericPreTable();
    const int numPreCount = numPreTable.size();
    vector<TimeDependentLimit> boundsImpliedByCondition(numPreCount, TimeDependentLimit());
    
    {
        for (int np = 0; np < numPreCount; ++np) {
            
            const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[np];
                                
            if (lpDebug & 1) {
                cout << "  - Looking for time in " << currPre << endl;
            }
            
            
            bool foundTime = false;
            double timeWeight = 0.0;
            double durationWeight = 0.0;

            pair<double,double> valueOfRest(0.0, 0.0);
            
            int v = currPre.LHSVariable;
            if (v == -19) {
                durationWeight = -1.0;
            } else if (v == -3) {
                durationWeight = 1.0;
            } else if (v < pneCount) {
                const map<int,double>::const_iterator tItr = tickers.find(v);
                if (tItr != tickers.end()) {
                    foundTime = true;
                    timeWeight += tItr->second;
                    if (lpDebug & 1) {
                        cout << "- Found it: " << *(RPGBuilder::getPNE(v)) << "*" << timeWeight << endl;
                    }
                } else {
                    if (lpDebug & 1) {
                        cout << "- Not a ticker: " << *(RPGBuilder::getPNE(v)) << ", bounds [";
                        if (varBounds[v].first == -DBL_MAX) {
                            cout << "-inf,";
                        } else {
                            cout << varBounds[v].first << ",";
                        }
                        if (varBounds[v].second == DBL_MAX) {
                            cout << "inf]\n";
                        } else {
                            cout << varBounds[v].second << "]\n";
                        }
                    }

                    if (varBounds[v].second == DBL_MAX) {
                        valueOfRest.second = DBL_MAX;
                    } else if (valueOfRest.second != DBL_MAX) {
                        valueOfRest.second += varBounds[v].second;
                    }
                                                                    
                    if (varBounds[v].first == -DBL_MAX) {
                        valueOfRest.first = -DBL_MAX;
                    } else if (valueOfRest.first != -DBL_MAX) {
                        valueOfRest.first += varBounds[v].first;
                    }
                                            
                }
            } else if (v < 2 * pneCount) {
                v -= pneCount;
                const map<int,double>::const_iterator tItr = tickers.find(v);
                if (tItr != tickers.end()) {
                    foundTime = true;
                    timeWeight -= tItr->second;
                    if (lpDebug & 1) {
                        cout << "- Found it: " << *(RPGBuilder::getPNE(v)) << "*" << timeWeight << endl;
                    }
                    
                } else {
                    if (lpDebug & 1) {
                        cout << "- Not a ticker: " << *(RPGBuilder::getPNE(v)) << ", bounds [";
                        if (varBounds[v].first == -DBL_MAX) {
                            cout << "-inf,";
                        } else {
                            cout << varBounds[v].first << ",";
                        }
                        if (varBounds[v].second == DBL_MAX) {
                            cout << "inf]\n";
                        } else {
                            cout << varBounds[v].second << "]\n";
                        }
                    }

                    
                    if (varBounds[v].first == -DBL_MAX) {
                        valueOfRest.second = DBL_MAX;
                    } else if (valueOfRest.second != DBL_MAX) {
                        valueOfRest.second -= varBounds[v].first;
                    }
                    if (varBounds[v].second == DBL_MAX) {
                        valueOfRest.first = -DBL_MAX;
                    } else if (valueOfRest.first != -DBL_MAX) {
                        valueOfRest.first -= varBounds[v].second;
                    }
                }
            } else {
                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(v);
                valueOfRest.first += currAV.constant;
                valueOfRest.second += currAV.constant;
                for (int s = 0; s < currAV.size; ++s) {
                    v = currAV.fluents[s];
                    if (v == -19) {
                        durationWeight -= currAV.weights[s];
                    } else if (v == -3) {
                        durationWeight += currAV.weights[s];
                    } else if (v < pneCount) {
                        const map<int,double>::const_iterator tItr = tickers.find(v);
                        if (tItr != tickers.end()) {
                            foundTime = true;
                            timeWeight += tItr->second * currAV.weights[s];
                            if (lpDebug & 1) {
                                cout << "- Found it: " << *(RPGBuilder::getPNE(v)) << "*" << timeWeight << endl;
                            }
                            
                        } else {
                            if (lpDebug & 1) {
                                cout << "- Not a ticker: " << *(RPGBuilder::getPNE(v)) << ", bounds [";
                                if (varBounds[v].first == -DBL_MAX) {
                                    cout << "-inf,";
                                } else {
                                    cout << varBounds[v].first << ",";
                                }
                                if (varBounds[v].second == DBL_MAX) {
                                    cout << "inf]\n";
                                } else {
                                    cout << varBounds[v].second << "]\n";
                                }
                            }

                            
                            if (varBounds[v].second == DBL_MAX) {
                                valueOfRest.second = DBL_MAX;
                            } else if (valueOfRest.second != DBL_MAX) {
                                valueOfRest.second += varBounds[v].second * currAV.weights[s];
                            }
                            if (varBounds[v].first == -DBL_MAX) {
                                valueOfRest.first = -DBL_MAX;
                            } else if (valueOfRest.first != -DBL_MAX) {
                                valueOfRest.first += varBounds[v].first * currAV.weights[s];
                            }
                        }
                    } else {
                        v -= pneCount;
                        const map<int,double>::const_iterator tItr = tickers.find(v);
                        if (tItr != tickers.end()) {
                            foundTime = true;
                            timeWeight -= tItr->second * currAV.weights[s];
                            if (lpDebug & 1) {
                                cout << "- Found it: " << *(RPGBuilder::getPNE(v)) << "*" << timeWeight << endl;
                            }
                            
                        } else {
                            if (lpDebug & 1) {
                                cout << "- Not a ticker: " << *(RPGBuilder::getPNE(v)) << ", bounds [";
                                if (varBounds[v].first == -DBL_MAX) {
                                    cout << "-inf,";
                                } else {
                                    cout << varBounds[v].first << ",";
                                }
                                if (varBounds[v].second == DBL_MAX) {
                                    cout << "inf]\n";
                                } else {
                                    cout << varBounds[v].second << "]\n";
                                }
                            }

                            
                            if (varBounds[v].first == -DBL_MAX) {
                                valueOfRest.second = DBL_MAX;
                            } else if (valueOfRest.second != DBL_MAX) {
                                valueOfRest.second -= varBounds[v].first * currAV.weights[s];
                            }
                            if (varBounds[v].second == DBL_MAX) {
                                valueOfRest.first = -DBL_MAX;
                            } else if (valueOfRest.first != -DBL_MAX) {
                                valueOfRest.first -= varBounds[v].second * currAV.weights[s];
                            }
                        }
                    }
                }
            }
            
            if (!foundTime) {
                continue;
            }
            
            if (lpDebug & 1) {
                cout << "Found a precondition containing weighted " << timeWeight << " time: " << currPre << endl;
                cout << "RHS is " << currPre.RHSConstant << endl;
                cout << "The rest of the LHS evaluates to " << valueOfRest.first << "," << valueOfRest.second << endl;
            }
            
            if (valueOfRest.second != DBL_MAX) {                
                boundsImpliedByCondition[np] = TimeDependentLimit(currPre.RHSConstant, durationWeight, timeWeight, valueOfRest.second);
                
                if (lpDebug & 1) {
                    if (boundsImpliedByCondition[np].timeWeight > 0.0) {
                        cout << "Lower bound implied by condition: (" << boundsImpliedByCondition[np].RHSconstant - boundsImpliedByCondition[np].maxValueOfRest <<  " - " << durationWeight << " * ?duration) / " << boundsImpliedByCondition[np].timeWeight << endl;
                    }
                    if (boundsImpliedByCondition[np].timeWeight < 0.0) {
                        cout << "Upper bound implied by condition: (" << -boundsImpliedByCondition[np].RHSconstant + boundsImpliedByCondition[np].maxValueOfRest <<  " + " << durationWeight << " * ?duration) / " << -boundsImpliedByCondition[np].timeWeight << endl;
                    }
                }
            }
            
                        
        }
    }
    
    static bool firstCall = true;    

    for (int actID = 0; actID < actCount; ++actID) {
        
        if (RPGBuilder::rogueActions[actID]) {
            continue;
        }

        if (globalActionDurationBounds[actID].first > globalActionDurationBounds[actID].second) {
            pruneAction.push_back(actID);
            continue;
        }
        
        if (lpDebug & 1) {
            cout << "Seeing where " << *(RPGBuilder::getInstantiatedOp(actID)) << " sits on the TIL timelines\n";
        }
        
        pair<double,double> startBounds(0.0, DBL_MAX);
        pair<double,double> endBounds(globalActionDurationBounds[actID].first, DBL_MAX);
        
        bool keep = true;
        
        for (int pass = 0; keep && pass < 2; ++pass) {
            const list<int> & instantPres = (pass ? RPGBuilder::getEndPreNumerics()[actID] : RPGBuilder::getStartPreNumerics()[actID]);            
            
            if (lpDebug & 1) {
                if (instantPres.empty()) {
                    if (pass) {
                        cout << "- No end numeric preconditions\n";
                    } else {
                        cout << "- No start numeric preconditions\n";
                    }
                    
                } else {
                    if (pass) {
                        cout << "- Looking for time in the end numeric preconditions\n";
                    } else {
                        cout << "- Looking for time in the start numeric preconditions\n";
                    }
                                        
                }
            }
            list<int>::const_iterator ipItr = instantPres.begin();
            const list<int>::const_iterator ipEnd = instantPres.end();
            
            for (; ipItr != ipEnd; ++ipItr) {

                const double impliedLB = boundsImpliedByCondition[*ipItr].getLower(globalActionDurationBounds[actID].first, globalActionDurationBounds[actID].second);
                const double impliedUB = boundsImpliedByCondition[*ipItr].getUpper(globalActionDurationBounds[actID].first, globalActionDurationBounds[actID].second);                
                
                if (pass) {
                    if (impliedLB > endBounds.first) {
                        if (lpDebug & 1) {
                            cout << "- Pushed end lower bound up to " << impliedLB << " because of " << RPGBuilder::getNumericPreTable()[*ipItr] << endl;
                        }
                        endBounds.first = impliedLB;
                    }
                    
                    if (impliedUB < endBounds.second) {
                        if (lpDebug & 1) {
                            cout << "- Pushed end upper bound down to " << impliedUB << " because of " << RPGBuilder::getNumericPreTable()[*ipItr] << endl;
                        }
                        endBounds.second = impliedUB;
                    }
                } else {
                    if (impliedLB > startBounds.first) {
                        if (lpDebug & 1) {
                            cout << "- Pushed start lower bound up to " << impliedLB << " because of " << RPGBuilder::getNumericPreTable()[*ipItr] << endl;
                        }
                        startBounds.first = impliedLB;
                    }
                    
                    if (impliedUB < startBounds.second) {
                        if (lpDebug & 1) {
                            cout << "- Pushed start upper bound down to " << impliedUB << " because of " << RPGBuilder::getNumericPreTable()[*ipItr] << endl;
                        }
                        startBounds.second = impliedUB;
                    }
                }
                    
                    
            }
        }

        reboundSingleAction(actID, globalActionDurationBounds, keep, startBounds, endBounds, workingGlobally);
        
        
        if (!keep) {
            pruneAction.push_back(actID);     
            continue;                            
        }
        
        if (actionTSBounds[actID][0].first < startBounds.first) {
            actionTSBounds[actID][0].first = startBounds.first;
        }
        
        if (actionTSBounds[actID][1].first < endBounds.first) {
            actionTSBounds[actID][1].first = endBounds.first;
        }
        
        if (actionTSBounds[actID][0].second > startBounds.second) {
            actionTSBounds[actID][0].second = startBounds.second;
        }
        
        if (actionTSBounds[actID][1].second > endBounds.second) {
            actionTSBounds[actID][1].second = endBounds.second;
        }
        
        
    }

    if (firstCall) {    
        list<int>::const_iterator pruneItr = pruneAction.begin();
        const list<int>::const_iterator pruneEnd = pruneAction.end();
    
        for (; pruneItr != pruneEnd; ++pruneItr) {
            #ifdef ENABLE_DEBUGGING_HOOKS
            Globals::eliminatedAction(*pruneItr, "TIL timelines cannot find a point at which it can happen");
            #endif
            cout << "Pruning " << *(RPGBuilder::getInstantiatedOp(*pruneItr)) << " - the TIL timelines never allow it to be applied\n";
            RPGBuilder::pruneIrrelevant(*pruneItr);
        }

        firstCall = false;
    }

    recalculateDurationsFromBounds();

   
}

struct RelevantTimelinePointsAndOffset {
    
    TILTimeline::const_iterator adder;
    TILTimeline::const_iterator itrEnd;
    double startOffset;
    double endOffset;
    
    RelevantTimelinePointsAndOffset(const TILTimeline::const_iterator & a,
                                    const TILTimeline::const_iterator & b,
                                    const double & so, const double & eo)
                                    : adder(a), itrEnd(b), startOffset(so), endOffset(eo) {
    }
};

void TemporalAnalysis::reboundSingleAction(const int & actID, const vector<pair<double,double> > & durationBounds, bool & keep, pair<double,double> & startBounds, pair<double,double> & endBounds, const bool workingGlobally)
{

    
    static const int lpDebug = 0;
    bool pushedForwards = false;
                                    
    if (keep) {
        double t;
        
        t = endBounds.first - durationBounds[actID].second;
        if (t > startBounds.first) {
            startBounds.first = t;
            if (lpDebug & 1) {
                cout << "- Pushing lower bound of start up to " << t << endl;
            }
        }
        if (endBounds.second != DBL_MAX) {
            t = endBounds.second - durationBounds[actID].first;
            if (t < startBounds.second) {
                if (lpDebug & 1) {
                    cout << "- Pushing upper bound of start down to " << t << endl;
                }
                startBounds.second = t;
            }
        }
        
        if (startBounds.first > startBounds.second) {
            if (lpDebug & 1) {
                cout << "- Pruning action: start lower bound of " << startBounds.first << " exceeds upper bound of " << startBounds.second << endl;
            }
            keep = false;
        }    
        
        if (endBounds.first > endBounds.second) {
            if (lpDebug & 1) {
                cout << "- Pruning action: end lower bound of " << endBounds.first << " exceeds upper bound of " << endBounds.second << endl;
            }
            keep = false;
        }
    }
    
    #ifdef ENABLE_DEBUGGING_HOOKS
    if (workingGlobally) {
        if (RPGBuilder::getRPGDEs(actID).empty()) {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
        } else {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
        }
    }
    #endif
    
    if (!keep) {
        return;
    }
    
    vector<list<RelevantTimelinePointsAndOffset> > relevantTimelinePointsAndTheirEnds(2);
    
    for (int pass = 0; keep && pass < 2; ++pass) {
                    
        const map<int,list<int> > & pointLookIn = (pass ? actionEndUsesAbstractedFact : actionStartUsesAbstractedFact);

        double & overallWorkingUpper = (pass ? endBounds.second : startBounds.second);
        double & actualBoundForSuccessors = (pass ? endBounds.first : startBounds.first);
                    
        for (int offsetPass = 0; keep && offsetPass < 2; ++offsetPass) {
            
            const map<int,list<int> > & lookIn = (offsetPass ? actionOverAllUsesAbstractedFact : pointLookIn);
            const double UBoffset = (offsetPass && pass ? 0.0 : EPSILON);
            const double LBoffset = (offsetPass && !pass ? 0.0 : EPSILON);
            const double canTolerateLaterAddBy = (offsetPass && !pass ? EPSILON : 0.0);
            
            map<int, list<int> >::const_iterator tdItr = lookIn.find(actID);
            if (tdItr != lookIn.end()) {
                const list<int> & instantPres = tdItr->second;
            
                list<int>::const_iterator pItr = instantPres.begin();
                const list<int>::const_iterator pEnd = instantPres.end();                                        
                
                for (; keep && pItr != pEnd; ++pItr) {
                    
                    const TILTimeline * const currTimeline = TemporalAnalysis::timelineOnTILFact(*pItr);
                    
                    if (!currTimeline) {
                        continue;
                    }
                    
                    if (!currTimeline->isOnlyEverAddedByTILs()) {
                        continue;
                    }
                    
                    {
                        TILTimeline::const_iterator ub = currTimeline->getLastDeletor();
                        if (ub != currTimeline->end() && ub->first - UBoffset < overallWorkingUpper) {
                            if (lpDebug & 1) {
                                if (offsetPass == 0) {
                                    cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " pushes upper bound " << pass << " down to " << ub->first - UBoffset << ", i.e. before the last TIL deletor\n";
                                } else {
                                    cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " being over all pushes upper bound " << pass << " down to " << ub->first - UBoffset << ", i.e. alonside the last TIL deletor\n";
                                }
                            }
                            overallWorkingUpper = ub->first - UBoffset;
                            
                            if (overallWorkingUpper < actualBoundForSuccessors) {
                                if (lpDebug & 1) {
                                    cout << "- This is before the lower bound " << pass << " of " << actualBoundForSuccessors << ", so the LP would be unsolvable\n";
                                }
                                keep = false;
                                break;
                            }
                        }
                    }
                
                    if (lpDebug & 1) {
                        cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " - looking for suitable adder for time " << actualBoundForSuccessors + canTolerateLaterAddBy << endl;
                    }
                    TILTimeline::const_iterator adder = currTimeline->firstAdderSuitableForTime(actualBoundForSuccessors + canTolerateLaterAddBy);

                    if (adder == currTimeline->end()) {
                        if (lpDebug & 1) {
                            cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " means that the LP cannot ever be solved: there is no true-TIL-window that can contain " << actualBoundForSuccessors + canTolerateLaterAddBy << endl;
                        }
                        keep = false; break;
                    }
                
                    if (adder->first + LBoffset > actualBoundForSuccessors) {
                        if (lpDebug & 1) {
                            if (offsetPass == 0) {
                                cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " leads to pushing lower-bound " << pass << " up to " << adder->first  + LBoffset << endl;
                            } else {
                                cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " being over all leads to pushing lower-bound " << pass << " up to " << adder->first << " + " << LBoffset << " = " << LBoffset << endl;
                            }
                        }
                        
                        pushedForwards = (!relevantTimelinePointsAndTheirEnds[0].empty() || !relevantTimelinePointsAndTheirEnds[1].empty());
                        actualBoundForSuccessors = adder->first + LBoffset;
                        if (overallWorkingUpper < actualBoundForSuccessors) {
                            if (lpDebug & 1) {
                                cout << "- This is after the upper bound " << pass << " of " << overallWorkingUpper << ", so the LP would be unsolvable\n";
                            }
                            keep = false;
                            #ifdef ENABLE_DEBUGGING_HOOKS
                            if (workingGlobally) {                            
                                if (RPGBuilder::getRPGDEs(actID).empty()) {
                                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
                                } else {
                                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
                                }
                            }
                            #endif
                            break;
                        }
                    } else {
                        if (lpDebug & 1) {
                            cout << "- " << *(RPGBuilder::getLiteral(*pItr)) << " is okay for now: " << adder->first << " is below the known lower bound " << pass << "\n";
                        }
                    }
                
                    if (pass) {
                        if (offsetPass) {
                            relevantTimelinePointsAndTheirEnds[pass].push_back(RelevantTimelinePointsAndOffset(adder, currTimeline->end(), EPSILON, EPSILON));
                        } else {
                            relevantTimelinePointsAndTheirEnds[pass].push_back(RelevantTimelinePointsAndOffset(adder, currTimeline->end(), 0.0, EPSILON));
                        }
                        
                    } else {
                
                        if (offsetPass) {
                            relevantTimelinePointsAndTheirEnds[pass].push_back(RelevantTimelinePointsAndOffset(adder, currTimeline->end(), 0.0, 0.0));
                        } else {
                            relevantTimelinePointsAndTheirEnds[pass].push_back(RelevantTimelinePointsAndOffset(adder, currTimeline->end(), 0.0, EPSILON));
                        }
                    }                    
                }
            }
        }
        
        if (pass == 0) {
            if (startBounds.first > 0.0) {
                endBounds.first = startBounds.first + durationBounds[actID].first;
            }
            if (startBounds.second < DBL_MAX) {
                endBounds.second = startBounds.second + durationBounds[actID].second;
            }
        }
    }
    
    
    if (keep) {
        double t;
        
        t = endBounds.first - durationBounds[actID].second;
        if (t > startBounds.first + 0.0005) {
            startBounds.first = t;
            if (lpDebug & 1) {
                cout << "- Pushing lower bound of start up to " << t << endl;
            }
            pushedForwards = (!relevantTimelinePointsAndTheirEnds[0].empty() || !relevantTimelinePointsAndTheirEnds[1].empty());
        }
        if (endBounds.second != DBL_MAX) {
            t = endBounds.second - durationBounds[actID].first;
            if (t < startBounds.second) {
                if (lpDebug & 1) {
                    cout << "- Pushing upper bound of start down to " << t << endl;
                }
                startBounds.second = t;
            }
        }
        
        if (startBounds.first > startBounds.second) {
            if (lpDebug & 1) {
                cout << "- Pruning action: start lower bound of " << startBounds.first << " exceeds upper bound of " << startBounds.second << endl;
            }
            keep = false;
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (workingGlobally) {                
                if (RPGBuilder::getRPGDEs(actID).empty()) {
                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
                } else {
                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
                }
            }
            #endif
        }           
        
        if (endBounds.first > endBounds.second) {
            if (lpDebug & 1) {
                cout << "- Pruning action: end lower bound of " << endBounds.first << " exceeds upper bound of " << endBounds.second << endl;
            }
            keep = false;
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (workingGlobally) {                
                if (RPGBuilder::getRPGDEs(actID).empty()) {
                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
                } else {
                    Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
                }
            }
            #endif
        }
    }
        
    if (!keep) {
        return;            
    }

    #ifdef ENABLE_DEBUGGING_HOOKS
    if (workingGlobally) {                                        
        if (RPGBuilder::getRPGDEs(actID).empty()) {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
        } else {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
        }
    }
    #endif
        
    for (int iCounter = 0; keep && pushedForwards; ++iCounter) {
            
            
        pushedForwards = false;
        
        for (int pass = 0; keep && pass < 2; ++pass) {
                    
            double & overallWorkingUpper = (pass ? endBounds.second : startBounds.second);
            double & boundForSuccessors = (pass ? endBounds.first : startBounds.first);
        
            if (lpDebug & 1) {
                cout << "- Revisiting TIL timelines from " << boundForSuccessors << ", pass " << iCounter << ":" << pass << endl;
                if (pushedForwards) {
                    cout << "Will push forwards again after this\n";
                } else {
                    cout << "Will not push forwards again after this\n";
                }
            }
                
            list<RelevantTimelinePointsAndOffset>::iterator rtItr = relevantTimelinePointsAndTheirEnds[pass].begin();
            const list<RelevantTimelinePointsAndOffset>::iterator rtEnd = relevantTimelinePointsAndTheirEnds[pass].end();
            
            for (; rtItr != rtEnd; ++rtItr) {
                
                {
                    TILTimeline::const_iterator next = rtItr->adder;
                    ++next;
                    
                    
                    if (next == rtItr->itrEnd) {
                        // the last thing on the TIL timeline is an add
                        continue;
                    }
                }
                
                TILTimeline::const_iterator lastDeletorBeforeBoundForSuccessors = rtItr->itrEnd;

                TILTimeline::const_iterator curr = rtItr->adder;
                
                while (curr != rtItr->itrEnd && curr->first <= (boundForSuccessors + rtItr->startOffset)) {
                    if (curr->second.deleted) {
                        lastDeletorBeforeBoundForSuccessors = curr;
                        if (lpDebug & 1) {
                            cout << "  > Skipping " << curr->first << ", but it's a deletor\n";
                        }
                    } else {
                        if (lpDebug & 1) {
                            cout << "  > Skipping " << curr->first << endl;
                        }
                    }
                    ++curr;
                }
                
                // curr points to the happening before the 'boundForSuccessors' time
                
                if (lastDeletorBeforeBoundForSuccessors != rtItr->itrEnd) {
                    // some deletor has occurred between the previously relied upon TIL and now
                    // thus, the next adder must precede nowAfter - push forwards the last deletor until we find an adding happening
                    
                    for (; lastDeletorBeforeBoundForSuccessors != rtItr->itrEnd && !lastDeletorBeforeBoundForSuccessors->second.added; ++lastDeletorBeforeBoundForSuccessors) ;
                                                        
                    if (lastDeletorBeforeBoundForSuccessors == rtItr->itrEnd) {
                        // no new adder exists
                        if (lpDebug & 1) {
                            cout << "- There is no adder after a now-past deletor on this timeline\n";
                        }
                        keep = false;
                        break;
                    }
                    
                    rtItr->adder = lastDeletorBeforeBoundForSuccessors;
                    
                    if (rtItr->adder->first + EPSILON - rtItr->startOffset  > boundForSuccessors) {
                        boundForSuccessors = rtItr->adder->first + EPSILON - rtItr->startOffset;
                        if (lpDebug & 1) {
                            cout << "- To get past a deletor on this timeline, and then be added again " << EPSILON - rtItr->startOffset << " before, the lower bound is pushed to " << boundForSuccessors << endl;
                        }
                        if (overallWorkingUpper < boundForSuccessors) {
                            if (lpDebug & 1) {
                                cout << "- This is after the upper bound of " << overallWorkingUpper << ", so the LP would be unsolvable\n";
                            }
                            keep = false; break;
                        }
                        pushedForwards = true;
                    }
                    

                    
                } else {
                    if (lpDebug & 1) {
                        cout << "- Can keep pre-existing adder on this timeline\n";
                    }
                }
                
            }
            
            if (pass == 0) {
                double t;
                t = startBounds.first + durationBounds[actID].first;
                if (t > endBounds.first) {
                    if (lpDebug & 1) {
                        cout << "- Pushing lower bound of end up to " << t << endl;
                    }
                    endBounds.first = t;
                }
                if (startBounds.second < DBL_MAX) {
                    t = startBounds.second + durationBounds[actID].second;
                    if (t < endBounds.second) {
                        if (lpDebug & 1) {
                            cout << "- Pushing upper bound of end up to " << t << endl;
                        }
                        endBounds.second = t;
                    }
                }
                
                if (endBounds.first > endBounds.second) {
                    if (lpDebug & 1) {
                        cout << "- Pruning action: end lower bound of " << endBounds.first << " exceeds upper bound of " << endBounds.second << endl;
                    }
                    keep = false;
                    #ifdef ENABLE_DEBUGGING_HOOKS
                    if (workingGlobally) {                        
                        if (RPGBuilder::getRPGDEs(actID).empty()) {
                            Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
                        } else {
                            Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
                        }
                    }
                    #endif
                }
            }
        }
        
        if (keep) {
            double t;
            
            t = endBounds.first - durationBounds[actID].second;
            if (t > startBounds.first + 0.0005) {
                if (lpDebug & 1) {
                    cout << "- Pushing lower bound of start up to " << t << endl;
                }
                startBounds.first = t;                    
                pushedForwards = true;
            }
            if (endBounds.second != DBL_MAX) {
                t = endBounds.second - durationBounds[actID].first;
                if (t < startBounds.second) {
                    if (lpDebug & 1) {
                        cout << "- Pushing upper bound of start down to " << t << endl;
                    }
                    startBounds.second = t;
                }
            }
            
            if (startBounds.first > startBounds.second) {
                if (lpDebug & 1) {
                    cout << "- Pruning action: start lower bound of " << startBounds.first << " exceeds upper bound of " << startBounds.second << endl;
                }
                keep = false;
                #ifdef ENABLE_DEBUGGING_HOOKS
                if (workingGlobally) {                    
                    if (RPGBuilder::getRPGDEs(actID).empty()) {
                        Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
                    } else {
                        Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
                    }
                }
                #endif
            }           
        }

    }
    
    #ifdef ENABLE_DEBUGGING_HOOKS
    if (workingGlobally) {                                    
        if (RPGBuilder::getRPGDEs(actID).empty()) {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second);
        } else {
            Globals::checkActionBounds(actID, startBounds.first, startBounds.second, endBounds.first, endBounds.second);
        }
    }
    #endif
    
}


void TemporalAnalysis::recalculateDurationsFromBounds(const bool workingGlobally)
{

    static const bool localDebug = false;        
    
    assert(initialisedGlobalActionDurationBounds);
    
    const int actCount = RPGBuilder::getStartPropositionalPreconditions().size();
    
    for (int actID = 0; actID < actCount; ++actID) {
        
        if (RPGBuilder::rogueActions[actID]) {
            continue;
        }
    
        vector<RPGBuilder::RPGDuration*> & durs = RPGBuilder::getRPGDEs(actID);
        
        if (!durs.empty()) {
            if (actionTSBounds[actID][1].second != DBL_MAX) {
                const double timelineMax = actionTSBounds[actID][1].second - actionTSBounds[actID][0].first;
                if (timelineMax < globalActionDurationBounds[actID].second) {
                    
                    #ifdef ENABLE_DEBUGGING_HOOKS
                    if (workingGlobally) {                                                                        
                        Globals::checkActionDurationBounds(actID, globalActionDurationBounds[actID].first, timelineMax);
                    }
                    #endif
                    
                    if (localDebug) {
                        std::cerr << "Action " << *(RPGBuilder::getInstantiatedOp(actID)) << " in fact can take at most ";
                        std::cerr << timelineMax;
                        std::cerr << ", rather than " << globalActionDurationBounds[actID].second << endl;                
                    }
                                
                
                    list<RPGBuilder::DurationExpr *>::const_iterator deItr = durs[0]->max.begin();
                    const list<RPGBuilder::DurationExpr *>::const_iterator deEnd = durs[0]->max.end();
                    
                    bool constantFound = false;
                    
                    for (; deItr != deEnd; ++deItr) {
                        if ((*deItr)->variables.empty()) {
                            constantFound = true;
                            if ((*deItr)->constant > timelineMax) {
                                (*deItr)->constant = timelineMax;
                            }
                        }
                    }
                    
                    if (!constantFound) {
                        durs[0]->max.push_back(new RPGBuilder::DurationExpr(timelineMax));
                    }
                    
                    RPGBuilder::boostMaxDuration(actID, timelineMax);
                    
                    globalActionDurationBounds[actID].second = timelineMax;
                }
            }
            
            if (actionTSBounds[actID][0].second != DBL_MAX) {
                const double timelineMin = actionTSBounds[actID][1].first - actionTSBounds[actID][1].second;
                if (timelineMin > globalActionDurationBounds[actID].first) {
                    
                    #ifdef ENABLE_DEBUGGING_HOOKS
                    if (workingGlobally) {                                                                        
                        Globals::checkActionDurationBounds(actID, timelineMin, globalActionDurationBounds[actID].second);
                    }
                    #endif
                    
                    if (localDebug) {
                        std::cerr << "Action " << *(RPGBuilder::getInstantiatedOp(actID)) << " in fact takes at least ";
                        std::cerr << timelineMin;
                        std::cerr << ", rather than " << globalActionDurationBounds[actID].first << endl;                
                    }
                                
                
                    list<RPGBuilder::DurationExpr *>::const_iterator deItr = durs[0]->min.begin();
                    const list<RPGBuilder::DurationExpr *>::const_iterator deEnd = durs[0]->min.end();
                    
                    bool constantFound = false;
                    
                    for (; deItr != deEnd; ++deItr) {
                        if ((*deItr)->variables.empty()) {
                            constantFound = true;
                            if ((*deItr)->constant < timelineMin) {
                                (*deItr)->constant = timelineMin;
                            }
                        }
                    }
                    
                    if (!constantFound) {
                        durs[0]->min.push_back(new RPGBuilder::DurationExpr(timelineMin));
                    }
                    
                    RPGBuilder::boostMinDuration(actID, timelineMin);
                    
                    globalActionDurationBounds[actID].first = timelineMin;
                }
            }
            
            #ifdef ENABLE_DEBUGGING_HOOKS
            if (workingGlobally) {                                                        
                Globals::checkActionDurationBounds(actID,  globalActionDurationBounds[actID].first, globalActionDurationBounds[actID].second);
            }
            #endif


        }
        
    }
}

extern void sanityCheck(MinimalState & theState);

void TemporalAnalysis::pullInAbstractTILs(MinimalState & theState, list<FFEvent> & planToAddDummyStepsTo)
{

    if (!abstractTILsWherePossible) {
        return;
    }
    
    assert(planToAddDummyStepsTo.empty() && theState.planLength == 0);
    
    map<int, TILTimeline>::const_iterator tilItr = timelineOnTILs.begin();
    const map<int, TILTimeline>::const_iterator tilEnd = timelineOnTILs.end();
    
    for (; tilItr != tilEnd; ++tilItr) {
        if (!factIsAbstract[tilItr->first]) {
            continue;
        }
        
        // have an abstracted TIL
        
        const TILTimeline::const_iterator firstAdder = tilItr->second.getFirstAdder();
        assert(firstAdder != tilItr->second.end());
        
        theState.temporalConstraints->extend(1);
        
        planToAddDummyStepsTo.push_back(FFEvent(-1 - tilItr->first));
        planToAddDummyStepsTo.back().lpMinTimestamp = firstAdder->first;
        planToAddDummyStepsTo.back().lpTimestamp = firstAdder->first;                        
        
        const TILTimeline::const_iterator lastDeletor = tilItr->second.getLastDeletor();
        
        if (lastDeletor == tilItr->second.end()) {
            planToAddDummyStepsTo.back().lpMaxTimestamp = DBL_MAX;
        } else {
            planToAddDummyStepsTo.back().lpMaxTimestamp = lastDeletor->first;
        }
        
        planToAddDummyStepsTo.back().getEffects = false;
        
        if (firstAdder->first >= 0.0) { // not an initial-state add
                
            const PropositionAnnotation afterNow(theState.planLength);        
            theState.first.insert(make_pair(tilItr->first, afterNow));
            
        } else {
            #ifndef NDEBUG
            if (theState.first.find(tilItr->first) == theState.first.end()) {
                std::cerr << "Fatal error: TIL-manipulated fact " << *(RPGBuilder::getLiteral(tilItr->first)) << " is down as being usable from epsilon after " << firstAdder->first << ", but it isn't in the initial state\n";
                assert(theState.first.find(tilItr->first) != theState.first.end());
            }
            #endif
        }
        
        ++theState.planLength;
    }
    
    sanityCheck(theState);
    
    assert(theState.planLength == planToAddDummyStepsTo.size());
}

void TemporalAnalysis::doDurationLimitingEffectAnalysis(const double & costLimit, vector<pair<double,double> > & actionDurationBounds)
{
    static const bool debug = false;
        
    static bool isolatedDurationLimitingEffects = false;
    static list<int> durationLimitingEffects;
    static map<int,double> metricVarCostWeights;
    static const int pneCount = RPGBuilder::getPNECount();
    static const bool minimisationMetric = (RPGBuilder::getMetric() ? RPGBuilder::getMetric()->minimise : true);
    const vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();
        
    if (!isolatedDurationLimitingEffects) {
        isolatedDurationLimitingEffects = true;

        NumericAnalysis::findWhetherTheMetricIsMonotonicallyWorsening();

        if (Globals::optimiseSolutionQuality && RPGBuilder::getMetric() && NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
        
            list<int>::const_iterator mvItr = RPGBuilder::getMetric()->variables.begin();
            const list<int>::const_iterator mvEnd = RPGBuilder::getMetric()->variables.end();
            
            if (debug) {
                cout << "Number of metric variables: " << RPGBuilder::getMetric()->variables.size() << endl;
            }

            list<double>::const_iterator mwItr = RPGBuilder::getMetric()->weights.begin();
            
            for (; mvItr != mvEnd; ++mvItr, ++mwItr) {

                if (*mvItr < 0) {
                    // preferences or makespan
                    if (debug) {
                        cout << "Ignoring metric term on special var " << *mvItr << endl;
                    }
                    continue;
                }
                
                if (*mvItr < pneCount) {
                    if (RPGBuilder::getMetric()->minimise) {
                        metricVarCostWeights.insert(make_pair(*mvItr, -*mwItr));
                        if (debug) {
                            cout << "Metric weight on " << *(RPGBuilder::getPNE(*mvItr)) << " = " << -*mwItr << endl;
                        }
                    } else {
                        metricVarCostWeights.insert(make_pair(*mvItr, *mwItr));
                    }
                } else {
                    assert(*mvItr < 2 * pneCount);
                    if (RPGBuilder::getMetric()->minimise) {
                        metricVarCostWeights.insert(make_pair(*mvItr - pneCount, *mwItr));
                        if (debug) {
                            cout << "Metric weight on " << *(RPGBuilder::getPNE(*mvItr - pneCount)) << " = " << -*mwItr << endl;
                        }

                    } else {
                        metricVarCostWeights.insert(make_pair(*mvItr - pneCount, -*mwItr));
                    }
                }
            }
            
            if (!metricVarCostWeights.empty()) {
                
                const int effCount = effTable.size();
                
                for (int i = 0; i < effCount; ++i) {
                    const RPGBuilder::RPGNumericEffect & currEff = effTable[i];

                    if (metricVarCostWeights.find(currEff.fluentIndex) == metricVarCostWeights.end()) {
                        if (debug) {
                            cout << currEff << " is not an effect on the metric\n";
                        }
                        continue;
                    }

                    
                    bool found = false;
                    bool safe = true;
                    
                    for (int s = 0; s < currEff.size; ++s) {
                        if (currEff.variables[s] == -3 || currEff.variables[s] == -19) { // ?duration or -?duration
                            found = true;
                        } else {
                            safe = false;
                        }
                    }
                    
                    if (found && safe) {
                        durationLimitingEffects.push_back(i);
                        if (debug) {
                            cout << currEff << " is a duration-limiting effect\n";
                        }
                    } else {
                        if (debug) {
                            cout << currEff << " is not a duration-limiting effect\n";
                        }
                    }
                }
            }
        } else {
            if (debug) {
                if (!Globals::optimiseSolutionQuality) {
                    cout << "Not optimising solution quality, so not tightening duration bounds\n";
                }
                if (!RPGBuilder::getMetric()) {
                    cout << "No metric,, so not tightening duration bounds\n";
                }
                if (!NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
                    cout << "Metric isn't monotonically worsening, so not tightening duration bounds\n";
                }
            }
        }
    }
    
    actionDurationBounds = globalActionDurationBounds;
    
    if (durationLimitingEffects.empty()) {
        if (debug) {
            cout << "No duration-limiting effects\n";
        }
        return;
    }

    if (costLimit == -DBL_MAX) {
        if (debug) {
            cout << "For now, not doing any duration tightening: no upper bound on cost\n";
        }
        return;
    } else {
        if (debug) {
            cout << "Cost limit: " << costLimit << endl;
        }
        assert(costLimit != DBL_MAX);
    }
    
    list<int>::const_iterator effItr = durationLimitingEffects.begin();
    const list<int>::const_iterator effEnd = durationLimitingEffects.end();
    
    for (; effItr != effEnd; ++effItr) {
        
        const RPGBuilder::RPGNumericEffect & currEff = effTable[*effItr];
        
        double fixedCost = currEff.constant;
        double costGradient = 0.0;
        
        for (int s = 0; s < currEff.size; ++s) {
            if (currEff.variables[s] == -3) {
                costGradient += currEff.weights[s];
            } else {
                assert(currEff.variables[s] == -19);
                costGradient -= currEff.weights[s];                
            }
        }

        map<int,double>::const_iterator wItr = metricVarCostWeights.find(currEff.fluentIndex);
        assert(wItr != metricVarCostWeights.end());

        fixedCost *= wItr->second;
        costGradient *= wItr->second;
        
        if (debug) {
            cout << currEff << ": gives a fixed cost of " << fixedCost << " and cost gradient of " << costGradient << endl;
        }

        const list<pair<int, Planner::time_spec> > & deps = RPGBuilder::getRpgNumericEffectsToActions()[*effItr];
        
        if (costGradient > 0.0) {
            // longer duration reduces cost
            const double minDur = (costLimit - fixedCost) / costGradient;
            list<pair<int, Planner::time_spec> >::const_iterator depItr = deps.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator depEnd = deps.end();
            
            for (; depItr != depEnd; ++depItr) {
                if (minDur > actionDurationBounds[depItr->first].first) {
                    if (debug) {
                        cout << "Increased min duration on " << *(RPGBuilder::getInstantiatedOp(depItr->first)) << " from " << actionDurationBounds[depItr->first].first << " to " << minDur << endl;
                    }

                    actionDurationBounds[depItr->first].first = minDur;
                }
            }
        } else {
            assert(costGradient < 0.0);
            // longer duration consumes cost
            const double maxDur = (costLimit - fixedCost) / costGradient;
            list<pair<int, Planner::time_spec> >::const_iterator depItr = deps.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator depEnd = deps.end();
            
            for (; depItr != depEnd; ++depItr) {
                if (maxDur < actionDurationBounds[depItr->first].second) {
                    if (debug) {
                        cout << "Decreased max duration on " << *(RPGBuilder::getInstantiatedOp(depItr->first)) << " from " << actionDurationBounds[depItr->first].second << " to " << maxDur << endl;
                    }

                    actionDurationBounds[depItr->first].second = maxDur;
                }
            }
            
        }
        
    }
    
}

void TemporalAnalysis::doGlobalDurationLimitingEffectAnalysis()
{
    if (Globals::bestSolutionQuality == -DBL_MAX) {
        return;
    }
    
    vector<pair<double,double> > replacement;
    doDurationLimitingEffectAnalysis(Globals::bestSolutionQuality, replacement);
    
    globalActionDurationBounds = replacement;
    TemporalAnalysis::reboundActionsGivenTILTimelines();

   
}

 
}
