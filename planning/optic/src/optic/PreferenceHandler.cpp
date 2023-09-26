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

#include "PreferenceHandler.h"
#include "numericanalysis.h"
#include "NNF.h"
#include <TypedAnalyser.h>

#include <cstdlib>

using VAL::theTC;

#include <iostream>
#include <sstream>
using std::cerr;
using std::ostringstream;
using std::endl;

#define TEMPORALSAFEAUTOMATONSEMANTICS

#include "colours.h"
#include "PreferenceData.h"

namespace Planner {

const char * positionName[8] = {"satisfied", "unsatisfied", "triggered", "unreachable", "eternally satisfied", "satisfied, but goal seen already and still holds", "satisfied, but if goal seen again, becomes unsatisfied", "probably satisfied/eternally satisfied"};
    


    
    
bool canBeSatisfied(const AutomatonPosition::Position & p)
{
    return (p != AutomatonPosition::unreachable);
}

bool isSatisfied(const AutomatonPosition::Position & p)
{
    return (p == AutomatonPosition::satisfied || p == AutomatonPosition::eternallysatisfied || p == AutomatonPosition::probablyeternallysatisfied
            || p == AutomatonPosition::seenoncealreadyandstillholds || p == AutomatonPosition::seenoncealready);
}
    
    
bool PreferenceHandler::preferenceDebug = false;

vector<PreferenceFSA*> PreferenceHandler::automata;
vector<const vector<vector<int> >* > PreferenceHandler::comparisonData;
vector<AutomatonPosition::Position> PreferenceHandler::initialAutomataPositions;

vector<list<LiteralCellDependency<pair<int,bool> > > > PreferenceHandler::preconditionsToPrefs;
vector<list<LiteralCellDependency<pair<int,bool> > > > PreferenceHandler::negativePreconditionsToPrefs;
vector<list<LiteralCellDependency<pair<int,bool> > > > PreferenceHandler::numericPreconditionsToPrefs;

set<pair<int,bool> > PreferenceHandler::defaultTruePrefParts;
int PreferenceHandler::ptrTableInit = 0;
bool PreferenceHandler::temporalPreferences = false;
vector<int> PreferenceHandler::relevantNumericPreconditions;
list<int> PreferenceHandler::withinPreferences;
list<int> PreferenceHandler::sometimePreferences;
list<int> PreferenceHandler::preferencesInNonDefaultPositionsInitially;

vector<bool> PreferenceHandler::numericVariableAffectsPreferences;

void PreferenceHandler::buildAutomata()
{
 
    //mappingFromFactsToPreferences.resize(RPGBuilder::getLiteralCount());
    //mappingFromNumericFactsToPreferences.resize(RPGBuilder::getNumericPreTable().size());
    
    
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const uint prefCount = prefs.size();
    const uint taskPrefCount = RPGBuilder::getTaskPrefCount();
    
    if (!prefCount) return;
    
    LiteralSet initialState;
    vector<double> initialFluents;    
    RPGBuilder::getInitialState(initialState, initialFluents);
    
    MinimalState initMS;
    
    initMS.secondMin = initialFluents;
    initMS.secondMax = initialFluents;    
    initMS.insertFacts(initialState.begin(), initialState.end(), StepAndBeforeOrAfter());
    
    const vector<double> minTimestamps;
    
    automata.resize(prefCount, (PreferenceFSA*) 0);
    comparisonData.resize(taskPrefCount, (const vector<vector<int> >*) 0);
    
    initialAutomataPositions.resize(taskPrefCount, AutomatonPosition::unsatisfied);
    initMS.preferenceStatus.resize(taskPrefCount);        
    
    for (uint p = 0; p < taskPrefCount; ++p) {
        list<NNFPreconditionChooser::Supporters> chosen;
    
        assert(initMS.preferenceStatus.size() > p);
        switch (prefs[p].cons) {
            case VAL::E_ALWAYS:
            {
                automata[p] = new AlwaysFSA(p, &(prefs[p]), initialAutomataPositions[p]);                
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,false), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                break;
            }
            case VAL::E_ATEND:
            {
                automata[p] = new AtEndFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,false), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                break;
            }
            case VAL::E_SOMETIME:
            {
                automata[p] = new SometimeFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,false), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                sometimePreferences.push_back(p);
                break;
            }
            case VAL::E_ATMOSTONCE:
            {
                automata[p] = new AtMostOnceFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,false), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                break;
            }
            case VAL::E_SOMETIMEAFTER:
            {
                automata[p] = new SometimeAfterFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,true), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                if (initialAutomataPositions[p] == AutomatonPosition::triggered) {
                    preferencesInNonDefaultPositionsInitially.push_back(p);
                }
                break;
            }                           
            case VAL::E_SOMETIMEBEFORE:
            {
                automata[p] = new SometimeBeforeFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,true), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                break;
            }           
            case VAL::E_WITHIN:
            {
                automata[p] = new WithinFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,false), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                if (initialAutomataPositions[p] == AutomatonPosition::unsatisfied) {
                    // if within preferences are unreachable or initially satisfied, they'll never introduce dummy steps that need checking
                    temporalPreferences = true;
                    withinPreferences.push_back(p);
                }
                break;
            }
            case VAL::E_ALWAYSWITHIN:
            {
                automata[p] = new AlwaysWithinFSA(p, &(prefs[p]), initialAutomataPositions[p]);
                initMS.preferenceStatus[p] = initialAutomataPositions[p];
                if (!automata[p]->update(&initMS, make_pair(true,true), minTimestamps, chosen)) {
                    postmortem_unsatisfiableConstraint();
                }
                initialAutomataPositions[p] = initMS.preferenceStatus[p];
                if (initialAutomataPositions[p] != AutomatonPosition::unreachable) {
                    // if always-within preferences are unreachable, they'll never introduce dummy steps that need checking
                    temporalPreferences = true;
                }
                if (initialAutomataPositions[p] == AutomatonPosition::triggered) {
                    preferencesInNonDefaultPositionsInitially.push_back(p);
                }                
                break;
            }
            default:
            {
                cerr << "Preference type " << prefs[p].cons << " is currently unhandled\n";
                exit(1);
            }
        }
        if (automata[p]) {
            comparisonData[p] = automata[p]->getComparisonData();
        }
    }
    
    for (uint p = taskPrefCount; p < prefCount; ++p) {
        automata[p] = new PreconditionPref(p, &(prefs[p]));
    }
    
    /*for (uint p = 0; p < prefCount; ++p) {
        automata[p]->populateFactToPreferenceMappings();
    }*/
    
}

#define CDPAIR(x,y,z) cd[x][y] = z; cd[y][x] = -z;

const vector<vector<int> >* AlwaysFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;
    
    if (!def) {
        cd.resize(4, vector<int>(4));
        for (int i = 0; i < 4; ++i) {
            cd[i][i] = 0;
        }
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unsatisfied,-1)
        def = true;
    }
    
    return &cd;
}

const vector<vector<int> >* AtEndFSA::getComparisonData()
{
       
    static vector<vector<int> > cd;
    static bool def = false;
    
    if (!def) {
        cd.resize(4, vector<int>(4));
        for (int i = 0; i < 4; ++i) {
            cd[i][i] = 0;
        }
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unsatisfied,-1)
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unreachable,-1)
        CDPAIR(AutomatonPosition::unsatisfied,AutomatonPosition::unreachable,-1)
                        
        def = true;
    }
    
    return &cd;
}

const vector<vector<int> >* SometimeFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;
   
    if (!def) {
        cd.resize(8, vector<int>(8));

        for (int i = 0; i < 8; ++i) {
            cd[i][i] = 0;
        }
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::unsatisfied,-1)
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::unreachable,-1)
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::probablyeternallysatisfied,-1)
        
        CDPAIR(AutomatonPosition::unsatisfied,AutomatonPosition::probablyeternallysatisfied,-1)
        CDPAIR(AutomatonPosition::unsatisfied,AutomatonPosition::unreachable,-1)
        
        def = true;
    }
        
    
    return &cd;
}

const vector<vector<int> >* AtMostOnceFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;

    if (!def) {
        cd.resize(7, vector<int>(7));
        
        for (int i = 0; i < 7; ++i) {
            cd[i][i] = 0;
        }
        
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::seenoncealreadyandstillholds,-1);
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::seenoncealready,-1);
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unreachable,-1);
                                     
        CDPAIR(AutomatonPosition::seenoncealreadyandstillholds,AutomatonPosition::seenoncealready,-1);
        CDPAIR(AutomatonPosition::seenoncealreadyandstillholds,AutomatonPosition::unreachable,-1);
        
        CDPAIR(AutomatonPosition::seenoncealready,AutomatonPosition::unreachable,-1);
                                                
        def = true;
    }
    
    
    return &cd;
}


const vector<vector<int> >* SometimeBeforeFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;

    if (!def) {
        
        cd.resize(8, vector<int>(8));
        
        for (int i = 0; i < 8; ++i) {
            cd[i][i] = 0;
        }
                
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unreachable,-1);

        CDPAIR(AutomatonPosition::probablyeternallysatisfied,AutomatonPosition::unreachable,-1);
        CDPAIR(AutomatonPosition::probablyeternallysatisfied,AutomatonPosition::satisfied,1);        
                
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::unreachable,-1);
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::satisfied,1);        
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::probablyeternallysatisfied,1);
        
        def = true;
    }
        
        
    return &cd;
}

const vector<vector<int> >* SometimeAfterFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;

    if (!def) {
        cd.resize(4, vector<int>(4));
        
        for (int i = 0; i < 4; ++i) {
            cd[i][i] = 0;
        }
                    
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::triggered,-1);
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unreachable,-1);
        
        CDPAIR(AutomatonPosition::triggered,AutomatonPosition::unreachable,-1);
        
        def = true;
    }
                            
    return &cd;
}

const vector<vector<int> >* WithinFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;
   
    if (!def) {
        cd.resize(5, vector<int>(5));

        for (int i = 0; i < 5; ++i) {
            cd[i][i] = 0;
        }
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::unsatisfied,-1)
        CDPAIR(AutomatonPosition::eternallysatisfied,AutomatonPosition::unreachable,-1)
        CDPAIR(AutomatonPosition::unsatisfied,AutomatonPosition::unreachable,-1)
        
        def = true;
    }
        
    
    return &cd;
}



/*void PreferenceFSA::populateFactToPreferenceMappings()
{
    cout << "Populating lookup tables for the dependencies of preference " << pref->name << " (" << prefIdx << ")\n";
    
    for (int pass = 0; pass < 2; ++pass) {
        
        
        int & toIncrement = (pass ? initialUnsatisfiedTriggerPreconditions : initialUnsatisfiedGoalPreconditions);
        
        toIncrement = 0;
        
        {
            const list<Literal*> & relevantLiterals = (pass ? pref->trigger : pref->goal);
            
            list<Literal*>::const_iterator factItr = relevantLiterals.begin();
            const list<Literal*>::const_iterator factItrEnd = relevantLiterals.end();
            for (; factItr != factItrEnd; ++factItr) {
                PreferenceHandler::mappingFromFactsToPreferences[(*factItr)->getID()].push_back(make_pair(prefIdx, (pass == 1)));
                ++toIncrement;
            }
            
        }
        {
            
            const list<pair<int,int> > & relevantNumerics = (pass ? pref->triggerRPGNum : pref->goalRPGNum);
            
            {
                cout << "Preference " << pref->name << " (" << prefIdx << ") has " << relevantNumerics.size() << " numeric precondition pairs relevant to its ";
                if (pass) {
                    cout << "trigger\n";
                } else {
                    cout << "goal\n";
                }
            }
            
            list<pair<int,int> >::const_iterator numItr = relevantNumerics.begin();
            const list<pair<int,int> >::const_iterator numEnd = relevantNumerics.end();
            
            
            for (int cidx = 0; numItr != numEnd; ++numItr, ++cidx) {

                for (int pass = 0; pass < 2; ++pass) {
                    const int preIdx = (pass ? numItr->second : numItr->first);
                    if (preIdx < 0) continue;
                    PreferenceHandler::mappingFromNumericFactsToPreferences[preIdx].push_back(make_pair(prefIdx, (pass == 1)));
                    {
                        cout << (RPGBuilder::getNumericPreTable()[preIdx]) << " is relevant to preference " << pref->name << " (" << prefIdx << ")\n";
                    }
                    ++toIncrement;
                }
            }
        }
    }
    
}*/


PreferenceFSA::PreferenceFSA(const int & i, RPGBuilder::Constraint * const p)
: prefIdx(i), pref(p), triggerType(0), goalType(0)
{
    ostringstream c;
    c << "Switch " << p->name;
    switchVarName = c.str();
    
    PreferenceData * const d = pref->d;
    
    if (!d->conditionLiterals[0].empty() || !d->conditionNegativeLiterals[0].empty()) {
        goalType |= 1;
    }
    
    if (!d->conditionLiterals[1].empty() || !d->conditionNegativeLiterals[1].empty()) {
        triggerType |= 1;
    }
    
    if (!d->conditionNums[0].empty()) {
        goalType |= 2;
    }
    
    if (!d->conditionNums[1].empty()) {
        triggerType |=2;
    }
        
}



bool PreferenceFSA::goalOrTriggerIsSatisfied(const MinimalState * theState, const int & partIdx)
{
    
    #ifndef NDEBUG
    
    /**
     *  Truth value by assuming it's an AND clause over the specified constituents.
     *  Only makes sense for debugging purposes.  First value is whether it's
     *  defined, second value is what was decided upon.
     */
    pair<bool, bool> secondOpinion(false, false);
    
    if (false) {/// This assumes the domain does *not* use ADL - only uncomment it for debugging purposes
        secondOpinion.first = true;
        secondOpinion.second = true;
        
        {
            const list<int> & litList = pref->d->conditionLiterals[partIdx];
            
            list<int>::const_iterator lItr = litList.begin();
            const list<int>::const_iterator lEnd = litList.end();
            
            for (; lItr != lEnd; ++lItr) {
                if (theState->first.find(*lItr) == theState->first.end()) {
                    secondOpinion.second = false;
                    break;
                }
            }
        }
        
        if (secondOpinion.second) {
            const list<int> & numList = pref->d->conditionNums[partIdx];
            
            list<int>::const_iterator lItr = numList.begin();
            const list<int>::const_iterator lEnd = numList.end();
            
            for (; lItr != lEnd; ++lItr) {
                if (!RPGBuilder::getNumericPreTable()[*lItr].isSatisfiedWCalculate(theState->secondMin, theState->secondMax)) {
                    secondOpinion.second = false;
                    break;
                }
            }
        }
    }
    
    #endif
    
    NNF_Flat * const f = pref->d->flattened[partIdx];
    if (!f) {
        if (PreferenceHandler::preferenceDebug) {
            if (partIdx) {
                cout << "Preference's trigger considered to always be ";
            } else {                
                cout << "Preference's goal considered to always be ";
            }
            if (pref->d->nodes[partIdx].second) {
                cout << " true\n";
            }  else {
                cout << " false\n";
            }  
        
        }
        #ifndef NDEBUG
        if (secondOpinion.first) {
            assert(secondOpinion.second == pref->d->nodes[partIdx].second);
        }
        #endif
        return pref->d->nodes[partIdx].second;        
    }
    
    f->reset();
    
    if (PreferenceHandler::preferenceDebug && pref->cons != VAL::E_ATEND) {
        cout << "Before looking at the current state, the preference " << pref->name << ":" << prefIdx << " would be ";
        cout << positionName[theState->preferenceStatus[prefIdx]] << ", i.e. ";
        if (f->isSatisfied()) {
            cout << "satisfied\n";
        } else {
            cout << "unsatisfied\n";
        }
    }
    
    const NNF_Flat::Cell * const cells = f->getCells();
    const int cellCount = f->getCellCount();
    
    for (int c = 0; c < cellCount; ++c) {
        if (!(cells[c].isCell())) continue;
        
        if (cells[c].lit) {
            if (cells[c].polarity) {
                if (theState->first.find(cells[c].lit->getStateID()) != theState->first.end()) {
                    f->satisfy(c);
                }
            } else {
                if (theState->first.find(cells[c].lit->getStateID()) != theState->first.end()) {
                    f->unsatisfy(c);
                }
            }
        } else {
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[cells[c].num];
            if (cells[c].polarity) {
                if (currPre.isSatisfiedWCalculate(theState->secondMin,theState->secondMax)) {
                    f->satisfy(c);
                }
            } else {
                if (currPre.canBeUnsatisfiedWCalculate(theState->secondMin,theState->secondMax)) {
                    f->unsatisfy(c);
                }
            }
        }
    }
    
    const bool retVal = f->isSatisfied();
    
    #ifndef NDEBUG
    if (secondOpinion.first) {
        assert(secondOpinion.second == retVal);
    }
    #endif
    
    return retVal;
}

double cheapestRootedAt(list<Literal*> & answer, list<Literal*> & answerNegative,
                        list<int> * answerNumeric,
                        const int & node, const NNF_Flat::Cell * const cells,
                        const bool * cellIsAnAnd, const int * parentIDs, const int & cellCount, const EpsilonResolutionTimestamp & factLayerTime,
                        const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                        const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{

    if (cells[node].isCell()) {
        if (cells[node].lit) {
            if (!cells[node].polarity) {                
                if (negativeLiteralAchievedInLayer[cells[node].lit->getStateID()].isUndefined()) {
                    return DBL_MAX;
                } else {
                    // for now, return zero cost for achieved negative preconditions
                    answerNegative.push_back(cells[node].lit);
                    return 0.0;
                }
            } else {
                const list<CostedAchieverDetails> & currList = literalCosts[cells[node].lit->getStateID()];
                if (currList.empty()) { // then we've never seen it
                    return DBL_MAX;
                } else {
                    
                    if (factLayerTime.isInfinite()) {                
                        answer.push_back(cells[node].lit);
                        return currList.back().preferenceCosts.cost;
                    }
                    
                    list<CostedAchieverDetails>::const_reverse_iterator abItr = currList.rbegin();
                    
                    for (; abItr != currList.rend() && abItr->getLayer() > factLayerTime; ++abItr) ;
                    
                    if (abItr == currList.rend()) {
                        return DBL_MAX;
                    }
                    
                    answer.push_back(cells[node].lit);
                    return abItr->preferenceCosts.cost;
                }
            }                
        } else {
            if (answerNumeric) {
                assert(cells[node].polarity);
                if (!(*numericAchievedInLayer)[cells[node].num].isUndefined()) {
                    answerNumeric->push_back(cells[node].num);
                    return 0.0;
                } else {
                    return DBL_MAX;
                }
            } else {
                return 0.0;
            }
        }
    }

    double toReturn;
    if (cellIsAnAnd[node]) {        
        toReturn = 0.0;
        for (int c = node + 1; c < cellCount; ++c) {
            if (parentIDs[c] == node) {
                const double childCost = cheapestRootedAt(answer, answerNegative, answerNumeric, c, cells, cellIsAnAnd, parentIDs, cellCount, factLayerTime, literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
                if (childCost == DBL_MAX) {
                    // never seen fact, so this branch is false
                    return DBL_MAX;
                }
                toReturn += childCost;
            }
        }
    } else {
        toReturn = DBL_MAX;
        list<Literal*> incumbent;
        list<Literal*> incumbentNegative;
        list<int> incumbentNum;
        for (int c = node + 1; c < cellCount; ++c) {
            if (parentIDs[c] == node) {
                list<Literal*> tmp;
                list<Literal*> tmpNegative;
                list<int> tmpNum;
                const double childCost = cheapestRootedAt(tmp, tmpNegative, (answerNumeric ? &tmpNum : (list<int>*) 0), c, cells, cellIsAnAnd, parentIDs, cellCount, factLayerTime, literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
                if (childCost != DBL_MAX) {
                    if (childCost < toReturn) {
                        toReturn = childCost;
                        tmp.swap(incumbent);
                        tmpNegative.swap(incumbentNegative);
                        if (answerNumeric) {
                            tmpNum.swap(incumbentNum);
                        }
                    }
                }
            }
        }
        if (toReturn != DBL_MAX) {
            answer.insert(answer.end(), incumbent.begin(), incumbent.end());
            answerNegative.insert(answerNegative.end(), incumbentNegative.begin(), incumbentNegative.end());
            if (answerNumeric) {
                answerNumeric->insert(answerNumeric->end(), incumbentNum.begin(), incumbentNum.end());
            }
        }
    }
    
    return toReturn;
}

void PreferenceFSA::satisfyAtLowCost(const NNF_Flat * flattened,
                                     const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                     const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer,
                                     list<list<Literal*> > & dest, list<list<Literal*> > & destNegative, list<list<int> > * destNumeric)
{
    const NNF_Flat::Cell * const cells = flattened->getCells();
    const int cellCount = flattened->getCellCount();
    const bool * cellIsAnAnd = flattened->cellIsAnAnd();
    const int * const parentIDs = flattened->getParentIDs();
    
    dest.push_back(list<Literal*>());
    destNegative.push_back(list<Literal*>());
    
    list<Literal*> & answer = dest.back();
    list<Literal*> & answerNegative = destNegative.back();

    list<int> * answerNumeric = 0;
    
    if (destNumeric) {
        destNumeric->push_back(list<int>());
        answerNumeric = &(destNumeric->back());
    }
    
    cheapestRootedAt(answer, answerNegative, answerNumeric, 0, cells, cellIsAnAnd, parentIDs, cellCount, EpsilonResolutionTimestamp::infinite(), literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
}

void PreferenceFSA::getPreconditionsToSatisfy(list<Literal*> & literals, list<Literal*> & negativeLiterals, 
                                              list<int> * numericPres, const bool & theTrigger, const EpsilonResolutionTimestamp & factLayerTime,
                                              const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                              const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    const NNF_Flat * const flattened = pref->d->flattened[(theTrigger ? 1 : 0)];
    
    if (!flattened) return;
    
    const NNF_Flat::Cell * const cells = flattened->getCells();
    const int cellCount = flattened->getCellCount();
    const bool * cellIsAnAnd = flattened->cellIsAnAnd();
    const int * const parentIDs = flattened->getParentIDs();
    
    cheapestRootedAt(literals, negativeLiterals, numericPres, 0, cells, cellIsAnAnd, parentIDs, cellCount, factLayerTime, literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
}
                                                  

/// common code

namespace PrefCommon {

    /**
     *  Work out if the addition of one fact can trigger a preference - either then
     *  breaking a precarious at-most-once, or a sometime before, or a sometime after.
     */
    void workOutIfAddingOneThingCanTrigger(bool & addingOneThingCanTrigger,
                                           list<ConditionAndPolarity> & addingThisWouldTrigger,
                                           PreferenceData * d, const int & partIdx)
    {
        static const bool oneThingDebug = false;
        
        addingOneThingCanTrigger = true;
        
        /*const int litTrigCount = d->conditionLiterals[partIdx].size();
        const int negativeLitTrigCount = d->conditionNegativeLiterals[partIdx].size();
        const int numTrigCount = d->conditionNums[partIdx].size();
        const int negativeNumTrigCount = d->conditionNegativeNums[partIdx].size();
        
        if (litTrigCount + negativeLitTrigCount + numTrigCount + negativeNumTrigCount == 0) {
            addingOneThingCanTrigger = false;
            return;        
        }*/
        
        if (!d->flattened[partIdx]) {
            addingOneThingCanTrigger = false;
            return;
        }
        
        const int nodeCount = d->flattened[partIdx]->getInteriorNodeCount();
        
        if (nodeCount != 1) {
            addingOneThingCanTrigger = false;
            if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                cout << "Cannot find a single possible trigger - NNF tree contains " << nodeCount << " interior nodes, rather than 1\n";
            }
            return;
        }
        
        const NNF_Flat::Cell * const cells = d->flattened[partIdx]->getCells();
        const int cellCount = d->flattened[partIdx]->getCellCount();
        const bool * const cellIsAnAnd = d->flattened[partIdx]->cellIsAnAnd();
        const int * const parentIDs = d->flattened[partIdx]->getParentIDs();
        
        if (cellIsAnAnd[0]) {
            if (cellCount > 2) {
                addingOneThingCanTrigger = false;
                if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                    cout << "Cannot find a single possible trigger - NNF tree has an AND at the root, and " << (cellCount - 1) << " leaves\n";
                }
                return;
            }
        }
        
        if (PreferenceHandler::preferenceDebug || oneThingDebug) {
            cout << "Preference can be triggered by:\n";
        }
        
        for (int ci = 1; ci < cellCount; ++ci) {
            assert(parentIDs[ci] == 0);
            assert(cells[ci].isCell());
            
            if (cells[ci].lit) {
                if (cells[ci].polarity) {
                    if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                        cout << "\t" << *(cells[ci].lit) << endl;
                    }
                    addingThisWouldTrigger.push_back(ConditionAndPolarity(cells[ci].lit->getStateID(), false, true));        
                } else {
                    if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                        cout << "\t¬" << *(cells[ci].lit) << endl;
                    }                    
                    addingThisWouldTrigger.push_back(ConditionAndPolarity(cells[ci].lit->getStateID(), false, false));
                }
            } else {
                if (cells[ci].polarity) {
                    if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                        cout << "\t" << RPGBuilder::getNumericPreTable()[cells[ci].num] << endl;
                    }                    
                    addingThisWouldTrigger.push_back(ConditionAndPolarity(cells[ci].num, true, true));
                } else {
                    if (PreferenceHandler::preferenceDebug || oneThingDebug) {
                        cout << "\t¬" << RPGBuilder::getNumericPreTable()[cells[ci].num] << endl;
                    }                                        
                    addingThisWouldTrigger.push_back(ConditionAndPolarity(cells[ci].num, true, false));
                }
            }
        }                        
    }
    
    void getSubsumedPresAndEffs(list<int> & presOut, list<int> & effsOut, const int & numCondID, const bool & polarity) {
        presOut.push_back(numCondID);
                        
        const vector<RPGBuilder::RPGNumericPrecondition> & numPres = RPGBuilder::getNumericPreTable();
        
        const int PNECount = RPGBuilder::getPNECount();

        int masterVar;
        VAL::comparison_op op;
        double constVal;
        
                
        {
            const RPGBuilder::RPGNumericPrecondition & master = numPres[numCondID];
            
            masterVar = master.LHSVariable;           
            constVal = master.RHSConstant;
        
            if (master.LHSVariable < PNECount) {
                op = master.op;
            } else if (master.LHSVariable < 2 * PNECount) {
                masterVar -= PNECount;
                if (master.RHSConstant != 0.0) {
                    constVal = -master.RHSConstant;
                }
                if (master.op == VAL::E_GREATER) {
                    op = VAL::E_LESS;
                } else {
                    op = VAL::E_LESSEQ;
                }             
            } else {
                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(master.LHSVariable);
                
                if (currAV.size != 1) return;
                
                masterVar = currAV.fluents[0];
                constVal -= currAV.constant;
                
                constVal /= currAV.weights[0];
                
                if (masterVar < PNECount) {
                    op = master.op;
                } else {
                    masterVar -= PNECount;
                    if (constVal != 0.0) {
                        constVal = -constVal;
                    }
                    if (master.op == VAL::E_GREATER) {
                        op = VAL::E_LESS;
                    } else {
                        op = VAL::E_LESSEQ;
                    }
                }
            }
        }
        
        assert(polarity);
                
        {
            const int loopLim = numPres.size();
           
            for (int p = 0; p < loopLim; ++p) {
                if (p == numCondID) continue;
                if (numPres[p].LHSVariable < PNECount) {
                    assert(numPres[p].op == VAL::E_GREATER || numPres[p].op == VAL::E_GREATEQ);
                    if (masterVar == numPres[p].LHSVariable
                        && (op == VAL::E_GREATER || op == VAL::E_GREATEQ)) {                        
                        
                        if (numPres[p].op == op) {
                            if (numPres[p].RHSConstant >= constVal) {
                                presOut.push_back(p);
                            }
                        } else if (numPres[p].op == VAL::E_GREATER && op == VAL::E_GREATEQ) {
                            if (numPres[p].RHSConstant >= constVal) {
                                presOut.push_back(p);
                            }
                        } else if (numPres[p].op == VAL::E_GREATEQ && op == VAL::E_GREATER) {
                            if (numPres[p].RHSConstant >= constVal + 0.001) {
                                presOut.push_back(p);
                            }
                        } else {
                            assert(false);
                        }
                    }
                } else if (numPres[p].RHSVariable < (2 * PNECount)) {
                    const double flipped = (numPres[p].RHSConstant != 0.0 ? -numPres[p].RHSConstant : 0.0);
                    if (masterVar == numPres[p].LHSVariable - PNECount
                        && (op == VAL::E_LESS || op == VAL::E_LESSEQ)) {                        
                        const VAL::comparison_op flippedOp = (numPres[p].op == VAL::E_GREATER ? VAL::E_LESS : VAL::E_LESSEQ);
                        
                        if (flippedOp == op) {
                            if (flipped <= constVal) {
                                presOut.push_back(p);
                            }
                        } else if (flippedOp == VAL::E_LESS && op == VAL::E_LESSEQ) {
                            if (flipped <= constVal) {
                                presOut.push_back(p);
                            }
                        } else if (flippedOp == VAL::E_LESSEQ && op == VAL::E_LESS) {
                            if (flipped <= constVal - 0.001) {
                                presOut.push_back(p);
                            }
                        } else {
                            assert(false);
                        }
                    }
                } else {
                    const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(numPres[p].LHSVariable);
                    
                    if (currAV.size != 1) continue;
                    
                    double newRHS = numPres[p].RHSConstant - currAV.constant;
                    
                    assert(fabs(currAV.weights[0] - 1.0) < 0.00001);
                    
                    if (currAV.fluents[0] < PNECount) {
                        if (masterVar == currAV.fluents[0]) {
                            if (numPres[p].op == op) {
                                if (newRHS >= constVal) {
                                    presOut.push_back(p);
                                }
                            } else if (numPres[p].op == VAL::E_GREATER && op == VAL::E_GREATEQ) {
                                if (newRHS >= constVal) {
                                    presOut.push_back(p);
                                }
                            } else if (numPres[p].op == VAL::E_GREATEQ && op == VAL::E_GREATER) {
                                if (newRHS >= constVal + 0.001) {
                                    presOut.push_back(p);
                                }
                            } else {
                                assert(false);
                            }
                        }
                    } else {
                        
                        if (masterVar == (currAV.fluents[0] - PNECount)
                            && (op == VAL::E_LESS || op == VAL::E_LESSEQ)) {                        
                            
                            const double flipped = (newRHS == 0.0 ? 0.0 : -newRHS);
                            const VAL::comparison_op flippedOp = (numPres[p].op == VAL::E_GREATER ? VAL::E_LESS : VAL::E_LESSEQ);
                            
                            if (flippedOp == op) {
                                if (flipped <= constVal) {
                                    presOut.push_back(p);
                                }
                            } else if (flippedOp == VAL::E_LESS && op == VAL::E_LESSEQ) {
                                if (flipped <= constVal) {
                                    presOut.push_back(p);
                                }
                            } else if (flippedOp == VAL::E_LESSEQ && op == VAL::E_LESS) {
                                if (flipped <= constVal - 0.001) {
                                    presOut.push_back(p);
                                }
                            } else {
                                assert(false);
                            }
                        }
                        
                    }
                                    
                }
            }
        }
        
        double minEffect;
        
        if (op == VAL::E_GREATER || op == VAL::E_GREATEQ) {
            const double B = NumericAnalysis::getVariableBounds()[masterVar].first;
            if (B == -DBL_MAX) return;
            minEffect = constVal - B;
        } else {
            const double B = NumericAnalysis::getVariableBounds()[masterVar].second;
            if (B == DBL_MAX) return;
            minEffect = constVal - B;
        }
        
        static const bool localDebug = false;
        static const int pneCount = RPGBuilder::getPNECount();
        {
            const vector<RPGBuilder::RPGNumericEffect> & numEffs = RPGBuilder::getNumericEff();
            
            const int effCount = numEffs.size();
            
            for (int e = 0; e < effCount; ++e) {
                
                if (numEffs[e].fluentIndex != masterVar) continue;
                
                if (localDebug) {
                    cout << "Seeing if " << numEffs[e] << " implies " << numPres[numCondID] << endl;
                }
                
                bool fitsInEveryCase = true;
                bool everSeen = false;

                for (int condPass = 0; fitsInEveryCase && condPass < 2; ++condPass) {
                    if (condPass == 1 && NumericAnalysis::getNumericEffectsThatAreInConditionalEffects().find(e) == NumericAnalysis::getNumericEffectsThatAreInConditionalEffects().end()) {
                        continue;
                    }
                    const list<pair<int, Planner::time_spec> > & acts = (condPass ? NumericAnalysis::getNumericEffectsThatAreInConditionalEffects().find(e)->second
                                                                                  : RPGBuilder::getRpgNumericEffectsToActions()[e]);
                    
                    list<pair<int, Planner::time_spec> >::const_iterator actItr = acts.begin();
                    const list<pair<int, Planner::time_spec> >::const_iterator actEnd = acts.end();
                    
                    for (; fitsInEveryCase && actItr != actEnd; ++actItr) {                    
                    
                        
                        if (localDebug) {
                            cout << "  Found on " << *(RPGBuilder::getInstantiatedOp(actItr->first)) << ", ";
                            if (actItr->second == Planner::E_AT_START) {
                                cout << "start\n";
                            } else {
                                cout << "end\n";
                            }
                        }
                        
                        everSeen = true;
                        
                        NumericAnalysis::MaskedVariableBounds localBounds;
                                            
                        const list<int> & actPres = (actItr->second == Planner::E_AT_END ? RPGBuilder::getEndPreNumerics()[actItr->first]
                                                                                         : RPGBuilder::getStartPreNumerics()[actItr->first]);
                        
                        list<int>::const_iterator apItr = actPres.begin();
                        const list<int>::const_iterator apEnd = actPres.end();
                        
                        for (; apItr != apEnd; ++apItr) {
                            bool thisPreCouldBeBuilt = false;
                            VarOpConst currPre(RPGBuilder::getNumericPreTable()[*apItr], thisPreCouldBeBuilt);
                            
                            if (thisPreCouldBeBuilt) {
                                if (currPre.op == VAL::E_GREATER || currPre.op == VAL::E_GREATEQ) {
                                    localBounds.tightenLower(currPre.var, currPre.constant);
                                    if (localDebug) {
                                        cout << "    Locally, the lower bound on " << *(RPGBuilder::getPNE(currPre.var)) << " is " << currPre.constant << endl;
                                    }
                                } else {
                                    localBounds.tightenUpper(currPre.var, currPre.constant);
                                    if (localDebug) {
                                        cout << "    Locally, the upper bound on " << *(RPGBuilder::getPNE(currPre.var)) << " is " << currPre.constant << endl;
                                    }
                                }
                            }
                        }
                        
                        localBounds.tightenLower(-3, RPGBuilder::getOpMinDuration(actItr->first, -1));
                        localBounds.tightenUpper(-3, RPGBuilder::getOpMaxDuration(actItr->first, -1));
                        
                        for (int pass = 0; fitsInEveryCase && pass < 2; ++pass) {
                            double localBoundToUpdate = numEffs[e].constant;
                            
                            for (int term = 0; term < numEffs[e].size; ++term) {

                                double relevantBound;
                                switch (numEffs[e].variables[term]) {
                                    case -3: {
                                        // ?duration - assume in range [epsilon, infinity]
                                        relevantBound = numEffs[e].weights[term] * (pass ? localBounds[-3].second : localBounds[-3].first);
                                        break;
                                    }
                                    case -19: {
                                        // -?duration - assume in range [-infinity, -epsilon]
                                        relevantBound = numEffs[e].weights[term] * (pass ? -localBounds[-3].first : -localBounds[-3].second);
                                        break;
                                    }
                                    default: {
                                        assert(numEffs[e].variables[term] >= 0);
                                        if (numEffs[e].variables[term] >= pneCount) {
                                            relevantBound = -numEffs[e].weights[term] * (pass ? localBounds[numEffs[e].variables[term] - pneCount].first : localBounds[numEffs[e].variables[term] - pneCount].second);
                                        } else {
                                            relevantBound = numEffs[e].weights[term] * (pass ? localBounds[numEffs[e].variables[term]].second : localBounds[numEffs[e].variables[term]].first);
                                        }
                                    }
                                }
                                if (localDebug) {
                                    cout << "   Contribution from term " << term << " = " << relevantBound << endl;
                                }
                                localBoundToUpdate += relevantBound;
                            }

                            if (numEffs[e].isAssignment) {
                                switch (op) {
                                    case VAL::E_GREATEQ: {
                                        if (localBoundToUpdate < constVal) {
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                            fitsInEveryCase = false;
                                        }
                                        break;
                                    }
                                    case VAL::E_GREATER: {
                                        if (localBoundToUpdate <= constVal) {
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    case VAL::E_LESSEQ: {
                                        if (localBoundToUpdate > constVal) {
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    case VAL::E_LESS: {
                                        if (localBoundToUpdate >= constVal) {
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        assert(false);
                                    }
                                }
                            } else {
                                const double preValue = (pass ? localBounds[masterVar].second : localBounds[masterVar].first);
                                switch (op) {
                                    case VAL::E_GREATEQ: {
                                        if (preValue == -DBL_MAX || localBoundToUpdate == -DBL_MAX
                                            || (preValue + localBoundToUpdate) < constVal) {

                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    case VAL::E_GREATER: {
                                        if (preValue == -DBL_MAX || localBoundToUpdate == -DBL_MAX
                                            || (preValue + localBoundToUpdate) <= constVal) {
                                            
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    case VAL::E_LESSEQ: {
                                        if (preValue == DBL_MAX || localBoundToUpdate == DBL_MAX
                                            || (preValue + localBoundToUpdate) > constVal) {
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    case VAL::E_LESS: {
                                        if (preValue == DBL_MAX || localBoundToUpdate == DBL_MAX
                                            || (preValue + localBoundToUpdate) >= constVal) {
                                            fitsInEveryCase = false;
                                            if (localDebug) {
                                                cout << "    ** Effect does not imply condition\n";
                                            }
                                        }
                                        break;
                                    }
                                    default: {
                                        assert(false);
                                    }
                                }
                                
                            }
                            
                        }
                    }
                }
                
                if (everSeen && fitsInEveryCase) {
                    if (localDebug) {
                        cout << " Yes - effect implies condition in every case\n";
                    }
                    effsOut.push_back(e);
                } else {
                    if (localDebug) {
                        if (!everSeen) {
                            cout << " No - effect never seen\n";
                        }
                        if (fitsInEveryCase) {
                            cout << " No - does not imply in every case\n";   
                        }
                    }
                }
            }
        }
        
    }
    
    void actionsWhichMeanWeHad(set<pair<int,Planner::time_spec> > & actVariables, list<ConditionAndPolarity> & addingThisWouldTriggerList)    
    {
        list<ConditionAndPolarity>::iterator tItr = addingThisWouldTriggerList.begin();
        const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTriggerList.end();
        
        for (; tItr != tEnd; ++tItr) {
            ConditionAndPolarity & addingThisWouldTrigger = *tItr;
            if (!addingThisWouldTrigger.second) {
                
                
                const int litID = addingThisWouldTrigger.first;
                const bool polarity = addingThisWouldTrigger.polarity;
                
                if (polarity) {
                    const vector<list<pair<int, Planner::time_spec> > > & preToAction = RPGBuilder::getPresToActions();
                    
                    list<pair<int, Planner::time_spec> >::const_iterator wpItr = preToAction[litID].begin();
                    const list<pair<int, Planner::time_spec> >::const_iterator wpEnd = preToAction[litID].end();
                    
                    for (; wpItr != wpEnd; ++wpItr) {
                        //assert(wpItr->second == VAL::E_AT_START);
                        actVariables.insert(*wpItr);
                    }
                }
                
                {
                    const vector<list<pair<int, Planner::time_spec> > > & eta = (polarity ? RPGBuilder::getEffectsToActions() : RPGBuilder::getNegativeEffectsToActions());
                    
                    list<pair<int, Planner::time_spec> >::const_iterator wpItr = eta[litID].begin();
                    const list<pair<int, Planner::time_spec> >::const_iterator wpEnd = eta[litID].end();
                    
                    for (; wpItr != wpEnd; ++wpItr) {
                        //assert(wpItr->second == VAL::E_AT_START);
                        actVariables.insert(*wpItr);
                    }
                }
                if (PreferenceHandler::preferenceDebug) {
                    cout << "The following actions mean any trajectory contains ";
                    if (!polarity) cout << "¬";
                    cout << *(RPGBuilder::getLiteral(litID)) << ":\n";
                }
                            
            } else {
                                    
                const int numCondID = addingThisWouldTrigger.first;
                const bool polarity = addingThisWouldTrigger.polarity;
                
                list<int> plusRelated;
                list<int> effRelated;
                
                getSubsumedPresAndEffs(plusRelated, effRelated, numCondID, polarity);
                
                {
                    const vector<list<pair<int, Planner::time_spec> > > & numPreToAction = RPGBuilder::getProcessedRPGNumericPreconditionsToActions();
                
                    list<int>::const_iterator prItr = plusRelated.begin();
                    const list<int>::const_iterator prEnd = plusRelated.end();
                    
                    for (; prItr != prEnd; ++prItr) {
                        list<pair<int, Planner::time_spec> >::const_iterator wpItr = numPreToAction[*prItr].begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator wpEnd = numPreToAction[*prItr].end();
                        
                        for (; wpItr != wpEnd; ++wpItr) {
                            //assert(wpItr->second == VAL::E_AT_START);
                            actVariables.insert(*wpItr);
                        }
                    }
                }
                
                {
                 
                    const vector<list<pair<int, Planner::time_spec> > > & eta = RPGBuilder::getRpgNumericEffectsToActions();
                    list<int>::const_iterator prItr = effRelated.begin();
                    const list<int>::const_iterator prEnd = effRelated.end();
                    
                    for (; prItr != prEnd; ++prItr) {
                        list<pair<int, Planner::time_spec> >::const_iterator wpItr = eta[*prItr].begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator wpEnd = eta[*prItr].end();
                        
                        for (; wpItr != wpEnd; ++wpItr) {
                            //assert(wpItr->second == VAL::E_AT_START);
                            actVariables.insert(*wpItr);
                        }
                    }
                }
                if (PreferenceHandler::preferenceDebug) {
                    cout << "The following actions mean any trajectory contains ";
                    if (!polarity) cout << "¬";
                    cout << (RPGBuilder::getNumericPreTable()[numCondID]) << ":\n";
                }
            }
            
            if (PreferenceHandler::preferenceDebug) {
                set<pair<int,Planner::time_spec> >::const_iterator avpItr = actVariables.begin();
                const set<pair<int,Planner::time_spec> >::const_iterator avpEnd= actVariables.end();
                
                for (; avpItr != avpEnd; ++avpItr) {
                    cout << "\t" << *(RPGBuilder::getInstantiatedOp(avpItr->first)) << "\n";
                }
            }
        }
    }
    
    
    
    
};


/// always constraints                        

AlwaysFSA::AlwaysFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p)
{
    assert(pref->cons == VAL::E_ALWAYS);    
    initPosn = AutomatonPosition::satisfied;
}

bool AlwaysFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool alwaysUpdateDebug = false;
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return (pref->cost != DBL_MAX);
    }
    
    assert(!goalOrTriggerChanged.second);
    
    if (!goalOrTriggerChanged.first) {
        return true;
    }
    
    if (goalOrTriggerIsSatisfied(state, 0)) {
        // preference still holds after being potentially perturbed
        // update recorded support
        
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
            cerr << "Fatal internal error: could not satisfy NNF tree of always preference that is true\n";
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
        
    } else {
        state->preferenceStatus[prefIdx] = AutomatonPosition::unreachable;
        if (alwaysUpdateDebug || PreferenceHandler::preferenceDebug) cout << "Preference " << pref->name << " is now violated\n";        
        return (pref->cost != DBL_MAX);
    }
    
    return true;
      
}

double AlwaysFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (PreferenceHandler::preferenceDebug) {
            cout << pref->name << ") cost is " << pref->cost << " because the always condition has been broken\n";
        }
        return pref->cost;
    }
    
    return 0.0;
}

double AlwaysFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
        
    return 0.0;
}

double AlwaysFSA::GCost(const MinimalState * state, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
            
    return 0.0;
}

                        

void AlwaysFSA::getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &)
{
    // Don't actually try to satisfy always preferences - just avoid breaking them
    return;
}

void AlwaysFSA::getCostsOfDeletion(const MinimalState & theState, map<int, set<int> > & factCost, map<int, map<double, set<int> > > & numChangeCost)
{
    if (theState.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) return;
    
    static const int varCount = RPGBuilder::getPNECount();
    
    const double pCost = pref->cost;
    
    if (pCost == 0.0) return;

    NNF_Flat * const f = pref->d->flattened[0];
    if (!f) return;
    
    const bool * const cellIsAnAnd = f->cellIsAnAnd();
    
    if (!cellIsAnAnd[0]) return;
            
    const NNF_Flat::Cell * const cells = f->getCells();
    const int * parentIDs = f->getParentIDs();
    const int cellCount = f->getCellCount();
    
    int fID;
    
    for (int c = 0; c < cellCount; ++c) {
        if (!(cells[c].isCell())) continue;
        if (parentIDs[c] != 0) continue;
        
        if (cells[c].lit) {
            if (cells[c].polarity) {
                fID = cells[c].lit->getStateID();
                assert(theState.first.find(fID) != theState.first.end());
                factCost[fID].insert(prefIdx);
            }
        } else {
            if (cells[c].polarity) {
                RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[cells[c].num];
                
                if (currPre.LHSVariable < varCount) {
                    double delta = currPre.RHSConstant - theState.secondMax[currPre.LHSVariable];
                    if (delta >= 0.0) delta = -1e-6;
                    numChangeCost[currPre.LHSVariable][delta].insert(prefIdx);
                } else if (currPre.LHSVariable < 2 * varCount) {
                    double delta = -currPre.RHSConstant - theState.secondMin[currPre.LHSVariable - varCount];
                    if (delta <= 0.0) delta = 1e-6;
                    numChangeCost[currPre.LHSVariable - varCount][delta].insert(prefIdx);
                } else {
                    const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                    if (currAV.size == 1) {
                        double rhc = currPre.RHSConstant - currAV.constant;
                        rhc /= currAV.weights[0];
                        
                        if (currAV.fluents[0] < varCount) {
                            double delta = rhc - theState.secondMax[currAV.fluents[0]];
                            if (delta >= 0.0) delta = -1e-6;
                            numChangeCost[currAV.fluents[0]][delta].insert(prefIdx);
                        } else {
                            double delta = -rhc - theState.secondMin[currAV.fluents[0] - varCount];
                            if (delta <= 0.0) delta = 1e-6;
                            numChangeCost[currAV.fluents[0] - varCount][delta].insert(prefIdx);
                        }
                    }
                }
            }
        }
    }
    
}

                                
/// at end constraints                        

AtEndFSA::AtEndFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p)
{
    assert(pref->cons == VAL::E_ATEND);    
    initPosn = AutomatonPosition::unsatisfied;
}

bool AtEndFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: at-end pref " << pref->name << " is unreachable, cost " << pref->cost << "\n";
            assert(!goalOrTriggerIsSatisfied(state, 0));
        }
        return (pref->cost != DBL_MAX);
    }                
    
    assert(!goalOrTriggerChanged.second);
    
    if (goalOrTriggerIsSatisfied(state, 0)) {
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: at-end pref " << pref->name << " is currently satisfied, cost " << pref->cost << "\n";
        
        // we don't need to put dummy steps in for at-ends, because if they're true at the end of the plan, they're true.
        
        /*chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
            cerr << "Fatal internal error: could not satisfy NNF tree of at-end preference\n";
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }*/
        
        state->preferenceStatus[prefIdx] = AutomatonPosition::satisfied;            
    } else {
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: at-end pref " << pref->name << " is currently unsatisfied, cost " << pref->cost << "\n";        
        state->preferenceStatus[prefIdx] = AutomatonPosition::unsatisfied;
    }

    return true;
      
}

double AtEndFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (!(preferenceStatus[prefIdx] == AutomatonPosition::satisfied)) {
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": at-end pref " << pref->name << " is currently unsatisfied, cost " << pref->cost << "\n";
        return pref->cost;
    }
    
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": at-end pref " << pref->name << " is currently satisfied\n";
    return 0.0;
}

double AtEndFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
        
    return 0.0;
}

double AtEndFSA::GCost(const MinimalState * state, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
            
    return 0.0;
}



void AtEndFSA::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        // If it was unreachable before, it's still unreachable now, so don't try to get it
        return;
    }    
    if (!pref->d->flattened[0]) return;
    toFill[0] = pref->d->flattened[0];
    toFill[0]->reset();
}

void AtEndFSA::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                               list<list<int> > * desiredNumeric,
                               const MinimalState & startState,
                               const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                               const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                               const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    if (startState.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || startState.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]->isSatisfied()) return;
    
    satisfyAtLowCost(unsatisfiedPreferenceConditions[prefIdx][0], literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer, desired, desiredNegative, desiredNumeric);
    
}


void AtEndFSA::updateCosts(const MinimalState & initialState,
                            const bool & wasTheTrigger,
                            vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                            map<int, AddingConstraints > & prefCostOfAddingFact,
                            map<int, map<double, AddingConstraints > > & numChangeCost,
                            list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
                                      
    if (wasTheTrigger) return;
    
    if (PreferenceHandler::preferenceDebug) {
        cout << "\t\t- At end preference " << pref->name << ", index " << prefIdx << " is satisfied\n";
    }
    
    optimisticAutomataPositions[prefIdx] = AutomatonPosition::satisfied;
    
}

/// sometime constraints

SometimeFSA::SometimeFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p)
{
    assert(pref->cons == VAL::E_SOMETIME);    
    initPosn = AutomatonPosition::unsatisfied;
}

bool SometimeFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool sometimeUpdateDebug = false;
    
    assert(!goalOrTriggerChanged.second);
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied || state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (sometimeUpdateDebug || PreferenceHandler::preferenceDebug) {
            if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied) {
                cout << prefIdx << ": update: sometime pref " << pref->name << " has already been eternally satisfied, cost " << pref->cost << "\n";
            } else {
                cout << prefIdx << ": update: sometime pref " << pref->name << " cannot be satisfied from here, cost " << pref->cost << "\n";
                assert(!goalOrTriggerIsSatisfied(state, 0));
            }
        }
        if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied) {
            return true;
        } else {
            return (pref->cost != DBL_MAX);
        }
    }
    
    if (goalOrTriggerIsSatisfied(state,0)) {
        if (sometimeUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime pref " << pref->name << " is probably eternally satisfied, cost " << pref->cost << "\n";
        state->preferenceStatus[prefIdx] = AutomatonPosition::probablyeternallysatisfied;        
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
            cerr << "Fatal internal error: could not satisfy NNF tree of sometime preference\n";
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
    } else {
        if (sometimeUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime pref " << pref->name << " is currently " << positionName[state->preferenceStatus[prefIdx]] << ", cost " << pref->cost << "\n";                
    }

    return true;
      
}

double SometimeFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (   preferenceStatus[prefIdx] != AutomatonPosition::eternallysatisfied
        && preferenceStatus[prefIdx] != AutomatonPosition::probablyeternallysatisfied
        && preferenceStatus[prefIdx] != AutomatonPosition::satisfied) {
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": sometime pref " << pref->name << " is currently " << positionName[preferenceStatus[prefIdx]] << ", cost " << pref->cost << "\n";
        return pref->cost;
    }
    
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": sometime pref " << pref->name << " is satisfied\n";
    return 0.0;
}

double SometimeFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
        
    return 0.0;
}

double SometimeFSA::GCost(const MinimalState * state, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
            
    return 0.0;
}


void SometimeFSA::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (state.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        // Once we've had a sometime preference, or shown it to be unreachable, we don't need to try to get it again
        return;
    }
    if (!pref->d->flattened[0]) return;
    toFill[0] = pref->d->flattened[0];
    toFill[0]->reset();
}

void SometimeFSA::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                                  list<list<int> > * desiredNumeric,
                                  const MinimalState & startState,
                                  const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                  const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                  const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    if (startState.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || startState.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]->isSatisfied()) return;
            
    satisfyAtLowCost(unsatisfiedPreferenceConditions[prefIdx][0], literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer, desired, desiredNegative, desiredNumeric);
    
}

void SometimeFSA::updateCosts(const MinimalState & initialState,
                               const bool & wasTheTrigger,
                               vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                               map<int, AddingConstraints > & prefCostOfAddingFact,
                               map<int, map<double, AddingConstraints > > & numChangeCost,
                               list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
   
    if (wasTheTrigger) return;
       
    optimisticAutomataPositions[prefIdx] = AutomatonPosition::satisfied;
   
}

/// at-most-once constraints

AtMostOnceFSA::AtMostOnceFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p), triggerPartCount(0)
{
    assert(pref->cons == VAL::E_ATMOSTONCE);
    initPosn = AutomatonPosition::satisfied;
 
    PrefCommon::workOutIfAddingOneThingCanTrigger(addingOneThingCanTrigger, addingThisWouldTrigger,
                                                  pref->d, 0);

    if (addingOneThingCanTrigger) {
        PrefCommon::actionsWhichMeanWeHad(actionsImplyingTrigger, addingThisWouldTrigger);
    }
                                                                                                
}

bool AtMostOnceFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool atMostOnceUpdateDebug = false;
 
    assert(!goalOrTriggerChanged.second);
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " cannot be satisfied from here, cost " << pref->cost << "\n";
        }
        return (pref->cost != DBL_MAX);
    }
    
    const bool allPresent = goalOrTriggerIsSatisfied(state, 0);
        
    chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
    chosen.back().satisfyIt = allPresent;
    
    if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back()) != allPresent) {
        if (allPresent) {
            cerr << "Fatal internal error: could not satisfy NNF tree of at-most-once preference\n";
        } else {
            cerr << "Fatal internal error: could not unsatisfy NNF tree of at-most-once preference\n";
        }
        pref->d->nodes[0].first->write(cerr);
        cerr << endl;
        exit(1);
    }
    
    switch (state->preferenceStatus[prefIdx]) {
        case AutomatonPosition::satisfied:
        {
            if (allPresent) {
                state->preferenceStatus[prefIdx] = AutomatonPosition::seenoncealreadyandstillholds;
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " has now been seen once\n";
                }                
                return true;
            } else {
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " still never been seen\n";
                }                
                return true;
            }           
        }
        case AutomatonPosition::seenoncealreadyandstillholds:
        {
            if (allPresent) {
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " has been seen once, and still holds\n";
                }
                return true;
            } else {
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " has been seen once, but doesn't currently hold\n";
                }
                state->preferenceStatus[prefIdx] = AutomatonPosition::seenoncealready;
                return true;
            }

        }
        case AutomatonPosition::seenoncealready:
        {
            if (allPresent) {
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " has been violated - now seen twice - cost = " << pref->cost << endl;
                }
                state->preferenceStatus[prefIdx] = AutomatonPosition::unreachable;
                return (pref->cost != DBL_MAX);
            } else {
                if (atMostOnceUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: at-most-once pref " << pref->name << ":" << prefIdx << " has been seen once, and still doesn't currently hold\n";
                }
                return true;
            }

        }
        default:
        {
            cerr << "Internal error - should not have preference status " << positionName[state->preferenceStatus[prefIdx]] << " for the at-most-once preference " << pref->name << ":" << prefIdx << endl;
            exit(1);
        }
    }
    
    return true;
}

double AtMostOnceFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": at-most-once pref " << pref->name << " cannot be satisfied, cost " << pref->cost << "\n";
        return pref->cost;
    }
            
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": at-most-once pref " << pref->name << " is cost free: " << positionName[preferenceStatus[prefIdx]] << endl;
    return 0.0;
}

double AtMostOnceFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        return pref->cost;
    }
                
    return 0.0;
}

double AtMostOnceFSA::GCost(const MinimalState * state, const int & flag)
{
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        return pref->cost;
    }
                    
    return 0.0;
}
void AtMostOnceFSA::getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &)
{
    // Don't actually try to satisfy at-most-once preferences - just avoid breaking them
}

void AtMostOnceFSA::getCostsOfAdding(const MinimalState & theState, map<int, AddingConstraints > & factCost, map<int, map<double, AddingConstraints > > & numChangeCost)
{
    if (theState.preferenceStatus[prefIdx] != AutomatonPosition::seenoncealready) return;
    if (!addingOneThingCanTrigger) return;

    static const int varCount = RPGBuilder::getPNECount();
    
    const double pCost = pref->cost;
    
    if (pCost == 0.0) return;
    
    
    list<ConditionAndPolarity>::iterator tItr = addingThisWouldTrigger.begin();
    const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTrigger.end();
    
    for (; tItr != tEnd; ++tItr) {
        if (!tItr->polarity) {
            /// TODO - Implement negative triggers
            continue;
        }
                        
        if (tItr->second) {
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[tItr->first];
            
            if (currPre.LHSVariable < varCount) {
                double delta = currPre.RHSConstant - theState.secondMin[currPre.LHSVariable];
                if (delta >= 0.0) delta = -1e-6;
                numChangeCost[currPre.LHSVariable][delta].addingWillViolate.insert(prefIdx);
            } else if (currPre.LHSVariable < 2 * varCount) {
                double delta = -currPre.RHSConstant - theState.secondMax[currPre.LHSVariable - varCount];
                if (delta <= 0.0) delta = 1e-6;
                numChangeCost[currPre.LHSVariable - varCount][delta].addingWillViolate.insert(prefIdx);
            } else {
                const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                if (currAV.size == 1) {
                    double rhc = currPre.RHSConstant - currAV.constant;
                    rhc /= currAV.weights[0];
                    
                    if (currAV.fluents[0] < varCount) {
                        double delta = rhc - theState.secondMin[currAV.fluents[0]];
                        if (delta >= 0.0) delta = -1e-6;
                         numChangeCost[currAV.fluents[0]][delta].addingWillViolate.insert(prefIdx);
                    } else {
                        double delta = -rhc - theState.secondMax[currAV.fluents[0] - varCount];
                        if (delta <= 0.0) delta = 1e-6;
                        numChangeCost[currAV.fluents[0] - varCount][delta].addingWillViolate.insert(prefIdx);
                    }
                }
            }        
        } else {
            factCost[tItr->first].addingWillViolate.insert(prefIdx);
        }
    }
                                                                                                                        
}


/// sometime-after constraints

SometimeAfterFSA::SometimeAfterFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn, const VAL::constraint_sort shouldBe)
: PreferenceFSA(idx, p), triggerPartCount(0)
{
    assert(pref->cons == shouldBe);
    initPosn = AutomatonPosition::satisfied;
    
    PrefCommon::workOutIfAddingOneThingCanTrigger(addingOneThingCanTrigger, addingThisWouldTrigger, pref->d, 1);

    if (addingOneThingCanTrigger) {
        PrefCommon::actionsWhichMeanWeHad(actionsImplyingTrigger, addingThisWouldTrigger);
    }
    
}

bool SometimeAfterFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool sometimeAfterUpdateDebug = false;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: sometime-after pref " << pref->name << " cannot be satisfied from here, cost " << pref->cost << "\n";
        }
        return (pref->cost != DBL_MAX);
    }

    bool triggerChanged = false;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::satisfied) {
        if (goalOrTriggerChanged.second) {
            const bool allPresent = goalOrTriggerIsSatisfied(state, 1);
            
            chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,true));
            
            if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[1].first, chosen.back()) != allPresent) {
                if (allPresent) {
                    cerr << "Fatal internal error: could not satisfy NNF tree trigger of a sometime-after preference\n";
                } else {
                    cerr << "Fatal internal error: could not unsatisfy NNF tree trigger of a sometime-after preference\n";
                }
                pref->d->nodes[1].first->write(cerr);
                cerr << endl;
                exit(1);
            }
            
            if (allPresent) {
                if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: sometime-after pref " << pref->name << " has been triggered\n";
                }
                state->preferenceStatus[prefIdx] = AutomatonPosition::triggered;
                triggerChanged = true;
            } else {
                if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: sometime-after pref " << pref->name << " won't trigger\n";
                }
            }
        }     
    }
    
    if (state->preferenceStatus[prefIdx] != AutomatonPosition::triggered) {
        if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: sometime-after pref hasn't been triggered\n";
        }
        return true;
    }
    
    if (goalOrTriggerChanged.first || triggerChanged) {

        if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: seeing if goal for sometime-after is true\n";
        }

        const bool allPresent = goalOrTriggerIsSatisfied(state, 0);
        
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
            
        if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back()) != allPresent) {
            if (allPresent) {
                cerr << "Fatal internal error: could not satisfy NNF tree goal of a sometime-after preference\n";
            } else {
                cerr << "Fatal internal error: could not unsatisfy NNF tree goal of a sometime-after preference\n";
            }
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
        
        if (allPresent) {
            if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime-after pref " << pref->name << " is now satisfied, cost " << pref->cost << "\n";       
            state->preferenceStatus[prefIdx] = AutomatonPosition::satisfied;            
        } else {
            if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime-after pref " << pref->name << " remains unsatisfied, cost " << pref->cost << "\n";       
        }
    }
    
    return true;
}

double SometimeAfterFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::triggered || preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        if (PreferenceHandler::preferenceDebug) {
            if (preferenceStatus[prefIdx] == AutomatonPosition::triggered) {
                cout << prefIdx << ": sometime-after pref " << pref->name << " is currently unsatisfied, cost " << pref->cost << "\n";
            } else {
                cout << prefIdx << ": sometime-after pref " << pref->name << " cannot be reached, cost " << pref->cost << "\n";
            }
        }
        return pref->cost;
    }
    
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": sometime-after pref " << pref->name << " is " << positionName[preferenceStatus[prefIdx]] << endl;
    return 0.0;
}

double SometimeAfterFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        return pref->cost;
    }
        
    return 0.0;
}

double SometimeAfterFSA::GCost(const MinimalState * state, const int & flag)
{    
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(goalType & flag)) return 0.0;
        return pref->cost;
    }
            
    return 0.0;
}
void SometimeAfterFSA::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        // If we can never satisfy the preference, don't bother trying
        return;
    }
    if (pref->d->flattened[0]) {
        toFill[0] = pref->d->flattened[0];
        toFill[0]->reset();
    }
    
    if (pref->d->flattened[1]) {
        toFill[1] = pref->d->flattened[1];        
        toFill[1]->reset();
    }
}

void SometimeAfterFSA::getCostsOfAdding(const MinimalState & theState, map<int, AddingConstraints > & factCost, map<int, map<double, AddingConstraints > > & numChangeCost)
{
    if (theState.preferenceStatus[prefIdx] == AutomatonPosition::unreachable || theState.preferenceStatus[prefIdx] == AutomatonPosition::triggered) return;
    #ifdef TEMPORALSAFEAUTOMATONSEMANTICS
    if (theState.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || theState.preferenceStatus[prefIdx] == AutomatonPosition::probablyeternallysatisfied) {
        // Temporal safety: if sometime-after a b, then in the non-temporal case, we penalise a until b appears.
        // This isn't makespan-estimate-preserving, so don't do it in POPF.
        return;
    }
    #endif
    if (!addingOneThingCanTrigger) return;
    
    const double pCost = pref->cost;
    
    if (pCost == 0.0) return;
        
    const bool allPresent = goalOrTriggerIsSatisfied(&theState, 0);
    
    if (allPresent) {
        /*if (addingThisWouldTrigger.second) {
        RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[addingThisWouldTrigger.first];
        cout << "No fear from " << pref->name << " of satisfying " << currPre << " - is already satisfied\n";
    }*/
        return;
    }
    
    static const int varCount = RPGBuilder::getPNECount();
    
    list<ConditionAndPolarity>::iterator tItr = addingThisWouldTrigger.begin();
    const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTrigger.end();
    
    for (; tItr != tEnd; ++tItr) {
        if (!tItr->polarity) {
            /// TODO - Implement negative triggers
            continue;
        }
        
        
        
        if (tItr->second) {
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[tItr->first];
            //cout << "Recording fear from " << pref->name << " of satisfying " << currPre << endl;
            
            if (currPre.LHSVariable < varCount) {
                double delta = currPre.RHSConstant - theState.secondMin[currPre.LHSVariable];
                if (delta >= 0.0) delta = -1e-6;
                numChangeCost[currPre.LHSVariable][delta].addingWillViolate.insert(prefIdx);
            } else if (currPre.LHSVariable < 2 * varCount) {
                double delta = -currPre.RHSConstant - theState.secondMax[currPre.LHSVariable - varCount];
                if (delta <= 0.0) delta = 1e-6;
                numChangeCost[currPre.LHSVariable - varCount][delta].addingWillViolate.insert(prefIdx);
            } else {
                const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                if (currAV.size == 1) {
                    double rhc = currPre.RHSConstant - currAV.constant;
                    rhc /= currAV.weights[0];
                    
                    if (currAV.fluents[0] < varCount) {
                        double delta = rhc - theState.secondMin[currAV.fluents[0]];
                        if (delta >= 0.0) delta = -1e-6;
                        numChangeCost[currAV.fluents[0]][delta].addingWillViolate.insert(prefIdx);
                    } else {
                        double delta = -rhc - theState.secondMax[currAV.fluents[0] - varCount];
                        if (delta <= 0.0) delta = 1e-6;
                        numChangeCost[currAV.fluents[0] - varCount][delta].addingWillViolate.insert(prefIdx);
                    }
                }
            }        
        } else {
            factCost[tItr->first].addingWillViolate.insert(prefIdx);
        }
    }
}

void SometimeAfterFSA::updateCosts(const MinimalState & initialState,
                                   const bool & wasTheTrigger,
                                   vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                                   map<int, AddingConstraints > & prefCostOfAddingFact,
                                   map<int, map<double, AddingConstraints > > & numChangeCost,
                                   list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
    
    if (wasTheTrigger) return;
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::unreachable) return;
    
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::triggered) {
        optimisticAutomataPositions[prefIdx] = AutomatonPosition::satisfied;
        return;
    }
    
    #ifdef TEMPORALSAFEAUTOMATONSEMANTICS
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::satisfied || optimisticAutomataPositions[prefIdx] == AutomatonPosition::probablyeternallysatisfied) {
        // Temporal safety: if sometime-after a b, then in the non-temporal case, we penalise a until b appears.
        // This isn't makespan-estimate-preserving, so don't do it in POPF.
        return;
    }
    #endif
    
    if (!addingOneThingCanTrigger) return;
    
    static const int varCount = RPGBuilder::getPNECount();
    
    list<ConditionAndPolarity>::iterator tItr = addingThisWouldTrigger.begin();
    const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTrigger.end();
    
    for (; tItr != tEnd; ++tItr) {
    
        if (!tItr->polarity) {
            /// TODO - Implement negative triggers
            return;
        }
        if (tItr->first == -1) return;
        
        //cout << "Now no longer have to fear seeing the trigger of " << pref->name << " - the goal is reachable\n";
        
        
        if (tItr->second) {
            
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[tItr->first];
            
            //cout << "Removing fear of satisfying " << currPre << endl;
            
            if (currPre.LHSVariable < varCount) {
                map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currPre.LHSVariable);
                if(varItr != numChangeCost.end()) {
                    double delta = currPre.RHSConstant - initialState.secondMin[currPre.LHSVariable];
                    if (delta >= 0.0) delta = -1e-6;
                    
                    map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                    if (dItr != varItr->second.end()) {
                    
                        dItr->second.addingWillViolate.erase(prefIdx);
                        dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                    }
                }
            } else if (currPre.LHSVariable < 2 * varCount) {
                double delta = -currPre.RHSConstant - initialState.secondMax[currPre.LHSVariable - varCount];
                if (delta <= 0.0) delta = 1e-6;
                
                map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currPre.LHSVariable - varCount);
                if (varItr != numChangeCost.end()) {
                
                    map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                    if (dItr != varItr->second.end()) {
                    
                        dItr->second.addingWillViolate.erase(prefIdx);
                        dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                    }
                }
            } else {
                const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                if (currAV.size == 1) {
                    double rhc = currPre.RHSConstant - currAV.constant;
                    rhc /= currAV.weights[0];
                    
                    if (currAV.fluents[0] < varCount) {
                        double delta = rhc - initialState.secondMin[currAV.fluents[0]];
                        if (delta >= 0.0) delta = -1e-6;
                        
                        map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currAV.fluents[0]);
                        if (varItr != numChangeCost.end()) {
                        
                            map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                            if (dItr != varItr->second.end()) {
                            
                                dItr->second.addingWillViolate.erase(prefIdx);
                                dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                            }
                        }
                       
                        
                    } else {
                        double delta = -rhc - initialState.secondMax[currAV.fluents[0] - varCount];
                        if (delta <= 0.0) delta = 1e-6;
                        
                        map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currAV.fluents[0] - varCount);
                        if (varItr != numChangeCost.end()) {
                        
                            map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                            if (dItr != varItr->second.end()) {
                            
                                dItr->second.addingWillViolate.erase(prefIdx);
                                dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                            }
                        }
                    }
                }
            }        
        } else {
            map<int,AddingConstraints >::iterator fcItr = prefCostOfAddingFact.find(tItr->first);
            if (fcItr != prefCostOfAddingFact.end()) {
            
                fcItr->second.addingWillViolate.erase(prefIdx);
                fcItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));             
            }
        }
        
    }

    preferencesThatNowHaveNoAddCosts.push_back(make_pair(prefIdx,-1));
        
}


void SometimeAfterFSA::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                                       list<list<int> > * desiredNumeric,
                                       const MinimalState & startState,
                                       const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                       const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                       const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    if (startState.preferenceStatus[prefIdx] != AutomatonPosition::triggered) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]->isSatisfied()) return;
                    
    satisfyAtLowCost(unsatisfiedPreferenceConditions[prefIdx][0], literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer, desired, desiredNegative, desiredNumeric);
    
}

/// Sometime-before constraints

SometimeBeforeFSA::SometimeBeforeFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p), triggerPartCount(0)
{
    assert(pref->cons == VAL::E_SOMETIMEBEFORE);
    initPosn = AutomatonPosition::satisfied;
    
    PrefCommon::workOutIfAddingOneThingCanTrigger(addingOneThingCanTrigger, addingThisWouldTrigger, pref->d, 1);
    
    if (addingOneThingCanTrigger) {
        PrefCommon::actionsWhichMeanWeHad(actionsImplyingTrigger, addingThisWouldTrigger);
    }                                      
    
}

bool SometimeBeforeFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool sometimeBeforeUpdateDebug = false;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: sometime-before pref " << pref->name << " cannot be satisfied from here, cost " << pref->cost << "\n";
        }
        return (pref->cost != DBL_MAX);
    }

    if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied) {
        if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: sometime-before pref " << pref->name << " cannot be unsatisfied from here, cost " << pref->cost << "\n";
        }
        return true;
    }
    
    
    if (goalOrTriggerChanged.second) {

        const bool allPresent = goalOrTriggerIsSatisfied(state, 1);

        
        if (state->preferenceStatus[prefIdx] == AutomatonPosition::probablyeternallysatisfied) {

            chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,true));
            if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[1].first, chosen.back()) != allPresent) {
                if (allPresent) {
                    cerr << "Fatal internal error: could not satisfy trigger of sometime-before preference\n";
                } else {
                    cerr << "Fatal internal error: could not unsatisfy trigger of sometime-before preference\n";
                } 
            
                pref->d->nodes[1].first->write(cerr);
                cerr << endl;
                exit(1);
            }
            
            if (allPresent) {            
                if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: sometime-before pref " << pref->name << " is okay so long as the earlier satisfaction of its goal holds\n";
                }                        
            }
            
        } else {
        
            if (allPresent) {            
                if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: sometime-before pref " << pref->name << " is now broken forever, cost " << pref->cost << "\n";
                }                        
                state->preferenceStatus[prefIdx] = AutomatonPosition::unreachable;
                return (pref->cost != DBL_MAX);
            }
        }        
    }
    
    if (goalOrTriggerChanged.first) {
    
        const bool allPresent = goalOrTriggerIsSatisfied(state, 0);
        
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back()) != allPresent) {
            if (allPresent) {
                cerr << "Fatal internal error: could not satisfy NNF goal of sometime-before preference\n";
            } else {
                cerr << "Fatal internal error: could not unsatisfy NNF goal of sometime-before preference\n";
            }
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
        
        if (allPresent) {
            if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime-before pref " << pref->name << " has triggered, probably eternally satisfied\n";
            state->preferenceStatus[prefIdx] = AutomatonPosition::probablyeternallysatisfied;
            
        } else {
            if (sometimeBeforeUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: sometime-before pref " << pref->name << " still " << positionName[state->preferenceStatus[prefIdx]] << endl;
        }
    }
    return true;
}

double SometimeBeforeFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(triggerType & flag)) return 0.0;
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": sometime-before pref " << pref->name << " cannot be satisfied, cost " << pref->cost << "\n";
        return pref->cost;
    }
        
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": sometime-before pref " << pref->name << " is satisfied\n";
    return 0.0;
}

double SometimeBeforeFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(triggerType & flag)) return 0.0;
        return pref->cost;
    }
            
    return 0.0;
}

double SometimeBeforeFSA::GCost(const MinimalState * state, const int & flag)
{
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (!(triggerType & flag)) return 0.0;
        return pref->cost;
    }
                
    return 0.0;
}

void SometimeBeforeFSA::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable || state.preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied) {
        // If we can never satisfy/unsatisfy the preference, don't bother trying
        return;
    }
    
    if (pref->d->flattened[0]) {        
        toFill[0] = pref->d->flattened[0];
        toFill[0]->reset();
    }
    
    if (pref->d->flattened[1]) {        
        toFill[1] = pref->d->flattened[1];        
        toFill[1]->reset();
    }
}

void SometimeBeforeFSA::getCostsOfAdding(const MinimalState & theState, map<int, AddingConstraints > & factCost, map<int, map<double, AddingConstraints > > & numChangeCost)
{
    if (theState.preferenceStatus[prefIdx] != AutomatonPosition::satisfied) return;
    if (!addingOneThingCanTrigger) return;
                
    static const int varCount = RPGBuilder::getPNECount();
        
    const double pCost = pref->cost;
    
    if (pCost == 0.0) return;
        
    list<ConditionAndPolarity>::iterator tItr = addingThisWouldTrigger.begin();
    const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTrigger.end();
    
    for (; tItr != tEnd; ++tItr) {
    
        if (!tItr->polarity) {
            /// TODO - Implement negative triggers
            continue;
        }
            
                                    
        if (tItr->second) {
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[tItr->first];
            
            if (currPre.LHSVariable < varCount) {
                double delta = currPre.RHSConstant - theState.secondMin[currPre.LHSVariable];
                if (delta >= 0.0) delta = -1e-6;
                numChangeCost[currPre.LHSVariable][delta].addingWillViolate.insert(prefIdx);
            } else if (currPre.LHSVariable < 2 * varCount) {
                double delta = -currPre.RHSConstant - theState.secondMax[currPre.LHSVariable - varCount];
                if (delta <= 0.0) delta = 1e-6;
                numChangeCost[currPre.LHSVariable - varCount][delta].addingWillViolate.insert(prefIdx);
            } else {
                const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                if (currAV.size == 1) {
                    double rhc = currPre.RHSConstant - currAV.constant;
                    rhc /= currAV.weights[0];
                    
                    if (currAV.fluents[0] < varCount) {
                        double delta = rhc - theState.secondMin[currAV.fluents[0]];
                        if (delta >= 0.0) delta = -1e-6;
                         numChangeCost[currAV.fluents[0]][delta].addingWillViolate.insert(prefIdx);
                    } else {
                        double delta = -rhc - theState.secondMax[currAV.fluents[0] - varCount];
                        if (delta <= 0.0) delta = 1e-6;
                        numChangeCost[currAV.fluents[0] - varCount][delta].addingWillViolate.insert(prefIdx);
                    }
                }
            }        
        } else {
            //cout << "Adding " << *(RPGBuilder::getLiteral(tItr->first)) << " would kill " << pref->name << endl;
            factCost[tItr->first].addingWillViolate.insert(prefIdx);
        }
    }                                                       
}

void SometimeBeforeFSA::updateCosts(const MinimalState & initialState,
                                    const bool & wasTheTrigger,
                                    vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                                    map<int, AddingConstraints > & prefCostOfAddingFact,
                                    map<int, map<double, AddingConstraints > > & numChangeCost,
                                    list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
                                       
    if (wasTheTrigger) return;
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::unreachable
        || optimisticAutomataPositions[prefIdx] == AutomatonPosition::eternallysatisfied
        || optimisticAutomataPositions[prefIdx] == AutomatonPosition::probablyeternallysatisfied) return;
                                               
    optimisticAutomataPositions[prefIdx] = AutomatonPosition::eternallysatisfied;
    
                                                       
    if (!addingOneThingCanTrigger) return;
                    
    
    static const int varCount = RPGBuilder::getPNECount();
    
    list<ConditionAndPolarity>::iterator tItr = addingThisWouldTrigger.begin();
    const list<ConditionAndPolarity>::iterator tEnd = addingThisWouldTrigger.end();
    
    for (; tItr != tEnd; ++tItr) {    
        if (!tItr->polarity) {
            /// TODO - Implement negative triggers
            continue;
        }
        if (tItr->second) {
            RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[tItr->first];

            if (currPre.LHSVariable < varCount) {
                map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currPre.LHSVariable);
                assert(varItr != numChangeCost.end());
                double delta = currPre.RHSConstant - initialState.secondMin[currPre.LHSVariable];
                if (delta >= 0.0) delta = -1e-6;
                           
                map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                assert(dItr != varItr->second.end());

                dItr->second.addingWillViolate.erase(prefIdx);
                dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));

                           
            } else if (currPre.LHSVariable < 2 * varCount) {
                double delta = -currPre.RHSConstant - initialState.secondMax[currPre.LHSVariable - varCount];
                if (delta <= 0.0) delta = 1e-6;
                           
                map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currPre.LHSVariable - varCount);
                assert(varItr != numChangeCost.end());
               
                map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                assert(dItr != varItr->second.end());
               
                dItr->second.addingWillViolate.erase(prefIdx);
                dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
               
            } else {
                const RPGBuilder::ArtificialVariable & currAV =  RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                if (currAV.size == 1) {
                    double rhc = currPre.RHSConstant - currAV.constant;
                    rhc /= currAV.weights[0];

                    if (currAV.fluents[0] < varCount) {
                        double delta = rhc - initialState.secondMin[currAV.fluents[0]];
                        if (delta >= 0.0) delta = -1e-6;
                                           
                        map<int, map<double, AddingConstraints  > >::iterator varItr = numChangeCost.find(currAV.fluents[0]);
                        assert(varItr != numChangeCost.end());

                        map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                        assert(dItr != varItr->second.end());

                        dItr->second.addingWillViolate.erase(prefIdx);
                        dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                                           
                                                               
                    } else {
                        double delta = -rhc - initialState.secondMax[currAV.fluents[0] - varCount];
                        if (delta <= 0.0) delta = 1e-6;
                                           
                        map<int, map<double, AddingConstraints > >::iterator varItr = numChangeCost.find(currAV.fluents[0] - varCount);
                        assert(varItr != numChangeCost.end());

                        map<double, AddingConstraints >::iterator dItr = varItr->second.find(delta);
                        assert(dItr != varItr->second.end());

                        dItr->second.addingWillViolate.erase(prefIdx);
                        dItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));                    
                    }
                }
            }        
        } else {
            //cout << "Now, adding " << *(RPGBuilder::getLiteral(tItr->first)) << " won't kill " << pref->name << endl;
            
            map<int, AddingConstraints >::iterator fcItr = prefCostOfAddingFact.find(tItr->first);
            assert(fcItr != prefCostOfAddingFact.end());
           
            fcItr->second.addingWillViolate.erase(prefIdx);
            fcItr->second.extraGoalsToAvoidViolations.push_back(make_pair(prefIdx, wasTheTrigger));
                           
        }
    }
       
    preferencesThatNowHaveNoAddCosts.push_back(make_pair(prefIdx,0));
                                                                   
}

/// within constraints

WithinFSA::WithinFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: PreferenceFSA(idx, p)
{
    assert(pref->cons == VAL::E_WITHIN);
    initPosn = AutomatonPosition::unsatisfied;
}

bool WithinFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool withinUpdateDebug = false;
    
    assert(!goalOrTriggerChanged.second);
      
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied || state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (withinUpdateDebug || PreferenceHandler::preferenceDebug) {
            if (state->preferenceStatus[prefIdx] == AutomatonPosition::eternallysatisfied) {
                cout << prefIdx << ": update: within pref " << pref->name << " has already been eternally satisfied, cost " << pref->cost << "\n";
            } else {
                cout << prefIdx << ": update: within pref " << pref->name << " cannot be satisfied from here, cost " << pref->cost << "\n";
            }
        }
        return (pref->cost != DBL_MAX);
    }
    
    if (goalOrTriggerIsSatisfied(state,0)) {
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
            cerr << "Fatal internal error: could not satisfy NNF tree of within preference\n";
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
        NNFPreconditionChooser::Supporters ignore(prefIdx,false);
        const pair<bool,double> satisfiedAt = NNFPreconditionChooser::satisfyNNFEarly(*state, minTimestamps, pref->d->nodes[0].first, ignore);
        if (satisfiedAt.second < pref->deadline) {
            if (withinUpdateDebug || PreferenceHandler::preferenceDebug) cout << COLOUR_light_green << prefIdx << ": update: within pref " << pref->name << " is now satisfied at " << satisfiedAt.second << ", cost " << pref->cost << COLOUR_default << "\n";
            state->preferenceStatus[prefIdx] = AutomatonPosition::satisfied;        
        } else {
            if (withinUpdateDebug || PreferenceHandler::preferenceDebug) cout << COLOUR_light_red << prefIdx << ": update: within pref " << pref->name << " was satisfied now, but definitely not soon enough, so removing this option" << COLOUR_default << "\n";
            chosen.pop_back();
        }
    } else {
        if (withinUpdateDebug || PreferenceHandler::preferenceDebug) cout << COLOUR_yellow << prefIdx << ": update: within pref " << pref->name << " is currently " << positionName[state->preferenceStatus[prefIdx]] << ", cost " << pref->cost << COLOUR_default << "\n";        
    }

    return true;
      
}

double WithinFSA::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) {
        if (PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": within pref " << pref->name << " and the current flag are not related, taking cost as 0\n";
        }
        return 0.0;
    }
    
    if (preferenceStatus[prefIdx] != AutomatonPosition::satisfied
        && preferenceStatus[prefIdx] != AutomatonPosition::eternallysatisfied
        && preferenceStatus[prefIdx] != AutomatonPosition::probablyeternallysatisfied) {
        if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": within pref " << pref->name << " is currently " << positionName[preferenceStatus[prefIdx]] << ", current cost " << pref->cost << "\n";
        return pref->cost;
    }
    
    if (PreferenceHandler::preferenceDebug) cout << prefIdx << ": within pref " << pref->name << " is satisfied, current cost 0\n";
    return 0.0;
}

double WithinFSA::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
        
    return 0.0;
}

double WithinFSA::GCost(const MinimalState * state, const int & flag)
{
    if (!(goalType & flag)) return 0.0;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        return pref->cost;
    }
            
    return 0.0;
}


void WithinFSA::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (state.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        // Once we've had a within preference, or shown it to be unreachable, we don't need to try to get it again
        return;
    }
    if (!pref->d->flattened[0]) return;
    toFill[0] = pref->d->flattened[0];
    toFill[0]->reset();
}

void WithinFSA::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                                  list<list<int> > * desiredNumeric,
                                  const MinimalState & startState,
                                  const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                  const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                  const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    if (startState.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || startState.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]->isSatisfied()) return;
            
    satisfyAtLowCost(unsatisfiedPreferenceConditions[prefIdx][0], literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer, desired, desiredNegative, desiredNumeric);
    
}

void WithinFSA::updateCosts(const MinimalState & initialState,
                               const bool & wasTheTrigger,
                               vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                               map<int, AddingConstraints > & prefCostOfAddingFact,
                               map<int, map<double, AddingConstraints > > & numChangeCost,
                               list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
   
    if (wasTheTrigger) return;
       
    optimisticAutomataPositions[prefIdx] = AutomatonPosition::satisfied;
   
}

void WithinFSA::becomesUnreachableAtTime(const MinimalState & state, map<EpsilonResolutionTimestamp, list<int> > & unreachableAtTime) {

    if (state.preferenceStatus[prefIdx] == AutomatonPosition::satisfied || state.preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        // Once we've had a within preference, or shown it to be unreachable, we don't need to try to get it again
        return;
    }

    unreachableAtTime[EpsilonResolutionTimestamp(pref->deadline,true)].push_back(prefIdx);
}
                                   
/// Always-Within Preferences

AlwaysWithinFSA::AlwaysWithinFSA(const int & idx, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn)
: SometimeAfterFSA(idx, p, initPosn, VAL::E_ALWAYSWITHIN)
{
    
    // for now we only support always-withins where a single step triggers them, and definitely triggers them
    // this means the trigger is either a single fact, a single negative fact, or a numeric precondition
    // dependent on a single variable that is never subject to continuous numeric effects
    
    // TODO check these conditions hold
}

bool AlwaysWithinFSA::update(MinimalState * state, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    const bool sometimeAfterUpdateDebug = false;
    
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::unreachable) {
        if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: always-within pref " << pref->name << " cannot be satisfied from here, cost " << pref->cost << "\n";
        }
        return (pref->cost != DBL_MAX);
    }

    bool triggerChanged = false;
    if (state->preferenceStatus[prefIdx] == AutomatonPosition::satisfied) {
        
        // preference is definitely satisfied, seeing if we can trigger it
        
        if (goalOrTriggerChanged.second) {
        
            const bool allPresent = goalOrTriggerIsSatisfied(state, 1);
            
            chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,true));
            if (NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[1].first, chosen.back()) != allPresent) {
                if (allPresent) {
                    cerr << "Fatal internal error: could not satisfy NNF tree trigger of an always-within preference\n";
                } else {
                    cerr << "Fatal internal error: could not unsatisfy NNF tree trigger of an always-within preference\n";
                }
                pref->d->nodes[1].first->write(cerr);
                cerr << endl;
                exit(1);
            }
            
            if (allPresent) {
                if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: always-within pref " << pref->name << " has been triggered\n";
                }
                state->preferenceStatus[prefIdx] = AutomatonPosition::triggered;
                triggerChanged = true;
            } else {
                if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
                    cout << prefIdx << ": update: always-within pref " << pref->name << " won't trigger\n";
                }
            }
            
        }
        
        if (state->preferenceStatus[prefIdx] == AutomatonPosition::satisfied) {            
            // no change in state
            return true;
        }
    }
    
    assert(state->preferenceStatus[prefIdx] == AutomatonPosition::triggered || state->preferenceStatus[prefIdx] == AutomatonPosition::probablyeternallysatisfied);
    
    if (goalOrTriggerChanged.first || triggerChanged) {
        
        if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) {
            cout << prefIdx << ": update: seeing if goal for always-within is true\n";
        }
        const bool requirementPresent = goalOrTriggerIsSatisfied(state, 0);
        
        if (requirementPresent) {
            if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: always-within pref " << pref->name << " is now probably satisfied, cost " << pref->cost << "\n";       
            state->preferenceStatus[prefIdx] = AutomatonPosition::probablyeternallysatisfied;
            chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
            if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
                cerr << "Fatal internal error: could not satisfy NNF tree\n";
                pref->d->nodes[0].first->write(cerr);
                cerr << endl;
                exit(1);
            }
        } else {
            if (sometimeAfterUpdateDebug || PreferenceHandler::preferenceDebug) cout << prefIdx << ": update: always-within pref " << pref->name << " remains " << positionName[state->preferenceStatus[prefIdx]] << ", cost " << pref->cost << "\n";       
        }
    }
    
    return true;
      
}

void AlwaysWithinFSA::getCostsOfAdding(const MinimalState & theState, map<int, AddingConstraints > & factCost, map<int, map<double, AddingConstraints > > & numChangeCost)
{
    // For temporal safety, we can't penalise adding p for a (always-within 7 p q) style preference
    // as it could be that q can appear, just not yet.
}

void AlwaysWithinFSA::updateCosts(const MinimalState & initialState,
                                   const bool & wasTheTrigger,
                                   vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                                   map<int, AddingConstraints > & prefCostOfAddingFact,
                                   map<int, map<double, AddingConstraints > > & numChangeCost,
                                   list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
    
    if (wasTheTrigger) return;
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::unreachable) return;
    
    if (optimisticAutomataPositions[prefIdx] == AutomatonPosition::triggered) {
        optimisticAutomataPositions[prefIdx] = AutomatonPosition::satisfied;
    }
    
        
}


void AlwaysWithinFSA::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                                       list<list<int> > * desiredNumeric,
                                       const MinimalState & startState,
                                       const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                       const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                       const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    if (startState.preferenceStatus[prefIdx] != AutomatonPosition::triggered) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]) return;
    if (!unsatisfiedPreferenceConditions[prefIdx][0]->isSatisfied()) return;
                    
    satisfyAtLowCost(unsatisfiedPreferenceConditions[prefIdx][0], literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer, desired, desiredNegative, desiredNumeric);
    
}

const vector<vector<int> >* AlwaysWithinFSA::getComparisonData()
{
    static vector<vector<int> > cd;
    static bool def = false;

    if (!def) {
        cd.resize(8, vector<int>(8));
        
        for (int i = 0; i < 8; ++i) {
            cd[i][i] = 0;
        }
                    
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::triggered,-1);
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::unreachable,-1);
        CDPAIR(AutomatonPosition::satisfied,AutomatonPosition::probablyeternallysatisfied,-1);
        
        CDPAIR(AutomatonPosition::probablyeternallysatisfied,AutomatonPosition::triggered,-1);
        CDPAIR(AutomatonPosition::probablyeternallysatisfied,AutomatonPosition::unreachable,-1);
        
        CDPAIR(AutomatonPosition::triggered,AutomatonPosition::unreachable,-1);
        
        def = true;
    }
                            
    return &cd;
}


/// Precondition preferences

bool PreferenceHandler::recordPreconditionViolations = false;
    
map<int,int> PreferenceHandler::preconditionViolations;

PreconditionPref::PreconditionPref(const int & idx, RPGBuilder::Constraint * const p)
: PreferenceFSA(idx, p)
{
    p->neverTrue = false;
    
    if (!p->d->flattened[0]) {
        p->neverTrue = !(p->d->nodes[0].second);
    }
}

bool PreconditionPref::update(MinimalState * state, const pair<bool,bool> &, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    if (!goalOrTriggerIsSatisfied(state, 0)) {
        if (PreferenceHandler::preferenceDebug) cout << "Precondition preference " << pref->name << " not satisfied, cost " << pref->cost << endl;
        state->prefPreconditionViolations += pref->cost;
        if (PreferenceHandler::recordPreconditionViolations) {
            ++(PreferenceHandler::preconditionViolations.insert(make_pair(prefIdx,0)).first->second);
        }
    } else {
        if (PreferenceHandler::preferenceDebug) cout << "Precondition preference " << pref->name << " satisfied, cost " << pref->cost << endl;
        chosen.push_back(NNFPreconditionChooser::Supporters(prefIdx,false));
        if (!NNFPreconditionChooser::collectNNFDependencies(*state, pref->d->nodes[0].first, chosen.back())) {
            cerr << "Fatal internal error: could not satisfy NNF tree\n";
            pref->d->nodes[0].first->write(cerr);
            cerr << endl;
            exit(1);
        }
    }
    return true;
}

double PreconditionPref::currentCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{
    exit(1);
    return DBL_MAX;    
}

double PreconditionPref::reachableCost(const vector<AutomatonPosition::Position> & preferenceStatus, const int & flag)
{   
    exit(1);
    return DBL_MAX;
    
}

double PreconditionPref::GCost(const MinimalState * state, const int & flag)
{    
    exit(1);
    return DBL_MAX;
}

void PreconditionPref::getUnsatisfiedConditionCounts(const MinimalState & state, vector<NNF_Flat*> & toFill)
{
    if (pref->d->flattened[0]) {        
        toFill[0] = pref->d->flattened[0];
        toFill[0]->reset();
    }
}




/// Simple preference handler functions

bool PreferenceHandler::update(MinimalState & state, const vector<double> & minTimestamps,
                               const set<int> & newLiterals, const set<int> & newNegativeLiterals, 
                               const set<int> & affectedNumericVariables,
                               list<NNFPreconditionChooser::Supporters> & chosen)
{
    if (PreferenceHandler::preferenceDebug) cout << "Updating preference automata following action application\n";
    
    map<int, pair<bool,bool> > affected;
    static pair<int, pair<bool,bool> > dummyEntry(-1, make_pair(false,false));
    
    for (int pass = 0; pass < 2; ++pass) {
        const set<int> & localLiterals = (pass ? newNegativeLiterals : newLiterals);
        
        set<int>::const_iterator fItr = localLiterals.begin();
        const set<int>::const_iterator fEnd = localLiterals.end();
        
        for (; fItr != fEnd; ++fItr) {
            if (PreferenceHandler::preferenceDebug) {
                if (pass) {
                    cout << "- Lost ";
                } else {
                    cout << "- Gained ";
                } 
                cout << *(RPGBuilder::getLiteral(*fItr)) << endl;                    
            }
            
            list<LiteralCellDependency<pair<int,bool> > >::const_iterator depItr = preconditionsToPrefs[*fItr].begin();
            const list<LiteralCellDependency<pair<int,bool> > >::const_iterator depEnd = preconditionsToPrefs[*fItr].end();
            
            if (PreferenceHandler::preferenceDebug) {
                cout << "  - " << *(RPGBuilder::getLiteral(*fItr)) << " is a positive precondition of:";
            }
            
            for (; depItr != depEnd; ++depItr) {
                dummyEntry.first = depItr->dest.first;
                if (PreferenceHandler::preferenceDebug) {
                    cout << " " << RPGBuilder::getPreferences()[depItr->dest.first].name << ":" << depItr->dest.first;
                    if (depItr->dest.second) {
                        cout << ":1";
                    } else {
                        cout << ":0";
                    }
                }
                if (depItr->dest.second) {                
                    affected.insert(dummyEntry).first->second.second = true;
                } else {
                    affected.insert(dummyEntry).first->second.first = true;
                }
            }
            
            if (PreferenceHandler::preferenceDebug) {
                cout << endl;
            }
        }
    }
    
    for (int pass = 0; pass < 2; ++pass) {
        const set<int> & localLiterals = (pass ? newNegativeLiterals : newLiterals);

        set<int>::const_iterator fItr = localLiterals.begin();
        const set<int>::const_iterator fEnd = localLiterals.end();
        
        for (; fItr != fEnd; ++fItr) {
            list<LiteralCellDependency<pair<int,bool> > >::const_iterator depItr = negativePreconditionsToPrefs[*fItr].begin();
            const list<LiteralCellDependency<pair<int,bool> > >::const_iterator depEnd = negativePreconditionsToPrefs[*fItr].end();
            
            if (PreferenceHandler::preferenceDebug) {
                cout << "  - " << *(RPGBuilder::getLiteral(*fItr)) << " is a negative precondition of:";
            }
            
            for (; depItr != depEnd; ++depItr) {
                dummyEntry.first = depItr->dest.first;
                if (PreferenceHandler::preferenceDebug) {
                    cout << " " << RPGBuilder::getPreferences()[depItr->dest.first].name << ":" << depItr->dest.first;
                    if (depItr->dest.second) {
                        cout << ":1";
                    } else {
                        cout << ":0";
                    }
                }
                if (depItr->dest.second) {                
                    affected.insert(dummyEntry).first->second.second = true;
                } else {
                    affected.insert(dummyEntry).first->second.first = true;
                }
            }
            
            if (PreferenceHandler::preferenceDebug) {
                cout << endl;
            }
        }
    }
    
    {
        static const int pneCount = RPGBuilder::getPNECount();
        set<int> numericPres;
        
        set<int>::const_iterator vItr = affectedNumericVariables.begin();
        const set<int>::const_iterator vEnd = affectedNumericVariables.end();
        
        for (; vItr != vEnd; ++vItr) {
            if (PreferenceHandler::preferenceDebug) {
                cout << "- Touched " << *(RPGBuilder::getPNE(*vItr)) << endl;
            }
            for (int offset = 0; offset < 2; ++offset) {
                const list<int> & affectedA = RPGBuilder::affectsRPGNumericPreconditions(*vItr + offset * pneCount);
                numericPres.insert(affectedA.begin(), affectedA.end());
                            
                const list<int> & affectedAVs = RPGBuilder::getVariableDependencies(*vItr + offset * pneCount);
                
                list<int>::const_iterator avItr = affectedAVs.begin();
                const list<int>::const_iterator avEnd = affectedAVs.end();
                
                for (; avItr != avEnd; ++avItr) {
                    const list<int> & affectedB = RPGBuilder::affectsRPGNumericPreconditions(*avItr);
                    numericPres.insert(affectedB.begin(), affectedB.end());
                }
            }
        }
        
        set<int>::const_iterator fItr = numericPres.begin();
        const set<int>::const_iterator fEnd = numericPres.end();
        
        for (; fItr != fEnd; ++fItr) {
            list<LiteralCellDependency<pair<int,bool> > >::const_iterator depItr = numericPreconditionsToPrefs[*fItr].begin();
            const list<LiteralCellDependency<pair<int,bool> > >::const_iterator depEnd = numericPreconditionsToPrefs[*fItr].end();
            
            for (; depItr != depEnd; ++depItr) {
                dummyEntry.first = depItr->dest.first;
                if (depItr->dest.second) {                
                    affected.insert(dummyEntry).first->second.second = true;
                    if (PreferenceHandler::preferenceDebug) {
                        cout << "  - Revisiting trigger of " << RPGBuilder::getPreferences()[depItr->dest.first].name << ":" << depItr->dest.first << " due to " << RPGBuilder::getNumericPreTable()[*fItr] << endl;
                    }
                } else {
                    if (PreferenceHandler::preferenceDebug) {
                        cout << "  - Revisiting requirement of " << RPGBuilder::getPreferences()[depItr->dest.first].name << ":" << depItr->dest.first << " due to " << RPGBuilder::getNumericPreTable()[*fItr] << endl;
                    }
                    
                    affected.insert(dummyEntry).first->second.first = true;
                }
            }
        }
        
    }
    
    map<int, pair<bool,bool> >::const_iterator prefItr = affected.begin();
    const map<int, pair<bool,bool> >::const_iterator prefEnd = affected.end();
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (; prefItr != prefEnd; ++prefItr) {
        if (prefItr->first >= pCount) {
            // now onto precondition preferences - stop checking
            break;
        }
        if (PreferenceHandler::preferenceDebug) cout << "p)"; cout.flush();
        if (!automata[prefItr->first]->update(&state, prefItr->second, minTimestamps, chosen)) {
            return false;
        }
    }
    

    
    // expensive debugging check
#ifndef NDEBUG
    list<NNFPreconditionChooser::Supporters> ignoreChosen;
    const int taskPrefCount = RPGBuilder::getTaskPrefCount();
    for (int p = 0; p < taskPrefCount; ++p) {
        const AutomatonPosition::Position before = state.preferenceStatus[p];
        const bool shouldBeTrue = automata[p]->update(&state, make_pair(RPGBuilder::getPreferences()[p].d->flattened[0],RPGBuilder::getPreferences()[p].d->flattened[1]), minTimestamps, ignoreChosen);
        if (before != state.preferenceStatus[p] || !shouldBeTrue) {
            cerr << COLOUR_light_red << "When double-checking " << RPGBuilder::getPreferences()[p].name << " the position changed from " << positionName[before] << " to " << positionName[state.preferenceStatus[p]];
            if (!shouldBeTrue) {
                cerr << ", and it returned false when it should have returned true";
            }
            cerr << COLOUR_default << endl;
            exit(1);
        }
    }
#endif

    return true;
}

double PreferenceHandler::getCurrentCost(const MinimalState & state, const int flag)
{
    
    double toReturn = state.prefPreconditionViolations + RPGBuilder::getPermanentViolationCost();
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            toReturn += automata[p]->currentCost(&state, flag);
        }
    }
    
    return toReturn;
}

double PreferenceHandler::getCurrentCost(const int & specificPreference, const MinimalState & state, const int flag)
{
    if (automata[specificPreference]) {
        return automata[specificPreference]->currentCost(&state,flag);
    } else {
        return 0.0;
    } 
}

double PreferenceHandler::getCurrentCost(const int & specificPreference, const vector<AutomatonPosition::Position> & positions, const int flag)
{
    if (automata[specificPreference]) {
        return automata[specificPreference]->currentCost(positions,flag);
    } else {
        return 0.0;
    } 
}

double PreferenceHandler::getCurrentCost(const double & prefPreconditionViolations, const vector<AutomatonPosition::Position> & positions, const int flag)
{
    
    double toReturn = prefPreconditionViolations  + RPGBuilder::getPermanentViolationCost();
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            toReturn += automata[p]->currentCost(positions, flag);
        }
    }
    
    return toReturn;
}


string PreferenceHandler::getCurrentViolations(const MinimalState & state)
{
    
    string toReturn = "Violations:";
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            automata[p]->currentViolations(&state, toReturn);
        }
    }
 
    {
     
        const map<string,int> & permanents = RPGBuilder::getPermanentViolationDetails();
        map<string,int>::const_iterator pItr = permanents.begin();
        const map<string,int>::const_iterator pEnd = permanents.end();
        
        for (; pItr != pEnd; ++pItr) {
            for (int i = 0; i < pItr->second; ++i) {
                toReturn += (" " + pItr->first);
            }
        }
        
    }
    
    if (recordPreconditionViolations) {
        map<int,int>::const_iterator rvItr = preconditionViolations.begin();    
        const map<int,int>::const_iterator rvEnd = preconditionViolations.end();
        
        for (; rvItr != rvEnd; ++rvItr) {
            const string pname = " " + RPGBuilder::getPreferences()[rvItr->first].name;
            
            for (int i = 0; i < rvItr->second; ++i) {
                toReturn += pname;
            }
        }
    }
    return toReturn;
}


string PreferenceHandler::getCurrentViolations(const vector<AutomatonPosition::Position> & state)
{
    
    string toReturn = "Violations:";
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            automata[p]->currentViolations(state, toReturn);
        }
    }
 
    {
     
        const map<string,int> & permanents = RPGBuilder::getPermanentViolationDetails();
        map<string,int>::const_iterator pItr = permanents.begin();
        const map<string,int>::const_iterator pEnd = permanents.end();
        
        for (; pItr != pEnd; ++pItr) {
            for (int i = 0; i < pItr->second; ++i) {
                toReturn += (" " + pItr->first);
            }
        }
        
    }
    return toReturn;
}


double PreferenceHandler::getReachableCost(const MinimalState & state, const int flag)
{
    
    double toReturn = state.prefPreconditionViolations + RPGBuilder::getPermanentViolationCost();
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            toReturn += automata[p]->reachableCost(&state, flag);
        }
    }
        
    return toReturn;
}

double PreferenceHandler::getReachableCost(const int & specificPreference, const MinimalState & state,const int flag)
{
    
    if (automata[specificPreference]) {
        return automata[specificPreference]->reachableCost(&state,flag)        ;
    } else {
        return 0.0;
    } 
}

double PreferenceHandler::getReachableCost(const int & specificPreference, const vector<AutomatonPosition::Position> & positions,const int flag)
{
    
    if (automata[specificPreference]) {
        return automata[specificPreference]->reachableCost(positions,flag)        ;
    } else {
        return 0.0;
    } 
}


double PreferenceHandler::getG(const MinimalState & state, const int flag)
{
    
    double toReturn = state.prefPreconditionViolations  + RPGBuilder::getPermanentViolationCost();
    
    const int pCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            toReturn += automata[p]->GCost(&state, flag);
        }
    }
            
    return toReturn;
}

double PreferenceHandler::markUnreachables(MinimalState & theState , const list<int> & toMark)
{
    double toReturn = 0.0;
    
    const int tpCount = RPGBuilder::getTaskPrefCount();
    list<int>::const_iterator tmItr = toMark.begin();
    const list<int>::const_iterator tmEnd = toMark.end();
    
    for (; tmItr != tmEnd; ++tmItr) {        
        assert(automata[*tmItr]);
        if (*tmItr < tpCount) {
            if (theState.preferenceStatus[*tmItr] == AutomatonPosition::unreachable) continue;
            assert(automata[*tmItr]->GCost(&theState,3) == 0.0);
            
            theState.preferenceStatus[*tmItr] = AutomatonPosition::unreachable;
            
            if (RPGBuilder::preferences[*tmItr].cost == DBL_MAX) {
                return DBL_MAX;
            } else {
                toReturn += automata[*tmItr]->GCost(&theState,3);
            }
        }
    }
    
    return toReturn;
}

void PreferenceHandler::getUnsatisfiedConditionCounts(const MinimalState & theState, vector<vector<NNF_Flat*> > & toFill, map<EpsilonResolutionTimestamp, list<int> > & unreachableAtTime)
{
    const int pCount = automata.size();
    toFill.resize(pCount, vector<NNF_Flat*>(2,(NNF_Flat*)0) );
    
    for (int p = 0; p < pCount; ++p) {
        if (automata[p]) {
            automata[p]->getUnsatisfiedConditionCounts(theState, toFill[p]);
            automata[p]->becomesUnreachableAtTime(theState, unreachableAtTime);
        }
    }
}

void PreferenceHandler::getCostsOfDeletion(const MinimalState & theState, map<int, set<int> > & prefCostOfDeletingFact, map<int, map<double, set<int> > > & prefCostOfChangingNumber)
{
    const int tpCount = RPGBuilder::getTaskPrefCount();
    for (int p = 0; p < tpCount; ++p) {
        if (automata[p]) {
            automata[p]->getCostsOfDeletion(theState, prefCostOfDeletingFact, prefCostOfChangingNumber);
        }
    }
}

void PreferenceHandler::getCostsOfAdding(const MinimalState & theState, map<int, AddingConstraints > & prefCostOfDeletingFact, map<int, map<double, AddingConstraints > > & prefCostOfChangingNumberB)
{
    const int tpCount = RPGBuilder::getTaskPrefCount();
    
    for (int p = 0; p < tpCount; ++p) {
        if (automata[p]) {
            automata[p]->getCostsOfAdding(theState, prefCostOfDeletingFact, prefCostOfChangingNumberB);
        }
    }
}

void PreferenceHandler::updateCostsAndPreferenceStatus(const MinimalState & initialState, const pair<int,bool> & whatHasBeenSatisfied,
                                                       vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                                                       map<int, AddingConstraints > & prefCostOfAddingFact,
                                                       map<int, map<double, AddingConstraints > > & prefCostOfChangingNumberB,
                                                       list<pair<int,int> > & preferencesThatNowHaveNoAddCosts)
{
    static const int tpCount = RPGBuilder::getTaskPrefCount();
    if (whatHasBeenSatisfied.first >= tpCount) return;
    
    assert(automata[whatHasBeenSatisfied.first]);
    automata[whatHasBeenSatisfied.first]->updateCosts(initialState, whatHasBeenSatisfied.second, optimisticAutomataPositions, prefCostOfAddingFact, prefCostOfChangingNumberB, preferencesThatNowHaveNoAddCosts);
    if (preferenceDebug) {
        cout << "\t\tAfter that, optimistic preference status is " << positionName[optimisticAutomataPositions[whatHasBeenSatisfied.first]] << endl;
    }
}

void PreferenceHandler::getDesiredGoals(list<list<Literal*> > & desired, list<list<Literal*> > & desiredNegative,
                                        list<list<int> > * desiredNumeric,
                                        const MinimalState & startState,
                                        const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                        const vector<AutomatonPosition::Position> & optimisticAutomatonPositions,
                                        /*const set<int> & prefsUnsatisfied,*/
                                        /*vector<list<PreferenceSetAndCost> > * literalCosts,*/ 
                                        const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                        const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    const int tpCount = RPGBuilder::getTaskPrefCount();
    
    for (int sv = 0; sv < tpCount; ++sv) {
        if (!automata[sv]) {
            continue;   
        }
        if (!canBeSatisfied(startState.preferenceStatus[sv])) continue;
        if (!isSatisfied(optimisticAutomatonPositions[sv])) continue;
        
        
        automata[sv]->getDesiredGoals(desired, desiredNegative, desiredNumeric, startState, unsatisfiedPreferenceConditions, literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
        
    }
    
    
}

/// PreferenceHandler 2.0 - now with ADL etc.

void PreferenceHandler::initialiseNNF()
{
    
    WhereAreWeNow = PARSE_CONSTRAINTS;
    
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const unsigned int prefCount = prefs.size();     
    
    
    for (unsigned int p = 0; p < prefCount; ++p) {
        prefs[p].d = new PreferenceData();
        for (int part = 0; part < 2; ++part) {
            VAL::goal * const lookAt = (part ? prefs[p].parsed_trigger : prefs[p].parsed_goal);
            if (lookAt == 0) {
                continue;
            }
            if (PreferenceHandler::preferenceDebug) {
                cout << "Building NNF for " << prefs[p].name << ":" << p << " part " << part << "\n";
            }
            prefs[p].d->nodes[part] = NNFUtils::buildNNF(theTC,prefs[p].fe,lookAt);
            if (prefs[p].d->nodes[part].first) {
                if (PreferenceHandler::preferenceDebug) {
                    cout << "NNF " << p << " for " << prefs[p].name << ":" << p << " part " << part << "\n";
                    prefs[p].d->nodes[part].first->write(cout);
                }
            } else {                
                if (PreferenceHandler::preferenceDebug) {
                    cout << "NNF " << p << " for " << prefs[p].name << " evaluates to ";
                    if (prefs[p].d->nodes[part].second) {
                        cout << "true\n";
                    } else {
                        cout << "false\n";
                    } 
                }
                
            }
        }
    }
    
    WhereAreWeNow = PARSE_UNKNOWN;
}

void PreferenceHandler::substituteRPGNumericPreconditions(RPGBuilder::BuildingNumericPreconditionData & commonData) {

    WhereAreWeNow = PARSE_CONSTRAINTS;

    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const unsigned int prefCount = prefs.size();     
    
    
    for (unsigned int i = 0; i < prefCount; ++i) {
        for (int part = 0; part < 2; ++part) {
            NNFNode * const oldRoot = prefs[i].d->nodes[part].first;
            if (oldRoot) {
                bool desirable = false;
                bool undesirable = false;
                
                 switch (prefs[i].cons) {
                    case VAL::E_ALWAYS:
                    {
                        desirable = true;
                        break;
                    }
                    case VAL::E_ATEND:
                    {
                        desirable = true;
                        break;
                    }
                    case VAL::E_SOMETIME:
                    {
                        desirable = true;
                        break;
                    }
                    case VAL::E_ATMOSTONCE:
                    {
                        // desirable if we've tripped it, and hence keeping it true is a good idea
                        desirable = true;
                        // undesirable if we've not yet tripped it, or have tripped it in the past, and hence keeping it false is a good idea
                        undesirable = true;
                        break;
                    }
                    case VAL::E_SOMETIMEAFTER:
                    case VAL::E_ALWAYSWITHIN:
                    {
                        // part 1 is the a in (sometime-after a b)
                        // it isn't desirable, as it causes us extra work
                        // the b, part 0, is desirable, though
                        desirable = (part == 0);
                        break;
                    }                           
                    case VAL::E_SOMETIMEBEFORE:
                    {
                        // part 1 is the a in (sometime-before a b)
                        // it isn't desirable; the b part is, though,
                        // as it allows a plan to later achieve a without cost
                        desirable = (part == 0);
                        break;
                    }                               
                    default:
                    {
                        desirable = true;
                    }
                }

                prefs[i].d->nodes[part] = NNFUtils::substituteRPGNumerics(oldRoot,desirable,undesirable,commonData);                
            }
        }
    }

    WhereAreWeNow = PARSE_UNKNOWN;
};

void PreferenceHandler::pruneStaticLiterals(vector<pair<bool,bool> > & staticLiterals) {
    
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const unsigned int prefCount = prefs.size();     
    
    for (int unsigned i = 0; i < prefCount; ++i) {
        PreferenceData * const d = prefs[i].d;
        assert(d);
        for (unsigned int part = 0; part < 2; ++part) {
            assert(part < d->nodes.size());
            NNFNode * const oldRoot = d->nodes[part].first;
            if (oldRoot) {
                prefs[i].d->nodes[part] = NNFUtils::pruneStaticLiterals(oldRoot,staticLiterals);
            }
        }
    }
    
        
};


void PreferenceHandler::flattenNNF() {
    
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const unsigned int prefCount = prefs.size();     
    
    for (unsigned int i = 0; i < prefCount; ++i) {
        for (int part = 0; part < 2; ++part) {
            NNFNode * & oldRoot = prefs[i].d->nodes[part].first;
            if (oldRoot) {
                oldRoot = NNFUtils::simplifyNNF(oldRoot);            
                if (oldRoot) {
                    prefs[i].d->flattened[part] = NNFUtils::flattenNNF(oldRoot);
                    if (preferenceDebug) {
                        cout << "NNF for " << prefs[i].name << ":" << i << " part " << part << ":\n";
                        cout << *(prefs[i].d->flattened[part]);
                    }
                } else {
                    cout << "NNF simplified to " << oldRoot << endl;
                }
            }
        }
    }
    initPTRTable();
    
    
    #ifndef NDEBUG
    
    
    for (unsigned int i = 0; i < prefCount; ++i) {
        for (int part = 0; part < 2; ++part) {            
            list<Literal*> & dest = (part ? prefs[i].debug_trigger : prefs[i].debug_goal);
            list<pair<int,int> > & destNum = (part ? prefs[i].debug_triggerRPGNum : prefs[i].debug_goalRPGNum);
            list<int>::const_iterator litItr = prefs[i].d->conditionLiterals[part].begin();
            const list<int>::const_iterator litEnd = prefs[i].d->conditionLiterals[part].end();
            
            for (; litItr != litEnd; ++litItr) {
                dest.push_back(RPGBuilder::getLiteral(*litItr));
            }
            
            list<int>::const_iterator numItr = prefs[i].d->conditionNums[part].begin();
            const list<int>::const_iterator numEnd = prefs[i].d->conditionNums[part].end();
            
            for (; numItr != numEnd; ++numItr) {
                destNum.push_back(make_pair(*numItr,-1));
            }
            

            
        }
    }
    
    #endif
    
};

void PreferenceHandler::collectRequiredFactsInNNF(const int& pref, const bool& wasTheTrigger, std::set< int >& requiredPositive, std::set< int >& requiredNegative)
{
    NNFNode * & oldRoot = RPGBuilder::getPreferences()[pref].d->nodes[wasTheTrigger ? 1 : 0].first;
    if (oldRoot) {
        NNFUtils::findFactsDefinitelyNeeded(oldRoot, requiredPositive, requiredNegative);
    }
}

void PreferenceHandler::collectAllFactsInNNF(const int& pref, const bool& wasTheTrigger, std::set< int >& requiredPositive, std::set< int >& requiredNegative)
{
    NNF_Flat * const currNNF = RPGBuilder::getPreferences()[pref].d->flattened[wasTheTrigger ? 1 : 0];
    
    if (currNNF) {
        const int cellCount = currNNF->getCellCount();
        for (int c = 0; c < cellCount; ++c) {
            if (currNNF->getCells()[c].isCell()) {
                if (currNNF->getCells()[c].lit) {
                    if (currNNF->getCells()[c].polarity) {
                        requiredPositive.insert(currNNF->getCells()[c].lit->getStateID());
                    } else {
                        requiredNegative.insert(currNNF->getCells()[c].lit->getStateID());
                    }
                }
            }
        }
    }
}


bool PreferenceHandler::couldBeBeneficialToOppose(const int & p, const bool & wasTheTrigger)
{
    const uint taskPrefCount = RPGBuilder::getTaskPrefCount();
    
    if ((size_t) p >= taskPrefCount) {
        // is never a good idea to violate precondition preferences
        return false;
    }
        
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    
    switch (prefs[p].cons) {
        case VAL::E_ATMOSTONCE: {
            // at most onces are best avoided
            return true;
        }
        case VAL::E_SOMETIMEAFTER:
        case VAL::E_SOMETIMEBEFORE:
        case VAL::E_ALWAYSWITHIN: {
           
            
            // it can be beneficial to avoid the trigger of a sometime after to avoid having to reach the requirement,
            // or to avoid the trigger of a sometime before to avoid violating the preference if the requirement has not yet been seen
            return wasTheTrigger;
            //return true; // this should be wrong
        }                           
        default: {
            return false;
            // return true;// this should be wrong
        }
    }
    
}

bool PreferenceHandler::couldBeBeneficialToSupport(const int & p, const bool & wasTheTrigger)
{
    const uint taskPrefCount = RPGBuilder::getTaskPrefCount();
    
    if ((size_t) p >= taskPrefCount) {
        // is never a good idea to violate precondition preferences, so always support them
        return true;
    }
        
    const vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getPreferences();
    
    switch (prefs[p].cons) {
        case VAL::E_ATMOSTONCE: {
            // at most onces are best avoided
            return false;
            //return true; // this should be wrong
        }
        case VAL::E_SOMETIMEAFTER:
        case VAL::E_SOMETIMEBEFORE:
        case VAL::E_ALWAYSWITHIN: {
           
            // support the requirement of sometime afters or sometime before, but not the triggers
            return !wasTheTrigger;
            //return true; // this should be wrong
        }                           
        default: {
            // anything else - always, at end, sometime, etc.  need to be supported
            return true;
        }
    }
    
}

void PreferenceHandler::initPTRTable()
{
    if (ptrTableInit >= 2) return;

    const unsigned int litCount = instantiatedOp::howManyNonStaticLiterals();
    const unsigned int numPreCount = RPGBuilder::getNumericPreTable().size();
    const int pneCount = RPGBuilder::getPNECount();
    
    preconditionsToPrefs.resize(litCount);
    negativePreconditionsToPrefs.resize(litCount);
    
    numericPreconditionsToPrefs.resize(numPreCount);
            
    numericVariableAffectsPreferences.resize(pneCount, false);
    
    vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getEditablePreferences();
    const unsigned int prefCount = prefs.size();     
    
    for (unsigned int i = 0; i < prefCount; ++i) {
        PreferenceData* const d = prefs[i].d;
        for (int part = 0; part < 2; ++part) {
            const pair<int,bool> currReference(i, part == 1);
            
            NNFNode * const oldRoot = d->nodes[part].first;
            
            if (oldRoot) {
                NNFUtils::buildLiteralsToPreconditions<pair<int,bool> >(d->flattened[part],
                    preconditionsToPrefs,negativePreconditionsToPrefs,
                    numericPreconditionsToPrefs,
                    d->conditionLiterals[part], d->conditionNegativeLiterals[part],
                    d->conditionNums[part],
                    currReference);

                d->flattened[part]->reset();
                if (d->flattened[part]->isSatisfied()) defaultTruePrefParts.insert(currReference);
                
                const int cellCount = d->flattened[part]->getCellCount();
                
                int rnp;
                
                for (int c = 0; c < cellCount; ++c) {
                    
                    rnp = d->flattened[part]->getCells()[c].num;
                    if (rnp == -1) {
                        continue;
                    }
                    
                    const RPGBuilder::RPGNumericPrecondition & currRNP = RPGBuilder::getNumericPreTable()[rnp];
                    
                    if (currRNP.LHSVariable < pneCount) {
                        numericVariableAffectsPreferences[currRNP.LHSVariable] = true;
                    } else if (currRNP.LHSVariable < 2 * pneCount) {
                        numericVariableAffectsPreferences[currRNP.LHSVariable - pneCount] = true;
                    } else {
                        const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currRNP.LHSVariable);
                        
                        for (int s = 0; s < currAV.size; ++s) {
                            if (currAV.fluents[s] < pneCount) {
                                numericVariableAffectsPreferences[currAV.fluents[s]] = true;
                            } else {
                                numericVariableAffectsPreferences[currAV.fluents[s] - pneCount] = true;
                            }
                        }
                    }
                    
                }
            }
        }
    }
    
    for (unsigned int i = 0; i < numPreCount; ++i) {
        if (!numericPreconditionsToPrefs[i].empty()) {
            relevantNumericPreconditions.push_back(i);
        }
    }

    if (preferenceDebug) {
        for (unsigned int l = 0; l < litCount; ++l) {
            for (int isneg = 0; isneg < 2; ++isneg) {                
                list<LiteralCellDependency<pair<int,bool> > >::iterator depItr = (isneg ? negativePreconditionsToPrefs[l].begin() : preconditionsToPrefs[l].begin());
                const list<LiteralCellDependency<pair<int,bool> > >::iterator depEnd = (isneg ? negativePreconditionsToPrefs[l].end() : preconditionsToPrefs[l].end());

                for (int p = 0 ; depItr != depEnd; ++depItr,++p) {
                    if (!p) {
                        if (isneg) cout << "¬";
                        cout << *(RPGBuilder::getLiteral(l)) << " [" << l << "] is used in:\n";
                    }
                    if (depItr->dest.second) {
                        cout << "\tTrigger of preference ";
                    } else {
                        cout << "\tGoal of preference ";
                    }                
                    cout << prefs[depItr->dest.first].name;
                    cout << ":" << depItr->dest.first << " @ " << depItr->index << "\n";
                }
            }
        }
    }

    ptrTableInit = 2;
};

void PreferenceHandler::getPreconditionsToSatisfy(list<Literal*> & literals, list<Literal*> & negativeLiterals,
                                                  list<int> * numPres,
                                                  const pair<int,bool> & satisfied,  const EpsilonResolutionTimestamp & factLayerTime,
                                                  const vector<list<CostedAchieverDetails> > & literalCosts,  const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                                  const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer)
{
    assert(automata[satisfied.first]);
    automata[satisfied.first]->getPreconditionsToSatisfy(literals, negativeLiterals, numPres, satisfied.second, factLayerTime, literalCosts, negativeLiteralAchievedInLayer, numericAchievedInLayer);
}
                                      

void PreferenceHandler::aboutToApply(MinimalState & theState, const ActionSegment & act, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen)
{
    //if this is a TIL then there can't be any preferences on it
    if(!act.first) {
        return;
    }
    const vector<int> & prePrefs = (act.second == Planner::E_AT_START ? RPGBuilder::getStartPreferences()[act.first->getID()]
                                                                      : RPGBuilder::getEndPreferences()[act.first->getID()]);
    
    const int ppCount = prePrefs.size();
    
    if (preferenceDebug) {
        if (ppCount) {
            cout << "Checking the " << ppCount << " precondition preferences of " << *(act.first) << endl;
        } else {
            cout << "No precondition preferences attached to " << *(act.first) << endl;
        }
    }
    
    for (int p = 0; p < ppCount; ++p) {
        if (!automata[prePrefs[p]]->update(&theState, make_pair(true,false), minTimestamps, chosen)) {
            cerr << "Fatal internal error: precondition preference update returned false, i.e. it was somehow in the :constraints section\n";
            exit(1);
        }
    }
    
}
                                          
bool PreferenceHandler::constraintsAreSatisfied(const vector<AutomatonPosition::Position> & automataPositions)
{
    for (int p = 0; p < RPGBuilder::taskConstraintCount; ++p) {
        if (automata[p] && automata[p]->currentCost(automataPositions,3) != 0.0) {
            return false; 
        }
    }
    
    return true;
}

                                          
};

