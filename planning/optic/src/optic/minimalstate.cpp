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

#include "minimalstate.h"
#include "temporalconstraints.h"
#include "PreferenceHandler.h"
#include "numericanalysis.h"

#include "algorithm"

using std::transform;
using std::endl;

#include <cstring>
#include "RPGBuilder.h"

#include <sstream>

using std::ostringstream;

namespace Planner
{

StateTransformer* MinimalState::globalTransformer = 0;


#ifdef STOCHASTICDURATIONS

void MinimalState::deleteGoalStepRecords()
{    
    delete [] stepFromWhichLiteralGoalsHold;
    
    stepFromWhichLiteralGoalsHold = 0;
    
    if (stepsFromWhichNumericGoalsHold) {
        static const int numGoalCount = RPGBuilder::getNumericRPGGoals().size() * 2;
        for (int i = 0; i < numGoalCount; ++i) {
            delete [] stepsFromWhichNumericGoalsHold[i];
        }
        delete [] stepsFromWhichNumericGoalsHold;
        
        stepsFromWhichNumericGoalsHold = 0;        
    }
}

void MinimalState::copyGoalStepRecords(const int * const literalIn, int** const numericIn)
{
 
    if (literalIn) {
        static const int litGoalCount = RPGBuilder::getLiteralGoals().size();
        static const int litGoalBytes = litGoalCount * sizeof(int);
        
        stepFromWhichLiteralGoalsHold = new int[litGoalCount];
        
        memcpy(stepFromWhichLiteralGoalsHold, literalIn, litGoalBytes);
        
    } else {
        stepFromWhichLiteralGoalsHold = 0;
    }
    
    if (numericIn) {
        
        #ifdef MEMDEBUG
        cout << "Coping array of numeric goal achievement times from " << numericIn << endl;
        #endif
        
        static const int numGoalCount = RPGBuilder::getNumericRPGGoals().size();        
        static const int numGoalArrayCount = numGoalCount * 2;
        
        stepsFromWhichNumericGoalsHold = new int*[numGoalArrayCount];
        
        static int copySize;
        
        for (int i = 0; i < numGoalArrayCount; ++i) {
            
            if (numericIn[i]) {
                
                copySize = numericIn[i][0] + 1;
                
                stepsFromWhichNumericGoalsHold[i] = new int[copySize];
                memcpy(stepsFromWhichNumericGoalsHold[i], numericIn[i], copySize * sizeof(int));
                
            } else {
                stepsFromWhichNumericGoalsHold[i] = 0;
            }            
        }                
        
    } else {
        stepsFromWhichNumericGoalsHold = 0;
    }
    
}

void MinimalState::literalGoalHoldsFromStep(const int & gID, const int & stepID)
{
    if (!stepFromWhichLiteralGoalsHold) {
        static const int litGoalCount = RPGBuilder::getLiteralGoals().size();
        stepFromWhichLiteralGoalsHold = new int[litGoalCount];        
    }
    
    stepFromWhichLiteralGoalsHold[gID] = stepID;
}

void MinimalState::numericGoalHoldsFromSteps(const int & gID, const list<int> & stepIDs)
{
    if (!stepsFromWhichNumericGoalsHold) {
        
        static const int numGoalCount = RPGBuilder::getNumericRPGGoals().size();        
        static const int numGoalArrayCount = numGoalCount * 2;
        
        stepsFromWhichNumericGoalsHold = new int*[numGoalArrayCount];
        
        #ifdef MEMDEBUG
        cout << "Creating new array to hold numeric goal achievement times for " << this << " at " << stepsFromWhichNumericGoalsHold << endl;
        #endif
                
        
        memset(stepsFromWhichNumericGoalsHold, 0, numGoalArrayCount * sizeof(int*));
        
        #ifdef MEMDEBUG
        for (int i = 0; i < numGoalArrayCount; ++i) {
            if (stepsFromWhichNumericGoalsHold[i] != 0) {
                cout << "- Fatal internal error: memset has failed to fill entry " << i << " with 0" << endl;
            }
        }
        #endif
    }
    
    if (stepsFromWhichNumericGoalsHold[gID]) {
        delete [] stepsFromWhichNumericGoalsHold[gID];
    }
    
    const int arrSize = stepIDs.size();
    
    stepsFromWhichNumericGoalsHold[gID] = new int[arrSize + 1];
    stepsFromWhichNumericGoalsHold[gID][0] = arrSize;
    
    list<int>::const_iterator sItr = stepIDs.begin();
    const list<int>::const_iterator sEnd = stepIDs.end();
    
    for (int i = 1; sItr != sEnd; ++sItr, ++i) {
        stepsFromWhichNumericGoalsHold[gID][i] = *sItr;
    }
}
#endif

MinimalState::MinimalState(const StateFacts & f,
                           const vector<double> & sMin, const vector<double> & sMax,
                           const map<int, set<int> > & sa,
                           const vector<AutomatonPosition::Position> & ps, const double & ppv, const double * tdrStatus,
                           const int nt, const unsigned int pl, const unsigned int ae
#ifdef STOCHASTICDURATIONS
                           ,const int * const literalGoalStepsIn, int** const numericGoalStepsIn
#endif                                                      
                           )
        : first(f), secondMin(sMin), secondMax(sMax), startedActions(sa),
          preferenceStatus(ps), prefPreconditionViolations(ppv), lowerBoundOnTimeDependentRewardFacts(tdrStatus ? new double[NumericAnalysis::getFactsInTimeDependentRewards().size()] : 0),
          planLength(pl), actionsExecuting(ae), nextTIL(nt), temporalConstraints(globalTransformer->emptyTemporalConstraints())/*,
          statusOfTemporalPreferences(psa ? psa->clone() : 0)*/
{
    
    if (tdrStatus) {
        memcpy(lowerBoundOnTimeDependentRewardFacts, tdrStatus, sizeof(double) * NumericAnalysis::getFactsInTimeDependentRewards().size());
    }
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(literalGoalStepsIn, numericGoalStepsIn);
    #endif
}

#ifndef TOTALORDERSTATES
MinimalState::MinimalState(const set<int> & f, const vector<double> & sMin, const vector<double> & sMax,/* const PreferenceStatusArray * psa,*/
                           const map<int, set<int> > & sa,
                           const vector<AutomatonPosition::Position> & ps, const double & ppv, const double * tdrStatus,// const double & sc,
                           const int nt, const unsigned int pl, const unsigned int ae
                           #ifdef STOCHASTICDURATIONS
                           ,const int * const literalGoalStepsIn, int** const numericGoalStepsIn
                           #endif
                           )
        : secondMin(sMin), secondMax(sMax), startedActions(sa),
          preferenceStatus(ps), prefPreconditionViolations(ppv), lowerBoundOnTimeDependentRewardFacts(tdrStatus ? new double[NumericAnalysis::getFactsInTimeDependentRewards().size()] : 0),// cost(sc),        
          planLength(pl), actionsExecuting(ae), nextTIL(nt), temporalConstraints(globalTransformer->emptyTemporalConstraints())/*,
          statusOfTemporalPreferences(psa ? psa->clone() : 0)*/
{
    setFacts(f);
    if (tdrStatus) {
        memcpy(lowerBoundOnTimeDependentRewardFacts, tdrStatus, sizeof(double) * NumericAnalysis::getFactsInTimeDependentRewards().size());
    }    
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(literalGoalStepsIn, numericGoalStepsIn);
    #endif

}
#endif

void MinimalState::setFacts(const set<int> & f)
{
    insertIntFacts(f.begin(), f.end(), StepAndBeforeOrAfter());
}

void MinimalState::setFacts(const LiteralSet & f)
{
    insertFacts(f.begin(), f.end(), StepAndBeforeOrAfter());
}


void MinimalState::setFacts(const vector<double> & f)
{
    secondMin = f;
    secondMax = f;
}


MinimalState::MinimalState(const MinimalState & other, const int extendBy)
        :
        #ifdef TOTALORDERSTATES
        first(other.first), invariants(other.invariants), firstAnnotations(other.firstAnnotations), 
        #else
        first(other.first), retired(other.retired),
        #endif
        secondMin(other.secondMin), secondMax(other.secondMax), startedActions(other.startedActions),
        preferenceStatus(other.preferenceStatus), prefPreconditionViolations(other.prefPreconditionViolations),
        lowerBoundOnTimeDependentRewardFacts(other.lowerBoundOnTimeDependentRewardFacts ? new double[NumericAnalysis::getFactsInTimeDependentRewards().size()] : 0),// cost(other.cost),        
        planLength(other.planLength), actionsExecuting(other.actionsExecuting), nextTIL(other.nextTIL),
        temporalConstraints(globalTransformer->cloneTemporalConstraints(other.temporalConstraints, extendBy))/*,
        statusOfTemporalPreferences(other.statusOfTemporalPreferences ? other.statusOfTemporalPreferences->clone() : 0)*/
{
    if (other.lowerBoundOnTimeDependentRewardFacts) {
        memcpy(lowerBoundOnTimeDependentRewardFacts, other.lowerBoundOnTimeDependentRewardFacts, sizeof(double) * NumericAnalysis::getFactsInTimeDependentRewards().size());
    }
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(other.stepFromWhichLiteralGoalsHold, other.stepsFromWhichNumericGoalsHold);
    #endif        
}

MinimalState::MinimalState()
    : prefPreconditionViolations(0.0), lowerBoundOnTimeDependentRewardFacts(0), // cost(0.0),
    planLength(0), actionsExecuting(0), nextTIL(0),
    temporalConstraints(globalTransformer->emptyTemporalConstraints())/*,
    statusOfTemporalPreferences(0)*/
{
    #ifdef STOCHASTICDURATIONS
    stepFromWhichLiteralGoalsHold = 0;
    stepsFromWhichNumericGoalsHold = 0;
    #endif        
}

MinimalState::~MinimalState()
{
    delete temporalConstraints;
    delete lowerBoundOnTimeDependentRewardFacts;
//     delete statusOfTemporalPreferences;
    #ifdef STOCHASTICDURATIONS
    deleteGoalStepRecords();        
    #endif
}

MinimalState & MinimalState::operator =(const MinimalState & other)
{
    #ifdef TOTALORDERSTATES
    first = other.first;
    invariants = other.invariants;
    firstAnnotations = other.firstAnnotations;
    #else
    first = other.first;
    retired = other.retired;    
    #endif
    secondMin = other.secondMin;
    secondMax = other.secondMax;
    startedActions = other.startedActions;
    //cost = other.cost;
    prefPreconditionViolations = other.prefPreconditionViolations;
    preferenceStatus = other.preferenceStatus;
    if (other.lowerBoundOnTimeDependentRewardFacts) {
        if (!lowerBoundOnTimeDependentRewardFacts) {
            lowerBoundOnTimeDependentRewardFacts = new double[NumericAnalysis::getFactsInTimeDependentRewards().size()];
        }
        memcpy(lowerBoundOnTimeDependentRewardFacts, other.lowerBoundOnTimeDependentRewardFacts, sizeof(double) * NumericAnalysis::getFactsInTimeDependentRewards().size());
    } else {
        delete lowerBoundOnTimeDependentRewardFacts;
        lowerBoundOnTimeDependentRewardFacts = 0;        
    }
    planLength = other.planLength;
    actionsExecuting = other.actionsExecuting;
    nextTIL = other.nextTIL;
    delete temporalConstraints;
    temporalConstraints = globalTransformer->cloneTemporalConstraints(other.temporalConstraints);
    
//     delete statusOfTemporalPreferences;
//     if (other.statusOfTemporalPreferences) {
//         statusOfTemporalPreferences = other.statusOfTemporalPreferences->clone();
//     } else {
//         statusOfTemporalPreferences = 0;
//     }
    
    #ifdef STOCHASTICDURATIONS
    deleteGoalStepRecords();
    copyGoalStepRecords(other.stepFromWhichLiteralGoalsHold, other.stepsFromWhichNumericGoalsHold);
    #endif  
    return *this;
}

bool StrongStateEquality::operator()(const MinimalState & a, const MinimalState & b)
{
    return (a.first == b.first && a.secondMin == b.secondMin && a.secondMax == b.secondMax && a.startedActions == b.startedActions && a.nextTIL == b.nextTIL
            /*&& ((!a.statusOfTemporalPreferences && !b.statusOfTemporalPreferences) || (a.statusOfTemporalPreferences && b.statusOfTemporalPreferences && *a.statusOfTemporalPreferences == *b.statusOfTemporalPreferences)) */);
}

bool WeakStateEquality::operator()(const MinimalState & a, const MinimalState & b)
{
    return (a.first == b.first && a.secondMin == b.secondMin && a.secondMax == b.secondMax && a.startedActions == b.startedActions && a.nextTIL == b.nextTIL
            /*&& ((!a.statusOfTemporalPreferences && !b.statusOfTemporalPreferences) || (a.statusOfTemporalPreferences && b.statusOfTemporalPreferences && *a.statusOfTemporalPreferences == *b.statusOfTemporalPreferences)) */);
}

void MinimalState::printState(ostream & cout) const
{

    cout << "Literals:";
    {
        StateFacts::const_iterator itr = first.begin();
        const StateFacts::const_iterator itrEnd = first.end();

        for (; itr != itrEnd; ++itr) {
            cout << " " << FACTA(itr);
            #ifndef TOTALORDERSTATES
            cout << "[" << itr->second.availableFrom << "]";
            #endif
        }        
    }
    cout << "\nStarted actions:";
    {
        map<int, set<int> >::const_iterator itr = startedActions.begin();
        const map<int, set<int> >::const_iterator itrEnd = startedActions.end();

        for (; itr != itrEnd; ++itr) {
            cout << " " << itr->first << " with ends recorded at steps:";
            set<int>::const_iterator iItr = itr->second.begin();
            const set<int>::const_iterator iEnd = itr->second.end();

            for (; iItr != iEnd; ++iItr) {
                cout << " " << *iItr;
            }
            cout << "\n";
        }
    }

    cout << "\nNext TIL: " << nextTIL;
//     if (statusOfTemporalPreferences) {
//         cout << "\nPreference violation cost: " << statusOfTemporalPreferences->getCost();
//         cout << "\nPreference violations:" << statusOfTemporalPreferences->getWithinViolations() << endl;
//     }

    cout << "\n";

}

ostream & operator <<(ostream & o, const MinimalState & s)
{
    s.printState(o);
    return o;
}

ostream & operator <<(ostream & o, const StepAndBeforeOrAfter & s)
{
    s.write(o);
    return o;
}

// PreferenceStatusArray * PreferenceStatusArray::initialArray = 0;
// int PreferenceStatusArray::arraySize = 0;
// 
// void PreferenceStatusArray::initialise(const int & size) {
//     delete initialArray;
//     initialArray = 0;
//     arraySize = size;
//     
//     if (arraySize) {
//         initialArray = new PreferenceStatusArray();
//         for (int i = 0; i < size; ++i) {
//             (*initialArray)[i] = AutomatonPosition::satisfied;
//         }
//     }
// }
// 
// string PreferenceStatusArray::getWithinViolations() const
// {
// 
//     ostringstream s;
//     
//     for (int j = 0; j < arraySize; ++j) {
//         if (data[j] != AutomatonPosition::satisfied && data[j] != AutomatonPosition::eternallysatisfied) {
//             s << " " << RPGBuilder::getPreferences()[j].name;
//         }
//     }
//     
//     return s.str();
//     
// }

double MinimalState::calculateCost() const {
    double toReturn = 0.0;
//     if (statusOfTemporalPreferences) {
//         toReturn += statusOfTemporalPreferences->getCost();
//     }
    if (!RPGBuilder::getPreferences().empty()) {
        toReturn += PreferenceHandler::getCurrentCost(*this);
    }
    if (RPGBuilder::getMetric()) {
        toReturn += RPGBuilder::getMetric()->constant;
    }
    return toReturn;
}

double MinimalState::calculateGCost() const {
    double toReturn = 0.0;
//     if (statusOfTemporalPreferences) {
//         toReturn += statusOfTemporalPreferences->getCost();
//     }
    if (!RPGBuilder::getPreferences().empty()) {
        toReturn += PreferenceHandler::getG(*this);
    }
    if (RPGBuilder::getMetric()) {
        toReturn += RPGBuilder::getMetric()->constant;
    }
    return toReturn;
}

};
