#include "minimalstate.h"
#include "temporalconstraints.h"

#include "algorithm"

using std::transform;
using std::endl;

#ifdef STOCHASTICDURATIONS
#include <cstring>
#include "RPGBuilder.h"
#endif


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

MinimalState::MinimalState(const map<int, PropositionAnnotation> & f,
                           const vector<double> & sMin, const vector<double> & sMax,
                           const map<int, set<int> > & sa,
                           const int nt, const unsigned int pl, const unsigned int ae
#ifdef STOCHASTICDURATIONS
                           ,const int * const literalGoalStepsIn, int** const numericGoalStepsIn
#endif                                                      
                           )
        : first(f), secondMin(sMin), secondMax(sMax), startedActions(sa),
        planLength(pl), actionsExecuting(ae), nextTIL(nt), temporalConstraints(globalTransformer->emptyTemporalConstraints())
{
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(literalGoalStepsIn, numericGoalStepsIn);
    #endif
}

MinimalState::MinimalState(const set<int> & f, const vector<double> & sMin, const vector<double> & sMax, const map<int, set<int> > & sa,
                           const int nt, const unsigned int pl, const unsigned int ae
                           #ifdef STOCHASTICDURATIONS
                           ,const int * const literalGoalStepsIn, int** const numericGoalStepsIn
                           #endif
                           )
        : secondMin(sMin), secondMax(sMax), startedActions(sa),
        planLength(pl), actionsExecuting(ae), nextTIL(nt), temporalConstraints(globalTransformer->emptyTemporalConstraints())
{
    setFacts(f);
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(literalGoalStepsIn, numericGoalStepsIn);
    #endif

}

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
        : first(other.first), retired(other.retired), secondMin(other.secondMin), secondMax(other.secondMax), startedActions(other.startedActions),
        planLength(other.planLength), actionsExecuting(other.actionsExecuting), nextTIL(other.nextTIL), temporalConstraints(globalTransformer->cloneTemporalConstraints(other.temporalConstraints, extendBy))
{
    
    #ifdef STOCHASTICDURATIONS
    copyGoalStepRecords(other.stepFromWhichLiteralGoalsHold, other.stepsFromWhichNumericGoalsHold);
    #endif        
}

MinimalState::MinimalState()
    : planLength(0), actionsExecuting(0), nextTIL(0), temporalConstraints(globalTransformer->emptyTemporalConstraints())
{
    #ifdef STOCHASTICDURATIONS
    stepFromWhichLiteralGoalsHold = 0;
    stepsFromWhichNumericGoalsHold = 0;
    #endif        
}

MinimalState::~MinimalState()
{
    delete temporalConstraints;
    #ifdef STOCHASTICDURATIONS
    deleteGoalStepRecords();        
    #endif
}

MinimalState & MinimalState::operator =(const MinimalState & other)
{
    first = other.first;
    retired = other.retired;
    secondMin = other.secondMin;
    secondMax = other.secondMax;
    startedActions = other.startedActions;
    planLength = other.planLength;
    actionsExecuting = other.actionsExecuting;
    nextTIL = other.nextTIL;
    delete temporalConstraints;
    temporalConstraints = globalTransformer->cloneTemporalConstraints(other.temporalConstraints);
    
    #ifdef STOCHASTICDURATIONS
    deleteGoalStepRecords();
    copyGoalStepRecords(other.stepFromWhichLiteralGoalsHold, other.stepsFromWhichNumericGoalsHold);
    #endif  
    return *this;
}

bool StrongStateEquality::operator()(const MinimalState & a, const MinimalState & b)
{
    return (a.first == b.first && a.secondMin == b.secondMin && a.secondMax == b.secondMax && a.startedActions == b.startedActions && a.nextTIL == b.nextTIL);
}

bool WeakStateEquality::operator()(const MinimalState & a, const MinimalState & b)
{
    return (a.first == b.first && a.secondMin == b.secondMin && a.secondMax == b.secondMax && a.startedActions == b.startedActions && a.nextTIL == b.nextTIL);
}

void MinimalState::printState(ostream & cout) const
{

    cout << "Literals:";
    {
        map<int, PropositionAnnotation>::const_iterator itr = first.begin();
        const map<int, PropositionAnnotation>::const_iterator itrEnd = first.end();

        for (; itr != itrEnd; ++itr) {
            cout << " " << itr->first << "[" << itr->second.availableFrom << "]";
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

};
