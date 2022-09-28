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

#include "FFSolver.h"
#include "temporalconstraints.h"
#include "globals.h"
#include "numericanalysis.h"
#include "temporalanalysis.h"

#include "compressionsafescheduler.h"
#include "lpscheduler.h"
#include "PreferenceHandler.h"

#include "colours.h"

#ifdef STOCHASTICDURATIONS
#include "StochasticDurations.h"
#endif

#include "partialordertransformer.h"

#include <cfloat>
#include <limits>

#include <sys/times.h>

#include "solver.h"

namespace Planner
{

Solution FF::workingBestSolution;
    
list<pair<double, list<ActionSegment> > > FFcache_relaxedPlan;
list<ActionSegment> FFcache_helpfulActions;
RPGHeuristic::EvaluationInfo FFcache_h;
bool FFcache_upToDate;
bool FFheader_upToDate;
bool FFonly_one_successor;
double FFcache_makespanEstimate;
bool FF::steepestDescent = true;

double FF::doubleU = 5.0;
double FF::doubleUReduction = -1.0;
bool FF::WAStar = false;
bool FF::timeWAStar = false;

bool FF::bestFirstSearch = true;
bool FF::helpfulActions = true;

bool FF::biasG = false;
bool FF::biasD = false;

bool FF::pruneMemoised = true;

bool FF::firstImprover = false;

bool FF::incrementalExpansion = false;
bool FF::skipEHC = false;
bool FF::zealousEHC = true;
bool FF::startsBeforeEnds = true;
bool FF::invariantRPG = true;
bool FF::tsChecking = false;
bool FF::scheduleToMetric = false;
bool FF::makespanTieBreak = true;
bool FF::nonDeletorsFirst = false;
bool FF::openListOrderLowMakespanFirst = false;
bool FF::openListOrderLowCostFirst = false;
bool FF::skipRPG = false;
bool FF::allowCompressionSafeScheduler = false;
int FF::statesDiscardedAsTooExpensiveBeforeHeuristic = 0;

bool FF::costOptimalAStar = false;

#ifdef POPF3ANALYSIS
double FF::reprocessQualityBound = std::numeric_limits<double>::signaling_NaN();
#endif

const bool evaluationDiagnostics = false;

Solution::Solution()
    : plan(0), constraints(0), quality(std::numeric_limits<double>::signaling_NaN())
{

}


void Solution::update(const std::list< FFEvent >& newPlan, const Planner::TemporalConstraints*const newCons, const double& newMetric)
{
    
    delete plan;
    delete constraints;
    
    plan = new list<FFEvent>(newPlan);
    if (newCons) {
        constraints = new TemporalConstraints(*newCons);
    } else {
        assert(plan->empty());
        constraints = new TemporalConstraints();
    }
    quality = newMetric;

}


using std::endl;

double getMakespan(const list<FFEvent> & plan) {
    double toReturn = 0.0;
            
    list<FFEvent>::const_iterator pItr = plan.begin();
    const list<FFEvent>::const_iterator pEnd = plan.end();            
    double t;
    for (; pItr != pEnd; ++pItr) {
        if (pItr->isDummyStep()) {
            continue;
        }
        #ifdef STOCHASTICDURATIONS
        t = pItr->stochasticTimestamp->getTimestampForRPGHeuristic();
        #else
        t = pItr->lpTimestamp;
        #endif
        if (t > toReturn) {
            toReturn = t;
        }                                                
    }
    return toReturn;   
}
double FF::evaluateMetric(const MinimalState & theState, const list<FFEvent> & plan, const bool printMetric)
{
 
    RPGBuilder::Metric * const theMetric = RPGBuilder::getMetric();
    
    if (!theMetric) {
        if (plan.empty()) {
            if (printMetric) {
                cout << "; Plan empty, and no metric specified\n";
            }
            return 0.0;
        } else {
            if (printMetric) {
                cout << "; No metric specified - using makespan\n";
            }
            return getMakespan(plan);
        }     
    }

    double toReturn = theState.calculateCost();

    if (printMetric) {
        if (theMetric->constant != 0.0) {
            cout << "; Adding constant offset " << theMetric->constant << " to the metric\n";   
        }
        
        /*if (theState.statusOfTemporalPreferences) {
            cout << "; Cost accumulated by within preferences: " << theState.statusOfTemporalPreferences->getCost() << endl;
            cout << "; Violations:" << theState.statusOfTemporalPreferences->getWithinViolations() << endl;
        }*/        
        
        if (!RPGBuilder::getPreferences().empty()) {
            cout << "; Cost of preferences: " << PreferenceHandler::getCurrentCost(theState) << endl;
            cout << "; " << PreferenceHandler::getCurrentViolations(theState) << endl;
        }
    }
    
    const int pneCount = RPGBuilder::getPNECount();
    list<int>::const_iterator vItr = theMetric->variables.begin();
    const list<int>::const_iterator vEnd = theMetric->variables.end();
    
    list<double>::const_iterator wItr = theMetric->weights.begin();
    const list<double>::const_iterator wEnd = theMetric->weights.end();
    
    for (; wItr != wEnd; ++wItr, ++vItr) {
        if (*vItr < 0) {
            if (printMetric) {
                cout << "; Adding " << *wItr << " x makespan to the metric, i.e. adding " << getMakespan(plan) * *wItr << endl;
            }
            toReturn += getMakespan(plan) * *wItr;
        } else if (*vItr < pneCount) {
            const double value = theState.secondMin[*vItr];
            toReturn += value * *wItr;
            if (printMetric) {
                cout << "; Adding " << *wItr << " x " << *(RPGBuilder::getPNE(*vItr)) << " to the metric, i.e. adding " << value * *wItr << endl;
            }
        } else {
            const double value = -theState.secondMin[*vItr];
            toReturn += value * *wItr;
        }
    }
    
    return toReturn;
}

#ifdef POPF3ANALYSIS

bool knowThatCostsAreMonotonic = false;

double calculateAdmissibleCost(const MinimalState & theState, const double & makespan, const double & incomingBound, const bool & verbose)
{
    RPGBuilder::Metric * const theMetric = RPGBuilder::getMetric();
    
    static const bool localDebug = false;
    
    
    double gCost = 0.0;
    
    if (!theMetric) {
        // assume metric is minimise makespan
        gCost = makespan;
        
    } else {
        if (!knowThatCostsAreMonotonic) {
            NumericAnalysis::findWhetherTheMetricIsMonotonicallyWorsening();
            knowThatCostsAreMonotonic = true;
        }
        
        if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            
            if (localDebug) {
                cout << "Calculating admissible cost:\n  " << gCost << endl;
            }

            gCost += theState.calculateGCost();                                                                    
                        
            if (theState.lowerBoundOnTimeDependentRewardFacts) {
                const double bestAdditionalRewardFromHere = NumericAnalysis::bestAdditionalRewardFromHere(theState);
                if (theMetric->minimise) {
                    gCost -= bestAdditionalRewardFromHere;
                    if (localDebug) {
                        cout << "+ " << -bestAdditionalRewardFromHere << " due to TDRs\n";
                    }
                } else {
                    gCost += bestAdditionalRewardFromHere;
                    if (localDebug) {
                        cout << "+ " << bestAdditionalRewardFromHere  << " due to TDRs\n";
                    }
                }                
            }
                
        
            const int pneCount = RPGBuilder::getPNECount();
            list<int>::const_iterator vItr = theMetric->variables.begin();
            const list<int>::const_iterator vEnd = theMetric->variables.end();
            
            list<double>::const_iterator wItr = theMetric->weights.begin();
            const list<double>::const_iterator wEnd = theMetric->weights.end();
            
            for (; wItr != wEnd; ++wItr, ++vItr) {
                if (*vItr < 0) {
                    if (*wItr < 0.0) {
                        if (verbose) {
                            cout << "[Would need upper-bound on makespan]"; cout.flush();
                        }        
                        return incomingBound;
                    } else {
                        if (localDebug) {
                            cout << "+ " << makespan << "*" << *wItr << "  ; makespan term\n";
                        }
                        gCost += makespan * *wItr;
                    }
                } else if (*vItr < pneCount) {
                    const double value = theState.secondMin[*vItr];
                    gCost += value * *wItr;
                    if (localDebug) {
                        cout << "+ " << value << "*" << *wItr << "  ; " << *(RPGBuilder::getPNE(*vItr)) << " term\n";
                    }
                } else {
                    const double value = -theState.secondMax[*vItr - pneCount];
                    gCost += value * *wItr;
                    if (localDebug) {
                        cout << "+ " << value << "*" << *wItr << "  ; " << *(RPGBuilder::getPNE(*vItr - pneCount)) << " term\n";
                    }
                }        
            }
            
        } else {
            return std::numeric_limits< double >::signaling_NaN();
        }
    
    }
    
    if (!theMetric || theMetric->minimise) {
        if (gCost < incomingBound) {
            gCost = incomingBound;
        }
    } else {
        if (gCost > incomingBound) {
            gCost = incomingBound;
        }
    }
    
    if (localDebug) {
        cout << "[" << incomingBound << "=>gCost=" << gCost << "]";
        cout.flush();
    }
    
    return gCost;       
}

bool admissibleCostExceedsBound(/*const MinimalState & theState, */const double & precalculatedAdmissibleCost, const bool & verbose)
{

    if (!Globals::optimiseSolutionQuality) {
        return false;
    }
    
    RPGBuilder::Metric * const theMetric = RPGBuilder::getMetric();

    double gCost = precalculatedAdmissibleCost;
    
    if (!theMetric) {
        // assume metric is minimise makespan
        if (gCost != 0.0) {
            gCost = -gCost;
        }
        
    } else {
        if (!knowThatCostsAreMonotonic) {
            NumericAnalysis::findWhetherTheMetricIsMonotonicallyWorsening();
            knowThatCostsAreMonotonic = true;
        }
        
        if (!NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            if (verbose) {
                cout << "[Metric is non-monotonic]"; cout.flush();
            }
            
            return false;
        }
        
        if (theMetric->minimise && gCost != 0.0) {
            gCost = -gCost;
        }
    }
            
    if (Globals::bestSolutionQuality == -DBL_MAX) {
        if (verbose) {
            cout << "[No incumbent solution]"; cout.flush();
        }
        return false;
    }
        
    if (gCost <= Globals::bestSolutionQuality) {
        //cout << "Bound exceeded: this state has cost " << toReturn << " vs best " << Globals::bestSolutionQuality << endl;
        if (Globals::globalVerbosity & 1) {
            //cout << COLOUR_light_green << "[" << gCost << "^vs" << Globals::bestSolutionQuality << "]" << COLOUR_default;
            cout << COLOUR_light_green << "^" << COLOUR_default;
            cout.flush();
        }
        if (verbose) {
            cout << "[Exceeds metric]"; cout.flush();
        }     
        return true;
    }
    
    if (verbose) {
        cout << "[" << gCost << " > " << Globals::bestSolutionQuality << "]";
        cout.flush();
    }

    return false;
}


pair<bool,bool> FF::carryOnSearching(const MinimalState & theState,  const list<FFEvent> & plan, const pair<bool,double> & currentCost, const double & gCost, bool & wasNewBestSolution)
{
    
    wasNewBestSolution = false;
    if (!Globals::optimiseSolutionQuality) {
        workingBestSolution.update(plan, theState.temporalConstraints, evaluateMetric(theState, plan, false));
        if (Globals::globalVerbosity & 1) {
            cout << "g"; cout.flush();
        }
        return make_pair(false,false);
    }
    
    RPGBuilder::Metric * const theMetric = RPGBuilder::getMetric();
    
    double realMetric;
    
    if (currentCost.first) {
        if (Globals::globalVerbosity & 2) {
            cout << "; Using cost from the LP of " << currentCost.second << ", in case it was a continuous cost function" << endl;
        }
        realMetric = currentCost.second;
    } else {    
        realMetric = evaluateMetric(theState,plan,Globals::globalVerbosity & 2);
    }
        
    double metric = realMetric;
    
    if (theMetric) {
        
        if (theMetric->minimise) {            
            if (metric != 0.0) {
                metric = -metric;
            }        
        }
        
    } else {
        // default metric - minimise makespan
        if (metric != 0.0) {
            metric = -metric;
        }
    }
    
    if (metric > Globals::bestSolutionQuality + 0.01) {
        Globals::bestSolutionQuality = metric;
        wasNewBestSolution = true;

        if (Globals::globalVerbosity & 1) {
            cout << "g"; cout.flush();
        }
        cout << endl;        
        if (currentCost.first) {
            cout << "; LP calculated the cost\n";
            workingBestSolution.update(plan, theState.temporalConstraints, currentCost.second);
        } else {
            workingBestSolution.update(plan, theState.temporalConstraints, evaluateMetric(theState, plan, true));
        }
        
        cout << endl << "; Plan found with metric " << realMetric << endl;
        if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            cout << "; Theoretical reachable cost " << gCost << endl;
        }
        cout << "; States evaluated so far: " << RPGHeuristic::statesEvaluated << endl;
#ifdef POPF3ANALYSIS
        if (Globals::optimiseSolutionQuality) {
            cout << "; States pruned based on pre-heuristic cost lower bound: " << statesDiscardedAsTooExpensiveBeforeHeuristic << endl;
        }
#endif
        FFEvent::printPlan(plan);        
        
        FF::printPlanAsDot(cout, plan, theState.temporalConstraints);

        
        if (Globals::improvementBetweenSolutions != 0.0) {
            Globals::bestSolutionQuality += Globals::improvementBetweenSolutions;            
        }
        
        RPGBuilder::getHeuristic()->metricHasChanged();
        
        bool metricIsMinimiseMakespan = false;
        
        if (!theMetric) {
            metricIsMinimiseMakespan = true;
        } else if (theMetric->minimise && theMetric->variables.size() == 1 && theMetric->variables.front() < 0) {
            metricIsMinimiseMakespan = true;
        } 
        
        if (metricIsMinimiseMakespan) {
            RPGBuilder::updateGoalDeadlines(-metric);
            #ifdef STOCHASTICDURATIONS
            if (solutionDeadlineTime > -metric) {
                solutionDeadlineTime = -metric;
            }
            #endif
        }
        
        if (!RPGBuilder::getPreferences().empty() && theMetric->variables.empty()) {
            double theoreticalLower = RPGBuilder::getPermanentViolationCost();
            if ((!theoreticalLower || theMetric->minimise) && theoreticalLower != 0.0) {
                theoreticalLower = -theoreticalLower;
            }
            if (fabs(metric - theoreticalLower) < 0.001) {
                return make_pair(false,false);
            }
        }
        
        
        
    } else {
        if (Globals::globalVerbosity & 2) {
            cout << "`" << metric << "<" << Globals::bestSolutionQuality << "`";
            cout.flush();
        }
    }
    
    if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
        double gSigned = gCost;
        if ((!theMetric || theMetric->minimise) && gSigned != 0.0) {
            gSigned = -gSigned;
        }
        return make_pair(true, gSigned > metric);
        
    } else {
        return make_pair(true, true);
    }
    
    
}

#else

pair<bool,bool> FF::carryOnSearching(const MinimalState & theState,  const list<FFEvent> & plan)
{
    if (Globals::globalVerbosity & 1) {
        cout << "g"; cout.flush();
    }   
    workingBestSolution.update(plan, theState.temporalConstraints, evaluateMetric(theState, plan, false));
    
    return make_pair(false, false);
}

#endif


ExtendedMinimalState & ExtendedMinimalState::operator=(const ExtendedMinimalState & e)
{
    delete decorated;    
    decorated = new MinimalState(*(e.decorated));
    
    startEventQueue = e.startEventQueue;
    timeStamp = e.timeStamp;
    stepBeforeTIL = e.stepBeforeTIL;
    tilFanIn = e.tilFanIn;
    tilComesBefore = e.tilComesBefore;
    entriesForAction.clear();
    list<StartEvent>::iterator bqItr = startEventQueue.begin();
    const list<StartEvent>::iterator bqEnd = startEventQueue.end();

    for (; bqItr != bqEnd; ++bqItr) {
        entriesForAction[bqItr->actID].push_back(bqItr);
    }


    return *this;
}


/*void ImplicitFFEvent::pushToStart() {
//    cout << "Pushing back from implicit end with t in [" << lpMinTimestamp << "," << lpMaxTimestamp << "\n";
    const double newStartMin = lpMinTimestamp - toUpdate->maxDuration;
    if (newStartMin > toUpdate->lpMinTimestamp) {
        toUpdate->lpMinTimestamp = newStartMin;
    }
    double newStartMax = lpMaxTimestamp;
    if (newStartMax != DBL_MAX) newStartMax -= toUpdate->minDuration;
    if (newStartMax < toUpdate->lpMaxTimestamp) {
        toUpdate->lpMaxTimestamp = newStartMax;
    }
    if (toUpdate->lpEndTimestamp < lpMinTimestamp) {
        toUpdate->lpEndTimestamp = lpMinTimestamp;
        //cout << "Pushing " << lpMinTimestamp << " back as timestamp of end of skippable action\n";
    }
}*/

void printState(MinimalState & e)
{

    cout << e;

    cout << "State Finished\n";
};

void printState(const ExtendedMinimalState & e)
{

    cout << e.getInnerState();

    cout << "\nStart event queue:";
    {
        list<StartEvent>::const_iterator aItr = e.startEventQueue.begin();
        const list<StartEvent>::const_iterator aEnd = e.startEventQueue.end();
        for (; aItr != aEnd; ++aItr) {
            cout << aItr->stepID << ": " << aItr->actID << "\n";
        }
    }

    cout << "State Finished\n";

};

namespace CSBase
{

vector<bool> ignorableFluents;
vector<bool> nonDominatedFluent;

int compareSets(const set<int> & a, const set<int> & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    set<int>::const_iterator aItr = a.begin();
    const set<int>::const_iterator aEnd = a.end();

    set<int>::const_iterator bItr = b.begin();
    const set<int>::const_iterator bEnd = b.end();

    int av, bv;

    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        av = *aItr;
        bv = *bItr;
        if (av < bv) return 1;
        if (av > bv) return -1;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareSets(const set<StepAndBeforeOrAfter> & a, const set<StepAndBeforeOrAfter> & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    set<StepAndBeforeOrAfter>::const_iterator aItr = a.begin();
    const set<StepAndBeforeOrAfter>::const_iterator aEnd = a.end();

    set<StepAndBeforeOrAfter>::const_iterator bItr = b.begin();
    const set<StepAndBeforeOrAfter>::const_iterator bEnd = b.end();

    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        const StepAndBeforeOrAfter & av = *aItr;
        const StepAndBeforeOrAfter & bv = *bItr;
        if (av < bv) return 1;
        if (av > bv) return -1;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareSets(const map<StepAndBeforeOrAfter, bool> & a, const map<StepAndBeforeOrAfter, bool> & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    map<StepAndBeforeOrAfter, bool>::const_iterator aItr = a.begin();
    const map<StepAndBeforeOrAfter, bool>::const_iterator aEnd = a.end();

    map<StepAndBeforeOrAfter, bool>::const_iterator bItr = b.begin();
    const map<StepAndBeforeOrAfter, bool>::const_iterator bEnd = b.end();

    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        const StepAndBeforeOrAfter & av = aItr->first;
        const StepAndBeforeOrAfter & bv = bItr->first;
        if (av < bv) return 1;
        if (av > bv) return -1;

        if (!aItr->second && bItr->second) return 1;
        if (aItr->second && !bItr->second) return -1;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareAnnotations(const map<int, PropositionAnnotation> & a, const map<int, PropositionAnnotation> & b)
{
    map<int, PropositionAnnotation>::const_iterator aItr = a.begin();
    const map<int, PropositionAnnotation>::const_iterator aEnd = a.end();

    map<int, PropositionAnnotation>::const_iterator bItr = b.begin();

    int cMaps;
    for (; aItr != aEnd; ++aItr, ++bItr) {
        assert(aItr->first == bItr->first);
        {
            const StepAndBeforeOrAfter & av = aItr->second.availableFrom;
            const StepAndBeforeOrAfter & bv = bItr->second.availableFrom;
            if (av < bv) return 1;
            if (av > bv) return -1;
        }

        {
            const map<StepAndBeforeOrAfter, bool> & av = aItr->second.deletableFrom;
            const map<StepAndBeforeOrAfter, bool> & bv = bItr->second.deletableFrom;

            cMaps = compareSets(av, bv);
#ifdef STATEHASHDEBUG
            assert(cMaps * -1 == compareSets(bv, av));
#endif

            if (cMaps != 0) return cMaps;

        }

    }

    return 0;
}

#ifdef TOTALORDERSTATES
int compareAnnotations(const set<int> & a, const set<int> & b)
{
    return compareSets(a,b);    
}
#endif

#ifdef DOUBLESTATEHASH

int compareVecs(const vector<double> & a, const vector<double> & b);
int compareMaps(const map<int, int> & a, const map<int, int> & b);
int compareMaps(const map<int, set<int> > & a, const map<int, set<int> > & b);
int compareMaps(const map<int, map<int, int> > & a, const map<int, map<int, int> > & b);
int compareLists(const list<StartEvent> & a, const list<StartEvent> & b);

int oldCompareSets(const map<int, PropositionAnnotation> & a, const map<int, PropositionAnnotation> & b)
{
    map<int, PropositionAnnotation>::const_iterator aItr = a.begin();
    const map<int, PropositionAnnotation>::const_iterator aEnd = a.end();

    map<int, PropositionAnnotation>::const_iterator bItr = b.begin();
    const map<int, PropositionAnnotation>::const_iterator bEnd = b.end();

    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        if (aItr->first < bItr->first) return -1;
        if (aItr->first > bItr->first) return 1;
    }

    if (aItr == aEnd && bItr != bEnd) return -1;
    if (aItr != aEnd && bItr == bEnd) return 1;
        
    return 0;
}


#endif

int compareSets(const map<int, PropositionAnnotation> & a, const map<int, PropositionAnnotation> & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    map<int, PropositionAnnotation>::const_iterator aItr = a.begin();
    const map<int, PropositionAnnotation>::const_iterator aEnd = a.end();

    map<int, PropositionAnnotation>::const_iterator bItr = b.begin();
    const map<int, PropositionAnnotation>::const_iterator bEnd = b.end();

    int av, bv;
    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {

        av = aItr->first;
        bv = bItr->first;
        if (av < bv) return 1;
        if (av > bv) return -1;

    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

void skipTerminates(list<StartEvent>::const_iterator & itr, const list<StartEvent>::const_iterator & itrEnd)
{
    while (itr != itrEnd && itr->terminated) ++itr;
}

int compareLists(const list<StartEvent> & a, const list<StartEvent> & b)
{

    list<StartEvent>::const_iterator aItr = a.begin();
    const list<StartEvent>::const_iterator aEnd = a.end();

    list<StartEvent>::const_iterator bItr = b.begin();
    const list<StartEvent>::const_iterator bEnd = b.end();

    skipTerminates(aItr, aEnd);
    skipTerminates(bItr, bEnd);

    while (aItr != aEnd && bItr != bEnd) {
        const StartEvent& av = *aItr;
        const StartEvent& bv = *bItr;
        if (av.actID < bv.actID) return 1;
        if (av.actID > bv.actID) return -1;

        //          if (av.stepID < bv.stepID) return 1;
        //          if (av.stepID > bv.stepID) return -1;

        ++aItr;
        ++bItr;

        skipTerminates(aItr, aEnd);
        skipTerminates(bItr, bEnd);

    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}


int compareMaps(const map<int, int> & a, const map<int, int> & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    map<int, int>::const_iterator aItr = a.begin();
    const map<int, int>::const_iterator aEnd = a.end();

    map<int, int>::const_iterator bItr = b.begin();
    const map<int, int>::const_iterator bEnd = b.end();

    int av, bv, av2, bv2;
    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        av = aItr->first;
        bv = bItr->first;
        if (av < bv) return 1;
        if (av > bv) return -1;
        av2 = aItr->second;
        bv2 = bItr->second;
        if (av2 < bv2) return 1;
        if (av2 > bv2) return -1;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareMaps(const map<int, map<int, int> > & a, const map<int, map<int, int> > & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    map<int, map<int, int> >::const_iterator aItr = a.begin();
    const map<int, map<int, int> >::const_iterator aEnd = a.end();

    map<int, map<int, int> >::const_iterator bItr = b.begin();
    const map<int, map<int, int> >::const_iterator bEnd = b.end();

    int av, bv;
    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        av = aItr->first;
        bv = bItr->first;
        if (av < bv) return 1;
        if (av > bv) return -1;
        const int cMaps = compareMaps(aItr->second, bItr->second);
#ifdef STATEHASHDEBUG
        assert(-1 * cMaps == compareMaps(bItr->second, aItr->second));
#endif
        if (cMaps != 0) return cMaps;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareMaps(const map<int, set<int> > & a, const map<int, set<int> > & b)
{

    const bool aEmpty = a.empty();
    const bool bEmpty = b.empty();
    if (aEmpty && bEmpty) return 0;
    if (aEmpty && !bEmpty) return -1;
    if (bEmpty && !aEmpty) return 1;

    map<int, set<int> >::const_iterator aItr = a.begin();
    const map<int, set<int> >::const_iterator aEnd = a.end();

    map<int, set<int> >::const_iterator bItr = b.begin();
    const map<int, set<int> >::const_iterator bEnd = b.end();

    int av, bv, cMaps;
    for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
        av = aItr->first;
        bv = bItr->first;
        if (av < bv) return 1;
        if (av > bv) return -1;
        //          const int av2 = aItr->second;
        //          const int bv2 = bItr->second;
        //          if (av2 < bv2) return 1;
        //          if (av2 > bv2) return -1;
        cMaps = compareSets(aItr->second, bItr->second);
#ifdef STATEHASHDEBUG
        assert(-1 * cMaps == compareSets(bItr->second, aItr->second));
#endif
        if (cMaps != 0) return cMaps;
    }

    if (aItr == aEnd && bItr != bEnd) return 1;
    if (aItr != aEnd && bItr == bEnd) return -1;

    return 0;
}

int compareVecs(const vector<double> & a, const vector<double> & b)
{
    const int aSize = a.size();
    const int bSize = b.size();
    if (!aSize && !bSize) return 0;
    if (aSize < bSize) return 1;
    if (bSize > aSize) return -1;

    double av, bv;
    for (int i = 0; i < aSize; ++i) {
        if (!ignorableFluents[i]) {
            av = a[i];
            bv = b[i];
            //cout << *(RPGBuilder::getPNE(i)) << ": " << av << " vs " << bv << " in compareVecs()\n";
            if (av < bv - 0.0005) return 1;
            if (av > bv + 0.0005) return -1;
        } else {
            //cout << "Ignoring " << *(RPGBuilder::getPNE(i)) << " in compareVecs()\n";
        } 
    
    }

    return 0;
}

int compareNonDominatedVecs(const vector<double> & a, const vector<double> & b)
{
    const int aSize = a.size();
    const int bSize = b.size();
    if (!aSize && !bSize) return 0;
    if (aSize < bSize) return 1;
    if (bSize > aSize) return -1;
    
    double av, bv;
    for (int i = 0; i < aSize; ++i) {
        if (nonDominatedFluent[i]) {
            av = a[i];
            bv = b[i];
            if (av < bv - 0.0005) return 1;
            if (av > bv + 0.0005) return -1;
        }
    }
    
    return 0;
}


/*  int compareLists(const list<int> & a, const list<int> & b) {

        const bool aEmpty = a.empty();
        const bool bEmpty = b.empty();
        if (aEmpty && bEmpty) return 0;
        if (aEmpty && !bEmpty) return -1;
        if (bEmpty && !aEmpty) return 1;

        list<int>::const_iterator aItr = a.begin();
        const list<int>::const_iterator aEnd = a.end();

        list<int>::const_iterator bItr = b.begin();
        const list<int>::const_iterator bEnd = b.end();

        for (; aItr != aEnd && bItr != bEnd; ++aItr, ++bItr) {
            const int av = *aItr;
            const int bv = *bItr;
            if (av < bv) return 1;
            if (av > bv) return -1;
        }

        if (aItr == aEnd && bItr != bEnd) return 1;
        if (aItr != aEnd && bItr == bEnd) return -1;

        return 0;

    }*/

bool propAndNonDominatedVariableLessThan(const ExtendedMinimalState & ae, const ExtendedMinimalState & be)
{
    
    const MinimalState & a = ae.getInnerState();
    const MinimalState & b = be.getInnerState();
    
#ifdef DOMHASHDEBUG
    const bool shdVerbose = true;
    
    if (shdVerbose) {
        cout << "Seeing if " << &ae << " < " << &be;
        cout.flush();
    }
#endif
    
    const int csVal = CSBase::compareSets(a.first, b.first);
#ifdef DOMHASHDEBUG
    assert(-1*csVal == CSBase::compareSets(b.first, a.first));
#endif

    if (csVal > 0) {        
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 1\n";
        }
#endif
        return true;
    } else if (csVal < 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - no 1\n";
        }
#endif
        return false;
    }
    
    const int cv1Val = CSBase::compareNonDominatedVecs(a.secondMin, b.secondMin);
#ifdef DOMHASHDEBUG
    assert(-1 * cv1Val == CSBase::compareNonDominatedVecs(b.secondMin, a.secondMin));
#endif
    if (cv1Val > 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 2\n";
        }
#endif
        return true;
    } else if (cv1Val < 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - no 2\n";
        }
#endif
        return false;
    }

    const int cv2Val = CSBase::compareNonDominatedVecs(a.secondMax, b.secondMax);
#ifdef DOMHASHDEBUG
    assert(-1 * cv2Val == CSBase::compareNonDominatedVecs(b.secondMax, a.secondMax));
#endif
    if (cv2Val > 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 3\n";
        }
#endif
        return true;
    } else if (cv2Val < 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - no 3\n";
        }
#endif
        return false;
    }

    const int saVal = CSBase::compareMaps(a.startedActions, b.startedActions);
#ifdef DOMHASHDEBUG
    assert(-1 * saVal == CSBase::compareMaps(b.startedActions, a.startedActions));
#endif
    if (saVal > 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 4\n";
        }
#endif
        return true;
    } else if (saVal < 0) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - no 4\n";
        }
#endif
        return false;
    }

    if (a.nextTIL < b.nextTIL) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 5\n";
        }
#endif
        return true;
    } else if (a.nextTIL > b.nextTIL) {
#ifdef DOMHASHDEBUG
        if (shdVerbose) {
            cout << " - no 5\n";
        }
#endif
        return false;
    }

#ifdef DOMHASHDEBUG
    if (shdVerbose) {
        cout << " - identical (excluding comparisons on variables with dominance constraints)\n";
    }
#endif

    return false;

    
}

bool baseLessThan(const ExtendedMinimalState & ae, const ExtendedMinimalState & be)
{

    const MinimalState & a = ae.getInnerState();
    const MinimalState & b = be.getInnerState();

#ifdef STATEHASHDEBUG
    const bool shdVerbose = false;
    if (shdVerbose) {
        cout << "Seeing if " << &ae << " < " << &be;
        cout.flush();
    }
#endif

    const int csVal = CSBase::compareSets(a.first, b.first);
#ifdef STATEHASHDEBUG
    assert(-1*csVal == CSBase::compareSets(b.first, a.first));
#endif
    if (csVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 1\n";
        }
#endif
        return true;
    } else if (csVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 1\n";
        }
#endif
        return false;
    }

    const int cv1Val = CSBase::compareVecs(a.secondMin, b.secondMin);
#ifdef STATEHASHDEBUG
    assert(-1 * cv1Val == CSBase::compareVecs(b.secondMin, a.secondMin));
#endif
    if (cv1Val > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 2\n";
        }
#endif
        return true;
    } else if (cv1Val < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 2\n";
        }
#endif
        return false;
    }

    const int cv2Val = CSBase::compareVecs(a.secondMax, b.secondMax);
#ifdef STATEHASHDEBUG
    assert(-1 * cv2Val == CSBase::compareVecs(b.secondMax, a.secondMax));
#endif
    if (cv2Val > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 3\n";
        }
#endif
        return true;
    } else if (cv2Val < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 3\n";
        }
#endif
        return false;
    }


    const int saVal = CSBase::compareMaps(a.startedActions, b.startedActions);
#ifdef STATEHASHDEBUG
    assert(-1 * saVal == CSBase::compareMaps(b.startedActions, a.startedActions));
#endif
    if (saVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 4\n";
        }
#endif
        return true;
    } else if (saVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 4\n";
        }
#endif
        return false;
    }

    if (a.nextTIL < b.nextTIL) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 5\n";
        }
#endif
        return true;
    } else if (a.nextTIL > b.nextTIL) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 5\n";
        }
#endif
        return false;
    }

#ifdef STATEHASHDEBUG
    if (shdVerbose) {
        cout << " - identical\n";
    }
#endif



    return false;
}

bool secondaryLessThan(const ExtendedMinimalState & ae, const ExtendedMinimalState & be)
{

    const MinimalState & a = ae.getInnerState();
    const MinimalState & b = be.getInnerState();

#ifdef STATEHASHDEBUG
    const bool shdVerbose = false;
    if (shdVerbose) {
        cout << "Secondary map - seeing if " << &ae << " < " << &be;
        cout.flush();
    }
#endif

    const int caVal = CSBase::compareAnnotations(a.first, b.first);

#ifdef STATEHASHDEBUG
    assert(-1*caVal == CSBase::compareAnnotations(b.first, a.first));
#endif

    if (caVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes s1\n";
        }
#endif
        return true;
    } else if (caVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no s1\n";
        }
#endif
        return false;
    }


    const int ceVal = CSBase::compareLists(ae.startEventQueue, be.startEventQueue);
#ifdef STATEHASHDEBUG
    assert((-1 * ceVal) == CSBase::compareLists(be.startEventQueue, ae.startEventQueue));
#endif
    if (ceVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes s2\n";
        }
#endif
        return true;
    } else if (ceVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no s2\n";
        }
#endif
        return false;
    }
#ifdef STATEHASHDEBUG
    if (shdVerbose) {
        cout << " - identical\n";
    }
#endif

    return false;

}

bool fullLessThan(const ExtendedMinimalState & ae, const ExtendedMinimalState & be)
{


    const MinimalState & a = ae.getInnerState();
    const MinimalState & b = be.getInnerState();
    
#ifdef STATEHASHDEBUG
    const bool shdVerbose = true;
    if (shdVerbose) {
        cout << "Seeing if " << &ae << " < " << &be;
        cout.flush();
    }
#endif

    const int csVal = CSBase::compareSets(a.first, b.first);
#ifdef STATEHASHDEBUG
    assert(-1*csVal == CSBase::compareSets(b.first, a.first));
#endif
    if (csVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 1\n";
        }
#endif
        return true;
    } else if (csVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 1\n";
        }
#endif
        return false;
    }

    const int cv1Val = CSBase::compareVecs(a.secondMin, b.secondMin);
#ifdef STATEHASHDEBUG
    assert(-1 * cv1Val == CSBase::compareVecs(b.secondMin, a.secondMin));
#endif
    if (cv1Val > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 2\n";
        }
#endif
        return true;
    } else if (cv1Val < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 2\n";
        }
#endif
        return false;
    }

    const int cv2Val = CSBase::compareVecs(a.secondMax, b.secondMax);
#ifdef STATEHASHDEBUG
    assert(-1 * cv2Val == CSBase::compareVecs(b.secondMax, a.secondMax));
#endif
    if (cv2Val > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 3\n";
        }
#endif
        return true;
    } else if (cv2Val < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 3\n";
        }
#endif
        return false;
    }


    const int saVal = CSBase::compareMaps(a.startedActions, b.startedActions);
#ifdef STATEHASHDEBUG
    assert(-1 * saVal == CSBase::compareMaps(b.startedActions, a.startedActions));
#endif
    if (saVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 4\n";
        }
#endif
        return true;
    } else if (saVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 4\n";
        }
#endif
        return false;
    }

    if (a.nextTIL < b.nextTIL) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes 5\n";
        }
#endif
        return true;
    } else if (a.nextTIL > b.nextTIL) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no 5\n";
        }
#endif
        return false;
    }

#ifdef STATEHASHDEBUG
    if (shdVerbose) {
        cout << " - identical\n";
    }
#endif


    const int caVal = CSBase::compareAnnotations(a.first, b.first);

#ifdef STATEHASHDEBUG
    assert(-1*caVal == CSBase::compareAnnotations(b.first, a.first));
#endif

    if (caVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes s1\n";
        }
#endif
        return true;
    } else if (caVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no s1\n";
        }
#endif
        return false;
    }


    const int ceVal = CSBase::compareLists(ae.startEventQueue, be.startEventQueue);
#ifdef STATEHASHDEBUG
    assert((-1 * ceVal) == CSBase::compareLists(be.startEventQueue, ae.startEventQueue));
#endif
    if (ceVal > 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - yes s2\n";
        }
#endif
        return true;
    } else if (ceVal < 0) {
#ifdef STATEHASHDEBUG
        if (shdVerbose) {
            cout << " - no s2\n";
        }
#endif
        return false;
    }
#ifdef STATEHASHDEBUG
    if (shdVerbose) {
        cout << " - identical\n";
    }
#endif

    return false;
    
}



};

bool SecondaryExtendedStateLessThan::operator()(const ExtendedMinimalState * const ae, const ExtendedMinimalState * const be) const
{
    return operator()(*ae, *be);
}

bool SecondaryExtendedStateLessThan::operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const
{
    return CSBase::secondaryLessThan(ae, be);
}




bool WeakExtendedStateLessThan::operator()(const ExtendedMinimalState * const ae, const ExtendedMinimalState * const be) const
{
    return operator()(*ae, *be);
}

bool WeakExtendedStateLessThan::operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const
{
    return CSBase::baseLessThan(ae, be);
}

bool FullExtendedStateLessThan::operator()(const ExtendedMinimalState * const ae, const ExtendedMinimalState * const be) const
{
    return operator()(*ae, *be);
}

bool FullExtendedStateLessThan::operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const
{
    return CSBase::fullLessThan(ae, be);
}


bool ExtendedStateLessThanOnPropositionsAndNonDominatedVariables::operator()(const ExtendedMinimalState * const ae, const ExtendedMinimalState * const be) const
{
    return operator()(*ae, *be);
}

bool ExtendedStateLessThanOnPropositionsAndNonDominatedVariables::operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const
{
    return CSBase::propAndNonDominatedVariableLessThan(ae, be);
}


class SearchQueueItem
{

private:
    ExtendedMinimalState * internalState;
    bool ownState;

public:
#ifdef STATEHASHDEBUG
    bool mustNotDeleteState;
#endif


    inline ExtendedMinimalState * state() {
        return internalState;
    }

    list<FFEvent> plan;

    list<ActionSegment> helpfulActions;
    FF::HTrio heuristicValue;

    SearchQueueItem()
            : internalState(0), ownState(false) {
#ifdef STATEHASHDEBUG
        mustNotDeleteState = false;
#endif
    }



    /**
     *  Create a search queue item for the specified state.
     *
     *  @param sIn              The state to store in the search queue item
     *  @param clearIfDeleted   If <code>true</code>, mark that <code>sIn</code> should be deleted
     *                          if the search queue item is deleted (unless <code>releaseState()</code>
     *                          is called first).
     */
    SearchQueueItem(ExtendedMinimalState * const sIn, const bool clearIfDeleted)
            : internalState(sIn), ownState(clearIfDeleted) {
#ifdef STATEHASHDEBUG
        mustNotDeleteState = false;
#endif
        //cout << "Created SQI at " << this << " with EMS " << sIn << endl;
    }

    ~SearchQueueItem() {
        if (ownState) {
#ifdef STATEHASHDEBUG
            assert(!mustNotDeleteState);
#endif
            delete internalState;
        }
    }


    /**
     *  Return the state held in this search queue item, flagging that it should not be deleted by
     *  the search queue item's destructor.
     *
     *  @return The state held in this search queue item
     */
    ExtendedMinimalState * releaseState() {
        assert(ownState);
        ownState = false;
        return internalState;
    }


    void printPlan() {
        if (Globals::globalVerbosity & 2) {
            list<FFEvent>::iterator planItr = plan.begin();
            const list<FFEvent>::iterator planEnd = plan.end();

            for (int i = 0; planItr != planEnd; ++planItr, ++i) {
                if (planItr->isDummyStep()) {
                    cout << i << ": dummy step";
                } else {
                    if (!planItr->getEffects) cout << "(( ";
                    if (planItr->action) {
                        cout << i << ": " << *(planItr->action) << ", " << (planItr->time_spec == Planner::E_AT_START ? "start" : "end");
                    } else if (planItr->time_spec == Planner::E_AT) {
                        cout << i << ": TIL " << planItr->divisionID;

                    } else {
                        cout << i << ": null node!";
                        assert(false);
                    }
                    if (!planItr->getEffects) cout << " ))";
                }
                cout << " at " << planItr->lpMinTimestamp;
                cout << "\n";
            }
        }
    }

};

class SearchQueue
{

private:

    map<double, list<SearchQueueItem*> > qOne;
    map<double, list<SearchQueueItem*> > qTwo;
public:

    ~SearchQueue() {
        clear();
    }

    void clear() {
        for (int pass = 0; pass < 2; ++pass) {

            map<double, list<SearchQueueItem*> > & currMap = (pass ? qTwo : qOne);
            map<double, list<SearchQueueItem*> >::iterator cmItr = currMap.begin();
            const map<double, list<SearchQueueItem*> >::iterator cmEnd = currMap.end();

            for (; cmItr != cmEnd; ++cmItr) {
                list<SearchQueueItem*>::iterator qItr = cmItr->second.begin();
                const list<SearchQueueItem*>::iterator qEnd = cmItr->second.end();

                for (; qItr != qEnd; ++qItr) delete *qItr;
            }
            currMap.clear();

        }
    }

    SearchQueueItem* pop_front() {
        static int lastTime = 0;
        if (!qOne.empty()) {
            if (lastTime != 1) {
                lastTime = 1;
                if (Globals::globalVerbosity & 1) {
                    cout << "\n1: ";
                    cout.flush();
                }
            }
            map<double, list<SearchQueueItem*> >::iterator mItr = qOne.begin();
            SearchQueueItem* const toReturn = mItr->second.front();
            mItr->second.pop_front();
            if (mItr->second.empty()) qOne.erase(mItr);
            return toReturn;
        } else {
            if (lastTime != 2) {
                lastTime = 2;
                if (Globals::globalVerbosity & 1) {
                    cout << "\n2: ";
                    cout.flush();
                }
            }
            map<double, list<SearchQueueItem*> >::iterator mItr = qTwo.begin();
            SearchQueueItem* const toReturn = mItr->second.front();
            mItr->second.pop_front();
            if (mItr->second.empty()) qTwo.erase(mItr);
            return toReturn;
        }
    }

    SearchQueueItem * back() {
        if (qTwo.empty()) {
            return qOne.rbegin()->second.back();
        } else {
            return qTwo.rbegin()->second.back();
        }
    }

    void push_back(SearchQueueItem* p, const int category = 1) {
        
        list<SearchQueueItem*> & q = (category == 1 ? qOne[p->heuristicValue.qbreak] : qTwo[p->heuristicValue.qbreak]);

        list<SearchQueueItem*>::iterator qItr = q.begin();
        const list<SearchQueueItem*>::iterator qEnd = q.end();
        for (; qItr != qEnd; ++qItr) {
            if (p->heuristicValue < (*qItr)->heuristicValue) {
                q.insert(qItr, p);
                return;
            }
        }
        q.push_back(p);

    }

    void insert(SearchQueueItem* p, const int category = 1) {

        if (FF::costOptimalAStar) {
            const double pCost = p->heuristicValue.admissibleCostEstimate;
            list<SearchQueueItem*> & q = (category == 1 ? qOne[pCost] : qTwo[pCost]);
            
            list<SearchQueueItem*>::iterator qItr = q.begin();
            const list<SearchQueueItem*>::iterator qEnd = q.end();
            for (; qItr != qEnd; ++qItr) {
                if (p->heuristicValue < (*qItr)->heuristicValue) {
                    q.insert(qItr, p);
                    return;
                }
            }
            q.push_back(p);
            
            return;
        }
        
        double prim = p->heuristicValue.heuristicValue;
        if (FF::WAStar) {
            prim *= FF::doubleU;
            if (FF::timeWAStar) {
                prim += p->state()->timeStamp;
            } else {
                const int pps = p->state()->getInnerState().planLength - p->state()->getInnerState().actionsExecuting - p->state()->getInnerState().nextTIL;
                prim += pps;
            }
        }
        list<SearchQueueItem*> & q = (category == 1 ? qOne[prim] : qTwo[prim]);
        if (q.empty()) {
            q.push_back(p);
            return;
        }

        if (FF::biasG) {
            list<SearchQueueItem*>::iterator qItr = q.begin();
            const list<SearchQueueItem*>::iterator qEnd = q.end();
            for (; qItr != qEnd; ++qItr) {
                if (p->heuristicValue < (*qItr)->heuristicValue) {
                    q.insert(qItr, p);
                    return;
                }
            }
        }
        if (FF::openListOrderLowMakespanFirst) {
            list<SearchQueueItem*>::iterator qItr = q.begin();
            const list<SearchQueueItem*>::iterator qEnd = q.end();
            for (; qItr != qEnd; ++qItr) {
                if (p->heuristicValue.makespanEstimate < (*qItr)->heuristicValue.makespanEstimate) {
                    q.insert(qItr, p);
                    return;
                }
            }
        }
        if (FF::openListOrderLowCostFirst) {
            const double pCost = p->heuristicValue.admissibleCostEstimate; // p->state()->getInnerState().calculateCost();
            list<SearchQueueItem*>::iterator qItr = q.begin();
            const list<SearchQueueItem*>::iterator qEnd = q.end();
            for (; qItr != qEnd; ++qItr) {
                if (pCost < (*qItr) ->heuristicValue.admissibleCostEstimate) {//  (*qItr)->state()->getInnerState().calculateCost()) {
                    q.insert(qItr, p);
                    return;
                }
            }
        }

        
        q.push_back(p);

    }


    bool empty() const {
        return (qOne.empty() && qTwo.empty());
    }

};

void populateTimestamps(vector<double> & minTimestamps, double & makespan, list<FFEvent> & header, list<FFEvent> & now)
{
    int stepID = 0;

    if (Globals::globalVerbosity & 4) {
        cout << "[";
    }
    
    for (int pass = 0; pass < 2; ++pass) {
        list<FFEvent>::iterator planItr = (pass ? now.begin() : header.begin());
        const list<FFEvent>::iterator planEnd = (pass ? now.end() : header.end());

        for (; planItr != planEnd; ++planItr, ++stepID) {
            #ifdef STOCHASTICDURATIONS
            const double curr = planItr->stochasticTimestamp->getTimestampForRPGHeuristic();
            #else
            const double curr = planItr->lpMinTimestamp;
            #endif
            assert(curr >= 0.0);
            //cout << "Min timestamp of step " << stepID << endl;
            //cout << " = " << curr << endl;
            minTimestamps[stepID] = curr;
            if (curr > makespan) makespan = curr;
            if (Globals::globalVerbosity & 4) {
                cout << " " << stepID << ":" << minTimestamps[stepID];
            }
        }
    }
    
    if (Globals::globalVerbosity & 4) {
        cout << " ]\n";
    }
}

bool FF::relaxMIP = false;

FF::HTrio FF::calculateHeuristicAndSchedule(ExtendedMinimalState & theState, ExtendedMinimalState * prevState, set<int> & goals, set<int> & goalFluents,
                                            ParentData * const incrementalData, list<ActionSegment> & helpfulActions, pair<bool,double> & currentCost,
                                            list<FFEvent> & header, list<FFEvent> & now, const int & stepID, bool considerCache, map<double, list<pair<int, int> > > * justApplied, double tilFrom)
{

    if (evaluationDiagnostics) {
        cout << COLOUR_yellow << "  calculateHeuristicAndSchedule():\n" << COLOUR_default;
    }

    //cout << "Evaluating a state reached by " << header.size() + now.size() << " snap actions\n";
    //cout << "Has " << theState.startedActions.size() << " sorts of actions on the go\n";
//  LPScheduler tryToSchedule(header, now, theState.entriesForAction, (prevState ? &prevState->secondMin : 0), (prevState ? &prevState->secondMax : 0));

    if (FF::relaxMIP) {
        alwaysLPRelaxation = !scheduleToMetric;
    }

    LPScheduler tryToSchedule(theState.getInnerState(), theState.getEditableInnerState().preferenceStatus, header, now, stepID, theState.startEventQueue, incrementalData, theState.entriesForAction, (prevState ? &prevState->getInnerState().secondMin : 0), (prevState ? &prevState->getInnerState().secondMax : 0), &(theState.tilComesBefore), scheduleToMetric);

    if (scheduleToMetric) {
        HTrio toReturn(0, 0.0, 0.0, theState.getInnerState().planLength - theState.getInnerState().actionsExecuting, "Evaluated Successfully");        
        return toReturn;        
    }

#ifdef SCHEDULETWICE
    MinimalState scheduleTwiceState(theState.getInnerState());
    LPScheduler tryToScheduleAgain(scheduleTwiceState, scheduleTwiceState.preferenceStatus, header, now, stepID, theState.startEventQueue, incrementalData, theState.entriesForAction, (prevState ? &prevState->getInnerState().secondMin : 0), (prevState ? &prevState->getInnerState().secondMax : 0), &(theState.tilComesBefore), scheduleToMetric);
#endif
        
    if (!tryToSchedule.isSolved()) {
        if (evaluationDiagnostics) {
            cout << COLOUR_yellow << "\tState was not scheduled successfully" << COLOUR_default << endl;
        }
        return HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "LP deemed action choice invalid");
    }

    vector<double> timeAtWhichValueIsDefined;
    
    tryToSchedule.removeExpiredAbstractFacts(theState.getEditableInnerState().first);
    tryToSchedule.updateStateFluents(theState.getEditableInnerState().secondMin, theState.getEditableInnerState().secondMax, timeAtWhichValueIsDefined);

    #ifdef SCHEDULETWICE
    vector<double> timeAtWhichValueIsDefinedAgain;
    tryToScheduleAgain.removeExpiredAbstractFacts(scheduleTwiceState.first);
    tryToScheduleAgain.updateStateFluents(scheduleTwiceState.secondMin, scheduleTwiceState.secondMax, timeAtWhichValueIsDefinedAgain);
    #endif
    
    vector<double> extrapolatedMin, extrapolatedMax;
    
    if (LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction) {   
        extrapolatedMin = theState.getEditableInnerState().secondMin;
        extrapolatedMax = theState.getEditableInnerState().secondMax;
        tryToSchedule.extrapolateBoundsAfterRecentAction(&(theState.startEventQueue), extrapolatedMin, extrapolatedMax, timeAtWhichValueIsDefined);
    }
    
    #ifndef NDEBUG
    if (Globals::optimiseSolutionQuality && !RPGBuilder::getPreferences().empty() && tryToSchedule.werePlanCostsCalculated()) {
        if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            if (RPGBuilder::getMetric()->minimise) {
                if (!(tryToSchedule.getReachablePlanCost() >= RPGBuilder::getMetric()->constant + PreferenceHandler::getReachableCost(theState.getInnerState()) - 0.001)) {
                    std::cerr << "Fatal internal error: LP reachable cost estimate of " << tryToSchedule.getReachablePlanCost() << " should not be less than reachable preference cost of " << PreferenceHandler::getReachableCost(theState.getInnerState()) << endl;
                    std::cerr << "; Current violations: " << PreferenceHandler::getCurrentViolations(theState.getInnerState()) << endl;
                    
                    assert(tryToSchedule.getReachablePlanCost() >= PreferenceHandler::getReachableCost(theState.getInnerState()) - 0.001);
                }
            } else {
                if (!(tryToSchedule.getReachablePlanCost() <= RPGBuilder::getMetric()->constant + PreferenceHandler::getReachableCost(theState.getInnerState()) + 0.001)) {
                    std::cerr << "Fatal internal error: LP reachable reward estimate of " << tryToSchedule.getReachablePlanCost() << " should not be more than reachable preference cost of " << PreferenceHandler::getReachableCost(theState.getInnerState()) << endl;
                    std::cerr << "; Current violations: " << PreferenceHandler::getCurrentViolations(theState.getInnerState()) << endl;
                    assert(tryToSchedule.getReachablePlanCost() <= PreferenceHandler::getReachableCost(theState.getInnerState()) + 0.001);
                }
            }
        }
    }
    #endif
                                
    
    
    if (skipRPG) {
        if (LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction) {   
            theState.getEditableInnerState().secondMin.swap(extrapolatedMin);
            theState.getEditableInnerState().secondMax.swap(extrapolatedMax);
        }
        if (evaluationDiagnostics) {
            cout << COLOUR_yellow << "\tSkipping RPG" << COLOUR_default << endl;
        }
        return HTrio(-2.0, -2.0, -2.0, INT_MAX, "skipRPG specified - skipping RPG evaluation");
    }

    vector<double> minTimestamps(theState.getInnerState().planLength);
    double makespan = 0.0;

    populateTimestamps(minTimestamps, makespan, header, now);

    double costLimit = -DBL_MAX;
    
    if (NumericAnalysis::theMetricIsMonotonicallyWorsening() && tryToSchedule.werePlanCostsCalculated() && Globals::bestSolutionQuality != -DBL_MAX) {
        if (RPGBuilder::getMetric()->minimise) {
            costLimit = Globals::bestSolutionQuality + tryToSchedule.getReachablePlanCost();
        } else {
            costLimit = Globals::bestSolutionQuality - tryToSchedule.getReachablePlanCost();
        }
        if (Globals::globalVerbosity & 16) {
            cout << COLOUR_light_green << "Cost limit: " << costLimit << ", given reachable plan cost of " << tryToSchedule.getReachablePlanCost() << " and incumbent of quality " << Globals::bestSolutionQuality << COLOUR_default << endl;
        }
        
    }
 
#ifdef RELAXEDPLANTWICE
    {
        MinimalState dummy(theState.getEditableInnerState());
        double dummyTimestamp = theState.timeStamp;
        list<ActionSegment> dummyHA;
        double mes = 0.0;
        list<pair<double, list<ActionSegment> > > relaxedPlan;
        
        delete RPGBuilder::getHeuristic()->getRelaxedPlan(dummy, &(theState.startEventQueue), minTimestamps, dummyTimestamp, costLimit,
                                                          extrapolatedMin, extrapolatedMax, timeAtWhichValueIsDefined,                                  // for colin-jair heuristic
                                                          dummyHA, relaxedPlan, mes, justApplied, tilFrom);
                                                          
        --RPGHeuristic::statesEvaluated;
        
    }
#endif
    
    list<pair<double, list<ActionSegment> > > relaxedPlan;

    //printState(theState);
    static int oldBestH = INT_MAX;

    auto_ptr<RPGHeuristic::EvaluationInfo> h(0);
    double makespanEstimate = 0.0;
    if (considerCache) {
        if (FFcache_upToDate) {
            relaxedPlan = FFcache_relaxedPlan;
            helpfulActions.insert(helpfulActions.end(), FFcache_helpfulActions.begin(), FFcache_helpfulActions.end());
            h = auto_ptr<RPGHeuristic::EvaluationInfo>(new RPGHeuristic::EvaluationInfo(FFcache_h));
            makespanEstimate = FFcache_makespanEstimate;
            cout << "*";
            cout.flush();
        } else {
            if (evaluationDiagnostics) {
                cout << COLOUR_yellow << "\tGetting a relaxed plan\n" << COLOUR_default << endl;
            }
            h = auto_ptr<RPGHeuristic::EvaluationInfo>(RPGBuilder::getHeuristic()->getRelaxedPlan(theState.getEditableInnerState(), &(theState.startEventQueue), minTimestamps, theState.timeStamp, costLimit,
                                                                                                   extrapolatedMin, extrapolatedMax, timeAtWhichValueIsDefined,                                  // for colin-jair heuristic
                                                                                                   helpfulActions, relaxedPlan, makespanEstimate, justApplied, tilFrom));

            FFcache_relaxedPlan = relaxedPlan;
            FFcache_helpfulActions = helpfulActions;
            FFcache_h = RPGHeuristic::EvaluationInfo(*(h.get()));
            FFcache_makespanEstimate = makespanEstimate;
            FFcache_upToDate = true;
        }
    } else {
        //printState(theState);
        if (evaluationDiagnostics) {
            cout << COLOUR_yellow << "\tGetting a relaxed plan\n" << COLOUR_default << endl;
        }

        h = auto_ptr<RPGHeuristic::EvaluationInfo>(RPGBuilder::getHeuristic()->getRelaxedPlan(theState.getEditableInnerState(), &(theState.startEventQueue), minTimestamps, theState.timeStamp, costLimit,
                                                                                               extrapolatedMin, extrapolatedMax, timeAtWhichValueIsDefined,                                      // for colin-jair heuristic
                                                                                               helpfulActions, relaxedPlan, makespanEstimate, justApplied, tilFrom));

    }

    if (h->getH() < 0) return HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "RPG heuristic detected a deadend");

    if (h->getH() < oldBestH) {
        oldBestH = h->getH();
    }


    
    bool cycle = false;

    if (FF::incrementalExpansion && !FFonly_one_successor) {

        assert(false);
    } else {
        const bool oldVal = FF::incrementalExpansion;
        FF::incrementalExpansion = false;
        if (!RPGHeuristic::blindSearch) {
            cycle = !tryToSchedule.addRelaxedPlan(theState.startEventQueue, theState.getEditableInnerState().preferenceStatus, theState.getEditableInnerState().prefPreconditionViolations, header, now, relaxedPlan, stepID);
            if (!cycle) {
                tryToSchedule.removeExpiredAbstractFacts(theState.getEditableInnerState().first);
            }
            
            #ifdef SCHEDULETWICE
            tryToScheduleAgain.addRelaxedPlan(theState.startEventQueue, scheduleTwiceState.preferenceStatus, scheduleTwiceState.prefPreconditionViolations, header, now, relaxedPlan, stepID);
            if (!cycle) {
                tryToScheduleAgain.removeExpiredAbstractFacts(scheduleTwiceState.first);
            }
            
            #endif
        }
        FF::incrementalExpansion = oldVal;
    }

    auto_ptr<LPScheduler> mipModel;
    
    LPScheduler * scheduleToUse = &tryToSchedule;
    
    if (h->goalState) {
        
        int wo;
        if (FF::relaxMIP) {
            alwaysLPRelaxation = false;
            mipModel = auto_ptr<LPScheduler>(new LPScheduler(theState.getInnerState(), theState.getEditableInnerState().preferenceStatus, header, now, stepID, theState.startEventQueue, incrementalData, theState.entriesForAction, (prevState ? &prevState->getInnerState().secondMin : 0), (prevState ? &prevState->getInnerState().secondMax : 0), &(theState.tilComesBefore), scheduleToMetric));
            if (!mipModel->isSolved()) {
                return HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "MIP deemed action choice invalid");
            }
            
            wo = (mipModel->isSolution(theState.getInnerState(), header, now) ? 0 : 1);
            if (!wo) {
                scheduleToUse = mipModel.get();
            }
        } else {
            wo = (tryToSchedule.isSolution(theState.getInnerState(), header, now) ? 0 : 1);
            #ifdef SCHEDULETWICE
            tryToScheduleAgain.isSolution(scheduleTwiceState, header, now);
            #endif
        }
        if (wo) {
            h->incrementH(wo);
            h->goalState = false;
        }
        if (h->goalState && false) {
            int s = 0;
            for (int pass = 0; pass < 2; ++pass) {
                list<FFEvent>::iterator pItr = (pass ? now.begin() : header.begin());
                list<FFEvent>::iterator pEnd = (pass ? now.end() : header.end());
                for (; pItr != pEnd; ++pItr) {
                    cout << s << ": " << pItr->lpTimestamp << "\n";
                    ++s;
                }
            }
        }
    }


    if (cycle) {
        if (Globals::globalVerbosity & 1) cout << "c";
        return HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Cycle detected when adding relaxed plan data to LP");
    }


    if (LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction) {   
        theState.getEditableInnerState().secondMin.swap(extrapolatedMin);
        theState.getEditableInnerState().secondMax.swap(extrapolatedMax);
    }

    HTrio toReturn(h->getH(), makespan, makespanEstimate, theState.getInnerState().planLength - theState.getInnerState().actionsExecuting, "Evaluated Successfully", h->goalState);    
    
    toReturn.admissibleCostEstimate = h->admissibleReachablePrefCost;
    
    if (scheduleToUse->werePlanCostsCalculated()) {
        
        currentCost.first = true;
        currentCost.second = scheduleToUse->getCurrentPlanCost();
        
        if (Globals::globalVerbosity & 2) {
            cout << "/" << currentCost.second << "/";
            cout.flush();
        }
        if (NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            if (RPGBuilder::getMetric()->minimise) {
                
                if (scheduleToUse->getReachablePlanCost() > toReturn.admissibleCostEstimate) {
                    //cout << "LP boosted admissible cost estimate from " << toReturn.admissibleCostEstimate << " to " << tryToSchedule.getReachablePlanCost() << endl;
                    toReturn.admissibleCostEstimate = scheduleToUse->getReachablePlanCost();
                    
                } else {
                    //cout << "LP could not do better than the existing admissible cost estimate of " << toReturn.admissibleCostEstimate << endl;
                }
                
            } else {
                
                if (scheduleToUse->getReachablePlanCost() < toReturn.admissibleCostEstimate) {
                    toReturn.admissibleCostEstimate = scheduleToUse->getReachablePlanCost();
                }
                
            }
        }
        
    } else {
        if (Globals::globalVerbosity & 2) {
            cout << "/N/A/";
            cout.flush();
        }
    }
    
    //cout << "<ace=" << toReturn.admissibleCostEstimate << ">";
    //cout.flush();
    
    return toReturn;
}


FF::HTrio FF::calculateHeuristicAndCompressionSafeSchedule(ExtendedMinimalState & theState, ExtendedMinimalState * prevState, set<int> & goals, set<int> & goalFluents, list<ActionSegment> & helpfulActions, list<FFEvent> & header, list<FFEvent> & now, const int & stepID, map<double, list<pair<int, int> > > * justApplied, double tilFrom)
{
    if (evaluationDiagnostics) {
        cout << COLOUR_yellow << "  calculateHeuristicAndCompressionSafeSchedule():\n" << COLOUR_default;
    }

    
    assert(!scheduleToMetric);
    //cout << "Evaluating a state reached by " << header.size() + now.size() << " snap actions\n";
    //cout << "Has " << theState.startedActions.size() << " sorts of actions on the go\n";
//  LPScheduler tryToSchedule(header, now, theState.entriesForAction, (prevState ? &prevState->secondMin : 0), (prevState ? &prevState->secondMax : 0));

    CompressionSafeScheduler::assignTimestamps(theState.getInnerState(), header, now);
    
    vector<double> timeAtWhichValueIsDefined;

    if (LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction) {
        timeAtWhichValueIsDefined.resize(theState.getInnerState().secondMin.size(), -1.0);        
    }
    
    if (skipRPG) {
        return HTrio(-2.0, -2.0, -2.0, INT_MAX, "skipRPG specified - skipping RPG evaluation");
    }

    vector<double> minTimestamps(theState.getInnerState().planLength);
    double makespan = 0.0;

    populateTimestamps(minTimestamps, makespan, header, now);

    list<pair<double, list<ActionSegment> > > relaxedPlan;

    //printState(theState);
    static int oldBestH = INT_MAX;

    double makespanEstimate = 0.0;
    auto_ptr<RPGHeuristic::EvaluationInfo> h(RPGBuilder::getHeuristic()->getRelaxedPlan(theState.getEditableInnerState(), &(theState.startEventQueue), minTimestamps, theState.timeStamp, -DBL_MAX,
                                                       theState.getInnerState().secondMin, theState.getInnerState().secondMax, timeAtWhichValueIsDefined,                                      // for colin-jair heuristic
                                                       helpfulActions, relaxedPlan, makespanEstimate, justApplied, tilFrom));

    if (h->getH() < 0) return HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "RPG heuristic detected a deadend");

    if (h->getH() < oldBestH) {
        oldBestH = h->getH();
    }


    
    HTrio toReturn(h->getH(), makespan, makespanEstimate, theState.getInnerState().planLength - theState.getInnerState().actionsExecuting, "Compression-Safe Evaluated Successfully", h->goalState);    
    toReturn.admissibleCostEstimate = h->admissibleReachablePrefCost;
    
    return toReturn;
}


ExtendedMinimalState * FF::applyActionToState(ActionSegment & actionToApply, const ExtendedMinimalState & parent, const list<FFEvent> & plan, list<pair<int, FFEvent> > & newDummySteps)
{

//  static const double EPSILON = 0.001;
    const bool localDebug = false;

    if (localDebug) {
        if (actionToApply.second == Planner::E_AT) {
            cout << "Applying TIL " << actionToApply.divisionID << " to state:\n";
        } else {
            cout << "Applying action " << *(actionToApply.first);
            if (actionToApply.second == Planner::E_AT_START) {
                cout << " start";
            } else {
                cout << " end";
            }
            cout << " to state:\n";
        }
        //printState(theState);
    }

//  assert(actionToApply.needToFinish.empty());


    assert(!actionToApply.first || !RPGBuilder::rogueActions[actionToApply.first->getID()]);
    assert(RPGBuilder::getHeuristic()->testApplicability(parent.getInnerState(), parent.timeStamp, actionToApply, true));

    static vector<double> minTimestamps(10, 0.0);
    static int tsVecSize = 10;
    
    list<FFEvent>::const_iterator pItr = plan.begin();
    const list<FFEvent>::const_iterator pEnd = plan.end();
    
    {
        int s = 0;
    
        for (; pItr != pEnd; ++pItr, ++s) {
            if (s >= tsVecSize) {
                tsVecSize += 10;
                minTimestamps.resize(tsVecSize, 0.0);
            }
            minTimestamps[s] = pItr->lpMinTimestamp;
        }
    
        if (actionToApply.second == Planner::E_AT) {
            
            const int extraForTILs = (actionToApply.divisionID - parent.getInnerState().nextTIL) + 1;
            
            if (s + extraForTILs * 2 >= tsVecSize) { // *2 because we might need a dummy step after each TIL for preferences
                tsVecSize += 10 + extraForTILs * 2;
                minTimestamps.resize(tsVecSize, 0.0);
            }
            
            for (int ex = 0; ex < extraForTILs; ++ex) {
                minTimestamps[s++] = 0.0;
                minTimestamps[s++] = 0.0;
            }
            
        } else {
    
            if (s + 4 >= tsVecSize) { // 4 because we might need a dummy step after each stage of the snap-action
                tsVecSize += 14;
                minTimestamps.resize(tsVecSize, 0.0);
            }
            
            minTimestamps[s++] = 0.0;
            minTimestamps[s++] = 0.0;
            minTimestamps[s++] = 0.0;
            minTimestamps[s++] = 0.0;
            
        }
    }
    
    bool constraintsSatisfied = true;
    
    if (actionToApply.second == Planner::E_AT) { // til actions
        assert(actionToApply.divisionID == parent.getInnerState().nextTIL);
        ExtendedMinimalState * toReturn = parent.applyAction(actionToApply, minTimestamps, newDummySteps, constraintsSatisfied);
        if (!constraintsSatisfied) {
            delete toReturn;
            return 0;
        }
        return toReturn;
    }

    double minDur = 0.0;
    double maxDur = 0.0;

    bool nonTemporal = false;

    RPGBuilder::LinearEffects * const lEffs = RPGBuilder::getLinearDiscretisation()[actionToApply.first->getID()];

    if (actionToApply.second != Planner::E_AT_END) {

        pair<double, double> actDur(RPGBuilder::getOpDuration(actionToApply.first->getID(), (actionToApply.second == Planner::E_OVER_ALL ? actionToApply.divisionID + 1 : 0), parent.getInnerState().secondMin, parent.getInnerState().secondMax));

        minDur = actDur.first;
        maxDur = actDur.second;

        nonTemporal = RPGBuilder::getRPGDEs(actionToApply.first->getID()).empty();

        if (Globals::globalVerbosity & 4096 && !nonTemporal) {
            cout << "- Calculated duration of new action as being in the range [" << minDur << "," << maxDur << "]\n";
        }

        if (!nonTemporal) {
            if (minDur > maxDur) return 0;
        }

    } else {
        map<int, list<list<StartEvent>::iterator > >::const_iterator tsiOld = parent.entriesForAction.find(actionToApply.first->getID());
        assert(tsiOld != parent.entriesForAction.end());

        const list<StartEvent>::iterator pairWith = tsiOld->second.front();
        minDur = pairWith->minDuration;
        maxDur = pairWith->maxDuration;

    }


    ExtendedMinimalState * const toReturn = parent.applyAction(actionToApply, minTimestamps, newDummySteps, constraintsSatisfied, minDur, maxDur);

    if (!constraintsSatisfied) {
        delete toReturn;
        return 0;
    }
    
    if (actionToApply.second == Planner::E_AT_START) {

        if (!nonTemporal) {
            if (TemporalAnalysis::canSkipToEnd(actionToApply.first->getID())) {
                toReturn->startEventQueue.push_back(StartEvent(actionToApply.first->getID(), 0, toReturn->getInnerState().planLength - (2 + newDummySteps.size()), minDur, maxDur, 0.0));
            } else {
                toReturn->startEventQueue.push_back(StartEvent(actionToApply.first->getID(), 0, toReturn->getInnerState().planLength - (2 + newDummySteps.size()), minDur, maxDur, 0.0));
                list<StartEvent>::iterator backItr = toReturn->startEventQueue.end();
                --backItr;
                toReturn->entriesForAction[actionToApply.first->getID()].push_back(backItr);
                //cout << "Now " << theState.startedActions[actionToApply.first->getID()][0] << " instances of " << *(actionToApply.first) << " going\n";

            }
        }

    } else if (actionToApply.second == Planner::E_AT_END) {
        map<int, list<list<StartEvent>::iterator > >::iterator efaItr = toReturn->entriesForAction.find(actionToApply.first->getID());
        assert(efaItr != toReturn->entriesForAction.end());

        list<list<StartEvent>::iterator >::iterator efaMatch = efaItr->second.begin();
        const list<list<StartEvent>::iterator >::iterator efaEnd = efaItr->second.end();

        if (lEffs) {

            const int intToMatch = lEffs->divisions - 1;

            for (; efaMatch != efaEnd; ++efaMatch) {
                if ((*efaMatch)->divisionsApplied == intToMatch) break;
            }

            assert(efaMatch != efaEnd);


        }

        (*efaMatch)->terminated = true;

    } else {
        assert(false); // is neither a start nor an end
    }

    {
        set<int> checked;
        
        // check numeric invariants are all satisfied
        list<StartEvent>::const_iterator seqItr = toReturn->startEventQueue.begin();
        const list<StartEvent>::const_iterator seqEnd = toReturn->startEventQueue.end();       
        
        for (; seqItr != seqEnd; ++seqItr) {
            
            if (seqItr->terminated) {
                continue;
            }
            
            const list<int> & numInvs = RPGBuilder::getInvariantNumerics()[seqItr->actID];
            
            list<int>::const_iterator niItr = numInvs.begin();
            const list<int>::const_iterator niEnd = numInvs.end();
            
            for (; niItr != niEnd; ++niItr) {
                if (checked.insert(*niItr).second) {
                    const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[*niItr];
                    if (!currPre.isSatisfiedWCalculate(toReturn->getInnerState().secondMin, toReturn->getInnerState().secondMax)) {
                        if (Globals::globalVerbosity & 8192) {
                            cout << "Failed temporal soundness check: invariant " << currPre << " of " << *(RPGBuilder::getInstantiatedOp(seqItr->actID)) << " is now violated\n";
                        }
                        break;                        
                    }
                }
            }
            if (niItr != niEnd) {
                break;
            }
        }
        
        if (seqItr != seqEnd) {
            delete toReturn;
            return 0;
        }
        
    }

    return toReturn;
}

bool FF::stateHasProgressedBeyondItsParent(const ActionSegment & theAction, const ExtendedMinimalState & parent, const ExtendedMinimalState & child)
{
    
    if (theAction.second == Planner::E_AT_END || theAction.second == Planner::E_AT) {
        // ending an action or applying a TIL can be a good thing for temporal reasons
        // so assume it is, for completeness
        return true;
    }
    
    {
        // Check one: if child contains a fact that parent does not, progress has been made
        const StateFacts & childFacts = child.getInnerState().first;
        const StateFacts & parentFacts = parent.getInnerState().first;
        
        StateFacts::const_iterator cfItr = childFacts.begin();
        const StateFacts::const_iterator cfEnd = childFacts.end();
        
        StateFacts::const_iterator pfItr = parentFacts.begin();
        const StateFacts::const_iterator pfEnd = parentFacts.end();
        
        while (cfItr != cfEnd && pfItr != pfEnd) {
            if (FACTA(pfItr) < FACTA(cfItr)) {
                ++pfItr;
            } else if (FACTA(cfItr) < FACTA(pfItr)) {
                // have found a fact that is in child facts but not parents
                return true;
            } else {
               ++pfItr;
               ++cfItr;
            }
        }
        
        if (cfItr != cfEnd) {
            // still have facts left in the child - so it subsumes the parents facts
            return true;
        }
        
        
    }
    
    const list<int> & numStartEffs = RPGBuilder::getStartEffNumerics()[theAction.first->getID()];
    // If the action has numeric start effects...
    if (!numStartEffs.empty()) {
        
        // Check two: if a child contains a better value of a numeric variable, progress has been made
        const vector<NumericAnalysis::dominance_constraint> & dom = NumericAnalysis::getDominanceConstraints();
        
        list<int>::const_iterator effIdIterator = numStartEffs.begin();
        const list<int>::const_iterator effIdEnd = numStartEffs.end();
        
        for (; effIdIterator != effIdEnd; ++effIdIterator) {
            const int v = RPGBuilder::getNumericEff()[*effIdIterator].fluentIndex;
            
            const double & childLB = child.getInnerState().secondMin[v];
            const double & childUB = child.getInnerState().secondMax[v];

            const double & parentLB = parent.getInnerState().secondMin[v];
            const double & parentUB = parent.getInnerState().secondMax[v];
            
            
            switch (dom[v]) {
                case NumericAnalysis::E_NODOMINANCE:
                {
                    if (parentLB != childLB || parentUB != childUB) {
                        // no known dominance, and there's been some change - assume it might be useful
                        return true;
                    }
                    break;
                }
                case NumericAnalysis::E_SMALLERISBETTER:
                {
                    if (parentLB > childLB || parentUB > childUB) {
                        // smaller is better, and the child has a smaller upper or lower bound
                        return true;
                    }
                    break;
                }                    
                case NumericAnalysis::E_BIGGERISBETTER:
                {
                    if (parentLB < childLB || parentUB < childUB) {
                        // bigger is better, and the child has a bigger upper or lower bound
                        return true;
                    }
                    break;
                }
                case NumericAnalysis::E_IRRELEVANT:
                {
                    break;
                }
                case NumericAnalysis::E_METRICTRACKING:
                {
                    // TODO: check optimisation direction, only count beneficial metric change as useful
                    return true;
                }
                
            }
        }                
    }
    
    // If the code gets this far, there are no new facts, and no better numerics.  The only hope
    // is that it's the start of a temporal action with some end effects we might like.
    
    if (!RPGBuilder::getRPGDEs(theAction.first->getID()).empty()) {
        if (!RPGBuilder::getEndPropositionAdds()[theAction.first->getID()].empty()) {
            // Adds some facts at the end - might be useful
            return true;
        }
        if (!RPGBuilder::getEndEffNumerics()[theAction.first->getID()].empty()) {
            // TODO: check whether these are improving effects w.r.t. dominance constraints
            // For now, just return true as they might be.            
            return true;
        }

        if (RPGBuilder::getLinearDiscretisation()[theAction.first->getID()] && !RPGBuilder::getLinearDiscretisation()[theAction.first->getID()]->vars.empty()) {
            return true;
        }
    }
    
    // Either the action was a non-temporal action that did nothing interesting; or it was the start
    // of a temporal action that did nothing interesting, with an end that was going to do nothing
    // interesting.
    return false;
}


void ExtendedMinimalState::deQueueFirstOf(const int & actID, const int & divID)
{

    map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = entriesForAction.find(actID);
    assert(tsiOld != entriesForAction.end());

    list<list<StartEvent>::iterator >::iterator pwItr = tsiOld->second.begin();
    const list<list<StartEvent>::iterator >::iterator pwEnd = tsiOld->second.end();

    list<StartEvent>::iterator pairWith;

    bool removed = false;
    for (; pwItr != pwEnd; ++pwItr) {

        if ((*pwItr)->divisionsApplied == divID) {
            pairWith = *pwItr;
            tsiOld->second.erase(pwItr);
            removed = true;
            break;
        }
    }

    assert(removed);

    if (tsiOld->second.empty()) entriesForAction.erase(tsiOld);

    startEventQueue.erase(pairWith);

}

void ExtendedMinimalState::deQueueStep(const int & actID, const int & stepID)
{

    if (stepID == -1) return;

    map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = entriesForAction.find(actID);
    assert(tsiOld != entriesForAction.end());

    list<list<StartEvent>::iterator >::iterator pwItr = tsiOld->second.begin();
    const list<list<StartEvent>::iterator >::iterator pwEnd = tsiOld->second.end();

    for (; pwItr != pwEnd; ++pwItr) {
        if ((*pwItr)->stepID == stepID) {
            startEventQueue.erase(*pwItr);
            tsiOld->second.erase(pwItr);
            if (tsiOld->second.empty()) entriesForAction.erase(tsiOld);
            return;
        }
    }

    assert(pwItr != pwEnd);

}

     
static const bool pairingDebug = false;
         
void orderAllAppropriateBefore(TemporalConstraints * cons, const list<FFEvent> & header, const list<FFEvent> & nowList, const Planner::time_spec & time_spec, const int & prefID, const int & comeBeforeStep) {
    
    int stepID = 0;
    
    for (int pass = 0; pass < 2; ++pass) {
        
        const list<FFEvent> & currList = (pass ? nowList : header);
        
        list<FFEvent>::const_iterator sItr = currList.begin();
        const list<FFEvent>::const_iterator sEnd = currList.end();
        
        for (; sItr != sEnd; ++sItr, ++stepID) {
            if (sItr->time_spec == time_spec && sItr->divisionID == prefID) {
                cons->addOrdering(stepID, comeBeforeStep, false);
                if (pairingDebug) {
                    cout << "- Ordered after " << stepID << endl;
                }
            }
        }
        
    }
    
}

void FF::pairDummyStepsWithRealSteps(MinimalState & theState, int & currStepID, list<FFEvent> & header, list<FFEvent> & nowList, const list<pair<int, FFEvent> > & newDummySteps)
{
    
    if (newDummySteps.empty()) {
        return;
    }
        
    int stepID = header.size() + nowList.size();
    
    list<pair<int, FFEvent> >::const_iterator eItr = newDummySteps.begin();
    const list<pair<int, FFEvent> >::const_iterator eEnd = newDummySteps.end();
    
    for (; eItr != eEnd; ++eItr, ++stepID) {
        
        nowList.push_back(eItr->second);
        
        if (nowList.back().time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION) {
            continue;        
        }
        
        const int prefID =  nowList.back().divisionID;
        const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[prefID];                
        
        
        switch (pref.cons) {
            
            case VAL::E_ALWAYS:
            case VAL::E_SOMETIME:
            case VAL::E_WITHIN:
            {
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_GOAL_FALSE);
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                // single-point preferences, no need to add temporal constraints
                break;
            }
        
            case VAL::E_SOMETIMEBEFORE: {
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_GOAL_FALSE);
                
                if (nowList.back().time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                    // have sometime-before a b
                    // and are now at the a: order after all bs
                    
                    if (pairingDebug) {
                        cout << COLOUR_light_green << "Ordering step " << stepID << ", dummy for " << pref.name << " after earlier requirement-meeting dummies:\n" << COLOUR_default;
                    }
                    
                    orderAllAppropriateBefore(theState.temporalConstraints, header, nowList, Planner::E_DUMMY_TEMPORAL_GOAL_TRUE, prefID, stepID);
                }
                
                break;
            }
            case VAL::E_SOMETIMEAFTER:
            case VAL::E_ALWAYSWITHIN: {
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_GOAL_FALSE);
                assert(nowList.back().time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                
                if (nowList.back().time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE) {
                    // have sometime-after a b
                    // and are now at the b: order after all as              
                    if (pairingDebug) {
                        cout << COLOUR_light_green << "Ordering step " << stepID << ", dummy for " << pref.name << " after earlier trigger-meeting dummies:\n" << COLOUR_default;
                    }
                    
                    orderAllAppropriateBefore(theState.temporalConstraints, header, nowList, Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE, prefID, stepID);
                }
                                
                break;
            }
            case VAL::E_ATMOSTONCE: {
                // order after the most recent check before this one
                int localStepID = stepID;
                for (int pass = 0; pass < 2; ++pass) {
                    
                    const list<FFEvent> & currList = (pass ? header : nowList);
                    
                    list<FFEvent>::const_reverse_iterator sItr = currList.rbegin();
                    const list<FFEvent>::const_reverse_iterator sEnd = currList.rend();
                    
                    if (!pass) {
                        ++sItr;
                        --localStepID;
                    }
                    
                    for (; sItr != sEnd; ++sItr, --localStepID) {
                        if (   sItr->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_FALSE
                            || sItr->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE   ) {
                            
                            if (sItr->divisionID == prefID) {
                                theState.temporalConstraints->addOrdering(localStepID, stepID, false);
                                break;
                            }
                        }
                    }
                            
                    if (sItr != sEnd) {
                        break;
                    }
                }   
                break;  
                
            }
            case VAL::E_ATEND: {
                std::cerr << "Fatal internal error: should not have dummy steps for at-end preferences\n";
                exit(1);
            }
        }
            
        
        
        
    }
    
    
}

void FF::evaluateStateAndUpdatePlan(auto_ptr<SearchQueueItem> & succ,
                                    ExtendedMinimalState & state, ExtendedMinimalState * prevState,
                                    set<int> & goals, set<int> & goalFluents,
                                    ParentData * const incrementalData,
                                    list<ActionSegment> & helpfulActionsExport, pair<bool,double> & currentCost,
                                    const ActionSegment & actID,
                                    list<FFEvent> & header, const list<pair<int, FFEvent> > & newDummySteps)
{

    #ifdef POPF3ANALYSIS
    
    if (Globals::optimiseSolutionQuality && admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {
        
        succ->heuristicValue = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded incumbent solution cost");
        return;
    }
    #endif
    
    list<ActionSegment> helpfulActions;


    FFEvent extraEvent;
    FFEvent extraEventTwo;

    FFEvent * reusedEndEvent = 0;

    bool eventOneDefined = false;
    bool eventTwoDefined = false;

//  pair<int, ScheduleNode*> newCEN(0, 0);

    const bool rawDebug = false;

    map<double, list<pair<int, int> > > * justApplied = 0;
    map<double, list<pair<int, int> > > actualJustApplied;
    double tilFrom = 0.001;

    succ->plan = header;

    int stepID = -1;

    if (actID.second == Planner::E_AT_START) {
        if (rawDebug) cout << "RAW start\n";
        extraEvent = FFEvent(actID.first, state.startEventQueue.back().minDuration, state.startEventQueue.back().maxDuration);
        eventOneDefined = true;

        assert(extraEvent.time_spec == Planner::E_AT_START);
        makeJustApplied(actualJustApplied, tilFrom, state, true);
        if (!actualJustApplied.empty()) justApplied = &actualJustApplied;

        if (!RPGBuilder::getRPGDEs(actID.first->getID()).empty()) { // if it's not a non-temporal action

            const int startStepID = prevState->getInnerState().planLength;
            const int endStepID = startStepID + 1;
            
            extraEventTwo = FFEvent(actID.first, startStepID, state.startEventQueue.back().minDuration, state.startEventQueue.back().maxDuration);
            extraEvent.pairWithStep = endStepID;
            eventTwoDefined = true;

            if (!TemporalAnalysis::canSkipToEnd(actID.first->getID())) {
                extraEventTwo.getEffects = false;
            }

            stepID = startStepID;
        } else {
            stepID = prevState->getInnerState().planLength;
        }

    } else if (actID.second == Planner::E_AT_END) {
        if (rawDebug) cout << "RAW end\n";
        map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = state.entriesForAction.find(actID.first->getID());
        assert(tsiOld != state.entriesForAction.end());

        list<StartEvent>::iterator pairWith = tsiOld->second.front();
        tsiOld->second.pop_front();
        if (tsiOld->second.empty()) state.entriesForAction.erase(tsiOld);

        if (rawDebug || Globals::globalVerbosity & 1048576) cout << "Pairing with start at step " << pairWith->stepID << ", so activating end at " << pairWith->stepID + 1 << "\n";

        stepID = pairWith->stepID + 1;

        {
            list<FFEvent>::iterator pwItr = succ->plan.begin();
            for (int sID = 0; sID <= pairWith->stepID; ++sID, ++pwItr) ;
            pwItr->getEffects = true;
            reusedEndEvent = &(*pwItr);
        }

        state.startEventQueue.erase(pairWith);

        makeJustApplied(actualJustApplied, tilFrom, state, false);
        if (!actualJustApplied.empty()) justApplied = &actualJustApplied;
    } else {
        extraEvent = FFEvent(actID.divisionID);
        eventOneDefined = true;
        stepID = prevState->getInnerState().planLength;
    }


    FFcache_upToDate = false;

    list<FFEvent> nowList;

    //  extraEvent.needToFinish = actID.needToFinish;

    int currStepID = prevState->getInnerState().planLength;
    
    if (eventOneDefined) {
        nowList.push_back(extraEvent);
        ++currStepID;
    }
    
    if (eventTwoDefined) {
        nowList.push_back(extraEventTwo);
        ++currStepID;
    }
        
    const size_t dsCount = newDummySteps.size();
    
    pairDummyStepsWithRealSteps(state.getEditableInnerState(), currStepID, succ->plan, nowList, newDummySteps);
    
    

    #ifdef STOCHASTICDURATIONS
    
    bool isAStochasticGoalState = false;
    
    if (actID.second == Planner::E_AT_END) {
        if (!durationManager->updateTimestampsOfNewPlanStep(prevState->getInnerState(), state.getEditableInnerState(), succ->plan, reusedEndEvent, 0, stepID, isAStochasticGoalState)) {
            succ->heuristicValue = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded stochastic deadline");
            return;
        }
    } else {
        FFEvent * local1 = 0;
        FFEvent * local2 = 0;
        if (eventOneDefined && eventTwoDefined) {
            list<FFEvent>::reverse_iterator itr = nowList.rbegin();
            local2 = &(*itr);
            ++itr;
            local1 = &(*itr);
        } else {
            local1 = &(nowList.back());
        }
        if (!durationManager->updateTimestampsOfNewPlanStep(prevState->getInnerState(), state.getEditableInnerState(), succ->plan, local1, local2, stepID, isAStochasticGoalState)) {
            succ->heuristicValue = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded stochastic deadline");
            return;
        }
    }
    #endif
    
    assert(stepID != -1);

    HTrio h1;
    
    if (FF::allowCompressionSafeScheduler) {
        h1 = calculateHeuristicAndCompressionSafeSchedule(state, prevState, goals, goalFluents, helpfulActions, succ->plan, nowList, stepID, justApplied, tilFrom);
    } else {
        h1 = calculateHeuristicAndSchedule(state, prevState, goals, goalFluents, incrementalData, helpfulActions, currentCost, succ->plan, nowList, stepID, true, justApplied, tilFrom);
    }

    if (RPGBuilder::getMetric()) {        
        if (Globals::optimiseSolutionQuality) {
            if (RPGBuilder::getMetric()->minimise) {
                if ( h1.admissibleCostEstimate < succ->heuristicValue.admissibleCostEstimate) {
                    h1.admissibleCostEstimate = succ->heuristicValue.admissibleCostEstimate;
                }
            } else {
                if ( h1.admissibleCostEstimate > succ->heuristicValue.admissibleCostEstimate) {
                    h1.admissibleCostEstimate = succ->heuristicValue.admissibleCostEstimate;
                }
            }
            if (admissibleCostExceedsBound(h1.admissibleCostEstimate, false)) {
                succ->heuristicValue = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Cannot better the cost of the incumbent solution");
                return;
            }
        }
    }
    

    if (eventOneDefined) {
        extraEvent = nowList.front();
        nowList.pop_front();
    }
    
    
    if (eventTwoDefined) {
        extraEventTwo = nowList.front();
        nowList.pop_front();
    }


    HTrio hcurr(h1);
    //int actionsSaved = 0;

    #ifdef POPF3ANALYSIS
    #ifndef TOTALORDERSTATES
    if (actID.second == Planner::E_AT_START) {
        if (   !RPGBuilder::getRPGDEs(actID.first->getID()).empty()
            && TemporalAnalysis::canSkipToEnd(actID.first->getID())) { // if it's a compression-safe temporal action
            
            const int endStepID = prevState->getInnerState().planLength + 1;
            
            state.getEditableInnerState().updateWhenEndOfActionIs(actID.first->getID(), endStepID, extraEventTwo.lpMinTimestamp);
            
        }
    }
    #endif
    #endif

    helpfulActionsExport = helpfulActions;
    succ->heuristicValue = hcurr;
    // succ->plan = header;
    if (eventOneDefined) {
        succ->plan.push_back(extraEvent);
    }

    if (eventTwoDefined) {
        succ->plan.push_back(extraEventTwo);
    }

    assert(nowList.size() == dsCount);
    
    succ->plan.insert(succ->plan.end(), nowList.begin(), nowList.end());


    if (actID.second == Planner::E_AT_START // If it's the start of an action...
            && !RPGBuilder::getRPGDEs(actID.first->getID()).empty() // that is temporal..
            && TemporalAnalysis::canSkipToEnd(actID.first->getID())) { // and compression-safe

        // we can pull it off the start event queue as we don't need to worry about applying it

        state.startEventQueue.pop_back();
    }
}


bool FF::precedingActions(ExtendedMinimalState & theState, const ActionSegment & actionSeg, list<ActionSegment> & alsoMustDo, const int oldTIL, const double moveOn)
{

//  static const double EPSILON = 0.001;
    static const bool tsDebug = false;
    static vector<double> tilStamps;
    static vector<list<int> > tilNegativeEffects;
    static vector<list<int> > tilPermanentNegativeEffects;
    static int tilCount;
    static bool haveTILstamps = false;

    if (!haveTILstamps) {
        haveTILstamps = true;
        vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNonAbstractedTILVec();
        tilCount = tilVec.size();
        tilStamps = vector<double>(tilCount);
        tilNegativeEffects = vector<list<int> >(tilCount);
        tilPermanentNegativeEffects = vector<list<int> >(tilCount);
        set<int> addedLater;
        for (int i = tilCount - 1; i >= 0; --i) {
            tilStamps[i] = tilVec[i]->duration;
            {
                list<Literal*>::iterator effItr = tilVec[i]->addEffects.begin();
                const list<Literal*>::iterator effEnd = tilVec[i]->addEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    //tilEffects[i].push_back(currEffID);
                    addedLater.insert(currEffID);
                }
            }

            {
                list<Literal*>::iterator effItr = tilVec[i]->delEffects.begin();
                const list<Literal*>::iterator effEnd = tilVec[i]->delEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    tilNegativeEffects[i].push_back(currEffID);
                    if (RPGBuilder::getEffectsToActions(currEffID).empty() && addedLater.find(currEffID) == addedLater.end()) {
                        tilPermanentNegativeEffects[i].push_back(currEffID);
                    }
                }
            }
        }
    }


    const Planner::time_spec ts = actionSeg.second;

    if (ts == Planner::E_AT_START) {


        if (tsDebug) cout << "Considering start of " << *(actionSeg.first) << "\n";

        {
            list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
            const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

            for (; tsiItr != tsiEnd; ++tsiItr) {
                if (!tsiItr->terminated) {
                    const double wouldBe = tsiItr->elapsed + moveOn;
                    if (wouldBe > tsiItr->maxDuration) {
                        if (TemporalAnalysis::canSkipToEnd(tsiItr->actID)) {
                            alsoMustDo.push_back(ActionSegment(RPGBuilder::getInstantiatedOp(tsiItr->actID), Planner::E_AT_END, -16, RPGHeuristic::emptyIntList));
                            cout << "Also must do " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << "\n";
                        } else {
                            if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << " pt. " << tsiItr->divisionsApplied << ", this exceeds duration\n";
                            return false;
                        }
                    }
                }
            }
        }

    } else if (ts == Planner::E_AT_END) {

        if (tsDebug) cout << "Considering end of " << *(actionSeg.first) << "\n";

        map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = theState.entriesForAction.find(actionSeg.first->getID());
        assert(tsiOld != theState.entriesForAction.end());

        list<StartEvent>::iterator pairWith;

        {
            RPGBuilder::LinearEffects * leffs = RPGBuilder::getLinearDiscretisation()[actionSeg.first->getID()];
            if (leffs) {
                const int toMatch = leffs->divisions - 1;

                list<list<StartEvent>::iterator >::iterator tiItr = tsiOld->second.begin();
                const list<list<StartEvent>::iterator >::iterator tiEnd = tsiOld->second.end();

                for (; tiItr != tiEnd; ++tiItr) {
                    if ((*tiItr)->divisionsApplied == toMatch) {
                        pairWith = *tiItr;
                        break;
                    }
                }

                assert(tiItr != tiEnd);

            } else {
                pairWith = tsiOld->second.front();
            }
        }

        if (tsDebug) cout << "Started " << pairWith->elapsed << " ago, of duration [" << pairWith->minDuration << "," << pairWith->maxDuration << "\n";

        double extraTime = pairWith->advancingDuration;

        //if (pairWith->minDuration < pairWith->maxDuration) {
        if (extraTime < moveOn) extraTime = moveOn;
        //}

        if (tsDebug) cout << "extra time = " << extraTime << "\n";

        //if (extraTime < 0) {
        //  return false;

        //}

        const list<StartEvent>::iterator theRestEnd = theState.startEventQueue.end();

        for (list<StartEvent>::iterator bqItr = theState.startEventQueue.begin(); bqItr != pairWith; ++bqItr) {

            if (!bqItr->terminated) {

                if (tsDebug) cout << "Can advance " << *(RPGBuilder::getInstantiatedOp(bqItr->actID)) << " point " << bqItr->divisionsApplied << "\n";

                const double wouldBe = bqItr->elapsed + extraTime;
                if (wouldBe > bqItr->maxDuration) {
                    if (TemporalAnalysis::canSkipToEnd(bqItr->actID)) {
                        alsoMustDo.push_back(ActionSegment(RPGBuilder::getInstantiatedOp(bqItr->actID), Planner::E_AT_END, -16, RPGHeuristic::emptyIntList));
                        cout << "Also must do " << *(RPGBuilder::getInstantiatedOp(bqItr->actID)) << "\n";
                    } else {
                        if (tsDebug) cout << "Now " << bqItr->elapsed << " since point " << bqItr->divisionsApplied << " of " << *(RPGBuilder::getInstantiatedOp(bqItr->actID)) << ", this exceeds duration\n";
                        return false;
                    }
                }
            }

        }



        if (theState.getInnerState().nextTIL < tilCount) {
            if (tilStamps[theState.getInnerState().nextTIL] < theState.timeStamp + extraTime) {
                if (tsDebug) cout << "Too late for the next TIL: " << tilStamps[theState.getInnerState().nextTIL] << "\n";
                return false;
            }
        }


        {
            list<StartEvent>::iterator theRestItr = pairWith;

            ++theRestItr;

            for (; theRestItr != theRestEnd; ++theRestItr) {

                if (!theRestItr->terminated) {
                    const double wouldBe = theRestItr->elapsed + moveOn;
                    if (wouldBe > theRestItr->maxDuration) {
                        if (TemporalAnalysis::canSkipToEnd(theRestItr->actID)) {
                            alsoMustDo.push_back(ActionSegment(RPGBuilder::getInstantiatedOp(theRestItr->actID), Planner::E_AT_END, -1, RPGHeuristic::emptyIntList));
                            cout << "Also must do " << *(RPGBuilder::getInstantiatedOp(theRestItr->actID)) << "\n";
                        } else {
                            if (tsDebug) cout << "Now " << theRestItr->elapsed << " since point " << theRestItr->divisionsApplied << " of " << *(RPGBuilder::getInstantiatedOp(theRestItr->actID)) << ", this exceeds duration\n";
                            return false;
                        }
                    }
                }
            }
        }

    }

    return true;
}

bool FF::checkTemporalSoundness(ExtendedMinimalState * prevState, ExtendedMinimalState & theState, const ActionSegment & actionSeg, const int oldTIL, const double moveOn)
{

    //const int & theAction, const Planner::time_spec & ts


    if (!tsChecking) return true;

    static const bool tsDebug = (Globals::globalVerbosity & 8192);
    static vector<double> tilStamps;
    static vector<list<int> > tilNegativeEffects;
    static vector<list<int> > tilPermanentNegativeEffects;
    static int tilCount;
    static bool haveTILstamps = false;

    if (!haveTILstamps) {
        haveTILstamps = true;
        vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNonAbstractedTILVec();
        tilCount = tilVec.size();
        tilStamps = vector<double>(tilCount);
        tilNegativeEffects = vector<list<int> >(tilCount);
        tilPermanentNegativeEffects = vector<list<int> >(tilCount);
        set<int> addedLater;
        for (int i = tilCount - 1; i >= 0; --i) {
            tilStamps[i] = tilVec[i]->duration;
            {
                list<Literal*>::iterator effItr = tilVec[i]->addEffects.begin();
                const list<Literal*>::iterator effEnd = tilVec[i]->addEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    //tilEffects[i].push_back(currEffID);
                    addedLater.insert(currEffID);
                }
            }

            {
                list<Literal*>::iterator effItr = tilVec[i]->delEffects.begin();
                const list<Literal*>::iterator effEnd = tilVec[i]->delEffects.end();

                for (; effItr != effEnd; ++effItr) {
                    const int currEffID = (*effItr)->getStateID();
                    tilNegativeEffects[i].push_back(currEffID);
                    if (RPGBuilder::getEffectsToActions(currEffID).empty() && addedLater.find(currEffID) == addedLater.end()) {
                        tilPermanentNegativeEffects[i].push_back(currEffID);
                    }
                }
            }
        }
    }


    const Planner::time_spec ts = actionSeg.second;
    

    if (ts == Planner::E_AT_START || ts == Planner::E_AT_END) {
        if (LPScheduler::optimiseOrdering) {
            
            const int actID = actionSeg.first->getID();
            const bool nonTemporal = RPGBuilder::getRPGDEs(actID).empty();
            
            set<int> justAdded;
            bool madeJustAdded = false;
            
            list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
            const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

            for (; tsiItr != tsiEnd; ++tsiItr) {
                if (!tsiItr->terminated && !tsiItr->ignore && !TemporalAnalysis::canSkipToEnd(tsiItr->actID)) {

                    if (!madeJustAdded) {
                        for (int pass = 0; pass < 2; ++pass) {
                            if (ts == Planner::E_AT_END && pass == 0) {
                                continue;
                            }
                            
                            const list<Literal*> & addList = (pass == 0 ? RPGBuilder::getStartPropositionAdds()[actionSeg.first->getID()]
                                                                        : RPGBuilder::getEndPropositionAdds()[actionSeg.first->getID()]);
                            
                            list<Literal*>::const_iterator effItr = addList.begin();
                            const list<Literal*>::const_iterator effEnd = addList.end();
                
                            for (; effItr != effEnd; ++effItr) {
                                justAdded.insert((*effItr)->getStateID());
                            }
                            
                            if (ts == Planner::E_AT_START) {
                                if (nonTemporal || !TemporalAnalysis::canSkipToEnd(actID)) {
                                    break;
                                }
                            }
                        }        
                        madeJustAdded = true;
                    }
                    
                    const list<Literal*> & precs = RPGBuilder::getEndPropositionalPreconditions()[tsiItr->actID];                    
                    
                    list<Literal*>::const_iterator pItr = precs.begin();
                    const list<Literal*>::const_iterator pEnd = precs.end();
                    
                    for (int fID; pItr != pEnd; ++pItr) {
                        
                        fID = (*pItr)->getStateID();
                        
                        if (TemporalAnalysis::getFactIsAbstract()[fID]) {
                            continue;
                        }
                        
                        if (justAdded.find(fID) == justAdded.end()) {
                            // not just added
                            continue;
                        }
                        
                        const StateFacts::const_iterator ffItr = theState.getInnerState().first.find(fID);
                        if ( ffItr != theState.getInnerState().first.end()) {
                            
                            // end of the action requires a fact that has just been added - force an ordering on this
                            
                            const int stepID = tsiItr->stepID + 1;
                            
                            #ifdef TOTALORDERSTATES
                            
                            const StateBFacts::const_iterator stateBItr = theState.getInnerState().firstAnnotations.find(fID); 
                            if (stateBItr != theState.getInnerState().firstAnnotations.end()) {
                                
                                
                                set<int>::const_iterator epItr = stateBItr->second.first.begin();             
                                const set<int>::const_iterator epEnd = stateBItr->second.first.end();
                                
                                for (; epItr != epEnd; ++epItr) {
                                    if (*epItr != stepID) {
                                        if (tsDebug) {
                                            cout << "Ordering future end of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << " after new fact " << *(RPGBuilder::getLiteral(FACTA(ffItr))) << endl;
                                        }
                                        theState.getInnerState().temporalConstraints->addOrdering(*epItr, stepID, true);
                                    }
                                }
                            }
                            #else
                            
                            const StepAndBeforeOrAfter & addedBy = ffItr->second.availableFrom;
                            assert(addedBy.beforeOrAfter == StepAndBeforeOrAfter::AFTER);
                            
                            if (addedBy.stepID != stepID) {
                                if (tsDebug) {
                                    cout << "Ordering future end of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << " after new fact " << *(RPGBuilder::getLiteral(FACTA(ffItr))) << endl;
                                }
                                theState.getInnerState().temporalConstraints->addOrdering(addedBy.stepID, stepID, true);
                            }
                            
                            #endif
                            
                        }
                        
                    }
                    
                }
            }
            
            
        }
    }

    if (tsDebug) {
        cout << "Checking temporal soundness of step: ";
        cout.flush();
    }

    if (ts == Planner::E_AT_START) {

        const int actID = actionSeg.first->getID();

        if (tsDebug) cout << "Considering start of " << *(actionSeg.first) << "\n";
        const bool nonTemporal = RPGBuilder::getRPGDEs(actID).empty();

        {
            list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
            const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

            for (; tsiItr != tsiEnd; ++tsiItr) {
                if (!tsiItr->terminated) {
                    const double wouldBe = tsiItr->elapsed + moveOn;
                    if (wouldBe > tsiItr->maxDuration) {
                        return false;
                    } else {
                        tsiItr->elapsed = wouldBe;
                    }
                    if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << " pt. " << tsiItr->divisionsApplied << "\n";
                    tsiItr->advancingDuration -= moveOn;
                }
            }
        }

        if (tsDebug) cout << "Now " << moveOn << " since start of new action " << *(actionSeg.first) << "\n";

        
        theState.timeStamp += moveOn;

        if (theState.getInnerState().nextTIL < tilCount) {
            if (tilStamps[theState.getInnerState().nextTIL] < theState.timeStamp) return false;

            const double earliestFinish = theState.timeStamp + (nonTemporal ? 0.0 : theState.startEventQueue.back().advancingDuration);

            const list<Literal*> & precs = RPGBuilder::getEndPropositionalPreconditions()[actID];
            const list<Literal*> & inv   = RPGBuilder::getInvariantPropositionalPreconditions()[actID];

            for (int tc = theState.getInnerState().nextTIL; tc < tilCount; ++tc) {
                if (tilStamps[tc] < earliestFinish) { // if TIL has to occur during the execution of this action
                    {
                        list<int>::const_iterator pnItr = tilPermanentNegativeEffects[tc].begin();
                        const list<int>::const_iterator pnEnd = tilPermanentNegativeEffects[tc].end();

                        for (; pnItr != pnEnd; ++pnItr) {
                            list<Literal*>::const_iterator pItr = precs.begin();
                            const list<Literal*>::const_iterator pEnd = precs.end();

                            for (; pItr != pEnd; ++pItr) {
                                if ((*pItr)->getStateID() == *pnItr) return false;
                            }
                        }
                    }
                    {
                        list<int>::const_iterator pnItr = tilNegativeEffects[tc].begin();
                        const list<int>::const_iterator pnEnd = tilNegativeEffects[tc].end();

                        for (; pnItr != pnEnd; ++pnItr) {
                            list<Literal*>::const_iterator pItr = inv.begin();
                            const list<Literal*>::const_iterator pEnd = inv.end();

                            for (; pItr != pEnd; ++pItr) {
                                if ((*pItr)->getStateID() == *pnItr) return false;
                            }
                        }
                    }
                }
            }
        }

        if (!nonTemporal && TemporalAnalysis::canSkipToEnd(actionSeg.first->getID()) && LPScheduler::optimiseOrdering) {
            
            const int endOfNewStep = prevState->getInnerState().planLength + 1;
            TemporalConstraints * const cons = theState.getInnerState().temporalConstraints;
            
            
            
            const list<Literal*> & invs    = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
            
            if (!invs.empty()) {
                set<int> invSet;
                {
                    list<Literal*>::const_iterator deItr = invs.begin();
                    const list<Literal*>::const_iterator deEnd = invs.end();
                    for (; deItr != deEnd; ++deItr) {
                        invSet.insert((*deItr)->getStateID());
                    }
                }

                list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                ++tsiItr;

                for (; tsiItr != tsiEnd; ++tsiItr) {
                    if (!tsiItr->terminated) {
                        const list<Literal*> & openDels = RPGBuilder::getEndPropositionDeletes()[tsiItr->actID];
                        list<Literal*>::const_iterator odItr = openDels.begin();
                        const list<Literal*>::const_iterator odEnd = openDels.end();
                        for (; odItr != odEnd; ++odItr) {
                            if (TemporalAnalysis::getFactIsAbstract()[(*odItr)->getStateID()]) {
                                continue;
                            }
                            
                            if (invSet.find((*odItr)->getStateID()) != invSet.end()) {
                                cons->addOrdering(endOfNewStep, tsiItr->stepID + 1, true);
                                if (tsDebug) {
                                    cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come before " << tsiItr->stepID + 1 << ", to avoid an invariant violation\n" << COLOUR_default;
                                }
                                
                                break;
                            }
                        }
                    }
                }

            }
                
        }

        if (!nonTemporal && !TemporalAnalysis::canSkipToEnd(actionSeg.first->getID()) && LPScheduler::optimiseOrdering) {
            const int endOfNewStep = prevState->getInnerState().planLength + 1;
            
            TemporalConstraints * const cons = theState.getInnerState().temporalConstraints;
            
            {
                list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                int & thisFanIn = tsiItr->fanIn;
                int & thisStepID = tsiItr->stepID;
                const double thisIncr = tsiItr->minDuration - tsiItr->elapsed;
                StartEvent & eca = *tsiItr;
                if (thisIncr >= EPSILON) {
                    ++tsiItr;

                    for (; tsiItr != tsiEnd; ++tsiItr) {
                        if (!tsiItr->terminated) {
                            const double consIncr = tsiItr->maxDuration - tsiItr->elapsed;
                            if (consIncr < thisIncr && fabs(thisIncr - consIncr) > 0.0005) {
                                ++thisFanIn;
                                tsiItr->endComesBefore.insert(thisStepID);
                                eca.endComesBeforePair.insert(tsiItr->stepID);
                                cons->addOrdering(tsiItr->stepID + 1, endOfNewStep, true);
                                if (tsDebug) {
                                    cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come after " << tsiItr->stepID + 1 << ", due to long-inside-short avoidance\n" << COLOUR_default;
                                }
                            }
                        }
                        //cout << "Now " << tsiItr->second << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->first)) << "\n";
                    }
                    if (theState.getInnerState().nextTIL < tilCount) {
                        const double consIncr = tilStamps[theState.getInnerState().nextTIL] - theState.timeStamp;
                        if (consIncr < thisIncr && fabs(thisIncr - consIncr) > 0.0005) {
                            ++thisFanIn;
                            theState.tilComesBefore.push_back(thisStepID);
                        }
                    }
                }
            }

            {
                {
                    const list<Literal*> & delEffs =  RPGBuilder::getEndPropositionDeletes()[actID];
                    const list<Literal*> & invs    = RPGBuilder::getInvariantPropositionalPreconditions()[actID];
                    const LiteralSet & oneShotEndPrecs  = RPGBuilder::getEndOneShots(actID);

                    if (!delEffs.empty()) {
                        set<int> deSet;
                        {
                            list<Literal*>::const_iterator deItr = delEffs.begin();
                            const list<Literal*>::const_iterator deEnd = delEffs.end();
                            for (; deItr != deEnd; ++deItr) {
                                if (TemporalAnalysis::getFactIsAbstract()[(*deItr)->getStateID()]) {
                                    continue;
                                }
                                
                                deSet.insert((*deItr)->getStateID());
                            }
                        }

                        list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                        const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                        StartEvent & eca = *tsiItr;

                        ++tsiItr;

                        for (; tsiItr != tsiEnd; ++tsiItr) {
                            if (!tsiItr->terminated) {
                                bool precedes = false;
                                const list<Literal*> & openInvs = RPGBuilder::getInvariantPropositionalPreconditions()[tsiItr->actID];
                                list<Literal*>::const_iterator oiItr = openInvs.begin();
                                const list<Literal*>::const_iterator oiEnd = openInvs.end();
                                for (; oiItr != oiEnd; ++oiItr) {
                                    if (deSet.find((*oiItr)->getStateID()) != deSet.end()) {
                                        eca.endMustComeAfter(tsiItr->stepID);
                                        tsiItr->endMustComeAfterPair(eca.stepID);
                                        precedes = true;
                                        cons->addOrdering(tsiItr->stepID + 1, endOfNewStep, true);
                                        
                                        if (tsDebug) {
                                            cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come after " << tsiItr->stepID + 1 << ", to avoid deleting one of its invariants\n" << COLOUR_default;
                                        }
                                        
                                        
                                        break;
                                    }
                                }

                                if (!precedes) {
                                    const LiteralSet & thisEndOneShot = RPGBuilder::getEndOneShots(tsiItr->actID);

                                    LiteralSet::const_iterator apItr = thisEndOneShot.begin();
                                    const LiteralSet::const_iterator apEnd = thisEndOneShot.end();

                                    set<int>::const_iterator adItr = deSet.begin();
                                    const set<int>::const_iterator adEnd = deSet.end();

                                    while (apItr != apEnd && adItr != adEnd) {
                                        const int idOne = (*apItr)->getStateID();
                                        const int idTwo = *adItr;
                                        if (idOne < idTwo) {
                                            ++apItr;
                                        } else if (idTwo < idOne) {
                                            ++adItr;
                                        } else {
                                            eca.endMustComeAfter(tsiItr->stepID);
                                            tsiItr->endMustComeAfterPair(eca.stepID);
                                            cons->addOrdering(tsiItr->stepID + 1, endOfNewStep, true);
                                            
                                            if (tsDebug) {
                                                cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come after " << tsiItr->stepID + 1 << ", to avoid deleting one if its one-shot end preconditions.\n" << COLOUR_default;
                                            }
                                            
                                            
                                            break;
                                        }
                                    }

                                }
                            }
                        }

                    }

                    if (!invs.empty()) {
                        set<int> invSet;
                        {
                            list<Literal*>::const_iterator deItr = invs.begin();
                            const list<Literal*>::const_iterator deEnd = invs.end();
                            for (; deItr != deEnd; ++deItr) {
                                invSet.insert((*deItr)->getStateID());
                            }
                        }

                        list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                        const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                        int & thisStepID = tsiItr->stepID;

                        StartEvent & eca = *tsiItr;
                        ++tsiItr;

                        for (; tsiItr != tsiEnd; ++tsiItr) {
                            if (!tsiItr->terminated) {
                                const list<Literal*> & openDels = RPGBuilder::getEndPropositionDeletes()[tsiItr->actID];
                                list<Literal*>::const_iterator odItr = openDels.begin();
                                const list<Literal*>::const_iterator odEnd = openDels.end();
                                for (; odItr != odEnd; ++odItr) {
                                    if (TemporalAnalysis::getFactIsAbstract()[(*odItr)->getStateID()]) {
                                        continue;
                                    }
                                    
                                    if (invSet.find((*odItr)->getStateID()) != invSet.end()) {
                                        tsiItr->endMustComeAfter(thisStepID);
                                        eca.endMustComeAfterPair(tsiItr->stepID);
                                        cons->addOrdering(endOfNewStep, tsiItr->stepID + 1, true);
                                        if (tsDebug) {
                                            cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come before " << tsiItr->stepID + 1 << ", to avoid an invariant violation\n" << COLOUR_default;
                                        }
                                        
                                        break;
                                    }
                                }
                            }
                        }

                    }

                    if (!oneShotEndPrecs.empty()) {

                        list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                        const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                        int & thisStepID = tsiItr->stepID;

                        StartEvent & eca = *tsiItr;
                        ++tsiItr;

                        for (; tsiItr != tsiEnd; ++tsiItr) {
                            if (!tsiItr->terminated) {
                                const list<Literal*> & openDels = RPGBuilder::getEndPropositionDeletes()[tsiItr->actID];
                                list<Literal*>::const_iterator odItr = openDels.begin();
                                const list<Literal*>::const_iterator odEnd = openDels.end();
                                for (; odItr != odEnd; ++odItr) {
                                    if (TemporalAnalysis::getFactIsAbstract()[(*odItr)->getStateID()]) {
                                        continue;
                                    }
                                    
                                    if (oneShotEndPrecs.find(*odItr) != oneShotEndPrecs.end()) {
                                        tsiItr->endMustComeAfter(thisStepID);
                                        eca.endMustComeAfterPair(tsiItr->stepID);
                                        cons->addOrdering(endOfNewStep, tsiItr->stepID + 1, true);
                                        if (tsDebug) {
                                            cout << COLOUR_light_green << "End of action just started (" << endOfNewStep << ") must come before " << tsiItr->stepID + 1 << ", to avoid losing a one-shot end precondition\n" << COLOUR_default;
                                        }
                                        
                                        break;
                                    }
                                }
                            }
                        }

                    }


                }
            }
        }

    } else if (ts == Planner::E_OVER_ALL) {
        
        std::cerr << "Internal error: should not be able to apply actions with 'over all' time specifier\n";
        exit(1);
        
        
    } else if (ts == Planner::E_AT_END) {

        if (tsDebug) cout << "Considering end of " << *(actionSeg.first) << "\n";

        const map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = theState.entriesForAction.find(actionSeg.first->getID());
        assert(tsiOld != theState.entriesForAction.end());



        list<StartEvent>::iterator pairWith;

        {
            RPGBuilder::LinearEffects * leffs = RPGBuilder::getLinearDiscretisation()[actionSeg.first->getID()];
            if (leffs) {
                const int toMatch = leffs->divisions - 1;

                list<list<StartEvent>::iterator >::iterator tiItr = tsiOld->second.begin();
                const list<list<StartEvent>::iterator >::iterator tiEnd = tsiOld->second.end();

                for (; tiItr != tiEnd; ++tiItr) {
                    if ((*tiItr)->divisionsApplied == toMatch) {
                        pairWith = *tiItr;
                        break;
                    }
                }

                assert(tiItr != tiEnd);

            } else {
                pairWith = tsiOld->second.front();
            }
        }

        if (!pairWith->getEndComesAfter().empty()) {
            if (tsDebug) {
                cout << "ECA list is not empty, contains:";
                set<int>::const_iterator ecaItr = pairWith->getEndComesAfter().begin();
                const set<int>::const_iterator ecaEnd = pairWith->getEndComesAfter().end();

                for (; ecaItr != ecaEnd; ++ecaItr) {
                    cout << " " << *ecaItr;
                }
                cout << "\n";
            }
            return false;
        }

        if (!pairWith->getEndComesBeforePair().empty()) {
            if (tsDebug) cout << "ECB-pair list is not empty\n";
            return false;
        }

        if (tsDebug) cout << "Started " << pairWith->elapsed << " ago, of duration [" << pairWith->minDuration << "," << pairWith->maxDuration << "\n";

        double extraTime = pairWith->advancingDuration;

        //if (pairWith->minDuration < pairWith->maxDuration) {
        if (extraTime < moveOn) extraTime = moveOn;
        //}

        if (tsDebug) cout << "extra time = " << extraTime << "\n";

        //if (extraTime < 0) {
        //  return false;

        //}

        const list<StartEvent>::iterator theRestEnd = theState.startEventQueue.end();

        for (list<StartEvent>::iterator bqItr = theState.startEventQueue.begin(); bqItr != pairWith; ++bqItr) {

            if (!bqItr->terminated) {

                if (tsDebug) cout << "Can advance " << *(RPGBuilder::getInstantiatedOp(bqItr->actID)) << " point " << bqItr->divisionsApplied << "\n";

                if ((bqItr->elapsed = bqItr->elapsed + extraTime) > bqItr->maxDuration) {
                    if (tsDebug) cout << "Now " << bqItr->elapsed << " since point " << bqItr->divisionsApplied << " of " << *(RPGBuilder::getInstantiatedOp(bqItr->actID)) << ", this exceeds duration\n";
                    return false;
                }
                bqItr->advancingDuration -= extraTime;
            }

        }


        theState.timeStamp += extraTime;

        if (tsDebug) cout << "State timestamp is now " << theState.timeStamp << "\n";

        if (theState.getInnerState().nextTIL < tilCount) {
            if (tilStamps[theState.getInnerState().nextTIL] < theState.timeStamp) {
                if (tsDebug) cout << "Too late for the next TIL: " << tilStamps[theState.getInnerState().nextTIL] << "\n";
                return false;
            }
        }


        {
            list<StartEvent>::iterator theRestItr = pairWith;

            ++theRestItr;

            for (; theRestItr != theRestEnd; ++theRestItr) {

                if (!theRestItr->terminated) {

                    if ((theRestItr->elapsed = theRestItr->elapsed + moveOn) > theRestItr->maxDuration) {
                        if (tsDebug) cout << "Now " << theRestItr->elapsed << " since point " << theRestItr->divisionsApplied << " of " << *(RPGBuilder::getInstantiatedOp(theRestItr->actID)) << ", this exceeds duration\n";
                        return false;
                    }

                    theRestItr->advancingDuration -= extraTime;
                }
            }
        }

        if (LPScheduler::optimiseOrdering) {

            {
                set<int> & beforeList = pairWith->endComesBefore;

                if (!beforeList.empty()) {

                    set<int>::iterator cbeItr = beforeList.begin();
                    const set<int>::iterator cbeEnd = beforeList.end();

                    list<StartEvent>::iterator theRestItr = pairWith;
                    ++theRestItr;

                    if (*cbeItr == -1) {
                        --(theState.tilFanIn);
                        ++cbeItr;
                    }

                    if (cbeItr != cbeEnd) {
                        for (; theRestItr != theRestEnd; ++theRestItr) {

                            if (!theRestItr->terminated) {

                                if (*cbeItr == theRestItr->stepID) {
                                    theRestItr->endComesBeforePair.erase(pairWith->stepID);
                                    --(theRestItr->fanIn);
                                    ++cbeItr;
                                    if (cbeItr == cbeEnd) break;
                                    if (*cbeItr == -1) {
                                        --(theState.tilFanIn);
                                        ++cbeItr;
                                    }
                                    if (cbeItr == cbeEnd) break;
                                }
                            }
                        }
                    }

                }

            }

            {
                int & thisFanIn = pairWith->fanIn;

                if (thisFanIn) {

                    const int thisStepID = pairWith->stepID;

                    for (list<StartEvent>::iterator bqItr = theState.startEventQueue.begin(); thisFanIn && bqItr != pairWith; ++bqItr) {
                        if (!bqItr->terminated) {
                            set<int> & cbfList = bqItr->endComesBefore;
                            set<int>::iterator cbfItr = cbfList.begin();
                            const set<int>::iterator cbfEnd = cbfList.end();

                            for (; cbfItr != cbfEnd; ++cbfItr) {
                                const int & deref = *cbfItr;
                                if (deref > thisStepID) {
                                    break;
                                } else if (deref == thisStepID) {
                                    bqItr->endComesBeforePair.erase(thisStepID);
                                    cbfList.erase(cbfItr);
                                    --thisFanIn;
                                    break;
                                }
                            }
                        }

                    }

                    if (thisFanIn) {
                        list<int> & cbfList = theState.tilComesBefore;
                        list<int>::iterator cbfItr = cbfList.begin();
                        const list<int>::iterator cbfEnd = cbfList.end();

                        for (; cbfItr != cbfEnd; ++cbfItr) {
                            const int & deref = *cbfItr;
                            if (deref > thisStepID) {
                                break;
                            } else if (deref == thisStepID) {
                                cbfList.erase(cbfItr);
                                --thisFanIn;
                                break;
                            }
                        }
                    }

                }
            }

            {
                const int errStepID = pairWith->stepID;

                for (list<StartEvent>::iterator bqItr = theState.startEventQueue.begin(); bqItr != pairWith; ++bqItr) {
                    if (!bqItr->terminated) {
                        bqItr->actionHasFinished(errStepID);
                    }
                }

                list<StartEvent>::iterator theRestItr = pairWith;

                ++theRestItr;

                for (; theRestItr != theRestEnd; ++theRestItr) {
                    if (!theRestItr->terminated) {
                        theRestItr->actionHasFinished(errStepID);
                    }
                }
            }
        }
    } else { // TIL
        if (tsDebug) cout << "Applying TIL\n";

        for (int pass = oldTIL; pass <= actionSeg.divisionID; ++pass) {

            const double thisAdvancer = tilStamps[pass] - theState.timeStamp;

            list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
            const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

            for (; tsiItr != tsiEnd; ++tsiItr) {
                if (!tsiItr->terminated) {
                    if (tsiItr->stepID < theState.stepBeforeTIL) {
                        if ((tsiItr->elapsed = tsiItr->elapsed + thisAdvancer) > tsiItr->maxDuration) {
                            if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << ", this exceeds duration\n";
                            return false;
                        }
                        if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << "\n";
                        tsiItr->advancingDuration -= thisAdvancer;
                    } else {
                        if ((tsiItr->elapsed = tsiItr->elapsed + EPSILON) > tsiItr->maxDuration) {
                            if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << ", this exceeds duration\n";
                            return false;
                        }
                        if (tsDebug) cout << "Now " << tsiItr->elapsed << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->actID)) << "\n";
                        tsiItr->advancingDuration -= thisAdvancer;
                    }
                }
            }

            if (LPScheduler::optimiseOrdering) {
                {
                    list<int> & beforeList = theState.tilComesBefore;

                    if (!beforeList.empty()) {

                        list<int>::iterator cbeItr = beforeList.begin();
                        const list<int>::iterator cbeEnd = beforeList.end();

                        list<StartEvent>::iterator theRestItr = theState.startEventQueue.begin();
                        const list<StartEvent>::iterator theRestEnd = theState.startEventQueue.end();

                        while (theRestItr != theRestEnd && theRestItr->stepID < theState.stepBeforeTIL) ++theRestItr;

                        for (; theRestItr != theRestEnd; ++theRestItr) {
                            if (!theRestItr->terminated) {
                                if (*cbeItr == theRestItr->stepID) {
                                    --(theRestItr->fanIn);
                                    ++cbeItr;
                                    if (cbeItr == cbeEnd) break;
                                }
                            }

                        }

                    }

                }

                {
                    int & thisFanIn = theState.tilFanIn;

                    if (thisFanIn) {

                        list<StartEvent>::iterator bqItr = theState.startEventQueue.begin();
                        const list<StartEvent>::iterator bqEnd = theState.startEventQueue.end();

                        for (; thisFanIn && bqItr != bqEnd && bqItr->stepID < (theState.stepBeforeTIL - 1); ++bqItr) {
                            if (!bqItr->terminated) {
                                set<int> & cbfList = bqItr->endComesBefore;
                                set<int>::iterator cbfItr = cbfList.begin();
                                const set<int>::iterator cbfEnd = cbfList.end();

                                for (; cbfItr != cbfEnd; ++cbfItr) {
                                    const int & deref = *cbfItr;
                                    if (deref > -1) {
                                        break;
                                    } else if (deref == -1) {
                                        cbfList.erase(cbfItr);
                                        --thisFanIn;
                                        break;
                                    }
                                }
                            }

                        }

                    }
                }
            }

            theState.timeStamp = tilStamps[pass];
            theState.stepBeforeTIL = prevState->getInnerState().planLength + 1;
            theState.tilFanIn = 0;
            theState.tilComesBefore.clear();

            if (LPScheduler::optimiseOrdering) {

                if ((pass + 1) < tilCount) {
                    list<StartEvent>::reverse_iterator tsiItr = theState.startEventQueue.rbegin();
                    const list<StartEvent>::reverse_iterator tsiEnd = theState.startEventQueue.rend();

                    int & thisFanIn = theState.tilFanIn;
                    const double thisIncr = tilStamps[pass+1] - tilStamps[pass];
                    if (thisIncr >= EPSILON) {
                        for (; tsiItr != tsiEnd; ++tsiItr) {
                            if (!tsiItr->terminated) {
                                const double consIncr = tsiItr->maxDuration - tsiItr->elapsed;
                                if (consIncr < thisIncr && fabs(thisIncr - consIncr) > 0.0005) {
                                    ++thisFanIn;
                                    tsiItr->endComesBefore.insert(-1);
                                }
                            }
                            //cout << "Now " << tsiItr->second << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->first)) << "\n";
                        }
                    }
                }
            }
//what about the case where the TIL thing is quite small but it has to end before the action because it can't slide around so readily, i.e. no matter how far we shift an action to the left, this is always going to go inside it. i.e. it's timestamp which we can back-infer + min duration > timestamp + this til, we have an ordering.- think about this, it could be good....


        }



    }

    return true;

};


/*
bool FF::checkTSTemporalSoundness(RPGHeuristic* const rpg, ExtendedMinimalState & theState, const int & theAction, const Planner::time_spec & ts, const double & incr, const int oldTIL) {

    static const double EPSILON = 0.001;

    const bool localDebug = false;

    if (ts == Planner::E_AT_START) {

        list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
        list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

        --tsiEnd;

        for (; tsiItr != tsiEnd; ++tsiItr) {
            if ((tsiItr->elapsed = tsiItr->elapsed + incr) > tsiItr->maxDuration + 0.0005) {
                return false;
            }
            //cout << "Now " << tsiItr->second << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->first)) << "\n";
        }

        theState.timeStamp += EPSILON;


    } else if (ts == Planner::E_AT_END) {

        const double extraTime = incr;

        map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = theState.entriesForAction.find(theAction);
        assert(tsiOld != theState.entriesForAction.end());

        if (localDebug) cout << theAction << " started " << tsiOld->second.front()->elapsed << " ago, of duration " << tsiOld->second.front()->maxDuration << "\n";


        if (localDebug) cout << "extra time = " << extraTime << "\n";

        if (extraTime < -0.0005) {
            return false;

        }

        list<StartEvent>::iterator & pairWith = tsiOld->second.front();


        list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
        const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

        for (; tsiItr != pairWith; ++tsiItr) {
            if ((tsiItr->elapsed = tsiItr->elapsed + extraTime) > tsiItr->maxDuration + 0.0005) {

                return false;
            }
        }

        theState.timeStamp += extraTime;
        ++tsiItr;

        for (; tsiItr != tsiEnd; ++tsiItr) {
            if ((tsiItr->elapsed = tsiItr->elapsed + extraTime) > tsiItr->maxDuration + 0.0005) {

                return false;
            }
        }


    } else { // TIL
        for (int pass = oldTIL; pass <= theAction; ++pass) {
            list<StartEvent>::iterator tsiItr = theState.startEventQueue.begin();
            const list<StartEvent>::iterator tsiEnd = theState.startEventQueue.end();

            for (; tsiItr != tsiEnd; ++tsiItr) {
                if ((tsiItr->elapsed = tsiItr->elapsed + EPSILON) > tsiItr->maxDuration + 0.0005) {
                    return false;
                }
                //cout << "Now " << tsiItr->second << " since start of " << *(RPGBuilder::getInstantiatedOp(tsiItr->first)) << "\n";
            }
        }
        theState.timeStamp = RPGBuilder::getTILVec()[theAction]->duration;

    }

    return true;

};
*/
void reorderStartsBeforeEnds(list<ActionSegment > & applicableActions)
{

    if (false) {
        cout << "Before, ordered:\n";
        list<ActionSegment>::iterator postItr = applicableActions.begin();
        const list<ActionSegment>::iterator postEnd = applicableActions.end();

        for (; postItr != postEnd; ++postItr) {
            if (postItr->second != Planner::E_AT) {
                cout << "\t" << *(postItr->first);
                if (postItr->second == Planner::E_AT_START) {
                    cout << " start";
                } else {
                    cout << " end";
                }

                if (postItr->needToFinish.size()) {
                    cout << " ( with";
                    set<int>::iterator ntfItr = postItr->needToFinish.begin();
                    const set<int>::iterator ntfEnd = postItr->needToFinish.end();
                    for (; ntfItr != ntfEnd; ++ntfItr) {
                        cout << " " << *(RPGBuilder::getInstantiatedOp(*ntfItr));
                    }
                    cout << " before)";
                }
                cout << "\n";
            }
        }
    }


    list<ActionSegment > tmp(applicableActions);
    applicableActions.clear();

    list<ActionSegment >::iterator itr = tmp.begin();
    const list<ActionSegment >::iterator itrEnd = tmp.end();

    list<ActionSegment >::iterator firstEnd = applicableActions.end();

    const Planner::time_spec toMatch = (FF::startsBeforeEnds ? Planner::E_AT_START : Planner::E_AT_END);

    for (; itr != itrEnd; ++itr) {
        if (itr->second == toMatch) {
            if (firstEnd == applicableActions.end()) {
                applicableActions.push_back(*itr);
            } else {
                applicableActions.insert(firstEnd, *itr);
            }
        } else {
            applicableActions.push_back(*itr);
            if (firstEnd == applicableActions.end()) {
                --firstEnd;
            }
        }
    }

    if (false) {
        cout << "After, ordered:\n";
        list<ActionSegment>::iterator postItr = applicableActions.begin();
        const list<ActionSegment>::iterator postEnd = applicableActions.end();

        for (; postItr != postEnd; ++postItr) {
            if (postItr->second != Planner::E_AT) {
                cout << "\t" << *(postItr->first);
                if (postItr->second == Planner::E_AT_START) {
                    cout << " start";
                } else {
                    cout << " end";
                }

                if (postItr->needToFinish.size()) {
                    cout << " ( with";
                    set<int>::iterator ntfItr = postItr->needToFinish.begin();
                    const set<int>::iterator ntfEnd = postItr->needToFinish.end();
                    for (; ntfItr != ntfEnd; ++ntfItr) {
                        cout << " " << *(RPGBuilder::getInstantiatedOp(*ntfItr));
                    }
                    cout << " before)";
                }
                cout << "\n";
            }
        }
    }

};

void reorderNonDeletorsFirst(list<ActionSegment > & applicableActions)
{

    list<ActionSegment > tmp(applicableActions);
    applicableActions.clear();

    list<set<int> > preconditionFacts;
    
    {
        
        list<ActionSegment >::iterator itr = tmp.begin();
        const list<ActionSegment >::iterator itrEnd = tmp.end();
     
        for (; itr != itrEnd; ++itr) {
            preconditionFacts.push_back(set<int>());
            
            if (itr->second == Planner::E_AT) continue;
            
            set<int> & toFill = preconditionFacts.back();
            
            const list<Literal*> & pres = (itr->second == Planner::E_AT_START
                                           ? RPGBuilder::getProcessedStartPropositionalPreconditions()[itr->first->getID()]
                                           : RPGBuilder::getEndPropositionalPreconditions()[itr->first->getID()]);
                                           
            list<Literal*>::const_iterator pItr = pres.begin();
            const list<Literal*>::const_iterator pEnd = pres.end();
            
            for (; pItr != pEnd; ++pItr) {
                toFill.insert((*pItr)->getStateID());
            }
        }
    }
    
    list<int> penalties;
    
    list<set<int> >::const_iterator ownPFItr = preconditionFacts.begin();
    list<ActionSegment >::iterator itr = tmp.begin();
    const list<ActionSegment >::iterator itrEnd = tmp.end();

    for (; itr != itrEnd; ++itr, ++ownPFItr) {
        int penaltyScore = 0;
        if (itr->second != Planner::E_AT) {
            set<int> toFill;
            
            const list<Literal*> & effs = (itr->second == Planner::E_AT_START
                                            ? RPGBuilder::getStartPropositionDeletes()[itr->first->getID()]
                                            : RPGBuilder::getEndPropositionDeletes()[itr->first->getID()]);
                                            
            list<Literal*>::const_iterator eItr = effs.begin();
            const list<Literal*>::const_iterator eEnd = effs.end();

            for (; eItr != eEnd; ++eItr) {
                toFill.insert((*eItr)->getStateID());
            }
            
            list<set<int> >::const_iterator pfItr = preconditionFacts.begin();
            const list<set<int> >::const_iterator pfEnd = preconditionFacts.end();
            
            for (; pfItr != pfEnd; ++pfItr) {
                if (pfItr == ownPFItr) {
                    continue;
                }
                set<int> overlap;
                
                std::set_intersection(pfItr->begin(), pfItr->end(), toFill.begin(), toFill.end(),
                                      insert_iterator<set<int> >(overlap, overlap.begin()));
                                      
                if (!overlap.empty()) {
                    ++penaltyScore;
                }
            }
        }
        
        list<int>::iterator penItr = penalties.begin();
        list<ActionSegment>::iterator actItr = applicableActions.begin();
        
        for (; actItr != applicableActions.end() && penaltyScore >= *penItr; ++actItr, ++penItr) ;
        
        penalties.insert(penItr, penaltyScore);
        applicableActions.insert(actItr, *itr);
        
    }
};

void reorderHelpfulFirst(list<ActionSegment> & applicableActions, list<ActionSegment> & helpfulActions)
{

    list<ActionSegment> tmp(applicableActions);
    applicableActions.clear();

    list<int> weights;

    const list<ActionSegment>::iterator hitrStart = helpfulActions.begin();
    const list<ActionSegment>::iterator hitrEnd = helpfulActions.end();

    list<ActionSegment>::iterator itr = tmp.begin();
    const list<ActionSegment>::iterator itrEnd = tmp.end();

    for (; itr != itrEnd; ++itr) {
        int w = 0;
        for (list<ActionSegment>::iterator hitr = hitrStart; hitr != hitrEnd; ++hitr, ++w) {
            if (itr->first == hitr->first && itr->second == hitr->second && itr->divisionID == hitr->divisionID) {
                break;
            }
        }

        list<ActionSegment>::iterator aaItr = applicableActions.begin();
        const list<ActionSegment>::iterator aaEnd = applicableActions.end();
        list<int>::iterator wItr = weights.begin();

        for (; aaItr != aaEnd && (w >= *wItr); ++aaItr, ++wItr);

        applicableActions.insert(aaItr, *itr);
        weights.insert(wItr, w);

    }


};


void FF::makeJustApplied(map<double, list<pair<int, int> > > & justApplied, double & tilFrom, ExtendedMinimalState & state, const bool & lastIsSpecial)
{

    static const bool debugJA = false;
    static vector<double> tilStamps;
    static int tilCount;
    static bool haveTILstamps = false;

    if (!haveTILstamps) {
        haveTILstamps = true;
        vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNonAbstractedTILVec();
        tilCount = tilVec.size();
        tilStamps = vector<double>(tilCount);
        for (int i = 0; i < tilCount; ++i) {
            tilStamps[i] = tilVec[i]->duration;
        }
    }

    tilFrom = EPSILON;

    if (state.startEventQueue.empty() || !FF::invariantRPG || !FF::tsChecking) return;

    bool visitedTIL = (state.getInnerState().nextTIL >= tilCount);
    double tilAdvance = (visitedTIL ? DBL_MAX : tilStamps[state.getInnerState().nextTIL] - state.timeStamp);

    {
        list<StartEvent>::iterator seItr = state.startEventQueue.begin();
        const list<StartEvent>::iterator seEnd = state.startEventQueue.end();
        for (; seItr != seEnd; ++seItr) seItr->minAdvance = DBL_MAX;
    }

    list<StartEvent>::iterator seItr = state.startEventQueue.begin();
    list<StartEvent>::iterator seEnd = state.startEventQueue.end();

    if (lastIsSpecial) {
        --seEnd;
    }

    while (seItr != seEnd || !visitedTIL) {
        if (!visitedTIL && (seItr == seEnd || seItr->stepID >= state.stepBeforeTIL)) {

            const double refIncr = tilStamps[state.getInnerState().nextTIL] - state.timeStamp;
            double & inheritedIncr = tilAdvance;
            const double maxIncr = (refIncr < inheritedIncr ? refIncr : inheritedIncr);

            if (!state.tilComesBefore.empty()) {
                list<int>::iterator cbfItr = state.tilComesBefore.begin();
                const list<int>::iterator cbfEnd = state.tilComesBefore.end();

                list<StartEvent>::iterator seNext = seItr;

                for (; cbfItr != cbfEnd; ++cbfItr) {
                    int & deref = *cbfItr;
                    while (seNext != seEnd && seNext->stepID != deref) ++seNext;
                    if (seNext != seEnd) {
                        if (seNext->minAdvance > maxIncr) seNext->minAdvance = maxIncr;
                        ++seNext;
                    }
                }

            }

            {
                const double newElapsed = (state.getInnerState().nextTIL == 0 ? state.timeStamp : state.timeStamp - tilStamps[state.getInnerState().nextTIL - 1]) + maxIncr;
                const double equivalentDur = tilStamps[state.getInnerState().nextTIL] - (state.getInnerState().nextTIL == 0 ? 0.0 : tilStamps[state.getInnerState().nextTIL - 1]);
                if (newElapsed >= equivalentDur) {
//                  tilFrom = EPSILON;
                } else {
                    tilFrom = equivalentDur - newElapsed;
                }
            }

            visitedTIL = true;

        } else {
            if (!seItr->ignore) {
                const double refIncr = seItr->maxDuration - seItr->elapsed;
                double & inheritedIncr = seItr->minAdvance;
                const double maxIncr = (refIncr < inheritedIncr ? refIncr : inheritedIncr);

                if (!seItr->endComesBefore.empty()) {
                    set<int>::iterator cbfItr = seItr->endComesBefore.begin();
                    const set<int>::iterator cbfEnd = seItr->endComesBefore.end();

                    list<StartEvent>::iterator seNext = seItr;
                    ++seNext;

                    for (; cbfItr != cbfEnd; ++cbfItr) {
                        const int & deref = *cbfItr;
                        if (deref == -1) {
                            if (tilAdvance > maxIncr) tilAdvance = maxIncr;
                        } else {
                            while (seNext != seEnd && seNext->stepID != deref) ++seNext;
                            if (seNext != seEnd) {
                                if (seNext->minAdvance > maxIncr) seNext->minAdvance = maxIncr;
                                ++seNext;
                            }
                        }
                    }
                }

                {
                    const double newElapsed = seItr->elapsed + maxIncr;

///                 RPGBuilder::LinearEffects * const lEffs = RPGBuilder::getLinearDiscretisation()[seItr->actID];
                    double remainingDur = 0.0;
///                 if (lEffs && lEffs->divisions > 1) {
///                     for (int d = seItr->divisionsApplied + 1; d < lEffs->divisions; ++d) {
///                         remainingDur += lEffs->durations[d];
///                     }
///                 }



                    if (newElapsed >= seItr->minDuration) {
                        justApplied[remainingDur].push_back(pair<int, int>(seItr->actID, seItr->divisionsApplied));
                    } else {
                        const double insLayer = seItr->minDuration - newElapsed + remainingDur;
                        if (insLayer > EPSILON) {
                            justApplied[insLayer].push_back(pair<int, int>(seItr->actID, seItr->divisionsApplied));
                            if (debugJA) {
                                cout << insLayer << " left for step " << seItr->stepID << "\n";
                            }
                        }
                    }
                }
            }
            ++seItr;
        }
    }



    /*  if (state.nextTIL < tilCount) {
            const double tilIncr = tilStamps[state.nextTIL] - state.timeStamp;
            if (tilIncr < maxIncr) maxIncr = tilIncr;
        }


        double maxIncr = 0.0;

        list<StartEvent>::iterator seEnd = state.startEventQueue.end();

        {
            list<StartEvent>::iterator seItr = state.startEventQueue.begin();

            for (; seItr != seEnd; ++seItr) {
                if (!seItr->fanIn) {
                    const double thisIncr = seItr->maxDuration - seItr->elapsed;
                    if (maxIncr < thisIncr) maxIncr = thisIncr;
                }
            }
        }

        if (state.nextTIL < tilCount) {
            const double tilIncr = tilStamps[state.nextTIL] - state.timeStamp;
            if (tilIncr < maxIncr) maxIncr = tilIncr;
        }

        if (debugJA) cout << "Can advance by " << maxIncr << "\n";

        if (lastIsSpecial) --seEnd;

        {
            list<StartEvent>::iterator seItr = state.startEventQueue.begin();

            for (; seItr != seEnd; ++seItr) {
                const double newElapsed = seItr->elapsed + maxIncr;
                if (newElapsed >= seItr->minDuration) {
    //              justApplied[0.0].push_back(seItr->actID);
                } else {
                    justApplied[seItr->minDuration - newElapsed].push_back(seItr->actID);
                    if (debugJA) {
                        cout << seItr->minDuration - newElapsed << " left for step " << seItr->stepID << "\n";
                    }
                }
            }

        }*/

    if (lastIsSpecial) {

        const double newElapsed = seEnd->elapsed;

///     RPGBuilder::LinearEffects * const lEffs = RPGBuilder::getLinearDiscretisation()[seEnd->actID];
        double remainingDur = 0.0;
///     if (lEffs && lEffs->divisions > 1) {
///         for (int d = seEnd->divisionsApplied + 1; d < lEffs->divisions; ++d) {
///             remainingDur += lEffs->durations[d];
///         }
///     }

        if (newElapsed >= seEnd->minDuration) {
            justApplied[remainingDur].push_back(pair<int, int>(seEnd->actID, seEnd->divisionsApplied));
        } else {
            const double insLayer = seItr->minDuration - newElapsed + remainingDur;
            if (insLayer > EPSILON) {
                justApplied[insLayer].push_back(pair<int, int>(seEnd->actID, seEnd->divisionsApplied));
                if (debugJA) {
                    cout << insLayer << " left for step " << seEnd->stepID << " (the last one)\n";
                }
            }

        }
    }

};

class StatesToDelete
{

private:

    ExtendedMinimalState * neverDeleteThis;
    list<ExtendedMinimalState*> gc;

public:

    StatesToDelete(ExtendedMinimalState * s) : neverDeleteThis(s) {
        //cout << "Will never delete " << s << endl;
        //cout << s->getInnerState() << endl;
    }
    
    ~StatesToDelete() {
        list<ExtendedMinimalState*>::iterator cItr = gc.begin();
        const list<ExtendedMinimalState*>::iterator cEnd = gc.end();

        for (; cItr != cEnd; ++cItr) {
            //cout << "Deleting " << *cItr << endl;
            delete *cItr;
        }
        gc.clear();
    }

    void alsoCleanUp(ExtendedMinimalState * const c) {
        assert(c != neverDeleteThis);
        gc.push_back(c);
        //cout << "Will delete " <<  gc.back() << endl;
        //cout << gc.back()->getInnerState() << endl;
    }

    void alsoCleanUp(SearchQueueItem * const s) {
        gc.push_back(s->releaseState());
        //cout << "Due to SQI " << s << ", will delete " <<  gc.back() << endl;
        //cout << gc.back()->getInnerState() << endl;
    }


};

typedef map<ExtendedMinimalState*, double, SecondaryExtendedStateLessThan> InnerMap;
typedef map<ExtendedMinimalState*, pair<double, InnerMap>, WeakExtendedStateLessThan> OuterMap;

class StateHash {
    
public:
    
    class InsertIterator {

    protected:
        InsertIterator() {
        }
    public:    
        virtual ~InsertIterator() {
        }
        
        virtual void setTimestampOfThisState(const ExtendedMinimalState * const e) = 0;
        virtual bool primaryNewState() const = 0;
        virtual bool secondaryNewState() const = 0;
        virtual double previousTimestamp() const = 0;            
    };
    
    class FindIterator {
        
    protected:
        FindIterator() {
        }        
    public:    
        virtual ~FindIterator() {
        }
        
        virtual bool primaryNewState() const = 0;
        virtual bool secondaryNewState() const = 0;
        virtual double previousTimestamp() const = 0;            
        
    };
    
    virtual InsertIterator * insertState(SearchQueueItem * const s, StatesToDelete * const keptStates)  __attribute__((warn_unused_result)) = 0;
    virtual InsertIterator * insertState(ExtendedMinimalState * const e)  __attribute__((warn_unused_result)) = 0;
    virtual FindIterator* findState(ExtendedMinimalState * const e) const   __attribute__((warn_unused_result)) = 0;
    virtual void clear() = 0;
};

class NormalStateHash : protected OuterMap, public StateHash
{

public:

    class InsertIterator : public StateHash::InsertIterator {

    friend class NormalStateHash;
        
    protected:
        pair<OuterMap::iterator, bool> outerInsertion;
        pair<InnerMap::iterator, bool> innerInsertion;
        
    public:
        InsertIterator() {
        }

        virtual void setTimestampOfThisState(const ExtendedMinimalState * const e) {
            const double & t = e->timeStamp;

            double & previousTS = outerInsertion.first->second.first;
            if (previousTS > t) {
                previousTS = t;
            }
            innerInsertion.first->second = t;
        }
        
        virtual bool primaryNewState() const {
            return outerInsertion.second;
        }
        virtual bool secondaryNewState() const {
            return innerInsertion.second;
        }
        virtual double previousTimestamp() const {
            return innerInsertion.first->second;
        }
        
    };

    class FindIterator : public StateHash::FindIterator {

    friend class NormalStateHash;
    
    protected:
        OuterMap::const_iterator outerFind;
        InnerMap::const_iterator innerFind;

        OuterMap::const_iterator outerEnd;
        InnerMap::const_iterator innerEnd;
        
        FindIterator(const OuterMap::const_iterator & itr, const OuterMap::const_iterator & itrEnd)
                : outerFind(itr), outerEnd(itrEnd) {
        }
        
    public:
        virtual bool primaryNewState() const {
            return (outerFind == outerEnd);
        }
        virtual bool secondaryNewState() const {
            return (innerFind == innerEnd);
        }
        virtual double previousTimestamp() const {
            return innerFind->second;
        }
    };

    NormalStateHash() {
    }

    ~NormalStateHash() {
    }

    virtual InsertIterator * insertState(SearchQueueItem * const s, StatesToDelete * const keptStates)  __attribute__((warn_unused_result)) {
        static InnerMap emptyInner;
        InsertIterator* const toReturn = new InsertIterator();

        toReturn->outerInsertion = insert(make_pair(s->state(), make_pair(s->state()->timeStamp, emptyInner)));
        toReturn->innerInsertion = toReturn->outerInsertion.first->second.second.insert(make_pair(s->state(), s->state()->timeStamp));


        if (toReturn->outerInsertion.second || toReturn->innerInsertion.second) {
            keptStates->alsoCleanUp(s);
#ifdef STATEHASHDEBUG
            s->mustNotDeleteState = true;
#endif
        }

        return toReturn;

    }

    virtual InsertIterator * insertState(ExtendedMinimalState * const e)  __attribute__((warn_unused_result)) {
        static InnerMap emptyInner;
        InsertIterator* const toReturn = new InsertIterator();

        toReturn->outerInsertion = insert(make_pair(e, make_pair(e->timeStamp, emptyInner)));

#ifdef STATEHASHDEBUG
        /*if (toReturn.outerInsertion.second) {
            cout << "State " << e << " is new in the outer set\n";
        }*/
#endif

        toReturn->innerInsertion = toReturn->outerInsertion.first->second.second.insert(make_pair(e, e->timeStamp));

#ifdef STATEHASHDEBUG
        /*if (toReturn.innerInsertion.second) {
            cout << "State " << e << " is new in the inner set\n";
        }*/
#endif

        return toReturn;
    }


    virtual FindIterator* findState(ExtendedMinimalState * const e) const   __attribute__((warn_unused_result)) {
        FindIterator * const toReturn = new FindIterator(this->OuterMap::find(e), this->OuterMap::end());
        if (toReturn->outerFind != end()) {
            toReturn->innerFind = toReturn->outerFind->second.second.find(e);
            toReturn->innerEnd = toReturn->outerFind->second.second.end();
        }
        return toReturn;
    }

    virtual void clear() {
        this->OuterMap::clear();
    }

};

typedef map<ExtendedMinimalState*, double, FullExtendedStateLessThan> InnerDominanceMap;

struct ParetoStatesAndOthers {
    
    list<pair<ExtendedMinimalState*,double> > paretoStates;
    InnerDominanceMap others;
    
};

typedef map<ExtendedMinimalState*, ParetoStatesAndOthers, ExtendedStateLessThanOnPropositionsAndNonDominatedVariables> DominanceMap;

class DominanceStateHash : protected DominanceMap, public StateHash
{

private:
    
    static vector<int> varsWithDominanceConstraints;
    static vector<bool> thatVarIsBiggerBetter;
    static int numberOfVarsWithDominanceConstraints;
    
public:

    class InsertIterator : public StateHash::InsertIterator {

    friend class DominanceStateHash;
        
    protected:
        pair<DominanceMap::iterator, bool> outerInsertion;
        list<pair<ExtendedMinimalState*,double> >::iterator paretoStateListIterator;
        pair<InnerDominanceMap::iterator, bool> innerInsertion;
        
    public:
        InsertIterator() {
        }

        virtual void setTimestampOfThisState(const ExtendedMinimalState * const e) {
            const double & t = e->timeStamp;

            if (paretoStateListIterator != outerInsertion.first->second.paretoStates.end()) {
                double & previousTS = paretoStateListIterator->second;
                if (previousTS > t) {
                    previousTS = t;
                }
            }
            innerInsertion.first->second = t;
        }
        
        virtual bool primaryNewState() const {
            return (paretoStateListIterator != outerInsertion.first->second.paretoStates.end());
        }
        virtual bool secondaryNewState() const {
            return innerInsertion.second;
        }
        virtual double previousTimestamp() const {
            return innerInsertion.first->second;
        }
        
    };

    class FindIterator : public StateHash::FindIterator {

    friend class DominanceStateHash;
    
    protected:
        DominanceMap::const_iterator outerFind;
        InnerDominanceMap::const_iterator innerFind;
                
        DominanceMap::const_iterator outerEnd;
        InnerDominanceMap::const_iterator innerEnd;
        
        bool dominatedByAnotherState;
        
        FindIterator(const DominanceMap::const_iterator & itr, const DominanceMap::const_iterator & itrEnd)
                : outerFind(itr), outerEnd(itrEnd), dominatedByAnotherState(false) {
        }
        
    public:
        virtual bool primaryNewState() const {
            return ((outerFind == outerEnd) || !dominatedByAnotherState);
        }
        virtual bool secondaryNewState() const {
            return (innerFind == innerEnd);
        }
        virtual double previousTimestamp() const {
            return innerFind->second;
        }
    };

    static int countDominatedVariables() {
        const vector<NumericAnalysis::dominance_constraint> & dcs = NumericAnalysis::getDominanceConstraints();
        
        const int dcSize = dcs.size();
        
        map<int,double> metricVarWeights; // negative weights make plan quality worse
        
        const RPGBuilder::Metric * const theMetric = RPGBuilder::getMetric();
        
        if (theMetric) {
            list<int>::const_iterator vItr = theMetric->variables.begin();
            const list<int>::const_iterator vEnd = theMetric->variables.end();
            
            list<double>::const_iterator wItr = theMetric->weights.begin();
            const list<double>::const_iterator wEnd = theMetric->weights.end();
            
            for (; vItr != vEnd; ++vItr, ++wItr) {
                if (theMetric->minimise) {
                    metricVarWeights[*vItr] = -*wItr;
                } else {
                    metricVarWeights[*vItr] = *wItr;
                }                 
            }
        }
        
        for (int i = 0; i < dcSize; ++i) {
            if (dcs[i] == NumericAnalysis::E_BIGGERISBETTER) {
                varsWithDominanceConstraints.push_back(i);
                thatVarIsBiggerBetter.push_back(true);
            } else if (dcs[i] == NumericAnalysis::E_SMALLERISBETTER) {
                varsWithDominanceConstraints.push_back(i);
                thatVarIsBiggerBetter.push_back(false);
            } else if (dcs[i] == NumericAnalysis::E_METRICTRACKING && Globals::optimiseSolutionQuality) {
                assert(RPGBuilder::getMetric());
                const map<int,double>::const_iterator wItr = metricVarWeights.find(i);
                if (wItr != metricVarWeights.end()) {
                    if (wItr->second < 0) {
                        varsWithDominanceConstraints.push_back(i);
                        thatVarIsBiggerBetter.push_back(false);
                    } else if (wItr->second > 0) {
                        varsWithDominanceConstraints.push_back(i);
                        thatVarIsBiggerBetter.push_back(true);
                    }
                }
            }
        }
        
        numberOfVarsWithDominanceConstraints = varsWithDominanceConstraints.size();        
        
        return numberOfVarsWithDominanceConstraints;                
    }
    
    DominanceStateHash() {
        assert(numberOfVarsWithDominanceConstraints || !RPGBuilder::getPreferences().empty());
    }

    ~DominanceStateHash() {
    }

    virtual InsertIterator * insertState(SearchQueueItem * const s, StatesToDelete * const keptStates)  __attribute__((warn_unused_result)) {
        
        InsertIterator* const toReturn = insertState(s->state());

        if (toReturn->outerInsertion.second || toReturn->innerInsertion.second) {
            keptStates->alsoCleanUp(s);
#ifdef STATEHASHDEBUG
            s->mustNotDeleteState = true;
#endif
        }

        return toReturn;

    }

    virtual InsertIterator * insertState(ExtendedMinimalState * const e)  __attribute__((warn_unused_result)) {
        static const bool insDebug = false;
        static ParetoStatesAndOthers emptyInner;
        InsertIterator* const toReturn = new InsertIterator();

        toReturn->outerInsertion = insert(make_pair(e, emptyInner));
        toReturn->paretoStateListIterator = toReturn->outerInsertion.first->second.paretoStates.end();
        
        if (toReturn->outerInsertion.second) {
            if (insDebug) {
                cout << "No states previously at " << &(toReturn->outerInsertion.first->second) << ": " << e << " is the first one" << endl;
            }
            
            // haven't seen anything with this combination of propositions and non-dominated variable values before
            // so, it's got to be new.
            toReturn->outerInsertion.first->second.paretoStates.push_front(make_pair(e, e->timeStamp));
            toReturn->paretoStateListIterator = toReturn->outerInsertion.first->second.paretoStates.begin();
            toReturn->innerInsertion = toReturn->outerInsertion.first->second.others.insert(make_pair(e, e->timeStamp));            
        } else {
            // work out if this dominates any existing states on the list
                       
                       
            bool dominatesAnything = false;
            bool dominatedByAnything = false;
            bool identicalToAnything = false;
            bool betterThanAnExistingStateInAtLeastOneWay = false;
            
            list<pair<ExtendedMinimalState*, double> > & paretoStates = toReturn->outerInsertion.first->second.paretoStates;

            if (insDebug) {
                cout << "Checking " << paretoStates.size() << " pareto set of states at " << &(toReturn->outerInsertion.first->second) << endl;
            }
                                   
                                   
            
            list<pair<ExtendedMinimalState*, double> >::iterator psItr = paretoStates.begin();
            const list<pair<ExtendedMinimalState*, double> >::iterator psEnd = paretoStates.end();
            
            int v;
            
            const vector<double> & newStateMin = e->getInnerState().secondMin;
            const vector<double> & newStateMax = e->getInnerState().secondMax;
            const vector<AutomatonPosition::Position> & proposed = e->getInnerState().preferenceStatus;
            
            while (psItr != psEnd) {
                bool anythingBetter = false;
                bool anythingWorse = false;
                
                if (insDebug) {
                    cout << "- Comparing to " << psItr->first << endl;
                }
                                       

                if (e->getInnerState().prefPreconditionViolations > psItr->first->getInnerState().prefPreconditionViolations) {
                    anythingWorse = true;
                } else if (e->getInnerState().prefPreconditionViolations < psItr->first->getInnerState().prefPreconditionViolations) {
                    anythingBetter = true;
                }
                                                                              
                const vector<double> & oldStateMin = psItr->first->getInnerState().secondMin;
                const vector<double> & oldStateMax = psItr->first->getInnerState().secondMax;
                
                for (int i = 0; i < numberOfVarsWithDominanceConstraints; ++i) {
                    v = varsWithDominanceConstraints[i];
                    if (thatVarIsBiggerBetter[i]) {                        
                        if (newStateMin[v] > oldStateMin[v] + 0.0005 || newStateMax[v] > oldStateMax[v] + 0.0005) {
                            if (insDebug) {
                                cout << "New bounds on " << *(RPGBuilder::getPNE(v)) << " are better: [" << newStateMin[v] << ", " << newStateMax[v] << "] vs [" << oldStateMin[v] << ", " << oldStateMax[v] << "]\n";
                            }
                            anythingBetter = true;
                        }
                        if (newStateMin[v] < oldStateMin[v] - 0.0005 || newStateMax[v] < oldStateMax[v] - 0.0005) {
                            if (insDebug) {
                                cout << "New bounds on " << *(RPGBuilder::getPNE(v)) << " are worse: [" << newStateMin[v] << ", " << newStateMax[v] << "] vs [" << oldStateMin[v] << ", " << oldStateMax[v] << "]\n";
                            }                            
                            anythingWorse = true;
                        }
                    } else {
                        if (newStateMin[v] < oldStateMin[v] - 0.0005 || newStateMax[v] < oldStateMax[v] - 0.0005) {
                            if (insDebug) {
                                cout << "New bounds on " << *(RPGBuilder::getPNE(v)) << " are better: [" << newStateMin[v] << ", " << newStateMax[v] << "] vs [" << oldStateMin[v] << ", " << oldStateMax[v] << "]\n";
                            }                            
                            anythingBetter = true;
                        }
                    if (newStateMin[v] > oldStateMin[v] + 0.0005 || newStateMax[v] > oldStateMax[v] + 0.0005) {
                            if (insDebug) {
                                cout << "New bounds on " << *(RPGBuilder::getPNE(v)) << " are worse: [" << newStateMin[v] << ", " << newStateMax[v] << "] vs [" << oldStateMin[v] << ", " << oldStateMax[v] << "]\n";
                            }                            
                            anythingWorse = true;
                        }
                    }
                }
                
                {
                    static int pStatus, p;
                    int tpCount = proposed.size();
                    const vector<AutomatonPosition::Position> & existing = psItr->first->getInnerState().preferenceStatus;
                    for (p = 0; p < tpCount; ++p) {
                        pStatus = PreferenceHandler::compareStatusOfPref(p,proposed[p], existing[p]);
                        if (pStatus > 0) {
                           anythingWorse = true;
                        } else if (pStatus < 0) {
                            anythingBetter = true;
                        }
                    }
                }
                
                if (anythingWorse) {
                    if (anythingBetter) {
                        betterThanAnExistingStateInAtLeastOneWay = true;
                        if (insDebug) {
                            cout << "  - New state is better in at least one way\n";
                        }                        
                    } else {
                        // something is worse but nothing is better - existing state dominates this one
                        dominatedByAnything = true;
                        if (insDebug) {
                            cout << "  - Dominates the new state\n";
                        }                        
                        break;                        
                    }
                    ++psItr;
                } else {
                    if (anythingBetter) {
                        psItr->first->hasBeenDominated = true;
                        const list<pair<ExtendedMinimalState*, double> >::iterator psDel = psItr++;
                        paretoStates.erase(psDel);
                        dominatesAnything = true;
                        if (insDebug) {
                            cout << "  - New state dominates this one\n";
                        }
                        
                    } else {
                        // nothing worse, nothing better - is identical to this state
                        // (at least on the primary criteria)
                        identicalToAnything = true;
                        if (insDebug) {
                            cout << "  - Identical to the new state\n";
                        }
                        
                        break;                        
                    }
                }
            }
            
            if (identicalToAnything || dominatedByAnything) {
                if (insDebug) {
                    cout << "As it's identical to something, or dominated by something, just doing a secondary insertion of " << e << "\n";
                }
                
                toReturn->innerInsertion = toReturn->outerInsertion.first->second.others.insert(make_pair(e, e->timeStamp));                
                
                if ((Globals::globalVerbosity & 1) && toReturn->innerInsertion.second) {
                    cout << "D"; cout.flush();
                }
            } else {
                if (dominatesAnything || betterThanAnExistingStateInAtLeastOneWay) {
                    if (insDebug) {
                        cout << "As it dominates something, or is non-dominated, doing a primary insertion of " << e << " and adding to the pareto list\n";
                    }
                    
                    toReturn->innerInsertion = toReturn->outerInsertion.first->second.others.insert(make_pair(e, e->timeStamp));

                    if (toReturn->innerInsertion.second) {
                        toReturn->outerInsertion.first->second.paretoStates.push_front(make_pair(e, e->timeStamp));
                        toReturn->paretoStateListIterator = toReturn->outerInsertion.first->second.paretoStates.begin();
                    } else {
                        if (insDebug) {
                            cout << "Actually just quietly doing a secondary insertion, as there looks to be a similar state from before\n";
                        }
                    }
                    
                    if ((Globals::globalVerbosity & 1) && !toReturn->innerInsertion.second) {
                        cout << "i"; cout.flush();
                    }
                } else {
                    if (insDebug) {
                        cout << "Secondary insertion of " << e << ": the residual case\n";
                    }
                    
                    toReturn->innerInsertion = toReturn->outerInsertion.first->second.others.insert(make_pair(e, e->timeStamp));
                    if ((Globals::globalVerbosity & 1) && toReturn->innerInsertion.second) {
                        cout << "D"; cout.flush();
                    }
                }
            }
            
        }
        
        return toReturn;
    }


    virtual FindIterator* findState(ExtendedMinimalState * const e) const   __attribute__((warn_unused_result)) {
        FindIterator * const toReturn = new FindIterator(this->DominanceMap::find(e), this->DominanceMap::end());
        if (toReturn->outerFind != end()) {
            toReturn->innerFind = toReturn->outerFind->second.others.find(e);
            toReturn->innerEnd = toReturn->outerFind->second.others.end();
            
            if (toReturn->outerFind->second.paretoStates.empty()) {
                toReturn->dominatedByAnotherState = false;
            } else {
                // check pareto list
                bool dominatesAnything = false;
                bool dominatedByAnything = false;
                bool identicalToAnything = false;
                bool betterThanAnExistingStateInAtLeastOneWay = false;
                
                const list<pair<ExtendedMinimalState*, double> > & paretoStates = toReturn->outerFind->second.paretoStates;
                
                list<pair<ExtendedMinimalState*, double> >::const_iterator psItr = paretoStates.begin();
                const list<pair<ExtendedMinimalState*, double> >::const_iterator psEnd = paretoStates.end();
                
                int v;
                
                const vector<double> & newStateMin = e->getInnerState().secondMin;
                const vector<double> & newStateMax = e->getInnerState().secondMax;
                
                for (; psItr != psEnd; ++psItr) {
                    bool anythingBetter = false;
                    bool anythingWorse = false;
                    const vector<double> & oldStateMin = psItr->first->getInnerState().secondMin;
                    const vector<double> & oldStateMax = psItr->first->getInnerState().secondMax;
                    
                    for (int i = 0; i < numberOfVarsWithDominanceConstraints; ++i) {
                        v = varsWithDominanceConstraints[i];
                        if (thatVarIsBiggerBetter[i]) {                        
                            if (newStateMin[v] > oldStateMin[v] || newStateMax[v] > oldStateMax[v]) {
                                anythingBetter = true;
                            }
                            if (newStateMin[v] < oldStateMin[v] && newStateMax[v] < oldStateMax[v]) {
                                anythingWorse = true;
                            }
                        } else {
                            if (newStateMin[v] < oldStateMin[v] || newStateMax[v] < oldStateMax[v]) {
                                anythingBetter = true;
                            }
                            if (newStateMin[v] > oldStateMin[v] && newStateMax[v] > oldStateMax[v]) {
                                anythingWorse = true;
                            }
                        }
                    }
                    if (anythingWorse) {
                        if (anythingBetter) {
                            betterThanAnExistingStateInAtLeastOneWay = true;
                        } else {
                            // something is worse but nothing is better - existing state dominates this one
                            dominatedByAnything = true;
                            break;                        
                        }
                    } else {
                        if (anythingBetter) {
                            dominatesAnything = true;
                            break;
                        } else {
                            // nothing worse, nothing better - is identical to this state
                            // (at least on the primary criteria)
                            identicalToAnything = true;
                            break;                        
                        }
                    }
                }
                
                if (identicalToAnything || dominatedByAnything) {
                    toReturn->dominatedByAnotherState = true;                
                } else {
                    if (dominatesAnything || betterThanAnExistingStateInAtLeastOneWay) {
                        toReturn->dominatedByAnotherState = false;
                    } else {
                        toReturn->dominatedByAnotherState = true;
                    }
                }                                
            }
        }
        return toReturn;
    }

    virtual void clear() {
        this->DominanceMap::clear();
    }

};

vector<int> DominanceStateHash::varsWithDominanceConstraints;
vector<bool> DominanceStateHash::thatVarIsBiggerBetter;
int DominanceStateHash::numberOfVarsWithDominanceConstraints;

#ifdef DOUBLESTATEHASH
struct OldCompareStates {


    bool operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const {
        
        const MinimalState & a = ae.getInnerState();
        const MinimalState & b = be.getInnerState();
        
        const int csVal = CSBase::oldCompareSets(a.first, b.first);
        if (csVal > 0) {
            return true;
        } else if (csVal < 0) {
            return false;
        }
        
        const int cv1Val = CSBase::compareVecs(a.secondMin, b.secondMin);
        if (cv1Val > 0) {
            return true;
        } else if (cv1Val < 0) {
            return false;
        }

        const int cv2Val = CSBase::compareVecs(a.secondMax, b.secondMax);
        if (cv2Val > 0) {
            return true;
        } else if (cv2Val < 0) {
            return false;
        }

    
        const int saVal = CSBase::compareMaps(a.startedActions, b.startedActions);

        if (saVal > 0) {
            return true;
        } else if (saVal < 0) {
            return false;
        }

/*      const int invVal = CSBase::compareMaps(a.invariants, b.invariants);

        if (invVal > 0) {
            return true;
        } else if (invVal < 0) {
            return false;
        }*/
    
        const int ceVal = CSBase::compareLists(ae.startEventQueue, be.startEventQueue);

        if (ceVal > 0) {
            return true;
        } else if (ceVal < 0) {
            return false;
        }
      
        if (a.nextTIL < b.nextTIL) return true;
        if (a.nextTIL > b.nextTIL) return false;

        return false;
    }

};


struct OldCompareStatesZealously {


    bool operator()(const ExtendedMinimalState & ae, const ExtendedMinimalState & be) const {

        const MinimalState & a = ae.getInnerState();
        const MinimalState & b = be.getInnerState();
        
        const int csVal = CSBase::oldCompareSets(a.first, b.first);
        if (csVal > 0) {
            return true;
        } else if (csVal < 0) {
            return false;
        }
        
        const int cv1Val = CSBase::compareVecs(a.secondMin, b.secondMin);
        if (cv1Val > 0) {
            return true;
        } else if (cv1Val < 0) {
            return false;
        }

        const int cv2Val = CSBase::compareVecs(a.secondMax, b.secondMax);
        if (cv2Val > 0) {
            return true;
        } else if (cv2Val < 0) {
            return false;
        }
    
        const int saVal = CSBase::compareMaps(a.startedActions, b.startedActions);

        if (saVal > 0) {
            return true;
        } else if (saVal < 0) {
            return false;
        }

        /*const int invVal = CSBase::compareMaps(a.invariants, b.invariants);

        if (invVal > 0) {
            return true;
        } else if (invVal < 0) {
            return false;
        }
          */
        if (a.nextTIL < b.nextTIL) return true;
        if (a.nextTIL > b.nextTIL) return false;

        return false;
    }

};


#endif

bool FF::useDominanceConstraintsInStateHash = false;

StateHash* FF::getStateHash() {
    if (useDominanceConstraintsInStateHash && (DominanceStateHash::countDominatedVariables() || !RPGBuilder::getPreferences().empty())) {
        return new DominanceStateHash();
    } else {
        return new NormalStateHash();
    }
}

bool FF::planMustSucceed = false;

list<FFEvent> * FF::doBenchmark(bool & reachedGoal, list<FFEvent> * oldSoln, const bool doLoops)
{

    static bool initCSBase = false;

    if (!initCSBase) {
        initCSBase = true;
        const vector<NumericAnalysis::dominance_constraint> & dcs = NumericAnalysis::getDominanceConstraints();
        const int pneCount = dcs.size();
        CSBase::ignorableFluents = vector<bool>(pneCount);
        CSBase::nonDominatedFluent = vector<bool>(pneCount);
        for (int i = 0; i < pneCount; ++i) {
            CSBase::ignorableFluents[i] = ((!Globals::optimiseSolutionQuality && dcs[i] == NumericAnalysis::E_METRICTRACKING) || (dcs[i] == NumericAnalysis::E_IRRELEVANT));
            CSBase::nonDominatedFluent[i] = (!(CSBase::ignorableFluents[i]) && dcs[i] == NumericAnalysis::E_NODOMINANCE);
        }
    }

    if (FF::allowCompressionSafeScheduler) {
        FF::allowCompressionSafeScheduler = CompressionSafeScheduler::canUseThisScheduler();
    }
    

    set<int> goals;
    set<int> numericGoals;
    ExtendedMinimalState initialState;

    initialState.timeStamp = 0.0;

    {
        LiteralSet tinitialState;
        vector<double> tinitialFluents;

        RPGBuilder::getNonStaticInitialState(tinitialState, tinitialFluents);

        initialState.getEditableInnerState().setFacts(tinitialState);
        initialState.getEditableInnerState().setFacts(tinitialFluents);
                
        
        {
            const int pneCount = RPGBuilder::getPNECount();
            
            for (int pne = 0; pne < pneCount; ++pne) {
                if (!RPGBuilder::getWhetherDefinedValueInInitialState()[pne]) {
                    initialState.getEditableInnerState().secondMin[pne] = DBL_MAX;
                    initialState.getEditableInnerState().secondMax[pne] = -DBL_MAX;
                }
            }
        }
//         
        
        #ifdef STOCHASTICDURATIONS        
        durationManager->prepareTheInitialState(initialState.getEditableInnerState());        
        #endif

    }
    {
        initialState.getEditableInnerState().preferenceStatus = PreferenceHandler::getInitialAutomataPositions();    
        initialState.getEditableInnerState().prefPreconditionViolations = 0.0;
        
        const int tdrFactCount = NumericAnalysis::getFactsInTimeDependentRewards().size();
        if (tdrFactCount) {
            
            double * toFill = initialState.getEditableInnerState().lowerBoundOnTimeDependentRewardFacts = new double[tdrFactCount];
            
            for (int f = 0; f < tdrFactCount; ++f) {
                toFill[f] = 0.0;
            }            
        }
        
        //initialState.getEditableInnerState().cost = 0.0;
    }
    
    {
        list<Literal*>::iterator gsItr = RPGBuilder::getLiteralGoals().begin();
        const list<Literal*>::iterator gsEnd = RPGBuilder::getLiteralGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            const pair<bool, bool> & currStatic = RPGBuilder::isStatic(*gsItr);
            if (currStatic.first) {
                if (!currStatic.second) {
                    cout << "Static goal " << *(*gsItr) << " resolves to false: no plan can solve this problem\n";
                    if (planMustSucceed && !oldSoln->empty()) {
                        exit(1);
                    }
                    reachedGoal = false;
                    return 0;
                }
            } else {
                goals.insert((*gsItr)->getStateID());
            }

        }

    }

    {
        list<pair<int, int> >::iterator gsItr = RPGBuilder::getNumericRPGGoals().begin();
        const list<pair<int, int> >::iterator gsEnd = RPGBuilder::getNumericRPGGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            if (gsItr->first != -1) {
                numericGoals.insert(gsItr->first);
            }
            if (gsItr->second != -1) {
                numericGoals.insert(gsItr->second);
            }
        }
    }


    #ifdef POPF3ANALYSIS
    /*if (reprocessQualityBound != std::numeric_limits<double>::signaling_NaN() && RPGBuilder::getMetric()) {
        if (reprocessQualityBound == 0.0) {
            Globals::bestSolutionQuality = 0.0;
        } else if (RPGBuilder::getMetric()->minimise) {
            Globals::bestSolutionQuality = -reprocessQualityBound;
        } else {
            Globals::bestSolutionQuality = -reprocessQualityBound;
        }
        
    }*/
    #endif


    list<FFEvent>::iterator osItr = oldSoln->begin();
    const list<FFEvent>::iterator osEnd = oldSoln->end();

    SearchQueueItem * currSQI = new SearchQueueItem(&initialState, false);

    TemporalAnalysis::pullInAbstractTILs(currSQI->state()->getEditableInnerState(), currSQI->plan);
    
    StatesToDelete * const keptStates = new StatesToDelete(&initialState);

    auto_ptr<StateHash> visitedStates(getStateHash());
    delete visitedStates->insertState(&initialState);

    set<int> ignoreStep;

    #ifdef ENABLE_DEBUGGING_HOOKS
    {
        Globals::remainingActionsInPlan.clear();
        list<FFEvent>::iterator rsItr = oldSoln->begin();
        for (; rsItr != osEnd; ++rsItr) {
            if (rsItr->time_spec == Planner::E_AT) {
                Globals::remainingActionsInPlan.push_back(ActionSegment((instantiatedOp*)0, Planner::E_AT, rsItr->divisionID, set<int>()));
            } else {
                Globals::remainingActionsInPlan.push_back(ActionSegment(rsItr->action,
                                                                        rsItr->time_spec,
                                                                        rsItr->divisionID,
                                                                        set<int>() ));
            }
        }
    }
    #endif
    
    if (!doLoops) {
        list<FFEvent> tEvent;
        HTrio h2;
        HTrio h1;        
        bool pruned = false;
        #ifdef POPF3ANALYSIS        
        if (Globals::optimiseSolutionQuality) {
            h2.makespan = 0.0;
            h2.admissibleCostEstimate = calculateAdmissibleCost(currSQI->state()->getInnerState(),0.0,(RPGBuilder::getMetric() && !RPGBuilder::getMetric()->minimise ? DBL_MAX : 0.0),false);
            if (admissibleCostExceedsBound(h2.admissibleCostEstimate, false)) {        
                h2 = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded incumbent solution cost");
                pruned = true;
            } else {
                cout << "Admissible cost of initial state: " << h2.admissibleCostEstimate << endl;
            }
        }
        #endif
        
        if (pruned) {
            cout << "Initial state pruned - skipping heuristic\n";
            h1 = h2;
        } else {
            cout << "Calculating initial state heuristic value\n";
            if (FF::allowCompressionSafeScheduler) {
                h1 = calculateHeuristicAndCompressionSafeSchedule(*(currSQI->state()), 0, goals, numericGoals,
                                                                  currSQI->helpfulActions, currSQI->plan, tEvent, -1);
                
            } else {
                pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
                
                h1 = calculateHeuristicAndSchedule(*(currSQI->state()), 0, goals, numericGoals,
                                                   (ParentData*) 0, currSQI->helpfulActions, currentCost, currSQI->plan, tEvent, -1);
            }
            
            if (RPGBuilder::getMetric()) {
                if (RPGBuilder::getMetric()->minimise) {
                    if ( h1.admissibleCostEstimate < h2.admissibleCostEstimate) {
                        h1.admissibleCostEstimate = h2.admissibleCostEstimate;
                    }
                } else {
                    if ( h1.admissibleCostEstimate > h2.admissibleCostEstimate) {
                        h1.admissibleCostEstimate = h2.admissibleCostEstimate;
                    }
                }
            }
        }

        currSQI->heuristicValue = h1;
        cout << "Heuristic value of initial state: ";
        if (h1.heuristicValue != -1.0) {
            cout << h1.heuristicValue << "\n";
        } else {
            cout << " dead end";
#ifndef NDEBUG
            if (h1.diagnosis) {
                cout << " - " << h1.diagnosis;
            }
#endif
            cout << "\n";
            if (planMustSucceed) {
                exit(1);
            }
        }
    }

    for (int i = 1; osItr != osEnd; ++osItr, ++i) {

        #ifdef ENABLE_DEBUGGING_HOOKS        
        Globals::remainingActionsInPlan.pop_front();        
        #endif
        
        ActionSegment actID(osItr->action, osItr->time_spec, osItr->divisionID, RPGHeuristic::emptyIntList);

        {
            cout << COLOUR_light_blue << "About to apply ";
            if (actID.second == Planner::E_AT_START) {
                cout << *(actID.first) << " start";
            } else if (actID.second == Planner::E_AT_END) {
                cout << *(actID.first) << " end";
            } else {
                cout << "TIL " << actID.divisionID;
            }
            cout << ", originally at " << osItr->lpTimestamp << COLOUR_default << "\n";
        }

        if (ignoreStep.find(i - 1) != ignoreStep.end()) {
            cout << "\tIs the end of a skippable action\n";
            continue;
        }

        #ifndef NDEBUG

        assert(actID.second == Planner::E_AT || !RPGBuilder::rogueActions[actID.first->getID()]);
        
        {
            list<ActionSegment > maybeApplicableActions;
            RPGBuilder::getHeuristic()->findApplicableActions(currSQI->state()->getInnerState(), currSQI->state()->timeStamp, maybeApplicableActions);
            
            list<ActionSegment >::const_iterator appItr = maybeApplicableActions.begin();
            const list<ActionSegment >::const_iterator appEnd = maybeApplicableActions.end();
            
            for (; appItr != appEnd; ++appItr) {
                if (appItr->second == Planner::E_AT && actID.second == Planner::E_AT) {
                    if (appItr->divisionID == actID.divisionID) {
                        cout << "Found match for the action in those applicable in the state\n";
                        break;
                    }
                } else {
                    if (appItr->first == actID.first && appItr->second == actID.second) {
                        cout << "Found match for the action in those applicable in the state\n";
                        break;
                    }
                }
            }
            if (appItr == appEnd) {
                cout << COLOUR_light_red << "*** Action was not considered applicable by findApplicableActions()\n" << COLOUR_default;
                exit(1);
            }
        }
        
        #endif

        auto_ptr<ParentData> pd(FF::allowCompressionSafeScheduler
                                  ? 0
                                  :  LPScheduler::prime(currSQI->plan, currSQI->state()->getInnerState().temporalConstraints,
                                     currSQI->state()->startEventQueue, Globals::optimiseSolutionQuality)
                               );

        const int oldTIL = currSQI->state()->getInnerState().nextTIL;                    
                                        
        list<pair<int, FFEvent> > newDummySteps;
        
        SearchQueueItem * succ = new SearchQueueItem(applyActionToState(actID, *(currSQI->state()), currSQI->plan, newDummySteps), true);

        succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;
        
        if (!succ->state()) {
            cout << "Takes us to a null state: trying to start an action whose min duration exceeds its max\n";
        }

        if (tsChecking) {
            if (!checkTemporalSoundness(currSQI->state(), *(succ->state()), actID, oldTIL)) {
                cout << COLOUR_light_red << "*** Trivial cycle detected\n" << COLOUR_default;
            } else {
                cout << "No cycles detected so far\n";
            }
        }

        if (!stateHasProgressedBeyondItsParent(actID, *(currSQI->state()), *(succ->state()))) {
            cout << COLOUR_light_blue << "*** Would prune the state, as it doesn't look to have improved on its parent\n" << COLOUR_default;
        }

        if (!RPGBuilder::getPreferences().empty()) {
            cout << COLOUR_yellow << "Current " << PreferenceHandler::getCurrentViolations(succ->state()->getInnerState()) << " with precondition violations " << succ->state()->getInnerState().prefPreconditionViolations;
            cout.flush();
            cout << ", can reach " << PreferenceHandler::getReachableCost(succ->state()->getInnerState()) << COLOUR_default << endl;
        }
        
        
        #ifdef POPF3ANALYSIS        
        if (Globals::optimiseSolutionQuality) {
            succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
            if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {            
                cout << COLOUR_light_red << "*** Would prune the state, for cost reasons\n" << COLOUR_default;                
            }
        }
        #endif

        if (!doLoops) {
            auto_ptr<StateHash::InsertIterator> insResult(visitedStates->insertState(succ, keptStates));

            if (insResult->primaryNewState()) {
                cout << "Next action takes us to a new state\n";
                insResult->setTimestampOfThisState(succ->state());
            } else {
                cout << "*** Next action takes us to a memoised state";
                if (succ->state()->timeStamp < insResult->previousTimestamp()) {
                    cout << " but at a better timestamp\n";
                    insResult->setTimestampOfThisState(succ->state());
                } else {
                    cout << "\n";
                }
            }

            if (!FF::bestFirstSearch) {
                list<ActionSegment>::iterator asItr = currSQI->helpfulActions.begin();
                const list<ActionSegment>::iterator asEnd = currSQI->helpfulActions.end();

                for (; asItr != asEnd; ++asItr) {
                    if (asItr->first == actID.first && asItr->second == actID.second && asItr->divisionID == actID.divisionID) break;
                    assert(!(asItr->first == actID.first && asItr->second == actID.second && asItr->second != Planner::E_AT));
                }
                if (asItr == asEnd) {
                    cout << "--\nAction was not helpful when it should have been.  The helpful actions were:\n";
                    asItr = currSQI->helpfulActions.begin();

                    for (; asItr != asEnd; ++asItr) {
                        cout << "\t";
                        if (asItr->first) {
                            cout << *(asItr->first);
                            if (asItr->second == Planner::E_AT_END) {
                                cout << " end\n";
                            } else {
                                cout << " start\n";
                            }
                        } else {
                            cout << "TIL " << asItr->divisionID << "\n";
                        }
                    }
                    /*              list<ActionSegment> prevHelpful;
                                  list<FFEvent> tEvent;
                                  const int oldVerbosity = Globals::globalVerbosity;
                                  Globals::globalVerbosity = oldVerbosity & 64;
                                  HTrio h1(evaluateStateWRTSchedule(rpg, *(currSQI->state), 0, goals, numericGoals, (ParentData*) 0, prevHelpful, currSQI->plan, tEvent, -1));
                                  Globals::globalVerbosity = oldVerbosity;*/
                }
            }
        }


        HTrio h1;

        
        const bool rawDebug = false;

        bool pruned = false;
        
        #ifdef POPF3ANALYSIS        
        if (Globals::optimiseSolutionQuality) {
            succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
            if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate,false)) {        
                h1 = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded incumbent solution cost");
                pruned = true;
            }
        }
        #endif

        
        FFEvent extraEvent;
        FFEvent extraEventTwo;

        FFEvent * reusedEndEvent = 0;

        bool eventOneDefined = false;
        bool eventTwoDefined = false;


        map<double, list<pair<int, int> > > actualJustApplied;

        succ->plan = currSQI->plan;

        int stepID = -1;



        if (actID.second == Planner::E_AT_START) {
            if (rawDebug) cout << "RAW start\n";
            extraEvent = FFEvent(actID.first, succ->state()->startEventQueue.back().minDuration, succ->state()->startEventQueue.back().maxDuration);
            eventOneDefined = true;
            assert(extraEvent.time_spec == Planner::E_AT_START);
            if (!RPGBuilder::getRPGDEs(actID.first->getID()).empty()) { // if it's not a non-temporal action

                const int startStepID = currSQI->state()->getInnerState().planLength;
                const int endStepID = startStepID + 1;
                
                extraEventTwo = FFEvent(actID.first, startStepID, succ->state()->startEventQueue.back().minDuration, succ->state()->startEventQueue.back().maxDuration);
                extraEvent.pairWithStep = endStepID;
                eventTwoDefined = true;

                if (!TemporalAnalysis::canSkipToEnd(actID.first->getID())) {
                    extraEventTwo.getEffects = false;
                } else {
                    ignoreStep.insert(osItr->pairWithStep);
                }

                stepID = startStepID;
            } else {
                stepID = currSQI->state()->getInnerState().planLength;
            }

        } else if (actID.second == Planner::E_AT_END) {
            if (rawDebug) cout << "RAW end\n";
            map<int, list<list<StartEvent>::iterator > >::iterator tsiOld = succ->state()->entriesForAction.find(actID.first->getID());
            assert(tsiOld != succ->state()->entriesForAction.end());

            list<StartEvent>::iterator pairWith = tsiOld->second.front();
            tsiOld->second.pop_front();
            if (tsiOld->second.empty()) succ->state()->entriesForAction.erase(tsiOld);

            stepID = pairWith->stepID + 1;

            {
                list<FFEvent>::iterator pwItr = succ->plan.begin();
                for (int sID = 0; sID <= pairWith->stepID; ++sID, ++pwItr) ;
                pwItr->getEffects = true;
                reusedEndEvent = &(*pwItr);
            }

            succ->state()->startEventQueue.erase(pairWith);


        } else {
            extraEvent = FFEvent(actID.divisionID);
            eventOneDefined = true;
            stepID = currSQI->state()->getInnerState().planLength;
        }

        FFcache_upToDate = false;

        int currStepID = currSQI->state()->getInnerState().planLength;
        
        list<FFEvent> nowList;
        if (eventOneDefined) {
            nowList.push_back(extraEvent);
            ++currStepID;
        }
        if (eventTwoDefined) {
            nowList.push_back(extraEventTwo);
            ++currStepID;
        }
        
        //const int dsSize = newDummySteps.size();
        
        pairDummyStepsWithRealSteps(succ->state()->getEditableInnerState(), currStepID, succ->plan, nowList, newDummySteps);
        
        
        #ifdef STOCHASTICDURATIONS
    
        bool isAStochasticGoalState = false;
        bool stochasticOkay = true;
        
        if (actID.second == Planner::E_AT_END) {
            if (!durationManager->updateTimestampsOfNewPlanStep(currSQI->state()->getInnerState(), succ->state()->getEditableInnerState(), succ->plan, reusedEndEvent, 0, stepID, isAStochasticGoalState)) {
                h1 = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded stochastic deadline");
                stochasticOkay = false;
            }
        } else {
            FFEvent * local1 = 0;
            FFEvent * local2 = 0;
            if (eventOneDefined && eventTwoDefined) {
                list<FFEvent>::reverse_iterator itr = nowList.rbegin();
                local2 = &(*itr);
                ++itr;
                local1 = &(*itr);
            } else {
                local1 = &(nowList.back());
            }
            if (!durationManager->updateTimestampsOfNewPlanStep(currSQI->state()->getInnerState(), succ->state()->getEditableInnerState(), succ->plan, local1, local2, stepID, isAStochasticGoalState)) {
                h1 = HTrio(-1.0, DBL_MAX, DBL_MAX, INT_MAX, "Exceeded stochastic deadline");
                stochasticOkay = false;
            }
        }
        #endif

        if (doLoops) cout << i << ",";

        tms before;
        times(&before);

        {
            list<FFEvent> toPrint(succ->plan);
            toPrint.insert(toPrint.end(), nowList.begin(), nowList.end());
            printPlanAsDot(cout, toPrint, succ->state()->getInnerState().temporalConstraints);
        }

        if (doLoops) {
            for (int rep = 0; rep < 99; ++rep) {
                if (rep) {
                    if (eventOneDefined) nowList.pop_back();
                    if (eventTwoDefined) nowList.pop_back();
                    if (eventOneDefined) nowList.push_back(extraEvent);
                    if (eventTwoDefined) nowList.push_back(extraEventTwo);
                }

                LPScheduler tryToSchedule(succ->state()->getInnerState(), succ->state()->getEditableInnerState().preferenceStatus, succ->plan, nowList, i - 1, succ->state()->startEventQueue,
                                          pd.get(), succ->state()->entriesForAction, &(currSQI->state()->getInnerState().secondMin),
                                          &(currSQI->state()->getInnerState().secondMax),  &(succ->state()->tilComesBefore), false);

                vector<double> timeAtWhichValueIsDefined;
                                          
                tryToSchedule.updateStateFluents(succ->state()->getEditableInnerState().secondMin, succ->state()->getEditableInnerState().secondMax, timeAtWhichValueIsDefined);
            }


            if (eventOneDefined) nowList.pop_back();
            if (eventTwoDefined) nowList.pop_back();
            if (eventOneDefined) nowList.push_back(extraEvent);
            if (eventTwoDefined) nowList.push_back(extraEventTwo);
            LPScheduler tryToSchedule(succ->state()->getInnerState(), succ->state()->getEditableInnerState().preferenceStatus, succ->plan, nowList, i - 1, succ->state()->startEventQueue, pd.get(),
                                      succ->state()->entriesForAction, &(currSQI->state()->getInnerState().secondMin), &(currSQI->state()->getInnerState().secondMax),  &(succ->state()->tilComesBefore), false);

            //assert(tryToSchedule.isSolved());

            vector<double> timeAtWhichValueIsDefined;
            tryToSchedule.removeExpiredAbstractFacts(succ->state()->getEditableInnerState().first);
            tryToSchedule.updateStateFluents(succ->state()->getEditableInnerState().secondMin, succ->state()->getEditableInnerState().secondMax, timeAtWhichValueIsDefined);
        } else {
            
            #ifdef STOCHASTICDURATIONS            
            if (stochasticOkay) {
            #endif
            
            if (FF::allowCompressionSafeScheduler) {
                h1 = calculateHeuristicAndCompressionSafeSchedule(*(succ->state()), currSQI->state(), goals, numericGoals,
                                                   succ->helpfulActions, succ->plan, nowList, stepID, 0, 0.001);
                
            } else {            
                pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
                
                h1 = calculateHeuristicAndSchedule(*(succ->state()), currSQI->state(), goals, numericGoals, pd.get(),
                                                       succ->helpfulActions, currentCost, succ->plan, nowList, stepID, true, 0, 0.001);
            }
            #ifdef STOCHASTICDURATIONS            
            }
            #endif
                                                   
            if (RPGBuilder::getMetric()) {
                if (RPGBuilder::getMetric()->minimise) {
                    if ( h1.admissibleCostEstimate < succ->heuristicValue.admissibleCostEstimate) {
                        h1.admissibleCostEstimate = succ->heuristicValue.admissibleCostEstimate;
                    }
                } else {
                    if ( h1.admissibleCostEstimate > succ->heuristicValue.admissibleCostEstimate) {
                        h1.admissibleCostEstimate = succ->heuristicValue.admissibleCostEstimate;
                    }
                }
            } 

        }

        tms refReturn;
        times(&refReturn);

        if (doLoops) {
            double secs = ((double)refReturn.tms_utime + (double)refReturn.tms_stime - (double)before.tms_utime - (double)before.tms_stime) / ((double) sysconf(_SC_CLK_TCK));

            int threedp = (int)(secs * 1000.0);
            int wholesecs = threedp / 1000;
            int centisecs = threedp % 1000;

            cout << wholesecs << ".";
            if (centisecs < 100) cout << "0";
            if (centisecs < 10) cout << "0";
            cout << centisecs << "\n";
        }

        if (eventOneDefined) {
            extraEvent = nowList.front();
            nowList.pop_front();
        }

        if (eventTwoDefined) {
            extraEventTwo = nowList.front();
            nowList.pop_front();
        }

        assert(nowList.size() == newDummySteps.size());
        
        if (eventOneDefined) {
            succ->plan.push_back(extraEvent);
            if (!doLoops) {
                cout << "Minimum timestamp of new step: " << extraEvent.lpMinTimestamp << "\n";
            }
        }

        if (eventTwoDefined) {
            succ->plan.push_back(extraEventTwo);
            if (!doLoops) {
                cout << "Minimum timestamp of its corresponding end: " << extraEventTwo.lpMinTimestamp << "\n";
            }
        }

        succ->plan.insert(succ->plan.end(), nowList.begin(), nowList.end());

        #ifdef POPF3ANALYSIS
        #ifndef TOTALORDERSTATES
        if (actID.second == Planner::E_AT_START) {
            if (!RPGBuilder::getRPGDEs(actID.first->getID()).empty()
                && TemporalAnalysis::canSkipToEnd(actID.first->getID())) { // if it's a compression-safe temporal action
                        
                const int endStepID = currSQI->state()->getInnerState().planLength + 1;
                                    
                succ->state()->getEditableInnerState().updateWhenEndOfActionIs(actID.first->getID(), endStepID, extraEventTwo.lpMinTimestamp);
                                    
            }
        }
        #endif
        #endif

        if (!doLoops && reusedEndEvent) {
            cout << "Minimum timestamp of reused end: " << reusedEndEvent->lpMinTimestamp << "\n";
        }

        if (actID.second == Planner::E_AT_START && !RPGBuilder::getRPGDEs(actID.first->getID()).empty() && TemporalAnalysis::canSkipToEnd(actID.first->getID())) {
            succ->state()->startEventQueue.pop_back();
        }



        {
            
            #ifndef NDEBUG
            if (h1.heuristicValue < 0.0) {
                cout << COLOUR_light_red << "*** ";
            }
            cout << "After step ";
            if (actID.second == Planner::E_AT_START) {
                cout << *(actID.first) << " start";
            } else if (actID.second == Planner::E_AT_END) {
                cout << *(actID.first) << " end";
            } else {
                cout << "TIL " << actID.divisionID;
            }
            if (h1.heuristicValue < 0.0) {
                cout << ", a dead end has been reached";
                if (h1.diagnosis) {
                    cout << ": " << h1.diagnosis;
                }
                cout << COLOUR_default << "\n";
                if (planMustSucceed) {
                    exit(1);
                }

            } else {
                cout << ", heuristic value is " << h1.heuristicValue;
                if (Globals::optimiseSolutionQuality && NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
                    cout << ", admissible cost estimate is " << h1.admissibleCostEstimate;
                }
                cout << "\n";
            }
            cout << COLOUR_default;
            #endif

            succ->heuristicValue = h1;
            
        }

        #ifdef POPF3ANALYSIS        
        if (Globals::optimiseSolutionQuality && Globals::bestSolutionQuality != -DBL_MAX && NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {            
                cout << COLOUR_light_red << "*** Would prune the state, for cost reasons\n" << COLOUR_default;                
            } else {
                cout << COLOUR_light_green << succ->heuristicValue.admissibleCostEstimate <<  " does not exceed incumbent solution quality of " << -Globals::bestSolutionQuality << COLOUR_default << endl;
            }
        }
        #endif
                                        


        currSQI = succ;
        if (rawDebug) cout << "Now done up to " << currSQI->plan.size() << " steps\n";

    }

    {
        cout << "digraph Plan {\n";
        cout << "\tnode [shape=rectangle, fontsize=14, color=black, fillcolor=white, fontcolor=black];\n";
        cout << "\tedge [style=solid, color=black];\n\n";

        list<FFEvent>::const_iterator printItr = currSQI->plan.begin();
        const list<FFEvent>::const_iterator printEnd = currSQI->plan.end();


        for (int i = 0; printItr != printEnd; ++printItr, ++i) {
            cout << "\tnode" << i << " [label=\"" << printItr->lpTimestamp << ": ";

            if (printItr->time_spec == Planner::E_AT_START) {
                cout << *(printItr->action);
                if (!RPGBuilder::getRPGDEs(printItr->action->getID()).empty()) {
                    cout << " start\"];\n";
                    assert(printItr->pairWithStep != -1);

                    cout << "\tnode" << i << " -> node" << printItr->pairWithStep << " [label=\"maxduration=" << printItr->maxDuration << "\"];\n";
                    cout << "\tnode" << printItr->pairWithStep << " -> node" << i << " [label=\"-minduration=" << -printItr->minDuration << "\"];\n";

                } else {
                    cout << "\"]\n";
                }
            } else if (printItr->time_spec == Planner::E_AT_END) {
                cout << *(printItr->action) << " end\"];\n";
            } else {
                cout << "TIL @ t=";
                cout << (printItr->lpMinTimestamp);
                cout << "\"];\n";
            }
            const int ignore = printItr->pairWithStep;


            const map<int, bool> * const stepsThatComeBeforeThisOne = currSQI->state()->getInnerState().temporalConstraints->stepsBefore(i);

            if (stepsThatComeBeforeThisOne) {
                map<int, bool>::const_iterator cbfItr = stepsThatComeBeforeThisOne->begin();
                const map<int, bool>::const_iterator cbfEnd = stepsThatComeBeforeThisOne->end();

                for (; cbfItr != cbfEnd; ++cbfItr) {
                    if (cbfItr->first == ignore) continue;
                    cout << "\tnode" << i << " -> node" << (cbfItr->first);
                    if (cbfItr->second) {
                        cout << " [label=\"-e\"];\n";
                    } else {
                        cout << " [label=\"0\"];\n";
                    }
                }
            }


        }
        cout << "}\n";
    }

    return new list<FFEvent>(currSQI->plan);
};

void registerFinished(ExtendedMinimalState & theState, set<int> & haveFinished)
{


    /*
    set<int>::iterator hfItr = haveFinished.begin();
    const set<int>::iterator hfEnd = haveFinished.end();

    for (; hfItr != hfEnd; ++hfItr) {

        map<int, pair<set<int>, set<int> > >::iterator fwfItr = theState.factsIfWeFinishActions.begin();
        const map<int, pair<set<int>, set<int> > >::iterator fwfEnd = theState.factsIfWeFinishActions.end();


        while (fwfItr != fwfEnd) {
            bool changed = false;
            {
                set<int>::iterator caItr = fwfItr->second.first.find(*hfItr);
                if (caItr != fwfItr->second.first.end()) {
    //                  cout << "Fact " << fwfItr->first << " now has no strings attached\n";
                    theState.first.insert(fwfItr->first);
                    fwfItr->second.first.erase(caItr);
                    changed = true;
                }
            }
            {
                set<int>::iterator caItr = fwfItr->second.second.find(*hfItr);
                if (caItr != fwfItr->second.second.end()) {
    //                  cout << "Deregistering invariant on fact " << fwfItr->first << "\n";
                    map<int,int>::iterator saItr = theState.invariants.find(fwfItr->first);
                    if (!(--(saItr->second))) {
                        theState.invariants.erase(saItr);
                    }
                    fwfItr->second.second.erase(caItr);
                    changed = true;
                }
            }
            if (changed && fwfItr->second.first.empty() && fwfItr->second.second.empty()) {
                const map<int, pair<set<int>, set<int> > >::iterator fwfDel = fwfItr++;
                theState.factsIfWeFinishActions.erase(fwfDel);
            } else {
                ++fwfItr;
            }

        }
    }
    */

}

void printASList(const list<ActionSegment> & helpfulActions) {
    
    {
        list<ActionSegment>::const_iterator haItr = helpfulActions.begin();
        const list<ActionSegment>::const_iterator haEnd = helpfulActions.end();
        for (int i = 0; haItr != haEnd; ++haItr, ++i) {
            cout << i << ": ";
            if (haItr->second == Planner::E_AT) {
                cout << "Timed initial literal action " << haItr->divisionID << "\n";
            } else {
                cout << *(haItr->first) << ", ";
                if (haItr->second == Planner::E_AT_START) cout << "start\n";
                if (haItr->second == Planner::E_AT_END) cout << "end\n";
                if (haItr->second == Planner::E_OVER_ALL) cout << "middle point " << haItr->divisionID << "\n";
            }
        }
    }
    
}

Solution FF::search(bool & reachedGoal)
{

    static bool initCSBase = false;

    if (!initCSBase) {
        initCSBase = true;
        const vector<NumericAnalysis::dominance_constraint> & dcs = NumericAnalysis::getDominanceConstraints();
        const int pneCount = dcs.size();
        CSBase::ignorableFluents = vector<bool>(pneCount);
        CSBase::nonDominatedFluent = vector<bool>(pneCount);
        for (int i = 0; i < pneCount; ++i) {
            CSBase::ignorableFluents[i] = ((!Globals::optimiseSolutionQuality && dcs[i] == NumericAnalysis::E_METRICTRACKING) || (dcs[i] == NumericAnalysis::E_IRRELEVANT));
            CSBase::nonDominatedFluent[i] = (!(CSBase::ignorableFluents[i]) && dcs[i] == NumericAnalysis::E_NODOMINANCE);
        }
    }

    if (FF::allowCompressionSafeScheduler) {
        FF::allowCompressionSafeScheduler = CompressionSafeScheduler::canUseThisScheduler();
    }

    const bool ffDebug = (Globals::globalVerbosity & 2);

    FFheader_upToDate = false;
    FFonly_one_successor = false;
    WAStar = false;
    set<int> goals;
    set<int> numericGoals;
    ExtendedMinimalState initialState;

    {
        LiteralSet tinitialState;
        vector<double> tinitialFluents;

        RPGBuilder::getNonStaticInitialState(tinitialState, tinitialFluents);

        initialState.getEditableInnerState().setFacts(tinitialState);
        initialState.getEditableInnerState().setFacts(tinitialFluents);
        
        {
            const int pneCount = RPGBuilder::getPNECount();
            
            for (int pne = 0; pne < pneCount; ++pne) {
                if (!RPGBuilder::getWhetherDefinedValueInInitialState()[pne]) {
                    initialState.getEditableInnerState().secondMin[pne] = DBL_MAX;
                    initialState.getEditableInnerState().secondMax[pne] = -DBL_MAX;
                }
            }
        }
//         if (RPGBuilder::getFactHasBeenSeenForWithinSoftDeadline()) {
//             initialState.getEditableInnerState().statusOfTemporalPreferences = PreferenceStatusArray::getInitialArray();
//         }
        
        
        #ifdef STOCHASTICDURATIONS        
        durationManager->prepareTheInitialState(initialState.getEditableInnerState());        
        #endif
                
        if (ffDebug) {
            cout << "Initial state has " << initialState.getInnerState().first.size() << " propositional facts and " << tinitialFluents.size() << " non-static fluents\n";
        }
        
    }
    {
        initialState.getEditableInnerState().preferenceStatus = PreferenceHandler::getInitialAutomataPositions();    
        initialState.getEditableInnerState().prefPreconditionViolations = 0.0;
        //initialState.getEditableInnerState().cost = 0.0;
        
        const int tdrFactCount = NumericAnalysis::getFactsInTimeDependentRewards().size();
        if (tdrFactCount) {
            
            double * toFill = initialState.getEditableInnerState().lowerBoundOnTimeDependentRewardFacts = new double[tdrFactCount];
            
            for (int f = 0; f < tdrFactCount; ++f) {
                toFill[f] = 0.0;
            }            
        }
        
    }

    {
        list<Literal*>::iterator gsItr = RPGBuilder::getLiteralGoals().begin();
        const list<Literal*>::iterator gsEnd = RPGBuilder::getLiteralGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            const pair<bool, bool> & currStatic = RPGBuilder::isStatic(*gsItr);
            if (currStatic.first) {
                if (!currStatic.second) {
                    cout << "Static goal " << *(*gsItr) << " resolves to false: no plan can solve this problem\n";
                    reachedGoal = false;
                    return workingBestSolution;
                }
            } else {
                goals.insert((*gsItr)->getStateID());
            }

        }

    }
    {
        list<pair<int, int> >::iterator gsItr = RPGBuilder::getNumericRPGGoals().begin();
        const list<pair<int, int> >::iterator gsEnd = RPGBuilder::getNumericRPGGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            if (gsItr->first != -1) {
                numericGoals.insert(gsItr->first);
            }
            if (gsItr->second != -1) {
                numericGoals.insert(gsItr->second);
            }
        }
    }

    if (ffDebug) {
        cout << "Solving subproblem\n";
    }

#ifdef DOUBLESTATEHASH
    map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double > >, OldCompareStates> oldVisitedStates;
    map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double > >, OldCompareStatesZealously> oldZealousVisitedStates;    
#endif    

    auto_ptr<StateHash> visitedStates(getStateHash());

    SearchQueue searchQueue;

    HTrio bestHeuristic;
    HTrio initialHeuristic;

    list<FFEvent> stepsForInitialAbstractTILs;
    
    pair<bool,double> bestCurrentCost(false, std::numeric_limits< double >::signaling_NaN());
    
    {
        SearchQueueItem * const initialSQI = new SearchQueueItem(&initialState, false);
        initialSQI->heuristicValue.makespan = 0.0;
        
        if (Globals::optimiseSolutionQuality) {
            initialSQI->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(initialSQI->state()->getInnerState(),initialSQI->heuristicValue.makespan,(RPGBuilder::getMetric() && !RPGBuilder::getMetric()->minimise ? DBL_MAX : -DBL_MAX), false);
            if (admissibleCostExceedsBound(initialSQI->heuristicValue.admissibleCostEstimate,false)) {
                cout << "; No plan can possibly improve on no plan at all, goals not met\n";
                reachedGoal = false;
                return workingBestSolution;
            }
        }

        TemporalAnalysis::pullInAbstractTILs(initialSQI->state()->getEditableInnerState(), stepsForInitialAbstractTILs);
                
        initialSQI->plan = stepsForInitialAbstractTILs;
        
        list<FFEvent> tEvent;
        FFheader_upToDate = false;
        FFonly_one_successor = true;
        if (FF::allowCompressionSafeScheduler) {
            bestHeuristic = calculateHeuristicAndCompressionSafeSchedule(initialState, 0, goals, numericGoals, initialSQI->helpfulActions, initialSQI->plan, tEvent, -1);
        } else {
            bestHeuristic = calculateHeuristicAndSchedule(initialState, 0, goals, numericGoals, (ParentData*) 0, initialSQI->helpfulActions, bestCurrentCost, initialSQI->plan, tEvent, -1);
        }
        
        if (bestHeuristic.heuristicValue == -1.0) {
            cout << "; Goals unreachable from the initial state\n";
            reachedGoal = false;
            return workingBestSolution;
        }
                
                
        if (RPGBuilder::getMetric()) {
            if (Globals::optimiseSolutionQuality) {
                if (RPGBuilder::getMetric()->minimise) {
                    if ( bestHeuristic.admissibleCostEstimate < initialSQI->heuristicValue.admissibleCostEstimate) {
                        bestHeuristic.admissibleCostEstimate = initialSQI->heuristicValue.admissibleCostEstimate;
                    }
                } else {
                    if ( bestHeuristic.admissibleCostEstimate > initialSQI->heuristicValue.admissibleCostEstimate) {
                        bestHeuristic.admissibleCostEstimate = initialSQI->heuristicValue.admissibleCostEstimate;
                    }
                }
            }
        }
        
        
        initialSQI->heuristicValue = bestHeuristic;
        
        if (bestHeuristic.goalsSatisfied) {
            reachedGoal = true;
            bool ignore;
            const pair<bool,bool> prognosis(carryOnSearching(initialSQI->state()->getInnerState(), initialSQI->plan, bestCurrentCost, bestHeuristic.admissibleCostEstimate, ignore));
            if (!prognosis.first ) {
                cout << "; The empty plan is optimal\n";
                return workingBestSolution;
            }
            if (!prognosis.second) {
                cout << "; No plan can possibly improve on no plan at all\n";
                return workingBestSolution;
            }
            
            
        }
        
        
        initialHeuristic = bestHeuristic;
        searchQueue.push_back(initialSQI, 1);
    }

    auto_ptr<StatesToDelete> statesKept(new StatesToDelete(&initialState));

    if (ffDebug || true) cout << "Initial heuristic = " << bestHeuristic.heuristicValue << ", admissible cost estimate " << bestHeuristic.admissibleCostEstimate << "\n";


    auto_ptr<list<FFEvent> > bestPlan(new list<FFEvent>());
    {

        ExtendedMinimalState * const toHash = initialState.clone();

        toHash->timeStamp = 0.0;

        auto_ptr<StateHash::InsertIterator> itr(visitedStates->insertState(toHash));
        itr->setTimestampOfThisState(toHash);

        statesKept->alsoCleanUp(toHash);
        
#ifdef DOUBLESTATEHASH
        {
            list<pair<pair<HTrio, bool>, double> > tList;
            tList.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(bestHeuristic, false), 0.0));
            
            oldVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*toHash, tList));
            oldZealousVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*toHash, tList));            
        }        
#endif

    }

    if (ffDebug) {
        cout << "(" << bestHeuristic.heuristicValue << ") ";
        cout.flush();
    }

    if (skipEHC) searchQueue.pop_front();



    while (!searchQueue.empty()) {
        
        if (Globals::timeLimit != INT_MAX) {

            tms refReturn;
            times(&refReturn);
            double secs = ((double)refReturn.tms_utime + (double)refReturn.tms_stime) / ((double) sysconf(_SC_CLK_TCK));

            if (secs >= Globals::timeLimit) {
                std::cerr << "\n\nTime limit reached: terminating\n";
                exit(2);
            }
        }

        if (Globals::globalVerbosity & 2) cout << "\n--\n";
        auto_ptr<SearchQueueItem> currSQI(searchQueue.pop_front());
        currSQI->printPlan();
        
        if (currSQI->state()->hasBeenDominated) {
            continue;
        }
        
        bool foundBetter = false;



        list<ActionSegment > maybeApplicableActions;
        list<ActionSegment >::iterator helpfulActsItr;
        list<ActionSegment >::iterator helpfulActsEnd;

        if (!foundBetter) {
            if (helpfulActions) {
                //cout << "(( " << currSQI->helpfulActions.size() << "))";
                RPGBuilder::getHeuristic()->filterApplicableActions(currSQI->state()->getInnerState(), currSQI->state()->timeStamp, currSQI->helpfulActions);
                //printASList(currSQI->helpfulActions);
                reorderStartsBeforeEnds(currSQI->helpfulActions);
                //printASList(currSQI->helpfulActions);
                if (nonDeletorsFirst) {
                    reorderNonDeletorsFirst(currSQI->helpfulActions);
                    //printASList(currSQI->helpfulActions);
                }
                helpfulActsItr = currSQI->helpfulActions.begin();
                helpfulActsEnd = currSQI->helpfulActions.end();
                //cout << "(( " << currSQI->helpfulActions.size() << "))";
                //cout.flush();
                FFonly_one_successor = (currSQI->helpfulActions.size() == 1);
            } else {
                RPGBuilder::getHeuristic()->findApplicableActions(currSQI->state()->getInnerState(), currSQI->state()->timeStamp, maybeApplicableActions);
                reorderStartsBeforeEnds(maybeApplicableActions);
                if (nonDeletorsFirst) {
                    reorderNonDeletorsFirst(maybeApplicableActions);
                }
                helpfulActsItr = maybeApplicableActions.begin();
                helpfulActsEnd = maybeApplicableActions.end();
                //cout << "(( " << maybeApplicableActions.size() << "))";
                //cout.flush();
                FFonly_one_successor = (maybeApplicableActions.size() == 1);
            }
        } else {
            helpfulActsItr = helpfulActsEnd = currSQI->helpfulActions.end();
        }

        FFheader_upToDate = false;


        const auto_ptr<ParentData> incrementalData(FF::allowCompressionSafeScheduler ? 0 : LPScheduler::prime(currSQI->plan, currSQI->state()->getInnerState().temporalConstraints,
                currSQI->state()->startEventQueue, Globals::optimiseSolutionQuality));



        for (; helpfulActsItr != helpfulActsEnd; ++helpfulActsItr) {

            auto_ptr<SearchQueueItem> succ;
            bool tsSound = false;
            const int oldTIL = currSQI->state()->getInnerState().nextTIL;

            list<pair<int, FFEvent> > newDummySteps;
            
            if (helpfulActsItr->second == Planner::E_AT) {
                set<int> needToFinish;// = RPGBuilder::TILneedsToHaveFinished(oldTIL, succ->state);
                // TODO: Does this need revisiting?
                // registerFinished(toSolve->rpg, succ->state, needToFinish);
                ActionSegment tempSeg(0, Planner::E_AT, oldTIL, RPGHeuristic::emptyIntList);
                succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(tempSeg, *(currSQI->state()), currSQI->plan, newDummySteps), true));

                if (succ->state()) {
                    tsSound = checkTemporalSoundness(currSQI->state(), *(succ->state()), tempSeg, oldTIL);
                } else {
                    tsSound = false;
                }
                
                if (tsSound) {
                    succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;

                    if (Globals::optimiseSolutionQuality) {
                        succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
                        if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {
                            ++statesDiscardedAsTooExpensiveBeforeHeuristic;
                            tsSound = false;
                        }
                    }


                }
                
            } else {
                //registerFinished(*(succ->state), helpfulActsItr->needToFinish);
                succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(*helpfulActsItr, *(currSQI->state()), currSQI->plan, newDummySteps), true));
                if (succ->state()) {
                    tsSound =    stateHasProgressedBeyondItsParent(*helpfulActsItr, *(currSQI->state()), *(succ->state()))  // it had some beneficial effects
                              && checkTemporalSoundness(currSQI->state(), *(succ->state()), *helpfulActsItr, oldTIL);                         // it didn't introduce a trivial cycle
                } else {
                    tsSound = false;
                }
                
                if (tsSound) {
                    succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;
                
                    if (Globals::optimiseSolutionQuality) {
                        succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
                        if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {
                            ++statesDiscardedAsTooExpensiveBeforeHeuristic;
                            tsSound = false;
                        }
                    }
                }
                
            }


            if (!tsSound) {
                if (Globals::globalVerbosity & 1) cout << "t"; cout.flush();
            } else {


                auto_ptr<SearchQueueItem> TILparentAutoDelete(0);
                SearchQueueItem * TILparent = 0;
                bool TILfailure = false;
                bool incrementalIsDead = false;


                if (helpfulActsItr->second == Planner::E_AT) {

                    bool visitTheState = false;

                    if (zealousEHC) {
                        const auto_ptr<StateHash::FindIterator> lookup(visitedStates->findState(succ->state()));
                        visitTheState = lookup->primaryNewState();
                    } else {
                        const auto_ptr<StateHash::FindIterator> lookup(visitedStates->findState(succ->state()));
                        visitTheState = lookup->primaryNewState();
                        if (!visitTheState) {
                            visitTheState = lookup->secondaryNewState();

                            if (!visitTheState) {
                                const double & previousTS = lookup->previousTimestamp();

                                visitTheState = (fabs(succ->state()->timeStamp - previousTS) > 0.0005
                                                 && succ->state()->timeStamp < previousTS);
                            }
                        }
                    }

                    if (visitTheState) {

                        TILparent = currSQI.get();

                        for (int tn = oldTIL + 1; tn <= helpfulActsItr->divisionID; ++tn) {
                            set<int> needToFinish;// = RPGBuilder::TILneedsToHaveFinished(tn, succ->state);
                            //registerFinished(toSolve->rpg, succ->state, needToFinish);

                            ActionSegment tempSeg(0, Planner::E_AT, tn - 1, RPGHeuristic::emptyIntList);
                            FFcache_upToDate = false;

                            pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
                            
                            evaluateStateAndUpdatePlan(succ, *(succ->state()), TILparent->state(), goals, numericGoals,
                                                       (incrementalIsDead ? (ParentData*) 0 : incrementalData.get()) ,
                                                       succ->helpfulActions, currentCost, tempSeg, TILparent->plan, newDummySteps);

                            if (succ->heuristicValue.heuristicValue == -1.0) {
                                TILfailure = true;
                                break;
                            }
                            if (TILparent != currSQI.get()) {
                                delete TILparent;
                                TILparentAutoDelete.release();
                            }

                            TILparent = succ.release();
                            TILparentAutoDelete = auto_ptr<SearchQueueItem>(TILparent);


                            tempSeg = ActionSegment(0, Planner::E_AT, tn, RPGHeuristic::emptyIntList);

                            newDummySteps.clear();
                            
                            succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(tempSeg, *(TILparent->state()), TILparent->plan, newDummySteps), true));

                            succ->heuristicValue.makespan = TILparent->heuristicValue.makespan;
                            
                            if (!succ->state() || !checkTemporalSoundness(TILparent->state(), *(succ->state()), tempSeg, tn - 1)) {
                                succ->heuristicValue.heuristicValue = -1.0;
                                TILfailure = true;
                                break;
                            }
                            incrementalIsDead = true;
                        }

                    }


                }

#ifdef DOUBLESTATEHASH
                map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> >, OldCompareStatesZealously>::iterator zvsItr;
                map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> >, OldCompareStates>::iterator vsItr;
#endif

                auto_ptr<StateHash::InsertIterator> insResult(0);
                bool visitTheState = false;

                if (!TILfailure) {

                    ExtendedMinimalState * const hunting = succ->state();
                    insResult = auto_ptr<StateHash::InsertIterator>(visitedStates->insertState(succ.get(), statesKept.get()));
                    visitTheState = insResult->primaryNewState();

                    if (!zealousEHC && !visitTheState) {
                        visitTheState = insResult->secondaryNewState();

                        if (!visitTheState) {
                            const double & previousTS = insResult->previousTimestamp();
                            visitTheState = (fabs(hunting->timeStamp - previousTS) > 0.0005
                                             && hunting->timeStamp < previousTS);
                        }

                    }
#ifdef STATEHASHDEBUG
                    if (visitTheState) {
                        succ->mustNotDeleteState = true;
                    }
#endif

#ifdef DOUBLESTATEHASH
                    if (zealousEHC) {
                        zvsItr = oldZealousVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*hunting, list<pair<pair<HTrio, bool>, double> >())).first;
                        if (zvsItr->second.empty()) {
                            if (!visitTheState) {
                                cout << "Old state hash wants to visit:\n";
                                printState(*(succ->state()));
                                cout << "New hash would say it's the same as:\n";
                                printState(*(insResult.outerInsertion.first->first));
                                
                                WeakExtendedStateLessThan t;
                                if (t.operator()(succ->state(), insResult.outerInsertion.first->first)) {
                                    cout << "State is less than that in old hash, according to new comparator\n";
                                }
                                SecondaryExtendedStateLessThan t2;
                                if (t2.operator()(succ->state(), insResult.outerInsertion.first->first)) {
                                    cout << "State is less than that in old hash, according to new secondary comparator\n";
                                }
                            }
                            assert(visitTheState);
                        } else {
                            assert(!visitTheState);
                        }
                    } else {
                        vsItr = oldVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*hunting, list<pair<pair<HTrio, bool>, double> >())).first;
                        if (vsItr->second.empty()) {
                            assert(visitTheState);
                        } else {
                            assert(!visitTheState);
                        }
                    }
#endif
                }

                if (!visitTheState) {
                    if (pruneMemoised) {
                        visitTheState = false;
                        if (Globals::globalVerbosity & 1) cout << "s";
                    }
                }

                if (visitTheState) {

                    pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());                                        
                    
                    if (helpfulActsItr->second == Planner::E_AT) {
                        evaluateStateAndUpdatePlan(succ, *(succ->state()), TILparent->state(), goals, numericGoals, (incrementalIsDead ? (ParentData*) 0 : incrementalData.get()), succ->helpfulActions, currentCost, *helpfulActsItr, TILparent->plan, newDummySteps);
                    } else {
                        evaluateStateAndUpdatePlan(succ,  *(succ->state()), currSQI->state(), goals, numericGoals, incrementalData.get(), succ->helpfulActions, currentCost, *helpfulActsItr, currSQI->plan, newDummySteps);
                    }

                    //succ->printPlan();
                    if (succ->heuristicValue.heuristicValue != -1.0) {

                        bool forceKeep = false;
                        if (succ->heuristicValue.goalsSatisfied) {
                            
                            reachedGoal = true;
                            bool forceRestart = false;
                            const pair<bool,bool> prognosis(carryOnSearching(succ->state()->getInnerState(), succ->plan, currentCost, succ->heuristicValue.admissibleCostEstimate, forceRestart));
                            if (!prognosis.first) {
                                return workingBestSolution;
                            }
                            foundBetter = true;
                            if (prognosis.second && !forceRestart) {
                                forceKeep = true;
                            } else {
                                searchQueue.clear();
                                break;
                            }
                            
                        }

                        insResult->setTimestampOfThisState(succ->state());

#ifdef DOUBLESTATEHASH
                        if (zealousEHC) {
                            zvsItr->second.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(succ->heuristicValue, false),succ->state()->timeStamp));
                        } else {
                            vsItr->second.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(succ->heuristicValue, false),succ->state()->timeStamp));
                        }
#endif  
                        if (forceKeep || ((succ->heuristicValue.heuristicValue < bestHeuristic.heuristicValue)
                                          || (FF::makespanTieBreak && (succ->heuristicValue.heuristicValue == bestHeuristic.heuristicValue)
                                                                   && (succ->heuristicValue.makespan < bestHeuristic.makespan)))
                           ) {

                            bestHeuristic = succ->heuristicValue;
                            cout << "b (" << bestHeuristic.heuristicValue << " | " << bestHeuristic.makespan << ")" ; cout.flush();
                            //succ->printPlan();
                            searchQueue.clear();
                            searchQueue.push_back(succ.release(), 1);
                            if (!FF::steepestDescent) {
                                foundBetter = true;
                                break;
                            }
                        } else {
                            if (Globals::globalVerbosity & 1) cout << "."; cout.flush();
                            searchQueue.push_back(succ.release(), 1);
                        }
                    } else {
                        if (Globals::globalVerbosity & 1) {
                            cout << "d";
                            cout.flush();
                        }
#ifndef NDEBUG
                        if (Globals::globalVerbosity & 2) {
                            cout << succ->heuristicValue.diagnosis << " ";
                            cout.flush();
                        }
#endif
                    }
                } else {
                    if (Globals::globalVerbosity & 1) cout << "p"; cout.flush();
                }
            }
        }

        FFonly_one_successor = false;
    }

    if (!bestFirstSearch) {
        cout << "\nProblem unsolvable by EHC, and best-first search has been disabled\n";

        reachedGoal = false;        
        return workingBestSolution;
    }

    visitedStates->clear();

    
    cout << "\nResorting to best-first search\n";

    WAStar = true;
    
    list<double> weightSeries;
    bool restartWithGoalStates = false;
    
    if (doubleUReduction == -1.0) {
        weightSeries.push_back(doubleU);
    } else {
        for (double W = doubleU; W >= 1.0; W -= doubleUReduction) {
            weightSeries.push_back(W);
        }
        if (weightSeries.back() != 1.0) {
            weightSeries.push_back(1.0);
        }
        restartWithGoalStates = true;
    }
    
    list<double>::const_iterator aStarWeightItr = weightSeries.begin();
    const list<double>::const_iterator aStarWeightEnd = weightSeries.end();
    
    for (; aStarWeightItr != aStarWeightEnd; ++aStarWeightItr) {
        doubleU = *aStarWeightItr;
    
        {
            list<double>::const_iterator tmpItr = aStarWeightItr;
            ++tmpItr;
            if (tmpItr == aStarWeightEnd) {
                restartWithGoalStates = false;
            }
        }
        
        
        if (restartWithGoalStates) {
            cout << "Running WA* with W = " << doubleU << ", restarting with goal states\n";
        } else {
            cout << "Running WA* with W = " << doubleU << ", not restarting with goal states\n";
        }
        
    #ifdef DOUBLESTATEHASH
        oldVisitedStates.clear();
        oldZealousVisitedStates.clear();
    #endif
        
        searchQueue.clear();
        statesKept = auto_ptr<StatesToDelete>(new StatesToDelete(&initialState));

        
        
        {

            if (FF::biasD) {
                initialHeuristic.qbreak = 1;
            } else if (FF::biasG) {
                initialHeuristic.qbreak = initialHeuristic.heuristicValue;
            } else {
                initialHeuristic.qbreak = 0;
            }


            SearchQueueItem * const initialSQI = new SearchQueueItem(&initialState, false);

            //cout << "About to insert SQI " << initialSQI << " into search queue\n";
            
            initialSQI->plan = stepsForInitialAbstractTILs;
            initialSQI->heuristicValue = initialHeuristic;
            bestHeuristic = initialHeuristic;
            searchQueue.insert(initialSQI, 1);
            //visitedStates.find(initialSQI->state)->second.second = true;

            {
                ExtendedMinimalState * const toHash = initialState.clone();
                toHash->timeStamp = 0.0;
                auto_ptr<StateHash::InsertIterator> itr(visitedStates->insertState(toHash));
                itr->setTimestampOfThisState(toHash);
                statesKept->alsoCleanUp(toHash);
                
    #ifdef DOUBLESTATEHASH
                list<pair<pair<HTrio, bool>, double> > tList;
                tList.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(bestHeuristic, true), 0.0));
                
                oldVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*toHash, tList));
                oldZealousVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*toHash, tList));
    #endif
            }
        }

        bool triggerRestart = false;
        
        while (!triggerRestart && !searchQueue.empty()) {

            if (Globals::timeLimit != INT_MAX) {

                tms refReturn;
                times(&refReturn);
                double secs = ((double)refReturn.tms_utime + (double)refReturn.tms_stime) / ((double) sysconf(_SC_CLK_TCK));

                if (secs >= Globals::timeLimit) {
                    std::cerr << "\n\nTime limit reached: terminating\n";
                    exit(2);
                }
            }

            
            auto_ptr<SearchQueueItem> currSQI(searchQueue.pop_front());

            //cout << "SQI at " << currSQI.get() << ", EMS at " << currSQI->state() << endl;
            
            if (currSQI->state()->hasBeenDominated) {
                continue;
            }
            
            if (Globals::globalVerbosity & 2) {
                cout << "\n--\n";
                cout << "Now visiting state with heuristic value of " << currSQI->heuristicValue.heuristicValue << " | " << currSQI->heuristicValue.makespan << "\n";
                printState(*(currSQI->state()));
                currSQI->printPlan();
                cout << "\n + \n";
            }

            #ifdef POPF3ANALYSIS
            if (Globals::optimiseSolutionQuality && admissibleCostExceedsBound(currSQI->heuristicValue.admissibleCostEstimate,false)) {
                if (Globals::globalVerbosity & 2) {
                    cout << "[" << -Globals::bestSolutionQuality << "<" << currSQI->heuristicValue.admissibleCostEstimate << "]";
                    cout.flush();
                } else if (Globals::globalVerbosity & 1) {
                    cout << "<";
                    cout.flush();
                }
                continue;
            }
            #endif

            bool foundBetter = false;

            //currSQI->printPlan();

            list<ActionSegment > applicableActions;

            if (!foundBetter) RPGBuilder::getHeuristic()->findApplicableActions(currSQI->state()->getInnerState(), currSQI->state()->timeStamp, applicableActions);

            reorderStartsBeforeEnds(applicableActions);

            reorderHelpfulFirst(applicableActions, currSQI->helpfulActions);

            if (nonDeletorsFirst) {
                reorderNonDeletorsFirst(applicableActions);
            }
            
            
            if (Globals::globalVerbosity & 2) {
                cout << "Applicable actions are:\n";
                list<ActionSegment >::iterator helpfulActsItr = applicableActions.begin();
                const list<ActionSegment >::iterator helpfulActsEnd = applicableActions.end();
                for (; helpfulActsItr != helpfulActsEnd; ++helpfulActsItr) {
                    if (helpfulActsItr->second == Planner::E_AT) {
                        cout << "\t Timed initial literal " << helpfulActsItr->divisionID << "\n";
                    } else {
                        cout << "\t " << *(helpfulActsItr->first) << ", ";
                        if (helpfulActsItr->second == Planner::E_AT_START) {
                            cout << "start\n";
                        } else if (helpfulActsItr->second == Planner::E_OVER_ALL) {
                            cout << "pt " << helpfulActsItr->divisionID << "\n";
                        } else {
                            cout << "end\n";
                        }
                    }
                }
                cout << "\nHeuristic values are:\n";

            }

            FFheader_upToDate = false;
            FFonly_one_successor = (applicableActions.size() == 1);

            list<ActionSegment >::iterator helpfulActsItr = applicableActions.begin();
            const list<ActionSegment >::iterator helpfulActsEnd = applicableActions.end();

            const auto_ptr<ParentData> incrementalData(FF::allowCompressionSafeScheduler ? 0 : LPScheduler::prime(currSQI->plan, currSQI->state()->getInnerState().temporalConstraints,
                    currSQI->state()->startEventQueue, Globals::optimiseSolutionQuality));

            for (; !triggerRestart && helpfulActsItr != helpfulActsEnd; ++helpfulActsItr) {
                auto_ptr<SearchQueueItem> succ;

                bool tsSound = false;
                const int oldTIL = currSQI->state()->getInnerState().nextTIL;

                list<ActionSegment> nowList;

                list<pair<int, FFEvent> > newDummySteps;
                
                if (helpfulActsItr->second == Planner::E_AT) {

                    ActionSegment tempSeg(0, Planner::E_AT, oldTIL, RPGHeuristic::emptyIntList);
                    succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(tempSeg, *(currSQI->state()), currSQI->plan, newDummySteps), true));

                    if (!succ->state()) {
                        tsSound = false;
                    } else {
                        tsSound = checkTemporalSoundness(currSQI->state(), *(succ->state()), tempSeg, oldTIL);
                    }
                    
                    if (tsSound) {
                        succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;
                        
                        if (Globals::optimiseSolutionQuality) {
                            succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
                            if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {
                                ++statesDiscardedAsTooExpensiveBeforeHeuristic;
                                tsSound = false;
                            }
                        }

                    }
                } else {

                    //registerFinished(*(succ->state), helpfulActsItr->needToFinish);
                    succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(*helpfulActsItr, *(currSQI->state()), currSQI->plan, newDummySteps), true));

                    if (!succ->state()) {
                        tsSound = false;
                    } else {
                        tsSound = (   stateHasProgressedBeyondItsParent(*helpfulActsItr, *(currSQI->state()), *(succ->state()))
                                && checkTemporalSoundness(currSQI->state(), *(succ->state()), *helpfulActsItr)                                  );
                    }
                    
                    if (tsSound) {
                        succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;
                        
                        if (Globals::optimiseSolutionQuality) {
                            succ->heuristicValue.admissibleCostEstimate = calculateAdmissibleCost(succ->state()->getInnerState(),succ->heuristicValue.makespan,currSQI->heuristicValue.admissibleCostEstimate,false);
                            if (admissibleCostExceedsBound(succ->heuristicValue.admissibleCostEstimate, false)) {
                                ++statesDiscardedAsTooExpensiveBeforeHeuristic;
                                tsSound = false;
                            }
                        }

                    }
                }

                /*cout << "Before:\n";
                printState(currSQI->state()->getInnerState());
                cout << "After:\n";
                if (succ->state()) {
                    printState(succ->state()->getInnerState());
                } else {
                    cout << "duration was invalid\n";
                }*/

                if (!tsSound) {
                    if (Globals::globalVerbosity & 2) {
                        cout << "\tTemporally invalid choice\n";
                    } else if (Globals::globalVerbosity & 1) {
                        cout << "t"; cout.flush();
                    }
                } else {
                    assert(succ->state());
                    if (Globals::globalVerbosity & 2) {
                        if (helpfulActsItr->first) {
                            cout << "\tAfter applying " << *(helpfulActsItr->first);
                        } else {
                            cout << "\tAfter applying TIL";
                        }
                        cout << " state is:\n";
                        printState(*(succ->state()));
                    }

                    auto_ptr<SearchQueueItem> TILparentAutoDelete(0);
                    SearchQueueItem * TILparent = 0;
                    bool TILfailure = false;
                    bool incrementalIsDead = false;

                    if (helpfulActsItr->second == Planner::E_AT) {

                        int visitTheState = 0;

                        const auto_ptr<StateHash::FindIterator> lookup(visitedStates->findState(succ->state()));

                        if (lookup->primaryNewState()) {
                            visitTheState = 1;
                        } else {
                            if (lookup->secondaryNewState()) {
                                visitTheState = 2;
                            } else {
                                const double & previousTS = lookup->previousTimestamp();
                                if (fabs(previousTS - succ->state()->timeStamp) > 0.0005 && (previousTS > succ->state()->timeStamp)) {
                                    visitTheState = 2;
                                }
                            }
                        }

                        if (visitTheState) {

                            TILparent = currSQI.get();


                            for (int tn = oldTIL + 1; tn <= helpfulActsItr->divisionID; ++tn) {
                                ActionSegment tempSeg(0, Planner::E_AT, tn - 1, RPGHeuristic::emptyIntList);
                                FFcache_upToDate = false;

                                pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
                                
                                evaluateStateAndUpdatePlan(succ, *(succ->state()), TILparent->state(), goals, numericGoals,
                                                        (incrementalIsDead ? (ParentData*) 0 : incrementalData.get()),
                                                        succ->helpfulActions, currentCost, tempSeg, TILparent->plan, newDummySteps);

                                if (succ->heuristicValue.heuristicValue == -1.0) {
                                    TILfailure = true;
                                    break;
                                }
                                if (TILparent != currSQI.get()) {
                                    delete TILparent;
                                    TILparentAutoDelete.release();
                                }

                                TILparent = succ.release();
                                TILparentAutoDelete = auto_ptr<SearchQueueItem>(TILparent);

                                tempSeg = ActionSegment(0, Planner::E_AT, tn, RPGHeuristic::emptyIntList);
                                
                                newDummySteps.clear();
                                succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(tempSeg, *(TILparent->state()), TILparent->plan, newDummySteps), true));
                                
                                succ->heuristicValue.makespan = TILparent->heuristicValue.makespan;
                                
                                if (!succ->state() || !checkTemporalSoundness(TILparent->state(), *(succ->state()), tempSeg, tn - 1)) {
                                    succ->heuristicValue.heuristicValue = -1.0;
                                    TILfailure = true;
                                    break;
                                }
                                incrementalIsDead = true;
                            }
                            FFcache_upToDate = false;
                        }
                    }

                    int visitTheState = 0;

                    auto_ptr<StateHash::InsertIterator> insResult(0);

    #ifdef DOUBLESTATEHASH
                    map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> >, OldCompareStatesZealously>::iterator zvsItr;
                    map<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> >, OldCompareStates>::iterator vsItr;
    #endif
                    
                    if (!TILfailure) {

                        insResult = auto_ptr<StateHash::InsertIterator>(visitedStates->insertState(succ.get(), statesKept.get()));

                        if (insResult->primaryNewState()) {
                            visitTheState = 1;
                        } else {
                            if (insResult->secondaryNewState()) {
                                visitTheState = 2;
                            } else {
                                const double & previousTS = insResult->previousTimestamp();
                                if (fabs(previousTS - succ->state()->timeStamp) > 0.0005 && (previousTS > succ->state()->timeStamp)) {
                                    visitTheState = 2;
                                }
                            }
                        }

    #ifdef STATEHASHDEBUG
                        if (insResult->outerInsertion.second || insResult->innerInsertion.second) {
                            succ->mustNotDeleteState = true;
                        }
    #endif

    #ifdef DOUBLESTATEHASH

                        int doubleVisitTheState = 0;
                        {
                            zvsItr = oldZealousVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*(succ->state()), list<pair<pair<HTrio, bool>, double> >())).first;
                            vsItr = oldVisitedStates.insert(pair<ExtendedMinimalState, list<pair<pair<HTrio, bool>, double> > >(*(succ->state()), list<pair<pair<HTrio, bool>, double> >())).first;
                            
                            if (vsItr->second.empty() || (fabs(vsItr->second.back().second - succ->state()->timeStamp) > 0.0005 && (vsItr->second.back().second > succ->state()->timeStamp))) {
                                doubleVisitTheState = 2;
                                if (zvsItr->second.empty()) {
                                    doubleVisitTheState = 1;
                                }
                                assert(visitTheState == doubleVisitTheState);
                            } else {
                                assert(visitTheState == 0);
                                                    
                            }
                            
                        }
    #endif

                        if (visitTheState == 0) {
                            if (Globals::globalVerbosity & 2) {
                                cout << "\tState visited before\n";
                            } else if (Globals::globalVerbosity & 1) {
                                cout << "s";
                            }
                        }
                    }

                    if (visitTheState) {

                        pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());                                        
                        
                        if (helpfulActsItr->second == Planner::E_AT) {
                            evaluateStateAndUpdatePlan(succ, *(succ->state()), TILparent->state(), goals, numericGoals,
                                                    (incrementalIsDead ? (ParentData*) 0 : incrementalData.get()),
                                                    succ->helpfulActions, currentCost, *helpfulActsItr, TILparent->plan, newDummySteps);

                        } else {

                            evaluateStateAndUpdatePlan(succ, *(succ->state()), currSQI->state(), goals, numericGoals,
                                                    incrementalData.get(), succ->helpfulActions, currentCost, *helpfulActsItr, currSQI->plan, newDummySteps);
                        }

                        //succ->printPlan();
                        if (succ->heuristicValue.heuristicValue != -1.0) {

                            bool keepState = true;
                            
                            if (succ->heuristicValue.goalsSatisfied) {
                                reachedGoal = true;                            
                                bool forceRestart = false;
                                const pair<bool,bool> prognosis(carryOnSearching(succ->state()->getInnerState(), succ->plan, currentCost, succ->heuristicValue.admissibleCostEstimate, forceRestart));
                                if (!prognosis.first) {
                                    return workingBestSolution;
                                }                                
                                keepState = prognosis.second;
                                if (forceRestart && restartWithGoalStates) {
                                    triggerRestart = true;
                                }
                                //return make_pair(new list<FFEvent>(succ->plan), new TemporalConstraints(*(succ->state()->getInnerState().temporalConstraints)));
                            }
                            insResult->setTimestampOfThisState(succ->state());

    #ifdef DOUBLESTATEHASH
                            vsItr->second.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(succ->heuristicValue, true),succ->state()->timeStamp));
                            zvsItr->second.push_back(pair<pair<HTrio, bool>, double>(pair<HTrio, bool>(succ->heuristicValue, true),succ->state()->timeStamp));
    #endif
                            if (keepState) {
                            
                                if (succ->heuristicValue.heuristicValue < bestHeuristic.heuristicValue || (FF::makespanTieBreak && (succ->heuristicValue.heuristicValue == bestHeuristic.heuristicValue && succ->heuristicValue.makespan < bestHeuristic.makespan))) {

                                    bestHeuristic = succ->heuristicValue;
                                    if (Globals::globalVerbosity & 2) {
                                        cout << "\t" << bestHeuristic.heuristicValue << " | " << bestHeuristic.makespan << ", category " << visitTheState << " - a new best heuristic value, with plan:\n";
                                        //succ->printPlan();
                                    } else {
                                        cout << "b (" << bestHeuristic.heuristicValue << " | " << bestHeuristic.makespan << ")" ; cout.flush();
                                    }

                                    searchQueue.insert(succ.release(), visitTheState);
                                } else {
                                    if (Globals::globalVerbosity & 2) {
                                        cout << "\t" << succ->heuristicValue.heuristicValue << " | " << succ->heuristicValue.makespan << ", category " << visitTheState << "\n";
                                    } else if (Globals::globalVerbosity & 1) {
                                        cout << "."; cout.flush();
                                    }
                                    searchQueue.insert(succ.release(), visitTheState);
                                }
                            }
                            
                        } else {
                            if (Globals::globalVerbosity & 1) {
                                cout << "d"; cout.flush();
                            }
    #ifndef NDEBUG
                            if (Globals::globalVerbosity & 2) {
                                cout << succ->heuristicValue.diagnosis << " ";
                                cout.flush();
                            }
    #endif
                        }
                    } else {
                        if (Globals::globalVerbosity & 1 && !(Globals::globalVerbosity & 2)) {
                            cout << "p"; cout.flush();
                        }
                    }
                }
            }

        }

        visitedStates->clear();
    }
    
    
    
    cout << "\nProblem Unsolvable\n";

    reachedGoal = false;
    return workingBestSolution;

};

list<FFEvent> * FF::reprocessPlan(list<FFEvent> * oldSoln, TemporalConstraints * cons)
{
    static bool initCSBase = false;

    if (!initCSBase) {
        initCSBase = true;
        const vector<NumericAnalysis::dominance_constraint> & dcs = NumericAnalysis::getDominanceConstraints();
        const int pneCount = dcs.size();
        CSBase::ignorableFluents = vector<bool>(pneCount);
        CSBase::nonDominatedFluent = vector<bool>(pneCount);
        for (int i = 0; i < pneCount; ++i) {
            CSBase::ignorableFluents[i] = ((!Globals::optimiseSolutionQuality && dcs[i] == NumericAnalysis::E_METRICTRACKING) || (dcs[i] == NumericAnalysis::E_IRRELEVANT));
            CSBase::nonDominatedFluent[i] = (!(CSBase::ignorableFluents[i]) && dcs[i] == NumericAnalysis::E_NODOMINANCE);
        }
    }

    if (FF::allowCompressionSafeScheduler) {
        FF::allowCompressionSafeScheduler = CompressionSafeScheduler::canUseThisScheduler();
    }
    

    const bool ffDebug = (Globals::globalVerbosity & 2);

    FFheader_upToDate = false;
    FFonly_one_successor = false;
    WAStar = false;
    set<int> goals;
    set<int> numericGoals;
    ExtendedMinimalState initialState;

    {
        LiteralSet tinitialState;
        vector<double> tinitialFluents;

        RPGBuilder::getNonStaticInitialState(tinitialState, tinitialFluents);

        initialState.getEditableInnerState().setFacts(tinitialState);
        initialState.getEditableInnerState().setFacts(tinitialFluents);

        {
            const int pneCount = RPGBuilder::getPNECount();
            
            for (int pne = 0; pne < pneCount; ++pne) {
                if (!RPGBuilder::getWhetherDefinedValueInInitialState()[pne]) {
                    initialState.getEditableInnerState().secondMin[pne] = DBL_MAX;
                    initialState.getEditableInnerState().secondMax[pne] = -DBL_MAX;
                }
            }
        }
//         if (RPGBuilder::getFactHasBeenSeenForWithinSoftDeadline()) {
//             initialState.getEditableInnerState().statusOfTemporalPreferences = PreferenceStatusArray::getInitialArray();
//         }
                        
        
        if (ffDebug) {
            cout << "Initial state has " << initialState.getInnerState().first.size() << " propositional facts\n";
        }
    }

    
    {
        initialState.getEditableInnerState().preferenceStatus = PreferenceHandler::getInitialAutomataPositions();    
        initialState.getEditableInnerState().prefPreconditionViolations = 0.0;
        //initialState.getEditableInnerState().cost = 0.0;

        const int tdrFactCount = NumericAnalysis::getFactsInTimeDependentRewards().size();
        if (tdrFactCount) {
            
            double * toFill = initialState.getEditableInnerState().lowerBoundOnTimeDependentRewardFacts = new double[tdrFactCount];
            
            for (int f = 0; f < tdrFactCount; ++f) {
                toFill[f] = 0.0;
            }            
        }
            
        
        
    }

    {
        list<Literal*>::iterator gsItr = RPGBuilder::getLiteralGoals().begin();
        const list<Literal*>::iterator gsEnd = RPGBuilder::getLiteralGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            const pair<bool, bool> & currStatic = RPGBuilder::isStatic(*gsItr);
            if (currStatic.first) {
                assert(currStatic.second);
            } else {
                goals.insert((*gsItr)->getStateID());
            }

        }

    }
    {
        list<pair<int, int> >::iterator gsItr = RPGBuilder::getNumericRPGGoals().begin();
        const list<pair<int, int> >::iterator gsEnd = RPGBuilder::getNumericRPGGoals().end();

        for (; gsItr != gsEnd; ++gsItr) {
            if (gsItr->first != -1) {
                numericGoals.insert(gsItr->first);
            }
            if (gsItr->second != -1) {
                numericGoals.insert(gsItr->second);
            }
        }
    }

    list<FFEvent*> sortedSoln;

    if (cons == 0) {

        list<FFEvent>::iterator osItr = oldSoln->begin();
        const list<FFEvent>::iterator osEnd = oldSoln->end();
        
        for (; osItr != osEnd; ++osItr) {
            if ((osItr->time_spec == Planner::E_AT_END) && TemporalAnalysis::canSkipToEnd(osItr->action->getID())) {
                continue;
            }
                    
            list<FFEvent*>::iterator sortedItr = sortedSoln.begin();
            const list<FFEvent*>::iterator sortedEnd = sortedSoln.end();
            
            for (; sortedItr != sortedEnd; ++sortedItr) {
                if (osItr->lpTimestamp < (*sortedItr)->lpTimestamp) {
                    sortedSoln.insert(sortedItr, &(*osItr));
                    break;
                }
            }
            if (sortedItr == sortedEnd) {
                sortedSoln.push_back(&(*osItr));
            }
        }
    } else {
        const int evCount = oldSoln->size();
        vector<set<int> > fanOut(evCount);
        vector<int> fanIn(evCount,0);
        vector<FFEvent*> eventForStep(evCount);
        
        list<int> openList;
        
        {
            list<FFEvent>::iterator osItr = oldSoln->begin();
            const list<FFEvent>::iterator osEnd = oldSoln->end();
            
            for (int ev = 0; osItr != osEnd; ++osItr, ++ev) {
                
                eventForStep[ev] = &(*osItr);
                
                const map<int,bool> * stepsBeforeThisOne = cons->stepsBefore(ev);
                
                if (stepsBeforeThisOne) {
                    map<int,bool>::const_iterator itr = stepsBeforeThisOne->begin();
                    const map<int,bool>::const_iterator itrEnd = stepsBeforeThisOne->end();
                    
                    for (; itr != itrEnd; ++itr) {
                        if (fanOut[itr->first].insert(ev).second) {
                            ++fanIn[ev];
                        }
                    }
                }

                if (osItr->time_spec == Planner::E_AT) {
                    list<FFEvent>::iterator ostItr = oldSoln->begin();
                    const list<FFEvent>::iterator ostEnd = oldSoln->end();
                    
                    for (int ost = 0; ostItr != ostEnd; ++ostItr, ++ost) {
                        if (osItr == ostItr) continue;
                        
                        if (ostItr->lpTimestamp < osItr->lpTimestamp - 0.0001) {
                            if (fanOut[ost].insert(ev).second) {
                                ++fanIn[ev];
                            }
                        } else if (osItr->lpTimestamp + 0.0001 < ostItr->lpTimestamp) {
                            if (fanOut[ev].insert(ost).second) {
                                ++fanIn[ost];
                            }
                        }
                    }
                }
            }
        }
        for (int ev = 0; ev < evCount; ++ev) {
            if (!(fanIn[ev])) {
                openList.push_back(ev);
            }
        }
        
        for (; !openList.empty(); openList.pop_front()) {
            
            const int & currStep = openList.front();         
            
            if ((eventForStep[currStep]->time_spec != Planner::E_AT_END) || !TemporalAnalysis::canSkipToEnd(eventForStep[currStep]->action->getID())) {            
                sortedSoln.push_back(eventForStep[currStep]);
            }
            
            set<int>::const_iterator foItr = fanOut[currStep].begin();
            const set<int>::const_iterator foEnd = fanOut[currStep].end();
            
            for (; foItr != foEnd; ++foItr) {
                if (!(--(fanIn[*foItr]))) {
                    openList.push_back(*foItr);
                }
            }
            
        }
    }
    
    if (Globals::globalVerbosity & 2) {
        list<FFEvent*>::const_iterator oldSolnItr = sortedSoln.begin();
        const list<FFEvent*>::const_iterator oldSolnEnd = sortedSoln.end();
        
        for (int stepID = 0; oldSolnItr != oldSolnEnd; ++oldSolnItr, ++stepID) {

            cout << "Sorted plan step " << stepID << ": ";
            if ((*oldSolnItr)->time_spec == Planner::E_AT) {
                cout << "TIL " << (*oldSolnItr)->divisionID << endl;
            } else {
                if ((*oldSolnItr)->time_spec == Planner::E_AT_START) {
                    cout << "start of ";
                } else {
                    cout << "end of ";
                }
                cout << *((*oldSolnItr)->action) << ", was at " << (*oldSolnItr)->lpTimestamp << endl;
            }
        }
            
    }
    
    #ifdef POPF3ANALYSIS
    if (reprocessQualityBound != std::numeric_limits<double>::signaling_NaN() && RPGBuilder::getMetric()) {
        if (reprocessQualityBound == 0.0) {
            Globals::bestSolutionQuality = 0.0;
        } else if (RPGBuilder::getMetric()->minimise) {
            Globals::bestSolutionQuality = -reprocessQualityBound;
        } else {
            Globals::bestSolutionQuality = -reprocessQualityBound;
        }
        
    }
    #endif

    
    auto_ptr<StateHash> visitedStates(getStateHash());

    const list<FFEvent*>::const_iterator oldSolnEnd = sortedSoln.end();
    
    SearchQueueItem * currSQI = new SearchQueueItem(&initialState, false);
    TemporalAnalysis::pullInAbstractTILs(currSQI->state()->getEditableInnerState(), currSQI->plan);
    
    {
        list<FFEvent> tEvent;
        FFheader_upToDate = false;
        FFonly_one_successor = true;
        
        #ifdef ENABLE_DEBUGGING_HOOKS
        {
            Globals::remainingActionsInPlan.clear();
            list<FFEvent*>::const_iterator remainingSolnItr = sortedSoln.begin();
            
            for (; remainingSolnItr != oldSolnEnd; ++remainingSolnItr) {
                if ((*remainingSolnItr)->time_spec == Planner::E_AT) {
                    Globals::remainingActionsInPlan.push_back(ActionSegment((instantiatedOp*)0, Planner::E_AT, (*remainingSolnItr)->divisionID, set<int>()));
                } else {
                    Globals::remainingActionsInPlan.push_back(ActionSegment((*remainingSolnItr)->action,
                                                                            (*remainingSolnItr)->time_spec,
                                                                            (*remainingSolnItr)->divisionID,
                                                                            set<int>()));
                }
            }
        }
        #endif
        if (FF::allowCompressionSafeScheduler) {
            calculateHeuristicAndCompressionSafeSchedule(initialState, 0, goals, numericGoals, currSQI->helpfulActions, currSQI->plan, tEvent, -1);        
        } else {
            pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
            calculateHeuristicAndSchedule(initialState, 0, goals, numericGoals, (ParentData*) 0, currSQI->helpfulActions, currentCost, currSQI->plan, tEvent, -1);        
        }
    }

    
    auto_ptr<StatesToDelete> statesKept(new StatesToDelete(&initialState));

    list<FFEvent*>::const_iterator oldSolnItr = sortedSoln.begin();
    
    const int lastStep = sortedSoln.size() - 1;
    
    for (int stepID = 0; oldSolnItr != oldSolnEnd; ++oldSolnItr, ++stepID) {

        #ifdef ENABLE_DEBUGGING_HOOKS
        Globals::remainingActionsInPlan.pop_front();
        #endif
                    
        ActionSegment nextSeg((*oldSolnItr)->action, (*oldSolnItr)->time_spec, (*oldSolnItr)->divisionID, RPGHeuristic::emptyIntList);
                
        if (Globals::globalVerbosity & 2) {
            cout << "[" << stepID << "] ";
            cout.flush();
        }
        
        if (stepID == lastStep) {
            scheduleToMetric = true;
        }
        
        const auto_ptr<ParentData> incrementalData(FF::allowCompressionSafeScheduler ? 0 : LPScheduler::prime(currSQI->plan, currSQI->state()->getInnerState().temporalConstraints,
                currSQI->state()->startEventQueue, Globals::optimiseSolutionQuality));
                
        list<pair<int, FFEvent> > newDummySteps;
        
        auto_ptr<SearchQueueItem> succ = auto_ptr<SearchQueueItem>(new SearchQueueItem(applyActionToState(nextSeg, *(currSQI->state()), currSQI->plan, newDummySteps), true));
        succ->heuristicValue.makespan = currSQI->heuristicValue.makespan;
        
        pair<bool,double> currentCost(false, std::numeric_limits< double >::signaling_NaN());
        
        evaluateStateAndUpdatePlan(succ,  *(succ->state()), currSQI->state(), goals, numericGoals, incrementalData.get(), succ->helpfulActions, currentCost, nextSeg, currSQI->plan, newDummySteps);

        delete currSQI;
        currSQI = succ.release();

    }
    list<FFEvent> * const toReturn = new list<FFEvent>(currSQI->plan);
    
    delete currSQI;
    return toReturn;
}

void FF::printPlanAsDot(ostream & o, const list<FFEvent> & plan, const TemporalConstraints * cons)
{
 
    if (!(Globals::globalVerbosity & 1024)) {
        return;
    }
    
    o << "digraph Plan {\n";
    o << "\ttimeZero [label=\"t0\"];\n";
    
    
    list<FFEvent>::const_iterator pItr = plan.begin();
    const list<FFEvent>::const_iterator pEnd = plan.end();
    
    for (int i = 0; pItr != pEnd; ++pItr, ++i) {
        
        if (pItr->time_spec == Planner::E_AT && pItr->divisionID < 0) {
            continue;
        }
        
        o << "\tstep" << i << " [label=\"";
        
        if (pItr->time_spec == Planner::E_AT) {
            o << "TIL@" << RPGBuilder::getNonAbstractedTILVec()[pItr->divisionID]->duration;
        } else if (pItr->time_spec == Planner::E_AT_END) {
            o << *(pItr->action) << ", end";
        } else {
            if (RPGBuilder::getRPGDEs(pItr->action->getID()).empty()) {
                o << *(pItr->action);
            } else {
                o << *(pItr->action) << ", start";
            }
        }
        o << "\"";
        if (!pItr->getEffects) {
            o << " color=blue";
        }
        o << "];\n";
        
        if (!cons->stepsBefore(i)) {
            o << "step" << i << " -> timeZero;";
        } else {
            map<int, bool>::const_iterator eItr = cons->stepsBefore(i)->begin();
            const map<int, bool>::const_iterator eEnd = cons->stepsBefore(i)->end();
            
            for (; eItr != eEnd; ++eItr) {
                o << "step" << i << " -> step" << eItr->first;
                if (eItr->second) {
                    o << " [label=\"-e\"];\n";
                } else {
                    o << " [label=\"0\"];\n";
                }
            }
        }
    }
    o << "}\n";
}

};
