#include "FFEvent.h"
#include "RPGBuilder.h"

#ifdef STOCHASTICDURATIONS
#include "StochasticDurations.h"
#endif

#include <cassert>
#include <limits>
#include <sstream>
#include <iostream>

#include <sys/times.h>

#include <unistd.h>

using std::ostringstream;
using std::endl;

namespace Planner {

int FFEvent::tilLimit = 0;
    
FFEvent::~FFEvent() {
    #ifdef STOCHASTICDURATIONS
    delete stochasticTimestamp;
    #endif            
}

FFEvent::FFEvent(instantiatedOp* a, const double & dMin, const double & dMax)
        : action(a), time_spec(VAL::E_AT_START), minDuration(dMin), maxDuration(dMax), pairWithStep(-1),
        getEffects(true),
        lpTimestamp(-1.0),lpMinTimestamp(-1.0), lpMaxTimestamp(std::numeric_limits<double>::max()),
        divisionID(-1)
{
    //cout << "FFEvent start\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = 0;
    #endif
            
}

FFEvent::FFEvent(instantiatedOp* a, const int & pw, const double & dMin, const double & dMax)
        : action(a), time_spec(VAL::E_AT_END), minDuration(dMin), maxDuration(dMax), pairWithStep(pw),
                getEffects(true), lpTimestamp(-1.0), /*lpEndTimestamp(-1.0), */lpMinTimestamp(-1.0), lpMaxTimestamp(std::numeric_limits<double>::max()), divisionID(-1)
{
    //cout << "FFEvent end\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = 0;
    #endif
            
}

FFEvent::FFEvent(instantiatedOp* a, const int & s, const int & pw, const double & dMin, const double & dMax)
        : action(a), time_spec(VAL::E_OVER_ALL), minDuration(dMin), maxDuration(dMax), pairWithStep(pw),
                getEffects(true), lpTimestamp(-1.0), /*lpEndTimestamp(-1.0), */lpMinTimestamp(-1.0), lpMaxTimestamp(std::numeric_limits<double>::max()), divisionID(s)
{
    //cout << "FFEvent end\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = 0;
    #endif
    
}

FFEvent::FFEvent(const int & t)
        : action(0), time_spec(VAL::E_AT), minDuration(-1.0), maxDuration(-1.0), pairWithStep(-1), getEffects(true),
          lpTimestamp(-1.0), /*lpEndTimestamp(-1.0), */lpMinTimestamp(-1.0), lpMaxTimestamp(std::numeric_limits<double>::max()), divisionID(t)
{
    assert(divisionID <= tilLimit);
    //cout << "FFEvent start\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = 0;
    #endif
    
}


FFEvent::FFEvent(const FFEvent & f)
        : action(f.action), time_spec(f.time_spec), minDuration(f.minDuration), maxDuration(f.maxDuration),
        pairWithStep(f.pairWithStep), getEffects(f.getEffects) , lpTimestamp(f.lpTimestamp),
        lpMinTimestamp(f.lpMinTimestamp), lpMaxTimestamp(f.lpMaxTimestamp), divisionID(f.divisionID), needToFinish(f.needToFinish)
{
    //cout << "FFEvent copy\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = (f.stochasticTimestamp ? f.stochasticTimestamp->clone() : 0);
    #endif
        
}

FFEvent::FFEvent()
        : action(0), time_spec(VAL::E_AT_START), minDuration(0.0), maxDuration(0.0), lpTimestamp(-1.0),
          lpMinTimestamp(-1.0), lpMaxTimestamp(std::numeric_limits<double>::max()), divisionID(-1)
{
    //cout << "FFEvent default\n";
    #ifdef STOCHASTICDURATIONS
    stochasticTimestamp = 0;
    #endif
    
}

FFEvent & FFEvent::operator=(const FFEvent & f)
{
    //cout << "FFEvent assignment op\n";
    action = f.action;
    time_spec = f.time_spec;
    minDuration = f.minDuration;
    maxDuration = f.maxDuration;
    pairWithStep = f.pairWithStep;
    getEffects = f.getEffects;
    lpTimestamp = f.lpTimestamp;
    lpMinTimestamp = f.lpMinTimestamp;
    lpMaxTimestamp = f.lpMaxTimestamp;
    divisionID = f.divisionID;
    needToFinish = f.needToFinish;
    
    #ifdef STOCHASTICDURATIONS
    delete stochasticTimestamp;
    stochasticTimestamp = (f.stochasticTimestamp ? f.stochasticTimestamp->clone() : 0);
    #endif
    
    return *this;
}


string threeDP(double d)
{
    ostringstream toReturn;
    
    d *= 1000;
    
    int asInt = d;
    
    d -= asInt;
    if (d >= 0.5) {
        asInt += 1;
    }
    
    int fractionalPart = asInt % 1000;
    
    toReturn << asInt / 1000 << ".";
       
    if (fractionalPart < 100) {
        toReturn << "0";
    }
    if (fractionalPart < 10) {
        toReturn << "0";
    }
    
    toReturn << asInt % 1000;
    
    return toReturn.str();
}

void FFEvent::printPlan(const list<FFEvent> & toPrint, int statesEvaluated, double quality, 
    ostream& out)
{
    tms refReturn;
    times(&refReturn);
    
    double secs = ((double)refReturn.tms_utime + (double)refReturn.tms_stime) / ((double) sysconf(_SC_CLK_TCK));

    int twodp = (int)(secs * 100.0);
    int wholesecs = twodp / 100;
    int centisecs = twodp % 100;

    out << "; Time " << wholesecs << ".";
    if (centisecs < 10) out << "0";
    out << centisecs << "\n";
    list<FFEvent>::const_iterator planItr = toPrint.begin();
    const list<FFEvent>::const_iterator planEnd = toPrint.end();
    const int planSize = toPrint.size();
    vector<double> endTS(planSize);
    #ifdef STOCHASTICDURATIONS
    vector<double> endSTS(planSize);
    #endif
    vector<const FFEvent*> planVector(planSize);
    map<double, list<int> > sorted;
    for (int i = 0; planItr != planEnd; ++planItr, ++i) {
        if (planItr->time_spec == VAL::E_AT_START) {
            sorted[planItr->lpTimestamp].push_back(i);
            planVector[i] = &(*planItr);
        } else if (planItr->time_spec == VAL::E_AT_END) {
            endTS[i] = planItr->lpTimestamp;
            #ifdef STOCHASTICDURATIONS
            endSTS[i] = planItr->stochasticTimestamp->getTimestampForRPGHeuristic();
            #endif
        }
    }
    map<double, list<int> >::iterator sortedItr = sorted.begin();
    const map<double, list<int> >::iterator sortedEnd = sorted.end();

    for (; sortedItr != sortedEnd; ++sortedItr) {
        list<int>::iterator iItr = sortedItr->second.begin();
        const list<int>::iterator iEnd = sortedItr->second.end();

        for (; iItr != iEnd; ++iItr) {
            const FFEvent * const planItr = planVector[*iItr];
            if (planItr->lpTimestamp < 0.0000001) {
                out << "0.000";
            } else {
                out << threeDP(planItr->lpTimestamp);
            }
            out << ": " << *(planItr->action) << " ";
            if (planItr->pairWithStep >= 0) {
                const double dur = endTS[planItr->pairWithStep] - planItr->lpTimestamp;
                out << " [" << threeDP(dur) << "]";
                #ifdef STOCHASTICDURATIONS
                out << ";\t\t {" << planItr->stochasticTimestamp->getTimestampForRPGHeuristic() << "} {" << endSTS[planItr->pairWithStep] << "}";
                #endif
            } else if (RPGBuilder::getRPGDEs(planItr->action->getID()).empty()) {
                out << " [" << threeDP(RPGBuilder::getNonTemporalDurationToPrint()[planItr->action->getID()]) << "]";
                #ifdef STOCHASTICDURATIONS
                out << ";\t\t {" << planItr->stochasticTimestamp->getTimestampForRPGHeuristic() << "} {" << EPSILON + planItr->stochasticTimestamp->getTimestampForRPGHeuristic() << "}";
                #endif                        
            } else {
                assert(false);
            }
            out << endl;
        }
    }
}

};

