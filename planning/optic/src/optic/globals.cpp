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

#include "globals.h"

#include <cfloat>
#include <climits>

#include "RPGBuilder.h"

#ifdef ENABLE_DEBUGGING_HOOKS

#include <FlexLexer.h>


#include <fstream>
using std::ifstream;

#include <ptree.h>
#include <instantiation.h>
using namespace Inst;

namespace VAL
{
    extern yyFlexLexer* yfl;
};

extern int yyparse();
extern int yydebug;

using namespace VAL;

#endif

const char * positionName[8] = {"satisfied", "unsatisfied", "triggered", "unreachable", "eternally satisfied", "satisfied, but goal seen already and still holds", "satisfied, but if goal seen again, becomes unsatisfied"};


namespace Planner
{

int Globals::writeableVerbosity = 0;

const int & Globals::globalVerbosity = writeableVerbosity;

bool Globals::paranoidScheduling = false;
bool Globals::profileScheduling = false;
bool Globals::totalOrder = false;

ostream & operator <<(ostream & o, const ActionSegment & s) {
    if (s.second == Planner::E_AT_START) {
        cout << *(s.first) << ", start";
    } else if (s.second == Planner::E_AT_END) {
        cout << *(s.first) << ", end";
    } else {
        cout << "TIL " << s.divisionID;
    }
    return o;
}

void ActionSegment::printIntTSPair(const pair<int, Planner::time_spec> & act) {
    if (act.second == Planner::E_AT) {
        cout << ActionSegment(0, Planner::E_AT, act.second, set<int>());
    } else {
        cout << ActionSegment(RPGBuilder::getInstantiatedOp(act.first), act.second, -1, set<int>());
    }
}

EpsilonResolutionTimestamp operator-(const EpsilonResolutionTimestamp & a, const EpsilonResolutionTimestamp & b) {
    EpsilonResolutionTimestamp toReturn(a);
    toReturn -= b;
    return toReturn;
}

EpsilonResolutionTimestamp operator-(const EpsilonResolutionTimestamp & a) {
    EpsilonResolutionTimestamp toReturn(0.0,true);
    toReturn -= a;
    return toReturn;
}

EpsilonResolutionTimestamp operator+(const EpsilonResolutionTimestamp & a, const EpsilonResolutionTimestamp & b) {
    EpsilonResolutionTimestamp toReturn(a);
    toReturn += b;
    return toReturn;
}

ostream & operator<<(ostream & o, const EpsilonResolutionTimestamp & t) {
    t.write(o);
    return o;
}


#ifdef ENABLE_DEBUGGING_HOOKS

list<ActionSegment> Globals::remainingActionsInPlan;
vector<bool> Globals::actionHasToBeKept;
vector<double> Globals::actionMustBeAbleToStartAtTime;
vector<double> Globals::actionMustBeAbleToEndAtTime;
const char * Globals::planFilename = 0;

void Globals::markThatActionsInPlanHaveToBeKept()
{    
    actionHasToBeKept.resize(instantiatedOp::howMany(), false);
    actionMustBeAbleToStartAtTime.resize(instantiatedOp::howMany(), -1.0);
    actionMustBeAbleToEndAtTime.resize(instantiatedOp::howMany(), -1.0);
    
    if (!planFilename) return;
    
    ifstream * const current_in_stream = new ifstream(planFilename);
    if (!current_in_stream->good()) {
        cout << "Exiting: could not open plan file " << planFilename << "\n";
        exit(1);
    }

    VAL::yfl = new yyFlexLexer(current_in_stream, &cout);
    yyparse();

    VAL::plan * const the_plan = dynamic_cast<VAL::plan*>(top_thing);

    delete VAL::yfl;
    delete current_in_stream;



    if (!the_plan) {
        cout << "Exiting: failed to load plan " << planFilename << "\n";
        exit(1);
    };

    if (!theTC->typecheckPlan(the_plan)) {
        cout << "Exiting: error when type-checking plan " << planFilename << "\n";
        exit(1);
    }

    pc_list<plan_step*>::const_iterator planItr = the_plan->begin();
    const pc_list<plan_step*>::const_iterator planEnd = the_plan->end();

    for (int idebug = 0, i = 0; planItr != planEnd; ++planItr, ++i, ++idebug) {
        plan_step* const currStep = *planItr;

        instantiatedOp * const currOp = instantiatedOp::findInstOp(currStep->op_sym, currStep->params->begin(), currStep->params->end());
        if (!currOp) {
            cout << "Exiting: step " << idebug << " in the input plan uses an action that the instantiation code did not create.\n";
            cout << "Use VALfiles/testing/checkplanstepsexist to find out why this is the case\n";
            exit(1);
        }
        const int ID = currOp->getID();
        
        actionHasToBeKept[ID] = true;
        
        actionMustBeAbleToStartAtTime[ID] = currStep->start_time;
        actionMustBeAbleToEndAtTime[ID] = currStep->start_time + currStep->duration;        
        
        cout << "Marking that " << *currOp << " (" << ID << ") must not be eliminated by the preprocessor\n";
    }

}

void Globals::eliminatedAction(const int & i, const char * synopsis)
{
    if (!planFilename) return;
    
    if (actionHasToBeKept[i]) {
        cout << "Error in preprocessor.  Pruned operator " << i << ", but should not have done.  Reason given was:\n";
        cout << synopsis << std::endl;
        exit(1);
    } else {
        cout << "Eliminated " << i << ": " << synopsis << std::endl;
    }
}

void Globals::checkActionBounds(const int & actID, const double & startBegin, const double & startEnd)
{
    if (actionMustBeAbleToStartAtTime[actID] == -1.0) {
        return;
    }
    
    if (actionMustBeAbleToStartAtTime[actID] < startBegin || actionMustBeAbleToStartAtTime[actID] > startEnd) {
        cout << "Error in preprocessor.  Action " << actID << " must be able to start at " << actionMustBeAbleToStartAtTime[actID] << ", which is not in the preprocessed range [" << startBegin << "," << startEnd << "]\n";
        exit(1);
    }
}

void Globals::checkActionBounds(const int & actID, const double & startBegin, const double & startEnd, const double & endBegin, const double & endEnd)
{
    if (actionMustBeAbleToStartAtTime[actID] == -1.0) {
        return;
    }
    
    if (actionMustBeAbleToStartAtTime[actID] < startBegin || actionMustBeAbleToStartAtTime[actID] > startEnd) {
        cout << "Error in preprocessor.  Action " << actID << " must be able to start at " << actionMustBeAbleToStartAtTime[actID] << ", which is not in the preprocessed range [" << startBegin << "," << startEnd << "]\n";
        exit(1);
    }
    
    if (actionMustBeAbleToEndAtTime[actID] < endBegin || actionMustBeAbleToEndAtTime[actID] > endEnd) {
        cout << "Error in preprocessor.  Action " << actID << " must be able to end at " << actionMustBeAbleToEndAtTime[actID] << ", which is not in the preprocessed range [" << endBegin << "," << endEnd << "]\n";
        exit(1);
    }
}

void Globals::checkActionDurationBounds(const int& actID, const double& durMin, const double& durMax)
{
    if (actionMustBeAbleToStartAtTime[actID] == -1.0) {
        return;
    }
    
    const double inputDur = actionMustBeAbleToEndAtTime[actID] - actionMustBeAbleToStartAtTime[actID];
    
    if (durMax < inputDur - 0.0005 || durMin > inputDur + 0.0005) {
        cout << "Error in preprocessor.  Action " << actID << " must be able to have the duration " << inputDur << ", but has been limited to [" << durMin << "," << durMax << "]\n";
        exit(1);
    }
}


#endif

#ifdef POPF3ANALYSIS
bool Globals::optimiseSolutionQuality = true;

double Globals::bestSolutionQuality = -DBL_MAX;
double Globals::givenSolutionQuality = std::numeric_limits<double>::signaling_NaN();
double Globals::improvementBetweenSolutions = 0.0;
bool Globals::givenSolutionQualityDefined = false;
#endif

int Globals::timeLimit = INT_MAX;
double Globals::numericTolerance = 0.001;

}
