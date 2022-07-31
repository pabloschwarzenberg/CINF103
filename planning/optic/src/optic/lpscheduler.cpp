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

#include "lpscheduler.h"
#include "globals.h"
#include "numericanalysis.h"
#include "temporalanalysis.h"
#include "temporalconstraints.h"
#include "colours.h"
#include "PreferenceHandler.h"
#include "PreferenceData.h"
#include "RPGBuilder.h"

/*#include "ClpSimplex.hpp"
#include "CoinHelperFunctions.hpp"
#include "CoinTime.hpp"
#include "CoinBuild.hpp"
#include "CoinModel.hpp"*/

#include "solver.h"

#include <limits>

#include <sstream>
#include <string>
#include <list>
#include <iterator>
#include <algorithm>
#include <iomanip>

using std::ostringstream;
using std::string;
using std::list;
using std::for_each;
using std::endl;
using std::cerr;

#define NaN std::numeric_limits<double>::signaling_NaN()

namespace Planner
{

bool ignoreABedges = false;
bool checkSanity = false;

bool LPScheduler::hybridBFLP = true;
bool LPScheduler::optimiseOrdering = true;

vector<double> LPScheduler::TILtimestamps;

vector<vector<list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > > > LPScheduler::gradientEffects;

vector<vector<list<RPGBuilder::RPGNumericEffect* > > > LPScheduler::instantEffects;
map<int, list<vector<list<RPGBuilder::RPGNumericEffect* > > > > LPScheduler::instantIntegralConditionalEffects;

vector<vector<list<const LPScheduler::Constraint*> > > LPScheduler::constraints;
map<int, list<vector<pair<const LPScheduler::Constraint*, const LPScheduler::Constraint*> > > > LPScheduler::instantIntegralConstraints;

vector<vector<LPScheduler::InterestingMap> > LPScheduler::interesting;

map<int, vector<pair<double,double> > > LPScheduler::boundsForAbstractFactOccurrences;

vector<vector<vector<double> > > LPScheduler::pointsThatWouldBeMutexWithOptimisationTILs;

vector<vector<pair<bool,bool> > > LPScheduler::boringAct;

vector<double> LPScheduler::initialValues;
LiteralSet LPScheduler::initialFacts;
vector<double> LPScheduler::initialGradients;

list<const LPScheduler::Constraint*> LPScheduler::goalConstraints;

int LPScheduler::numVars;
bool LPScheduler::initialised = false;


int LPScheduler::lpDebug = 0;
bool LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction = false;


set<LPScheduler::Constraint> LPScheduler::Constraint::constraintStore;
int LPScheduler::Constraint::constraintCount = 0;

static const double N = 100000.000;
static const double SAFE = 0.01;

void printRow(MILPSolver *, const int &, const int &);

void nicerLPPrint(MILPSolver *lp)
{
    const int cc = lp->getNumCols();
    
    for (int ci = 0; ci < cc; ++ci) {
        cout << "C" << ci << ", " << lp->getColName(ci) << ", has range [" << lp->getColLower(ci) << "," << lp->getColUpper(ci) << "]\n";
    }

    
    const int rc = lp->getNumRows();

    printRow(lp, 0, rc);

};

void printRow(MILPSolver * lp, const int & rs, const int & rc)
{


    for (int r = 0; r < rc; ++r) {
        if (r < rs) continue;

        cout << r << ",\"" << lp->getRowName(r) << "\",\"";

        vector<pair<int,double> > entries;
        
        lp->getRow(r, entries);;
        
        vector<pair<int,double> >::iterator thisRow = entries.begin();
        const vector<pair<int,double> >::iterator thisRowEnd = entries.end();

        for (int v = 0; thisRow != thisRowEnd; ++thisRow, ++v) {
            if (v) {
                if (thisRow->second >= 0.0) {
                    cout << " + ";
                    if (thisRow->second != 1.0) cout << thisRow->second << ".";
                } else {
                    if (thisRow->second == -1.0) {
                        cout << " - ";
                    } else {
                        cout << " " << thisRow->second << ".";
                    }
                }
            } else {
                if (thisRow->second == 1.0) {
                    cout << "";
                } else if (thisRow->second == -1.0) {
                    cout << "-";
                } else {
                    cout << thisRow->second << ".";
                }
            }

            cout << lp->getColName(thisRow->first);
        }
        cout << " in [";
        if (lp->getRowLower(r) == -LPinfinity) {
            cout << "-inf,";
        } else {
            cout << lp->getRowLower(r) << ",";
        }
        if (lp->getRowUpper(r) == LPinfinity) {
            cout << "inf]";
        } else {
            cout << lp->getRowUpper(r) << "]";
        }

        cout << "\"\n";
    }

}

void checkForZeroRows(MILPSolver *lp)
{

    cout << "Warning - checkForZeroRows not yet implemented\n";
    /*
    const int cc = lp->getNumCols();
    const int rc = lp->getNumRows();

    int * varBuf = new int[cc];
    double * wBuf = new double[cc];

    for (int r = 1; r <= rc; ++r) {
    const int vCount = get_rowex(lp, r, wBuf, varBuf);
    for (int v = 0; v < vCount; ++v) {
        if (wBuf[v] == 0.0) {
            cout << "Have a zero weight on row " << get_row_name(lp,r) << "\n";
            printRow(lp,r,r);
            break;
        }
    }
    }

    delete [] varBuf;
    delete [] wBuf;
    */
}

struct BFEdge {

    int from;
    int to;
    double min;
    double max;
    bool implicit;

    BFEdge(const int & i, const int & j, const double & a, const double & b, bool imp = false)
            : from(i), to(j), min(a), max(b), implicit(imp) {
        assert(i != j);
        if (Globals::globalVerbosity & 4096) {
            cout << "BFEdge from " << i << " to " << j;
            if (implicit) cout << ", marked as implicit";
            cout << "\n";
        }
    };

};


bool Propagation(LPQueueSet & Q, BFEdge & e, vector<double> & distFromZero, vector<double> & distToZero,
                 vector<int> & pairWith, const vector<FFEvent*> & events,
                 map<int, IncomingAndOutgoing > & temporaryEdges)
{

    static const double HALFEPSILON = EPSILON / 2;

    const bool bfDebug = (Globals::globalVerbosity & 4096);
    if (bfDebug) cout << "Propagating\n";

    Q.visit(e.from, e.to);
    assert(e.from == -1 || events[e.from]);
    assert(e.to == -1 || events[e.to]);

    if (e.implicit) {
        if (bfDebug) cout << "\tImplicit edge - skipping update\n";
    } else {
        if (bfDebug) cout << "\tExplicit edge - storing\n";
        if (e.to == -1) { // adding a minimum timestamp back to zero
            if (bfDebug) cout << "\tEdge from node " << e.from << " to time zero\n";
            if (e.min > events[e.from]->lpMinTimestamp) events[e.from]->lpMinTimestamp = e.min;
            if (e.max < events[e.from]->lpMaxTimestamp) events[e.from]->lpMaxTimestamp = e.max;
        } else if (e.from == -1) { // adding a maximum timestamp from zero
            if (bfDebug) cout << "\tEdge from time zero to node " << e.to << "\n";
            if (e.min > events[e.to]->lpMinTimestamp) {
                events[e.to]->lpMinTimestamp = e.min;
                if (bfDebug) cout << "\tMin timestamp of " << e.to << " updated to " << e.min << endl;
            }
            if (e.max < events[e.to]->lpMaxTimestamp) events[e.to]->lpMaxTimestamp = e.max;
        } else {

            if (bfDebug) cout << "\tEdge from node " << e.from << " to " << e.to << "\n";

            map<int, IncomingAndOutgoing >::iterator teFrom = temporaryEdges.find(e.from);

            if (teFrom == temporaryEdges.end()) {
                teFrom = temporaryEdges.insert(make_pair(e.from, IncomingAndOutgoing())).first;
            }

            map<int, IncomingAndOutgoing >::iterator teTo = temporaryEdges.find(e.to);
            if (teTo == temporaryEdges.end()) {
                teTo = temporaryEdges.insert(make_pair(e.to, IncomingAndOutgoing())).first;
            }

            IncomingAndOutgoing * const fromPair = &(teFrom->second);
            IncomingAndOutgoing * const toPair = &(teTo->second);
            
            if (e.min < HALFEPSILON) {
                if (!toPair->addPredecessor(e.from, false, 0.0)) {
                    return false;
                }
                if (!fromPair->addFollower(e.to, false, 0.0)) {
                    return false;
                }
            } else if (e.min < EPSILON + HALFEPSILON) {
                if (!toPair->addPredecessor(e.from, true, EPSILON)) {
                    return false;
                }
                if (!fromPair->addFollower(e.to, true, EPSILON)) {
                    return false;
                }
            } else {
                toPair->addPredecessor(e.from, false, e.min);
                fromPair->addFollower(e.to, false, e.min);
            }
            
            if (e.max != DBL_MAX) {
                
                if (e.max < HALFEPSILON) {
                    if (!fromPair->addPredecessor(e.to, false, 0.0)) {
                        return false;
                    }
                    if (!toPair->addFollower(e.from, false, 0.0)) {
                        return false;
                    }
                } else if (e.max < EPSILON + HALFEPSILON) {
                    if (!fromPair->addPredecessor(e.to, false, -EPSILON)) {
                        return false;                    
                    }
                    if (!toPair->addFollower(e.from, false, -EPSILON)) {
                        return false;
                    }
                } else {
                    if (!fromPair->addPredecessor(e.to, true, -e.max)) {
                        return false;
                    }
                    if (!toPair->addFollower(e.from, true, -e.max)) {
                        return false;                    
                    }
                }                
            }

            if (Globals::globalVerbosity & 4096) {
                cout << "Have " << fromPair->mustFollowThis().size() << " recorded successors of " << e.from << endl;
                cout << "Have " << toPair->mustPrecedeThis().size() << " recorded predecessors of " << e.to << endl;
            }
        }

        while (!Q.empty()) {

            int u = Q.pop_front();

            if (bfDebug) {
                if (u != -1) {
                    cout << "Next in queue: " << u << "\n";
                } else {
                    cout << "Next in queue: time 0\n";
                }
            }

            if (Q.UB[u]) {

                const double d0u = (u >= 0 ? distFromZero[u] : 0.0);

                if (d0u != DBL_MAX) {

                    if (bfDebug) {
                        if (u >= 0) {
                            if (events[u]->isDummyStep()) {
                                cout << "Edges out of dummy preference step " << u << endl;
                            } else if (events[u]->time_spec == Planner::E_AT) {
                                cout << "Edges out of TIL " << events[u]->divisionID << "\n";
                            } else {
                                cout << "Edges out of " << *(events[u]->action);
                                if (events[u]->time_spec == Planner::E_AT_START) {
                                    cout << ", start\n";
                                } else {
                                    if (TemporalAnalysis::canSkipToEnd(events[u]->action->getID())) {
                                        cout << ", implicit end\n";
                                    } else if (events[u]->getEffects == false) {
                                        cout << ", future end\n";
                                    } else {
                                        cout << ", end\n";
                                    }
                                }

                            }
                        } else {
                            cout << "Edges out of time zero\n";
                        }
                    }

                    if (u >= 0) {

                        // First, consider duration edges out of u

                        // For this u has to be a durative action action, so first, we ask
                        // what it's paired with...

                        const int v = pairWith[u];
                        if (v >= 0) {  // and this has to be a sensible value, i.e. u isn't a TIL or instantaneous action
                            double w;


                            if (u < v) {
                                if (bfDebug) {
                                    cout << "\tTo the end of the action (vertex " << v;
                                    cout.flush();
                                }

                                w = events[u]->maxDuration;
                                if (bfDebug) {
                                    cout << ", weight " << w << ")\n";
                                }

                            } else {
                                if (bfDebug) {
                                    cout << "\tTo the start of the action (vertex " << v; cout.flush();
                                }
                                w = -(events[v]->minDuration);
                                if (bfDebug) cout << ", weight " << w << ")\n";

                            }

                            const double d0uplusWuv = d0u + w;
                            double & d0v = distFromZero[v];

                            if (d0uplusWuv < (d0v - HALFEPSILON)) {
                                d0v = d0uplusWuv;
                                if (bfDebug) cout << "\t\td(zero-to-" << v << ") now = " << d0v << "\n";
                                if (d0v + distToZero[v] < -HALFEPSILON) {
                                    Q.cleanup(e.from, e.to);
                                    return false;
                                } else {
                                    if (Q.NEW[u] == v) {
                                        if (Q.UBP[v]) {
                                            Q.cleanup(e.from, e.to);
                                            return false;
                                        } else {
                                            Q.UBP[v] = true;
                                        }
                                    }
                                }
                                Q.UB[v] = true;
                                Q.push_back(v);
                                assert(v == -1 || events[v]);

                            }
                        }

                        // Having considered duration vars, now we look if there
                        // are any other edges - separation between this and
                        // previous plan steps.

                        const map<int, IncomingAndOutgoing >::iterator teFrom = temporaryEdges.find(u);

                        if (teFrom != temporaryEdges.end()) {
                            const map<int, pair<bool,double> > & backEdges = teFrom->second.mustPrecedeThis();

                            if (bfDebug) {
                                cout << "\t" << backEdges.size() << " edges back to earlier points\n";
                            }
                            map<int, pair<bool,double> >::const_iterator beItr = backEdges.begin();
                            const map<int, pair<bool,double> >::const_iterator beEnd = backEdges.end();

                            for (; beItr != beEnd; ++beItr) {
                                const int v = beItr->first;
                                if (v >= 0) {
                                    const double d0uplusWuv = d0u - beItr->second.first;
                                    double & d0v = distFromZero[v];
                                    if (d0uplusWuv < (d0v - HALFEPSILON)) {
                                        d0v = d0uplusWuv;
                                        if (bfDebug) {
                                            cout << "\t\td(zero-to-" << v << ") now = " << d0v << "\n";
                                        }
                                        if (d0v + distToZero[v] < -HALFEPSILON) {
                                            Q.cleanup(e.from, e.to);
                                            return false;
                                        } else {
                                            if (Q.NEW[u] == v) {
                                                if (Q.UBP[v]) {
                                                    Q.cleanup(e.from, e.to);
                                                    return false;
                                                } else {
                                                    Q.UBP[v] = true;
                                                }
                                            }
                                        }
                                        Q.UB[v] = true;
                                        Q.push_back(v);


                                    }
                                } else {
                                    if (bfDebug) cout << "One back to time zero, but we can't reduce d00\n";
                                }
                            }
                        }
                    } else { // doing edges out of the zero node - max ts on each node

                        const int loopLim = events.size();

                        for (int v = 0; v < loopLim; ++v) {
                            if (!events[v]) continue;
                            const double w = events[v]->lpMaxTimestamp;
                            if (w != DBL_MAX) {
                                double & d0v = distFromZero[v];
                                if (w < (d0v - HALFEPSILON)) {
                                    d0v = w;
                                    if (bfDebug) cout << "\t\td(zero-to-" << v << ") now = " << d0v << "\n";
                                    if (d0v + distToZero[v] < -HALFEPSILON) {
                                        Q.cleanup(e.from, e.to);
                                        return false;
                                    } else {
                                        if (Q.NEW[u] == v) {
                                            if (Q.UBP[v]) {
                                                Q.cleanup(e.from, e.to);
                                                return false;
                                            } else {
                                                Q.UBP[v] = true;
                                            }
                                        }
                                    }
                                    Q.UB[v] = true;
                                    Q.push_back(v);
                                    assert(v == -1 || events[v]);

                                }
                            }
                        }
                    }
                }
            }

            if (Q.LB[u]) {

                const double du0 = (u >= 0 ? distToZero[u] : 0.0);

                if (du0 != DBL_MAX) {
                    if (bfDebug) {
                        if (u >= 0) {

                            if (events[u]->isDummyStep()) {
                                cout << "Edges into dummy preference step " << u << endl;
                            } else if (events[u]->time_spec == Planner::E_AT) {
                                cout << "Edges into of TIL " << events[u]->divisionID << "\n";
                            } else {

                                cout << "Edges into " << *(events[u]->action);
                                if (events[u]->time_spec == Planner::E_AT_START) {
                                    cout << ", start\n";
                                } else {
                                    if (TemporalAnalysis::canSkipToEnd(events[u]->action->getID())) {
                                        cout << ", implicit end\n";
                                    } else if (!(events[u]->getEffects)) {
                                        cout << ", fake end\n";
                                    } else {
                                        cout << ", end\n";
                                    }
                                }
                            }
                        } else {
                            cout << "Edges into time zero\n";
                        }
                    }

                    if (u >= 0) {

                        {   // If it's a durative action, we'll have an edge in from the end of the action

                            const int v = pairWith[u];

                            if (v >= 0) {

                                // ...then it's the other end of this action - if it's less than 0
                                // that means we have a TIL or instantaneous action

                                double w;

                                if (u < v) {
                                    w = -events[u]->minDuration;
                                    if (bfDebug) cout << "\tFrom the corresponding end: " << w << "\n";
                                } else {
                                    w = events[v]->maxDuration;
                                    if (bfDebug) cout << "\tFrom the corresponding start: " << w << "\n";
                                }

                                if (w != DBL_MAX) {
                                    const double du0plusWvu = du0 + w;
                                    double & dv0 = distToZero[v];

                                    if (du0plusWvu < (dv0 - HALFEPSILON)) {
                                        if (bfDebug) cout << "\t\td(" << v << "-to-zero) was " << dv0;
                                        dv0 = du0plusWvu;
                                        if (bfDebug) cout << ", now = " << dv0 << "\n";

                                        if (distFromZero[v] != DBL_MAX && distFromZero[v] + dv0 < -HALFEPSILON) {
                                            if (bfDebug) cout << "\t\t... but distFromZero = " << distFromZero[v] << " - cycle\n";
                                            Q.cleanup(e.from, e.to);
                                            return false;
                                        } else { // figure 2, lines 20a to 20f
                                            if (Q.NEW[v] == u) {
                                                if (bfDebug) cout << "\t\tVertex from " << v << " to " << u << " was the new one, have revised lower bound\n";
                                                if (Q.LBP[u]) {
                                                    if (bfDebug) cout << "\t\tPreviously LBP tagged" << u << " - cycle\n";
                                                    Q.cleanup(e.from, e.to);
                                                    return false;
                                                } else {
                                                    if (bfDebug) cout << "\t\tLBP tagging " << u << "\n";
                                                    Q.LBP[u] = true;
                                                }
                                            }
                                        }

                                        Q.LB[v] = true;
                                        Q.push_back(v);
                                        assert(v == -1 || events[v]);

                                    }
                                } else {
                                    if (bfDebug) cout << "(i.e. edge weight is infinite)\n";
                                }
                            }
                        } // End of durative action case


                        // Then, in all cases, we need to consider the non-duration edges out of the node

                        const map<int, IncomingAndOutgoing >::iterator teFrom = temporaryEdges.find(u);

                        if (teFrom != temporaryEdges.end()) {

                            const map<int, pair<bool,double> > & foreEdges = teFrom->second.mustFollowThis();


                            map<int, pair<bool,double> >::const_iterator feItr = foreEdges.begin();
                            const map<int, pair<bool,double> >::const_iterator feEnd = foreEdges.end();

                            for (; feItr != feEnd; ++feItr) {
                                const int v = feItr->first;
                                if (v >= 0) {
                                    if (bfDebug) {
                                        cout << "\tEdge of weight ";
                                        if (feItr->second.first) {
                                            cout << "epsilon";
                                        } else {
                                            cout << feItr->second.second;
                                        }

                                        if (events[v]->getEffects) {
                                            cout << " from node " << v << "\n";
                                        } else {
                                            cout << " from future end node " << v << "\n";
                                        }
                                    }
                                    const double du0plusWvu = du0 - feItr->second.second;
                                    double & dv0 = distToZero[v];

                                    if (du0plusWvu < (dv0 - HALFEPSILON)) {
                                        dv0 = du0plusWvu;
                                        if (bfDebug) cout << "\t\td(" << v << "-to-zero) now = " << dv0 << "\n";

                                        if (distFromZero[v] != DBL_MAX && distFromZero[v] + dv0 < -HALFEPSILON) {
                                            if (bfDebug) cout << "\t\t... but distFromZero = " << distFromZero[v] << " - cycle\n";
                                            Q.cleanup(e.from, e.to);
                                            return false;
                                        } else { // figure 2, lines 20a to 20f
                                            if (Q.NEW[v] == u) {
                                                if (bfDebug) {
                                                    cout << "\t\tVertex from " << v << " to " << u << " was the new one\n";
                                                }
                                                if (Q.LBP[u]) {
                                                    if (bfDebug) {
                                                        cout << "\t\tLBP[" << u << "] has been seen before, found a negative cycle\n";
                                                    }
                                                    Q.cleanup(e.from, e.to);
                                                    return false;
                                                } else {
                                                    if (bfDebug) {
                                                        cout << "\t\tMarking LBP[" << u << "]\n";
                                                    }
                                                    Q.LBP[u] = true;
                                                }
                                            }
                                        }

                                        Q.LB[v] = true;
                                        Q.push_back(v);
                                        assert(v == -1 || events[v]);

                                    }
                                }
                            }

                        } // end of the edges to subsequent actions

                    } else { // edges into zero: min timestamps for each action
                        const int loopLim = events.size();
                        for (int v = 0; v < loopLim; ++v) {
                            if (!events[v]) continue;
                            double w = events[v]->lpMinTimestamp;
                            if (w != 0.0) w = -w;

                            if (bfDebug) cout << "\tEdge from node " << v << ", w = " << w << "\n";
                            double & dv0 = distToZero[v];

                            if (w < (dv0 - HALFEPSILON)) {
                                dv0 = w;

                                if (bfDebug) cout << "\t\td(" << v << "-to-zero) now = " << dv0 << "\n";


                                if (distFromZero[v] != DBL_MAX && distFromZero[v] + dv0 < -HALFEPSILON) {
                                    if (bfDebug) {
                                        cout << "\t\t... but distFromZero = " << distFromZero[v] << " - cycle\n";
                                    }
                                    Q.cleanup(e.from, e.to);
                                    return false;
                                } else { // figure 2, lines 20a to 20f
                                    if (Q.NEW[v] == u) {
                                        if (bfDebug) {
                                            cout << "\t\tVertex from " << v << " to " << u << " was the new one\n";
                                        }
                                        if (Q.LBP[u]) {
                                            Q.cleanup(e.from, e.to);
                                            return false;
                                        } else {
                                            Q.LBP[u] = true;
                                        }
                                    }
                                }

                                Q.LB[v] = true;
                                Q.push_back(v);
                                assert(v == -1 || events[v]);

                            }
                        }
                    }
                }
            }

            Q.LB[u] = false;
            Q.UB[u] = false;

        }
    }

    Q.reset(e.from, e.to);

    return true;
}


int remapPreferenceEdge(const FFEvent & step, const int & i, const TemporalConstraints * const cons) {
    
    switch (step.time_spec) {
        case Planner::E_DUMMY_PREFERENCE_PRECONDITION: {        
            return step.pairWithStep;        
        }
        case Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE: {
            const map<int,bool> * const prec = cons->stepsBefore(i);
            if (!prec || prec->empty()) {
                return -1;
            }
            if (RPGBuilder::getPreferences()[step.divisionID].cons == VAL::E_ALWAYSWITHIN) {
                assert(prec->size() == 1);
                return prec->begin()->first;
            } else {
                return i;
            }
        }
        default: {
            assert(step.time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
            return i;
        } 
    }
    
};

class ChildData
{

private:
    LPQueueSet * ownQ;
    LPQueueSet * Q;
    vector<double> distFromZero;
    vector<double> distToZero;
    vector<int> pairWith;
    vector<FFEvent*> eventsWithFakes;
    vector<int> softEdges;
    map<int, IncomingAndOutgoing> temporaryEdges;
    map<int, IncomingAndOutgoing> temporarySoftEdges;
    list<BFEdge> newEdges;
    list<FFEvent*> garbage;
    //pair<set<int>, set<int> > constraintsFromLastStep;
    bool needsLP;
    bool copyTimestampsOnDestruction;

    bool allHold(const IncomingAndOutgoing & localConstraints, const double & localDistToZero, const TemporalConstraints * const cons) {
        
        int mappedNodeIdx;
        
        {
            
            const map<int, pair<bool,double> > & incomingEdges = localConstraints.mustFollowThis();
            
            map<int, pair<bool,double> >::const_iterator edgeItr = incomingEdges.begin();
            const map<int, pair<bool,double> >::const_iterator edgeEnd = incomingEdges.end();
            
            for (; edgeItr != edgeEnd; ++edgeItr) {
                
                mappedNodeIdx = softEdges[edgeItr->first];
                if (mappedNodeIdx == -1) {
                    mappedNodeIdx = remapPreferenceEdge(*(eventsWithFakes[edgeItr->first]), edgeItr->first, cons);                    
                    if (mappedNodeIdx == -1) {
                        continue;
                    }
                
                }                
                
                if (localDistToZero - edgeItr->second.second < distToZero[mappedNodeIdx]) {
                    return false;
                }
            }
        }
        
        {
            
            const map<int, pair<bool,double> > & outgoingEdges = localConstraints.mustPrecedeThis();
            
            map<int, pair<bool,double> >::const_iterator edgeItr = outgoingEdges.begin();
            const map<int, pair<bool,double> >::const_iterator edgeEnd = outgoingEdges.end();
            
            for (; edgeItr != edgeEnd; ++edgeItr) {
                
                mappedNodeIdx = softEdges[edgeItr->first];
                if (mappedNodeIdx == -1) {
                    mappedNodeIdx = remapPreferenceEdge(*(eventsWithFakes[edgeItr->first]), edgeItr->first, cons);                    
                    if (mappedNodeIdx == -1) {
                        continue;
                    }
                
                }                
                
                if (distToZero[mappedNodeIdx] - edgeItr->second.second < localDistToZero) {
                    return false;
                }
            }
        }
        
        return true;
        
    }
    
    bool allHold(const IncomingAndOutgoing & localConstraints, const TemporalConstraints * const cons, double & workingDistToZero, double & workingDistFromZero) {
        
        static const bool localDebug = false;
        
        int mappedNodeIdx;
        
        workingDistToZero = 0.0;
        workingDistFromZero = DBL_MAX;
        
        double proposed;
        
        {
            
            const map<int, pair<bool,double> > & outgoingEdges = localConstraints.mustPrecedeThis();
            
            if (localDebug) {
                cout << "Number of outgoing edges: " << outgoingEdges.size() << endl;
            }
            
            
            map<int, pair<bool,double> >::const_iterator edgeItr = outgoingEdges.begin();
            const map<int, pair<bool,double> >::const_iterator edgeEnd = outgoingEdges.end();
            
            for (; edgeItr != edgeEnd; ++edgeItr) {
                
                mappedNodeIdx = softEdges[edgeItr->first];
                if (mappedNodeIdx == -1) {
                    mappedNodeIdx = remapPreferenceEdge(*(eventsWithFakes[edgeItr->first]), edgeItr->first, cons);                    
                    if (mappedNodeIdx == -1) {
                        if (localDebug) {
                            cout << "Skipping outgoing edges into dummy step " << edgeItr->first << "\n";
                        }
                        continue;
                    }
                                    
                }       
                
                if (localDebug) {
                    cout << "Edges to " << mappedNodeIdx << " (originally " << edgeItr->first << ")\n";
                }
                
                if (edgeItr->second.second >= 0.0) {
                    
                    // have a step which must come before the one we're looking at
                    // means the eariest we can have is at least that plus the edge weight (which is negative, but stored positively)
                    
                    proposed = distToZero[mappedNodeIdx] - edgeItr->second.second;        
                    
                    if (proposed < workingDistToZero) {
                        workingDistToZero = proposed;
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " to something with dist-to-zero of " << distToZero[mappedNodeIdx] << ", so dist to zero now " << workingDistToZero << endl;
                        }
                        
                    } else {
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " to something with dist-to-zero of " << distToZero[mappedNodeIdx] << ", dist to zero still " << workingDistToZero << endl;
                        }
                        
                    }
                }
                
                
                if (edgeItr->second.second <= 0.0) {
                    
                    // have a step which must come no later than a certain amount after the one we're looking at
                    // means the eariest we can have is at least that minus the edge weight (which is positive, but stored negatively)
                    
                    proposed = distToZero[mappedNodeIdx] + edgeItr->second.second;
                    
                    if (proposed < workingDistToZero) {
                        workingDistToZero = proposed;
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " to something with dist-to-zero of " << distToZero[mappedNodeIdx] << ", so dist to zero now " << workingDistToZero << endl;
                        }                        
                    } else {
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " to something with dist-to-zero of " << distToZero[mappedNodeIdx] << ", so dist to zero now " << workingDistToZero << endl;
                        }                        
                    }
                    
                }
            }
        }
                
        {
            
            const map<int, pair<bool,double> > & incomingEdges = localConstraints.mustFollowThis();

            if (localDebug) {
                cout << "Number of incoming edges: " << incomingEdges.size() << endl;
            }
            
            
            map<int, pair<bool,double> >::const_iterator edgeItr = incomingEdges.begin();
            const map<int, pair<bool,double> >::const_iterator edgeEnd = incomingEdges.end();
            
            for (; edgeItr != edgeEnd; ++edgeItr) {
                
                if (edgeItr->first == -1) {
                    // incoming soft edge from time zero
                    assert(edgeItr->second.second <= 0.0);
                    
                    if (localDebug) {
                        cout << "Edge from zero to a soft node, weight " << -edgeItr->second.second << endl;
                    }
                    
                    proposed = -edgeItr->second.second;
                    
                    if (proposed < workingDistFromZero) {                        
                        workingDistFromZero = proposed;
                        if (localDebug) {
                            cout << "- Dist from zero now " << workingDistFromZero << endl;
                        }                                                
                    } else {
                        if (localDebug) {
                            cout << "- Dist from zero stays at " << workingDistFromZero << endl;
                        }                                                
                    }
                    
                    continue;
                }
                
                assert(edgeItr->first >= 0 && edgeItr->first < softEdges.size());
                
                mappedNodeIdx = softEdges[edgeItr->first];
                if (mappedNodeIdx == -1) {
                    mappedNodeIdx = remapPreferenceEdge(*(eventsWithFakes[edgeItr->first]), edgeItr->first, cons);                    
                    if (mappedNodeIdx == -1) {
                        if (localDebug) {
                            cout << "Skipping incoming edges from dummy step " << edgeItr->first << endl;
                        }                                                
                        continue;
                    }
                
                }                
            
                if (localDebug) {
                    if (distFromZero[mappedNodeIdx] == DBL_MAX) {
                        cout << "Step " << mappedNodeIdx << " (originally " << edgeItr->first << ") has no upper bound on how late it can come - ignoring it\n";
                    }
                }
                
                if (edgeItr->second.second >= 0.0 && distFromZero[mappedNodeIdx] != DBL_MAX) {
                    
                    // have a step which must come after this one, with some minimum separation
                    // the latest we can come is then that minus the edge weight (which is negative, but stored positively)                    
                    
                    proposed = distFromZero[mappedNodeIdx] - edgeItr->second.second;
                    
                    if (proposed < workingDistFromZero) {
                        workingDistFromZero = proposed;
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " from something with dist-from-zero of " << distFromZero[mappedNodeIdx] << ", so dist from zero now " << workingDistFromZero << endl;
                        }
                    } else {
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " from something with dist-from-zero of " << distFromZero[mappedNodeIdx] << ", so dist from zero stays at " << workingDistFromZero << endl;
                        }
                    }
                    
                }
                
                if (edgeItr->second.second <= 0.0 && distFromZero[mappedNodeIdx] != DBL_MAX) {
                    
                    // have a step which must come before this one, with this one being a maximum distance after it
                    // the latest we can come is then that step's max, plus the edge weight (which is positive, but stored negatively)
                    
                    proposed = distFromZero[mappedNodeIdx] - edgeItr->second.second;
                    
                    if (proposed < workingDistFromZero) {
                        workingDistFromZero = proposed;
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " from something with dist-from-zero of " << distFromZero[mappedNodeIdx] << ", so dist from zero now " << workingDistFromZero << endl;
                        }
                    } else {
                        if (localDebug) {
                            cout << "- Weight " << -edgeItr->second.second << " from something with dist-from-zero of " << distFromZero[mappedNodeIdx] << ", so dist from zero stays at " << workingDistFromZero << endl;
                        }
                                                
                    }
                    
                }
                
            }
        }
        
        if (localDebug) {
            cout << "About to return, comparing working dist from zero of " << workingDistFromZero << " to working dist to zero of " << workingDistToZero << endl;
        }
        
        if (workingDistToZero == 0.0) {
            // can come as soon as time zero            
            return (workingDistFromZero >= 0.0);            
        }
                
        return (-workingDistToZero <= workingDistFromZero); // the earliest point at which the dummy can appear is at or before the latest by which it must have appeared
        
    }
    
public:

    map<int, double> autoMinima;

    ChildData(LPQueueSet * QIn,
              const vector<double> & dfz, const vector<double> & dtz, const vector<int> & pw,
              const vector<FFEvent*> & ewf, const vector<int> & se,
              const map<int, IncomingAndOutgoing > & tes, const map<int, IncomingAndOutgoing > & tses,
              const bool & nlp)
            : ownQ(0), Q(QIn),
            distFromZero(dfz), distToZero(dtz), pairWith(pw), eventsWithFakes(ewf), softEdges(se),
            temporaryEdges(tes), temporarySoftEdges(tses),
            needsLP(nlp), copyTimestampsOnDestruction(true) {
    };

    void addMoreGaps(list<int> & indicesGoInHere, const int & numberToAdd) {
        
        assert(numberToAdd >= 0);
        assert(!indicesGoInHere.empty());
        
        const int gapsStartAt = indicesGoInHere.back() + 1;

        delete ownQ;
        ownQ = new LPQueueSet(eventsWithFakes.size() + numberToAdd);
        Q = ownQ;            
        
        distFromZero.resize(distFromZero.size() + numberToAdd, DBL_MAX);
        distToZero.resize(distToZero.size() + numberToAdd, 0.0);
        pairWith.resize(pairWith.size() + numberToAdd, -1);
        eventsWithFakes.resize(eventsWithFakes.size() + numberToAdd, (FFEvent*) 0);
        softEdges.resize(softEdges.size() + numberToAdd, -1);
        
        for (int i = 0; i < numberToAdd; ++i) {
            indicesGoInHere.push_back(i + gapsStartAt);
        }
        
                        
    }
    
    void letTheLPSetTimestamps() {
        copyTimestampsOnDestruction = false;
    }
    
    inline const bool & willSetTimestamps() const {
        return copyTimestampsOnDestruction;
    }
    
    inline void updateLPNeed(const bool & b) {
        if (b) needsLP = true;
    };

    ~ChildData() {
        delete ownQ;
        if (copyTimestampsOnDestruction) {
            static const bool cdDebug = (Globals::globalVerbosity & 4096);
            const int ewfCount = eventsWithFakes.size();

            if (cdDebug) cout << "Copying " << ewfCount << " timestamps back\n";

            for (int e = 0; e < ewfCount; ++e) {
                if (eventsWithFakes[e]) {
                    eventsWithFakes[e]->lpMaxTimestamp = distFromZero[e];
                    if (distToZero[e] == 0.0) {
                        eventsWithFakes[e]->lpMinTimestamp = 0.0;
                    } else {
                        eventsWithFakes[e]->lpMinTimestamp = -distToZero[e];
                    }
                    eventsWithFakes[e]->lpTimestamp = eventsWithFakes[e]->lpMinTimestamp;
                    if (cdDebug) cout << "\t" << e << ": " << eventsWithFakes[e]->lpTimestamp << "\n";
                }
            }
        }
        list<FFEvent*>::iterator gItr = garbage.begin();
        const list<FFEvent*>::iterator gEnd = garbage.end();

        for (; gItr != gEnd; ++gItr) delete *gItr;
    }

    inline void gc(FFEvent * const g) {
        garbage.push_back(g);
    };
    inline void pairEventWith(const int & i, const int & j) {
        if (Globals::globalVerbosity & 4096) {
            cout << "Recording that " << i <<  " is paired with " << j << endl;
        }
        pairWith[i] = j; pairWith[j] = i;
    }

    inline void setTil(const int & i) {
        pairWith[i] = -2;
    };
    inline void setNonTemporal(const int & i) {
        pairWith[i] = -3;
    };
    inline void nonSoftEdges(const int & i, const int & mapTo) {
        softEdges[i] = mapTo;
    }
    
    inline const int & edgesAreNonSoft(const int & i) const {
        return softEdges[i];
    }
    
    vector<FFEvent*> & getEventsWithFakes() {
        return eventsWithFakes;
    };

    const vector<double> & getDistFromZero() const {
        return distFromZero;
    };
    const vector<double> & getDistToZero() const {
        return distToZero;
    };

    inline void setDFZ(const int & i, const double & d) {
        distFromZero[i] = d;
    }
    inline void setDTZ(const int & i, const double & d) {
        distToZero[i] = d;
    }

    inline void addNewEdge(const BFEdge & e) {
        newEdges.push_back(e);
    }
    
    inline IncomingAndOutgoing & makeEdgeListFor(const int & i) {
        return temporaryEdges[i];
    }
    
    inline IncomingAndOutgoing & makeSoftEdgeListFor(const int & i) {
        return temporarySoftEdges[i];
    }
    
    inline map<int, IncomingAndOutgoing >::iterator getEdgeListItr(const int & i) {
        return temporaryEdges.find(i);
    }
    inline map<int, IncomingAndOutgoing >::iterator getEdgeListEnd() {
        return temporaryEdges.end();
    }

    const vector<int> & getPairWith() const {
        return pairWith;
    };

    bool propagateNewEdges(const vector<AutomatonPosition::Position> & previousPreferenceStatus, const TemporalConstraints * const cons, bool & preferencesWereAsExpected);
    bool updateLPMinTimestamp(const double & d, const int & stepID);
    void sanityCheck() {
        const int loopLim = distToZero.size();
        for (int i = 0; i < loopLim; ++i) {
            if (eventsWithFakes[i] && distToZero[i] > 0) {
                cout << "Event " << i << " set to come " << -(distToZero[i]) << " before time zero\n";
                assert(distToZero[i] <= 0.0);
            }
            if (eventsWithFakes[i] && eventsWithFakes[i]->time_spec == Planner::E_AT && pairWith[i] != -2) {
                cout << "Event " << i << " is a TIL, but is not paired with -2\n";
                assert(pairWith[i] == -2);
            }
        }
    }
    bool checkItContainsAllTheseEdges(const TemporalConstraints * const cons) const;

    inline void moveZeroDists(const int & from, const int & to) {
        distToZero[to] = distToZero[from];
        distFromZero[to] = distFromZero[from];
        distToZero[from] = 0.0;
        distFromZero[from] = DBL_MAX;
    }
    void clearPairFor(const int & i) {
        pairWith[i] = -1;
        assert(!eventsWithFakes[i]);
    }
    inline const bool & doLPSolve() const {
        return needsLP;
    };

    void distsToLPStamps(const int debug = -1) {
        const int ll = eventsWithFakes.size();

        for (int i = 0; i < ll; ++i) {
            FFEvent * const f = eventsWithFakes[i];
            if (f) {
                double w = distToZero[i];
                if (w != 0.0) w = -w;
                if (debug == i && (!f->action || !TemporalAnalysis::canSkipToEnd(f->action->getID()))) {
                    if (fabs(w - f->lpTimestamp) > 0.0005) {
                        cout << "LP would put event " << i << " at " << f->lpTimestamp << ", but STN puts it at " << w << "\n";
                        assert(fabs(w - f->lpTimestamp) <= 0.0005);
                    }
                }

                f->passInMinMax(w, distFromZero[i]);
            }
        }
    }

    void distsToLPMinStamps() {
        const int ll = eventsWithFakes.size();

        for (int i = 0; i < ll; ++i) {
            FFEvent * const f = eventsWithFakes[i];
            if (f) {
                double w = distToZero[i];
                if (w != 0.0) w = -w;
                f->passInMinMax(w, distFromZero[i]);
            }
        }
    }

    void distsToLPMinStampsAndCheck(vector<FFEvent*> & withLPTimestamps) {
        const int ll = eventsWithFakes.size();

        for (int i = 0; i < ll; ++i) {
            FFEvent * const f = eventsWithFakes[i];
            if (f) {
                double w = distToZero[i];
                if (w != 0.0) w = -w;
                
                #ifndef NDEBUG
                if (w - withLPTimestamps[i]->lpTimestamp > 0.0000001) {
                    std::cerr << std::setprecision(6) << std::fixed << std::endl << "Error: step " << i << " has been given a timestamp of " << withLPTimestamps[i]->lpTimestamp << " by the LP, but the STP reported this had to be at least " << w << endl;
                    exit(1);
                }

                if (withLPTimestamps[i]->lpTimestamp - distFromZero[i] > 0.0000001) {
                    std::cerr << std::setprecision(6) << std::fixed << std::endl << "Error: step " << i << " has been given a timestamp of " << withLPTimestamps[i]->lpTimestamp << " by the LP, but the STP reported this could be no more than " << distFromZero[i] << endl;
                    exit(1);
                }
                #endif
                //f->passInMinMax(w, distFromZero[i]);
            }
        }
    }



    void printDotFile(ostream & o);
};



bool ChildData::checkItContainsAllTheseEdges(const TemporalConstraints * const cons) const
{
    bool toReturn = true;
    const int lim = cons->size();
    for (int i = 0; i < lim; ++i) {
        const map<int, bool> * const anyBefore = cons->stepsBefore(i);
        if (!anyBefore) continue;

        map<int, IncomingAndOutgoing >::const_iterator mItr = temporaryEdges.find(i);

        map<int, bool>::const_iterator sItr = anyBefore->begin();
        const map<int, bool>::const_iterator sEnd = anyBefore->end();

        if (mItr != temporaryEdges.end()) {
            //cout << "Have " << mItr->second.mustPrecedeThis().size() << " recorded predecessors of " << i << endl;
            map<int, pair<bool,double> >::const_iterator exItr = mItr->second.mustPrecedeThis().begin();
            const map<int, pair<bool,double> >::const_iterator exEnd = mItr->second.mustPrecedeThis().end();

            while (exItr != exEnd && sItr != sEnd) {
                if (exItr->first < sItr->first) {
                    //cout << "- Predecessor of " << exItr->first << " isn't in T\n";
                    ++exItr;
                } else if (sItr->first < exItr->first) {
                    if (sItr->first != pairWith[i]) {
                        cout << "Missing predecessor edge into " << sItr->first << " from " << i << endl;
                        toReturn = false;
                    } else {
                        //cout << "- Predecessor of " << sItr->first << " isn't in the data, but that might be okay\n";
                    }
                    ++sItr;
                } else {
                    //cout << "- Both record predecessor of " << sItr->first << endl;
                    ++exItr;
                    ++sItr;
                }
            }

        } else {
            //cout << "Have no recorded predecessors of " << i << endl;
        }

        for (; sItr != sEnd; ++sItr) {
            if (sItr->first != pairWith[i]) {
                cout << "Missing predecessor edge into " << sItr->first << " from " << i << endl;
                toReturn = false;
            }
        }
    }
    return toReturn;
}

void ChildData::printDotFile(ostream & o)
{

    o << "digraph STN {\n\n";
    o << "T0 [label=\"t0\"]\n";
    const int ll = eventsWithFakes.size();

    vector<vector<double> > edgeMatrix(ll + 1, vector<double>(ll + 1, DBL_MAX));
    vector<vector<string> > edgeLabels(ll + 1, vector<string>(ll + 1));

    edgeMatrix[0][0] = 0.0;

    for (int i = 0; i < ll; ++i) {
        if (eventsWithFakes[i]) {
            edgeMatrix[i+1][i+1] = 0.0;
        }
    }

    for (int i = 0; i < ll; ++i) {
        FFEvent * const f = eventsWithFakes[i];
        if (f) {
            double w = distToZero[i];
            if (w != 0.0) w = -w;
            o << "N" << i << " [label=\"" << w << ": ";
            if (f->isDummyStep()) {
                o << " dummy\"];\n";
            } else if (f->action) {
                o << *(f->action) << " ";
                if (f->time_spec == Planner::E_AT_START) {
                    o << " S\"];\n";
                } else {
                    if (TemporalAnalysis::canSkipToEnd(f->action->getID())) {
                        o << " E (implicit)\"];\n";
                    } else {
                        if (eventsWithFakes[i]->getEffects) {
                            o << " E\"];\n";
                        } else {
                            o << " E (future)\"];\n";
                        }
                    }
                }
            } else {
                o << "TIL " << f->divisionID << "\"];\n";
            }
        }
    }

    vector<pair<double, double> > endMinMax(ll, make_pair(0.0, DBL_MAX));

    for (int i = 0; i < ll; ++i) {
        FFEvent * const f = eventsWithFakes[i];
        if (f) {
            {
                if (f->action && f->time_spec == Planner::E_AT_START) {
                    const bool nonTemporal = RPGBuilder::getRPGDEs(f->action->getID()).empty();

                    const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[f->action->getID()];

                    double startMin = tsBounds[0].first;
                    double endMin = tsBounds[1].first;

                    double startMax = tsBounds[0].second;
                    double endMax = tsBounds[1].second;


                    if (!nonTemporal) {

                        {
                            const double sEndMin = startMin + f->minDuration;
                            if (sEndMin > endMin) endMin = sEndMin;
                        }
                        {
                            const double sStartMin = endMin - f->maxDuration;
                            if (sStartMin > startMin) startMin = sStartMin;

                        }

                        if (startMax != DBL_MAX && f->maxDuration != DBL_MAX) {
                            const double sEndMax = startMax + f->maxDuration;
                            if (sEndMax < endMax) endMax = sEndMax;
                        }

                        if (endMax != DBL_MAX) {
                            const double sStartMax = endMax - f->minDuration;
                            if (sStartMax < startMax) startMax = sStartMax;
                        }
                    }

                    if (startMin != 0.0) {
                        edgeMatrix[i+1][0] = -startMin;
                        if (startMin == 0.001) {
                            edgeLabels[i+1][0] = "-e, gmin";
                        } else {
                            ostringstream namestream;
                            namestream << -startMin << ", gmin";
                            edgeLabels[i+1][0] = namestream.str();
                        }
                    }
                    if (startMax < DBL_MAX) {
                        edgeMatrix[0][i+1] = startMax;
                        ostringstream namestream;
                        namestream << startMax << ", gmax";
                        edgeLabels[0][i+1] = namestream.str();
                    }

                    if (!nonTemporal) {
                        endMinMax[i] = make_pair(endMin, endMax);
                    }

                } else if (f->action && f->time_spec == Planner::E_AT_END) {
                    const double & startMin = endMinMax[pairWith[i]].first;
                    const double & startMax = endMinMax[pairWith[i]].second;

                    if (startMin != 0.0) {
                        edgeMatrix[i+1][0] = -startMin;
                        if (startMin == 0.001) {
                            edgeLabels[i+1][0] = "-e, gmin";
                        } else {
                            ostringstream namestream;
                            namestream << -startMin << ", gmin";
                            edgeLabels[i+1][0] = namestream.str();
                        }
                    }
                    if (startMax < DBL_MAX) {
                        edgeMatrix[0][i+1] = startMax;
                        ostringstream namestream;
                        namestream << startMax << ", gmax";
                        edgeLabels[0][i+1] = namestream.str();
                    }
                } else if (f->time_spec == Planner::E_AT) {
                    const double tilTime = LPScheduler::getTILTimestamp(f->divisionID);
                    {
                        edgeMatrix[i+1][0] = -tilTime;
                        ostringstream namestream;
                        namestream << -tilTime << ", til";
                        edgeLabels[i+1][0] = namestream.str();
                    }
                    {
                        edgeMatrix[0][i+1] = tilTime;
                        ostringstream namestream;
                        namestream << tilTime << ", til";
                        edgeLabels[0][i+1] = namestream.str();
                    }
                } else {
                    assert(false);
                }

            }
            /*{
                if (!i) {
                    edgeMatrix[i+1][i] = 0;
                    edgeLabels[i+1][i] = "0, seq";
                } else if (pairWith[i] != (i - 1)) {
                    edgeMatrix[i+1][i] = -EPSILON;
                    edgeLabels[i+1][i] = "-e, seq";
                } else {
                    cout << "No sequence edge for N" << i << ", as is paired with N" << pairWith[i] << "\n";
                }

                set<int>::iterator ntfItr = f->needToFinish.begin();
                const set<int>::iterator ntfEnd = f->needToFinish.end();

                for (; ntfItr != ntfEnd; ++ntfItr) {
                    edgeMatrix[i+1][pairWith[*ntfItr] + 1] = -EPSILON;
                    edgeLabels[i+1][pairWith[*ntfItr] + 1] = "-e, ntf";
                }
                if (pairWith[i] > i) {
                    if (f->maxDuration != DBL_MAX) {
                        edgeMatrix[i+1][pairWith[i] + 1] = f->maxDuration;
                        ostringstream namestream;
                        namestream << f->maxDuration;
                        edgeLabels[i+1][pairWith[i] + 1] = namestream.str();
                    }
                    double w = f->minDuration;
                    if (w != 0.0) w = -w;
                    if (w == -EPSILON) {
                        edgeMatrix[pairWith[i]+1][i + 1] = -EPSILON;
                        edgeLabels[pairWith[i]+1][i + 1] = "-e, mindur";
                    } else {
                        edgeMatrix[pairWith[i]+1][i + 1] = w;
                        ostringstream namestream;
                        namestream << w;
                        edgeLabels[pairWith[i]+1][i + 1] = namestream.str();
                    }
                }

            }*/

            {
                if (pairWith[i] > i) {
                    if (f->maxDuration != DBL_MAX) {
                        edgeMatrix[i+1][pairWith[i] + 1] = f->maxDuration;
                        ostringstream namestream;
                        namestream << f->maxDuration;
                        edgeLabels[i+1][pairWith[i] + 1] = namestream.str();
                    }
                    double w = f->minDuration;
                    if (w != 0.0) w = -w;
                    if (w == -EPSILON) {
                        edgeMatrix[pairWith[i] + 1][i + 1] = -EPSILON;
                        edgeLabels[pairWith[i] + 1][i + 1] = "-e, mindur";
                    } else {
                        edgeMatrix[pairWith[i] + 1][i + 1] = w;
                        ostringstream namestream;
                        namestream << w;
                        edgeLabels[pairWith[i] + 1][i + 1] = namestream.str();
                    }
                }

            }

            {

                {
                    map<int, IncomingAndOutgoing >::iterator teItr = temporaryEdges.find(i);
                    if (teItr != temporaryEdges.end()) {
                        map<int, pair<bool,double> >::const_iterator ntfItr = teItr->second.mustPrecedeThis().begin();
                        const map<int, pair<bool,double> >::const_iterator ntfEnd = teItr->second.mustPrecedeThis().end();

                        for (; ntfItr != ntfEnd; ++ntfItr) {
                            //if (ntfItr->first == eventCount - 1) continue;
                            if (ntfItr->second.second != 0.0) {
                                edgeMatrix[i+1][ntfItr->first + 1] = -ntfItr->second.second;
                                ostringstream s;
                                s << -ntfItr->second.second << ", temp";
                                edgeLabels[i+1][ntfItr->first + 1] = s.str();
                            } else {
                                edgeMatrix[i+1][ntfItr->first + 1] = 0;
                                edgeLabels[i+1][ntfItr->first + 1] = "0, temp";
                            }
                        }
                    }
                }
            }

        }
    }

    for (int i = 0; i <= ll; ++i) {
        for (int j = 0; j <= ll; ++j) {
            if (i == j) continue;
            if (edgeMatrix[i][j] != DBL_MAX) {
                if (i == 0) {
                    o << "T0 -> ";
                } else {
                    o << "N" << i - 1 << " -> ";
                }

                if (j == 0) {
                    o << "T0 ";
                } else {
                    o << "N" << j - 1 << " ";
                }
                o << "[label=\"" << edgeLabels[i][j] << "\"];\n";
            }
        }
    }

    o << "\n}\n";

    for (int k = 0; k <= ll; ++k) {
        for (int i = 0; i <= ll; ++i) {
            const double IK = edgeMatrix[i][k];
            if (IK == DBL_MAX) continue;
            for (int j = 0; j <= ll; ++j) {
                double KJ = edgeMatrix[k][j];
                if (KJ == DBL_MAX) continue;
                KJ += IK;
                if (KJ < edgeMatrix[i][j]) {
                    edgeMatrix[i][j] = KJ;
                }
            }
        }
    }
    for (int i = 0; i <= ll; ++i) {
        if (edgeMatrix[i][i] < 0.0) {
            if (!i) {
                cout << "Negative cycle for t0\n";
            } else {
                if (eventsWithFakes[i-1]) {
                    cout << "Negative cycle for ";
                    if (eventsWithFakes[i-1]->action) {
                        cout << *(eventsWithFakes[i-1]->action) << " ";
                        if (eventsWithFakes[i-1]->time_spec == Planner::E_AT_START) {
                            cout << "start\n";
                        } else {
                            cout << "end\n";
                        }
                    } else {
                        cout << "TIL " << eventsWithFakes[i-1]->divisionID << "\n";
                    }
                } else {
                    cout << "Negative cycle for unknown event - this should never happen\n";
                }
            }
        }
    }

}


void LPScheduler::InterestingMap::insertKeepingTrues(const pair<int, bool> & toInsert)
{
    if (toInsert.second) {
        __super::insert(toInsert).first->second = true;
    } else {
        __super::insert(toInsert);
    }
}


void LPScheduler::CountedConstraintSet::insert(const LPScheduler::Constraint* const c)
{
    ++(__super::insert(make_pair(c, 0)).first->second);
}

void LPScheduler::CountedConstraintSet::erase(const LPScheduler::Constraint* const c)
{
    __super::iterator fItr = find(c);
    if (fItr == end()) return;
    if (!(--(fItr->second))) {
        __super::erase(fItr);
    }
}

void LPScheduler::CountedConstraintSet::insert(const LPScheduler::ConstraintSet & c)
{

    iterator lastPos;
    bool firstTime = true;

    ConstraintSet::const_iterator cItr = c.begin();
    const ConstraintSet::const_iterator cEnd = c.end();

    for (; cItr != cEnd; ++cItr) {
        if (firstTime) {
            lastPos = __super::insert(make_pair(*cItr, 0)).first;
            firstTime = false;
        } else {
            lastPos = __super::insert(lastPos, make_pair(*cItr, 0));
        }
        ++(lastPos->second);
    }
}

void LPScheduler::CountedConstraintSet::erase(const LPScheduler::ConstraintSet & c)
{

    ConstraintSet::const_iterator cItr = c.begin();
    const ConstraintSet::const_iterator cEnd = c.end();

    for (; cItr != cEnd; ++cItr) {
        const iterator lastPos = find(*cItr);
        if (lastPos == end()) continue;
        if (!(--(lastPos->second))) {
            __super::erase(lastPos);
        }
    }
}


LPScheduler::LPScheduler(const MinimalState & s, vector<AutomatonPosition::Position> & preferenceStatus, list<FFEvent> & plan)
{
    static list<FFEvent> now;
    static map<int, list<list<StartEvent>::iterator > > compulsaryEnds;
    static list<StartEvent> dummySEQ;
    static list<int>* dummy;
    static ParentData * dummyP;

    LPScheduler(s, preferenceStatus, plan, now, -1, dummySEQ, dummyP, compulsaryEnds, 0, 0, dummy, false);
}


void LPScheduler::collateRelevantVariablesAndInvariants(InterestingMap & currInterest, CountedConstraintSet & activeInvariants,
        const int & stepID, const Planner::time_spec & currTS, const int & actID,
        vector<set<int> > & activeAncestorsOfStep,
        const vector<bool> & correspondEndHasBeenInserted,
        vector<map<int, ConstraintSet > > & invariantsThisStepStartsOnVariableI)
{
    if (currTS != Planner::E_AT) {
        currInterest = interesting[actID][1];
    }

    if (currTS == Planner::E_AT_START) {
        currInterest.insertKeepingTrues(interesting[actID][0].begin(), interesting[actID][0].end());
    }

    if (currTS == Planner::E_AT_END) {
        currInterest.insertKeepingTrues(interesting[actID][2].begin(), interesting[actID][2].end());
    }

    set<int> & activeAncestors = activeAncestorsOfStep[stepID];

    if (activeAncestors.empty()) {
        if (lpDebug & 1024) {
            cout << COLOUR_yellow << "No active ancestors of this step to cause any invariants" << COLOUR_default << endl;
        }
        return;
    }

    InterestingMap::iterator ciItr = currInterest.begin();
    const InterestingMap::iterator ciEnd = currInterest.end();

    for (; ciItr != ciEnd; ++ciItr) {

        if (!ciItr->second) continue;

        set<int>::iterator aaItr = activeAncestors.begin();
        const set<int>::iterator aaEnd = activeAncestors.end();

        for (; aaItr != aaEnd; ++aaItr) {

            if (correspondEndHasBeenInserted[*aaItr]) continue;
            
            const map<int, ConstraintSet >::iterator onThisVariable = invariantsThisStepStartsOnVariableI[*aaItr].find(ciItr->first);

            if (onThisVariable == invariantsThisStepStartsOnVariableI[*aaItr].end()) {
                if (lpDebug & 1024) {
                    cout << COLOUR_yellow << "No invariants on " << *(RPGBuilder::getPNE(ciItr->first)) << " started at step " << *aaItr << COLOUR_default << endl;
                }
                continue;
            }
            if (lpDebug & 1024) {
                cout << COLOUR_yellow << "Adding invariants on " << *(RPGBuilder::getPNE(ciItr->first)) << " that started at step " << *aaItr << COLOUR_default << endl;
            }

            activeInvariants.insert(onThisVariable->second);

        }
    }


    CountedConstraintSet::iterator csItr = activeInvariants.begin();
    const CountedConstraintSet::iterator csEnd = activeInvariants.end();

    for (; csItr != csEnd; ++csItr) {
        currInterest.insertPreconditions(csItr->first->variables.begin(), csItr->first->variables.end());
    }

}

void LPScheduler::recordVariablesInvolvedInThisStepsInvariants(const list<const Constraint*> & invariants,
                                                               map<int, ConstraintSet> & invariantsOnVariableI)
{

    list<const Constraint*>::const_iterator invItr = invariants.begin();
    const list<const Constraint*>::const_iterator invEnd = invariants.end();
    
    for (; invItr != invEnd; ++invItr) {
        const vector<int> & vars = (*invItr)->variables;
        
        const int lim = vars.size();
        
        for (int s = 0; s < lim; ++s) {
            if (lpDebug & 1024) {
                cout << COLOUR_light_green << "Step has an invariant depending on " << *(RPGBuilder::getPNE(vars[s])) << COLOUR_default << endl;
            }
            invariantsOnVariableI[vars[s]].insert(*invItr);
        }
    }
}


void LPScheduler::addConstraintsToGetValuesOfVariablesNow(InterestingMap & currInterest, const int & stepID, const int & currVar, LPScheduler::ValueOfVariablesAtSomeTime & beforeStep)
{

    static const vector<pair<int,double> > emptyEntries;


    int colIdx = lp->getNumCols();
    int constrIdx = lp->getNumRows();

    InterestingMap::iterator sItr = currInterest.begin();
    const InterestingMap::iterator sItrEnd = currInterest.end();

    for (; sItr != sItrEnd; ++sItr) {

        FluentTracking & tracker = finalNumericVars[sItr->first];
        
        if (tracker.statusOfThisFluent != FluentTracking::FS_NORMAL) {
            if (lpDebug & 1) {
                cout << "Not adding constraint to get value of " << *(RPGBuilder::getPNE(sItr->first)) << ": it is a metric tracking fluent";
                if (tracker.statusOfThisFluent == FluentTracking::FS_IGNORE) {
                    cout << " that is being ignored\n";
                } else {
                    cout << ", the effects on which are order-independent, and hence will be included directly in the objective function if needed\n";
                }
            }
            continue;
        }

        if (!tracker.activeGradientCount && tracker.lastEffectValueVariable == -1) {
            // special case: we know the previous value, so just clone it

            if (lpDebug & 1) {
                cout << "Not adding constraint at " << colIdx << " to get value of " << *(RPGBuilder::getPNE(sItr->first)) << " - we know it's " << tracker.postLastEffectValue << endl;
            }
                            
            beforeStep.addLastRecordAsIs(sItr->first, tracker);
        } else {
                
            if (lpDebug & 1) {
                cout << "Adding constraint at " << colIdx << " to get value of " << *(RPGBuilder::getPNE(sItr->first)) << " now";
                if (sItr->second) {
                    cout << " - intend to write to it";
                }
                cout << "\n";
            }

            lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);

            if (assertions) assert((lp->getNumCols() - 1) == colIdx);

            if (nameLPElements) {
                ostringstream namestream;
                namestream << *(RPGBuilder::getPNE(sItr->first));
                namestream << "b" << stepID;
                string asString = namestream.str();
                lp->setColName(colIdx, asString);
            }

            if (tracker.activeGradientCount && tracker.activeGradient != 0.0) {
                if (lpDebug & 1) cout << "Active gradient = " << tracker.activeGradient << "\n";
                if (tracker.lastEffectValueVariable != -1) {

                    static vector<pair<int,double> > entries(4);
                    
                    entries[0].second = 1.0;
                    entries[1].second = -1.0;
                    entries[2].second = -tracker.activeGradient;
                    entries[3].second = tracker.activeGradient;

                    if (assertions) assert(entries[3].second != 0.0);
                    if (assertions) assert(entries[2].second != 0.0);

                    entries[0].first = colIdx;
                    entries[1].first = tracker.lastEffectValueVariable;
                    entries[2].first = currVar;
                    entries[3].first = tracker.lastEffectTimestampVariable;

                    lp->addRow(entries, 0.0, 0.0);

                } else {
                    static vector<pair<int,double> > entries(3);
                    
                    entries[0].second = 1.0;
                    entries[1].second = -tracker.activeGradient;
                    entries[2].second = tracker.activeGradient;

                    if (assertions) assert(entries[2].second != 0.0);
                    if (assertions) assert(entries[1].second != 0.0);

                    entries[0].first = colIdx;
                    entries[1].first = currVar;
                    entries[2].first = tracker.lastEffectTimestampVariable;

                    lp->addRow(entries, tracker.postLastEffectValue, tracker.postLastEffectValue); // syntax for EQ prev

                }

                if (nameLPElements) {
                    ostringstream namestream;
                    namestream << stepID << "delta-" << *(RPGBuilder::getPNE(sItr->first));
                    string asString = namestream.str();
                    lp->setRowName(constrIdx, asString);
                }

                if (assertions) assert((lp->getNumRows() - 1) == constrIdx);

                ++constrIdx;



            } else {

                if (tracker.lastEffectValueVariable != -1) {
                    static vector<pair<int,double> > entries(2);
                    
                    entries[0].second = 1.0;
                    entries[1].second = -1.0;

                    entries[0].first = colIdx;
                    entries[1].first = tracker.lastEffectValueVariable;
                    
                    lp->addRow(entries, 0.0, 0.0);
                    
                    if (nameLPElements) {
                        ostringstream namestream;
                        namestream << stepID << "delta-0-" << *(RPGBuilder::getPNE(sItr->first));
                        string asString = namestream.str();
                        lp->setRowName(constrIdx, asString);
                    }
                    ++constrIdx;
                } else {
                    lp->setColBounds(colIdx, tracker.postLastEffectValue, tracker.postLastEffectValue);
                }
            }


            beforeStep.variableValueIsInColumn(sItr->first, colIdx);

            ++colIdx;
        }

    }
}


int LPScheduler::generateEndDetails(const Planner::time_spec & currTS, const int & actID, const int & stepID, FFEvent & currEvent,
                                    const vector<FFEvent*> & planAsAVector, int & nextImaginaryEndVar, vector<EndDetails> & imaginaryMinMax)
{

    int dummyEnd = -1;


    if (currTS == Planner::E_AT_START && !RPGBuilder::getRPGDEs(actID).empty()) {

        dummyEnd = timestampVars[stepID] + (currEvent.pairWithStep - stepID);

        if (!planAsAVector[currEvent.pairWithStep]->getEffects) {

            if (RPGBuilder::getRPGDEs(actID).back()->fixed.empty()) {
                imaginaryMinMax[stepID] = EndDetails(dummyEnd, nextImaginaryEndVar, -1);
                ++nextImaginaryEndVar;
                
                static vector<pair<int,double> > entries(2);
                
                entries[0].first = imaginaryMinMax[stepID].imaginaryMin;
                entries[1].first = imaginaryMinMax[stepID].imaginaryMax;
                entries[0].second = -1.0;
                entries[1].second = 1.0;
                assert(entries[0].first < lp->getNumCols());
                assert(entries[1].first < lp->getNumCols());
                lp->addRow(entries, 0.0, LPinfinity);

                if (nameLPElements) {
                    {
                        ostringstream namestream;
                        namestream << "minMax" << stepID;
                        string asString = namestream.str();
                        if (lpDebug & 64) {
                            cout << "R" << lp->getNumRows() - 1 << " = " << asString << "\n";
                            //                            checkRows[lp->getNumRows()] = asString;
                        }
                        lp->setRowName(lp->getNumRows() - 1, asString);
                    }
                    {
                        ostringstream namestream;
                        namestream << "iendmax" << currEvent.pairWithStep;
                        string asString = namestream.str();
                        lp->setColName(imaginaryMinMax[stepID].imaginaryMax, asString);
                    }
                }

            } else {
                imaginaryMinMax[stepID] = EndDetails(dummyEnd, dummyEnd, -1);
            }


        } else {
            imaginaryMinMax[stepID] = EndDetails(dummyEnd, dummyEnd, -1);
        }
    }

    return dummyEnd;
}


class LPScheduler::ConstraintAdder {

protected:
    LPScheduler* const parent;

    FFEvent & currEvent;
    const int stepID;
    int effCounter;
    
    InterestingMap * untouched;
    //set<int> * durationalVary;
    list<int> * stableNextTime;
    list<int> * unstableNextTime;

    int modifierCol;
    double modifierWeight;
    
    void addNormalEffect(RPGBuilder::RPGNumericEffect* const ceItr) {

        static const vector<pair<int,double> > emptyEntries;
        
        static const int varCount = RPGBuilder::getPNECount();

        const int currVar = ceItr->fluentIndex;
        
        const FluentTracking & tracker = parent->finalNumericVars[currVar];
        
        assert(tracker.statusOfThisFluent == FluentTracking::FS_NORMAL);
        
        int sLim = ceItr->size;

        const bool wasStable = parent->stableVariable[currVar];

        vector<pair<int,double> > entries;
        entries.reserve(sLim);
        
        bool isStable = ((tracker.activeGradientCount == 0) && (!parent->finalNumericVars[currVar].everHadADurationDependentEffect));

        bool hasDurationVar = false;

        int startStep;
        int endStep;
        
        if (currEvent.time_spec == Planner::E_AT_START) {
            startStep = parent->timestampVars[stepID];
            endStep = startStep + 1;
        } else {
            endStep = parent->timestampVars[stepID];
            startStep = endStep - 1;
        }
        
        double startStepWeight = 0.0;
        double endStepWeight = 0.0;
        
        double accruedConstant = 0.0;
        
        const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
        
        for (int s = 0; s < sLim; ++s) {
            double currW = -ceItr->weights[s];
            if (parent->assertions) assert(currW != 0.0);
            int varIdx = ceItr->variables[s];
                        
            if (varIdx >= varCount) {
                const map<int,double>::const_iterator tickerItr = tickers.find(varIdx - varCount);
                if (tickerItr != tickers.end()) {
                    varIdx = -20;
                    currW *= tickerItr->second;
                }
            } else if (varIdx >= 0) {
                const map<int,double>::const_iterator tickerItr = tickers.find(varIdx);
                if (tickerItr != tickers.end()) {
                    varIdx = -4;
                    currW *= tickerItr->second;
                }
            }
            
            
            
            if (varIdx >= 0) {
                if (varIdx >= varCount) {
                    varIdx -= varCount;
                    currW = ceItr->weights[s];
                }
                
                {
                    const ValueOfVariablesAtSomeTime::const_iterator atItr = applyTo->find(varIdx);
                    #ifndef NDEBUG
                    if (atItr == applyTo->end()) {
                        cerr << "Fatal internal error: in " << *ceItr << ", trying to refer to " << *RPGBuilder::getPNE(varIdx) << ", but it hasn't been made available at this point\n";
                    }
                    #endif
                    assert(atItr != applyTo->end());
                    if (atItr->second.first != -1) {
                        entries.push_back(make_pair(atItr->second.first, currW));
                    } else {
                        accruedConstant -= atItr->second.second * currW;
                    }
                }
                
                if (!parent->stableVariable[varIdx]) {
                    isStable = false;
                }
                
                if (parent->finalNumericVars[varIdx].everHadADurationDependentEffect) {
                    parent->finalNumericVars[currVar].everHadADurationDependentEffect = true;
                }
                //                        if (outstandingCTS.find(varIdx) != outstandingCTS.end()) stableVariable[currVar] = false;
            } else if (varIdx == -3 || varIdx == -19) {
                hasDurationVar = true;
                
                if (varIdx == -3) {             
                    endStepWeight += currW;
                    startStepWeight += ceItr->weights[s];
                } else {
                    endStepWeight += ceItr->weights[s];
                    startStepWeight += currW;
                }
                
                if (parent->assertions) assert(entries.back().second != 0.0);
                
                isStable = false;
                parent->finalNumericVars[currVar].everHadADurationDependentEffect = true;

            } else if (varIdx == -4) {
                // total-time, i.e. a ticker
                // substitute in the timestamp of the effect
                if (currEvent.time_spec == Planner::E_AT_START) {
                    startStepWeight += currW;
                } else {
                    endStepWeight += currW;
                }
                isStable = false;
                parent->finalNumericVars[currVar].everHadADurationDependentEffect = true;
            } else if (varIdx == -20) {
                // -total-time, i.e. a ticker
                // substitute in - the timestamp of the effect
                if (currEvent.time_spec == Planner::E_AT_START) {
                    startStepWeight -= currW;
                } else {
                    endStepWeight -= currW;
                }
                isStable = false;
                parent->finalNumericVars[currVar].everHadADurationDependentEffect = true;
            } else {
                cout << "Unprocessed continuous effect in LP scheduler, aborting.\n";
                assert(false);
            }
        }

        if (fabs(startStepWeight) > 0.000001) {
            entries.push_back(make_pair(startStep, startStepWeight));
        }
                
        if (fabs(endStepWeight) > 0.000001) {
            entries.push_back(make_pair(endStep, endStepWeight));
        }
        
        if (modifierCol != -1) {
            entries.push_back(make_pair(modifierCol, -modifierWeight));
            parent->finalNumericVars[currVar].everHadADurationDependentEffect = true;
            isStable = false;
        }

        if (!(ceItr->isAssignment)) {
            {
                const ValueOfVariablesAtSomeTime::const_iterator atItr = applyTo->find(currVar);
                assert(atItr != applyTo->end());
                if (atItr->second.first != -1) {                                
                    entries.push_back(make_pair(atItr->second.first, -1.0));            
                } else {
                    accruedConstant += atItr->second.second;
                }
            }
            isStable = (isStable && wasStable);
        }

        if (entries.empty()) {
            
            accruedConstant += ceItr->constant;
            
            output->variableValueIsConstant(currVar, accruedConstant);
        
            if (lpDebug & 1) {
                cout << *(RPGBuilder::getPNE(currVar)) << " is now " << accruedConstant << " due to effect " << *ceItr << endl;
            }
        } else {                
            
            parent->lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);

            const int colIdx = parent->lp->getNumCols() - 1;

            if (parent->nameLPElements) {
                ostringstream namestream;
                namestream << *(RPGBuilder::getPNE(currVar));
                namestream << "a" << stepID;
                string asString = namestream.str();
                parent->lp->setColName(colIdx, asString);
            }


            entries.push_back(make_pair(colIdx, 1.0));


            if (lpDebug & 1) {
                if (hasDurationVar) {
                    cout << "Adding effect dependent on duration:";
                    const int sLim = entries.size();
                    for (int sp = 0; sp < sLim; ++sp) {
                        cout << "\t";
                        if (sp > 0) cout << " + "; else cout << "   ";
                        cout << entries[sp].second << " * " << parent->lp->getColName(entries[sp].first) << "\n";
                    }
                    cout << "\t = " << ceItr->constant + accruedConstant;
                } else {
                    cout << "Added effect " << *ceItr;
                    
                    if (modifierCol != -1) {
                        cout << " + " << modifierWeight << "*" << parent->lp->getColName(modifierCol);
                    }
                    
                    cout << " to get value of " << *(RPGBuilder::getPNE(currVar)) << "\n";
                }
            }

            parent->lp->addRow(entries, ceItr->constant + accruedConstant, ceItr->constant + accruedConstant);

            if (parent->nameLPElements) {
                const int constrIdx = parent->lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << "eff@" << stepID << "n" << effCounter;
                string asString = namestream.str();
                parent->lp->setRowName(constrIdx, asString);
            }

            output->variableValueIsInColumn(currVar, colIdx);

        }

        InterestingMap::iterator untItr = untouched->find(currVar);
        assert(untItr != untouched->end());
        assert(untItr->second);
        untouched->erase(untItr);

        if (isStable && !wasStable) stableNextTime->push_back(currVar);
        
        if (!isStable && wasStable) {
            if (lpDebug & 1) {
                cout << "Effect " << *ceItr << " makes variable unstable next time\n";
            }
                    
            unstableNextTime->push_back(currVar);
        }
                
        ++effCounter;
    }

    void addOrderIndependentMetricEffect(RPGBuilder::RPGNumericEffect* const ceItr) {

        static const int varCount = RPGBuilder::getPNECount();

        const int currVar = ceItr->fluentIndex;
        
        FluentTracking & tracker = parent->finalNumericVars[currVar];
        
        assert(tracker.statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT);
        assert(!ceItr->isAssignment);

        const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();

        
        const int sLim = ceItr->size;

        for (int s = 0; s < sLim; ++s) {
            double thisW = ceItr->weights[s];
            int varIdx = ceItr->variables[s];
            
            if (varIdx >= varCount) {
                const map<int,double>::const_iterator tickerItr = tickers.find(varIdx - varCount);
                if (tickerItr != tickers.end()) {
                    varIdx = -20;
                    thisW *= tickerItr->second;
                }
            } else if (varIdx >= 0) {
                const map<int,double>::const_iterator tickerItr = tickers.find(varIdx);
                if (tickerItr != tickers.end()) {
                    varIdx = -4;
                    thisW *= tickerItr->second;
                }
            }
            
            if (varIdx >= 0) {
                if (varIdx >= varCount) {
                    varIdx -= varCount;
                    thisW = -thisW;
                }
                
                {
                    const ValueOfVariablesAtSomeTime::const_iterator atItr = applyTo->find(varIdx);
                    assert(atItr != applyTo->end());
                    if (atItr->second.first != -1) {
                        tracker.orderIndependentValueTerms.insert(make_pair(atItr->second.first, 0.0)).first->second += thisW;
                    } else {
                        tracker.orderIndependentValueConstant += thisW * atItr->second.second;
                    }
                }

                assert(parent->stableVariable[varIdx]);
                
            } else if (varIdx == -3 || varIdx == -19) {
                int startStep;
                int endStep;

                if (currEvent.time_spec == Planner::E_AT_START) {
                    startStep = parent->timestampVars[stepID];
                    endStep = startStep + 1;
                } else {
                    endStep = parent->timestampVars[stepID];
                    startStep = endStep - 1;
                }
                
                if (varIdx == -3) {
                    tracker.orderIndependentValueTerms.insert(make_pair(endStep, 0.0)).first->second += thisW;
                    tracker.orderIndependentValueTerms.insert(make_pair(startStep, 0.0)).first->second -= thisW;
                } else {
                    tracker.orderIndependentValueTerms.insert(make_pair(endStep, 0.0)).first->second -= thisW;
                    tracker.orderIndependentValueTerms.insert(make_pair(startStep, 0.0)).first->second += thisW;
                }

            } else if (varIdx == -4) {                
                tracker.orderIndependentValueTerms.insert(make_pair(parent->timestampVars[stepID], 0.0)).first->second += thisW;
            } else if (varIdx == -20) {
                tracker.orderIndependentValueTerms.insert(make_pair(parent->timestampVars[stepID], 0.0)).first->second -= thisW;
            } else {
                cout << "Unprocessed continuous effect in LP scheduler: refers to variable " << varIdx << ", aborting.\n";
                assert(false);
            }
        }

        if (modifierCol != -1) {
            tracker.orderIndependentValueTerms.insert(make_pair(modifierCol, 0.0)).first->second += modifierWeight;
        }
        
        tracker.orderIndependentValueConstant += ceItr->constant;

    }

    
    const char * label;
    mutable int suffix;
        
    mutable bool constraintsWereBroken;
    
public:
    ValueOfVariablesAtSomeTime * applyTo;    
    ValueOfVariablesAtSomeTime * output;
    
    
    
    ConstraintAdder(LPScheduler * const parentIn, FFEvent & ev, const char * const labelIn, const int & stepIDIn, ValueOfVariablesAtSomeTime & applyToIn)
        : parent(parentIn), currEvent(ev), stepID(stepIDIn), effCounter(0),
          untouched((InterestingMap*)0), stableNextTime((list<int>*)0), unstableNextTime((list<int>*)0),
          modifierCol(-1), modifierWeight(NaN),
          label(labelIn), suffix(0), constraintsWereBroken(false), applyTo(&applyToIn), output((ValueOfVariablesAtSomeTime*)0) {
    }

    const bool & wereConstraintsBroken() const {
        return constraintsWereBroken;
    }
    
    void supplyEffectData(ValueOfVariablesAtSomeTime & atStep, InterestingMap & unto, list<int> & snt, list<int> & unt) {
        output = &atStep;
        untouched = &unto;
        stableNextTime = &snt;
        unstableNextTime = &unt;
    }

    void changeLabel(const char * l) {
        label = l;
        suffix = 0;
    }

    void setRHSModifier(const int & col, const double & w) {
        modifierCol = col;
        modifierWeight = w;
    }
    
    void clearRHSModifier() {
        modifierCol = -1;
        modifierWeight = NaN;
    }
    
    void operator()(const Constraint * const csItr) const {

        const int cSize = csItr->weights.size();

        vector<pair<int,double> > entries;
        entries.reserve(cSize + 2);
        
        if (LPScheduler::lpDebug & 1024) {
            cout << "Adding constraint: ";
            for (int s = 0 ; s < cSize; ++s) {
                if (s) cout << " + ";                
                cout << csItr->weights[s] << "*";
                if (csItr->variables[s] == -19) {
                    cout << "-?duration";
                } else if (csItr->variables[s] == -3) {
                    cout << "?duration";
                } else if (csItr->variables[s] == -4) {
                    cout << "total-time";
                } else {                
                    const ValueOfVariablesAtSomeTime::const_iterator valItr = applyTo->find(csItr->variables[s]);
                    assert(valItr != applyTo->end());
                    if (valItr->second.first != -1) {
                        cout << parent->lp->getColName(valItr->second.first);
                    } else {
                        cout << *(RPGBuilder::getPNE(csItr->variables[s])) << " {" << valItr->second.second << "}";
                    }
                }

            }
            if (csItr->lower != -DBL_MAX) {
                cout << ", >= " << csItr->lower;
                if (modifierCol != -1) {
                    cout << " + " << modifierWeight << "*" <<  parent->lp->getColName(modifierCol);
                }
            }
            if (csItr->upper != DBL_MAX) {
                cout << ", <= " << csItr->upper;
                if (modifierCol != -1) {
                    cout << " + " << modifierWeight << "*" <<  parent->lp->getColName(modifierCol);
                }
            }
            cout << std::endl;
        }

        double startStepWeight = 0.0;
        double endStepWeight = 0.0;
        
        double accruedConstant = 0.0;
        int startStep;
        int endStep;
        
        if (currEvent.time_spec == Planner::E_AT_START) {
            startStep = parent->timestampVars[stepID];
            endStep = startStep + 1;
        } else {
            endStep = parent->timestampVars[stepID];
            startStep = endStep - 1;
        }                    
                
        for (int s = 0 ; s < cSize; ++s) {
            if (csItr->variables[s] < 0) {
                if (csItr->variables[s] == -3 || csItr->variables[s] == -19) {
                    
                    if (csItr->variables[s] == -3) {
                        endStepWeight += csItr->weights[s];
                        startStepWeight -= csItr->weights[s];
                    } else {
                        startStepWeight += csItr->weights[s];
                        endStepWeight -= csItr->weights[s];
                    }
                    
                } else if (csItr->variables[s] == -4) {
                    if (currEvent.time_spec == Planner::E_AT_START) {
                        startStepWeight += csItr->weights[s];
                    } else {
                        endStepWeight += csItr->weights[s];
                    }
                } else {
                    std::cerr << "Fatal internal error: variable index " << csItr->variables[s] << " used\n";
                    exit(1);
                }
            } else {
                const ValueOfVariablesAtSomeTime::const_iterator valItr = applyTo->find(csItr->variables[s]);
                assert(valItr != applyTo->end());
                if (valItr->second.first != -1) {
                    entries.push_back(make_pair(valItr->second.first, csItr->weights[s]));
                    if (parent->assertions) assert(entries.back().second != 0.0);
                } else {
                    accruedConstant += valItr->second.second * csItr->weights[s];
                    if (parent->assertions) assert(csItr->weights[s] != 0.0);
                }
                
            }
        }
        
        if (fabs(startStepWeight) > 0.000001) {
            entries.push_back(make_pair(startStep, startStepWeight));
        }
        
        if (fabs(endStepWeight) > 0.000001) {
            entries.push_back(make_pair(endStep, endStepWeight));
        }
        
        if (modifierCol != -1) {
            entries.push_back(make_pair(modifierCol, -modifierWeight)); // negated weight, because it's moved from the RHS to the LHS
        }

        if (entries.empty()) {
            if (csItr->lower != -DBL_MAX && accruedConstant < csItr->lower) {
                constraintsWereBroken = true;
            }
            if (csItr->upper != DBL_MAX && accruedConstant > csItr->lower) {
                constraintsWereBroken = true;
            }
        } else {
        
            parent->lp->addRow(entries,
                               (csItr->lower != -DBL_MAX ? csItr->lower - accruedConstant : -LPinfinity),
                               (csItr->upper != DBL_MAX  ? csItr->upper - accruedConstant : LPinfinity ) );

            if (parent->nameLPElements) {
                const int constrIdx = parent->lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << label << stepID << "n" << suffix;
                string asString = namestream.str();
                parent->lp->setRowName(constrIdx, asString);
                ++suffix;
            }
        }
    }

    void operator()(const pair<const Constraint*, unsigned int> & csItr) const {
        operator()(csItr.first);
    }

    void operator()(RPGBuilder::RPGNumericEffect* const ceItr) {

        const int currVar = ceItr->fluentIndex;
        
        FluentTracking & tracker = parent->finalNumericVars[currVar];

        switch (tracker.statusOfThisFluent) {
            case FluentTracking::FS_NORMAL:
            {
                addNormalEffect(ceItr);
                return;
            }
            case FluentTracking::FS_ORDER_INDEPENDENT:
            {
                addOrderIndependentMetricEffect(ceItr);
                return;
            }
            default:
            {
                return;
            }
        }
        
    }
    
    void operator()(const Literal* const litEff) {
        
        static vector<pair<int,double> > emptyEntries;
        
        const map<int, RPGBuilder::Guarded>::const_iterator sItr = RPGBuilder::getSemaphoreFacts().find(litEff->getStateID());
        
        if (sItr == RPGBuilder::getSemaphoreFacts().end()) {
            return;
        }
        
        set<int>::const_iterator vItr = sItr->second.guardedConditionVars.begin();
        const set<int>::const_iterator vEnd = sItr->second.guardedConditionVars.end();
        
        for (; vItr != vEnd; ++vItr) {

            FluentTracking & tracker = parent->finalNumericVars[*vItr];
            tracker.nowMustFollowCols.insert(parent->timestampVars[stepID]);            
        }
    }

};

struct LPScheduler::DurationAdder {

    LPScheduler * const parent;
    int durationID;
    FFEvent & currEvent;
    const int stepID;
    ValueOfVariablesAtSomeTime * beforeStep;
    const vector<bool> & stableVariable;
    
    int startToUse;
    int endToUse;

    VAL::comparison_op durationType;

    bool durationIsFixed;
    
    DurationAdder(LPScheduler * const parentIn, FFEvent & ev, const int & stepIDIn, ValueOfVariablesAtSomeTime & beforeStepIn, const vector<bool> & stableVariableIn)
            : parent(parentIn), durationID(0), currEvent(ev), stepID(stepIDIn), beforeStep(&beforeStepIn), stableVariable(stableVariableIn),
            startToUse(-1), endToUse(-1), durationType(VAL::E_EQUALS), durationIsFixed(true) {
    }

    void setStartEnd(const int & s, const int & e, const VAL::comparison_op & dt) {
        startToUse = s;
        endToUse = e;
        durationType = dt;
    }

    void operator()(RPGBuilder::DurationExpr* const currDE) {

        const int vSize = currDE->weights.size();
        vector<pair<int,double> > entries;
        entries.reserve(2 + vSize);
        
        entries.push_back(make_pair(endToUse, 1.0));
        entries.push_back(make_pair(startToUse, -1.0));
        
        assert(endToUse < parent->lp->getNumCols());
        assert(startToUse < parent->lp->getNumCols());
        
        bool allVariablesAreStable = true;
        
        double accruedConstant = 0.0;
        
        {
            for (int v = 0; v < vSize; ++v) {
                #ifdef STOCHASTICDURATIONS
                int & vToUse = currDE->variables[v].first;
                #else
                int & vToUse = currDE->variables[v];
                #endif
                if (vToUse != -1) {
                    const ValueOfVariablesAtSomeTime::const_iterator bsItr = beforeStep->find(vToUse);
                    #ifndef NDEBUG
                    if (bsItr == beforeStep->end()) {
                        if (vToUse >= RPGBuilder::getPNECount()) {
                            std::cerr << "Internal error: variable -" << *(RPGBuilder::getPNE(vToUse - RPGBuilder::getPNECount())) << " not defined in the LP at a step where it is needed for a duration constraint.\n";
                        } else {
                            std::cerr << "Internal error: variable " << *(RPGBuilder::getPNE(vToUse)) << " not defined in the LP at a step where it is needed for a duration constraint.\n";
                        }
                        assert(bsItr != beforeStep->end());
                    }
                    #endif
                    if (bsItr->second.first != -1) {
                        entries.push_back(make_pair(bsItr->second.first, -(currDE->weights[v])));
                        allVariablesAreStable = (allVariablesAreStable && stableVariable[vToUse]);
                    } else {
                        accruedConstant -= currDE->weights[v] * bsItr->second.second;
                    }
                    
                } else {
                    std::cerr << "Internal error: negative variable " << vToUse << " in duration expression\n";
                    exit(1);
                }
            }
        }

        const double DEconstant = currDE->constant - accruedConstant;
        
        switch (durationType) {
        case VAL::E_EQUALS: {
            if ((lpDebug & 1) && !vSize) cout << "Simple constant fixed duration: " << currDE->constant << " - " << accruedConstant << " = " << DEconstant << "\n";
                        
            const EpsilonResolutionTimestamp rounded(DEconstant,true);
            parent->lp->addRow(entries, rounded.toDouble(), rounded.toDouble());
            if (parent->nameLPElements) {
                int constrIdx = parent->lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << "dur" << startToUse << "fixed" << durationID << ": v" << startToUse << " -> v" << endToUse;
                string asString = namestream.str();
                parent->lp->setRowName(constrIdx, asString);
                durationIsFixed = (durationIsFixed || allVariablesAreStable);
            }
            break;
        }
        case VAL::E_GREATEQ: {
            if ((lpDebug & 1) && !vSize) cout << "Simple constant minimum duration: " << currDE->constant << " - " << accruedConstant << " = " << DEconstant << "\n";
                        
            const EpsilonResolutionTimestamp rounded(DEconstant,true);
            parent->lp->addRow(entries, rounded.toDouble(), LPinfinity);
            if (parent->nameLPElements) {
                int constrIdx = parent->lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << "dur" << startToUse << "min" << durationID << ": v" << startToUse << " -> v" << endToUse;
                string asString = namestream.str();
                parent->lp->setRowName(constrIdx, asString);
                durationIsFixed = false;
            }
            break;
        }
        case VAL::E_LESSEQ: {            
            
            if ((lpDebug & 1) && !vSize) cout << "Simple constant maximum duration: " << currDE->constant << " - " << accruedConstant << " = " << DEconstant << "\n";
            
            const EpsilonResolutionTimestamp rounded(DEconstant,true);
            parent->lp->addRow(entries, -LPinfinity, rounded.toDouble());
            if (parent->nameLPElements) {
                int constrIdx = parent->lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << "dur" << startToUse << "max" << durationID << ": v" << startToUse << " -> v" << endToUse;
                string asString = namestream.str();
                parent->lp->setRowName(constrIdx, asString);
                durationIsFixed = false;
            }
            break;
        }
        default:
            assert(false);
        }
        ++durationID;

    }

};

void LPScheduler::AbstractFactConstraintBlock::addUser(const int & stepID)
{
    static const bool debug = (LPScheduler::lpDebug & 1);
    static const bool nameLPElements = true;
    
    const int occCount = occurrenceBounds.size();    
    
    if (debug) {
        cout << "Abstract fact " << *(RPGBuilder::getLiteral(factID)) << endl;
    }
    
    static const vector<pair<int,double> > emptyEntries;
    
    if (!onlyOneUserPerWindow && occCount == 1) {

        if (debug) {
            cout << "Only one window: simple re-bounding if needed\n";
        }
        
        if (lp->getColLower(lpOffsetToPlanStepVariables + stepID) < occurrenceBounds[0].first) {
            lp->setColLower(lpOffsetToPlanStepVariables + stepID, EpsilonResolutionTimestamp(occurrenceBounds[0].first,true).toDouble());
        }
        
        if (lp->getColUpper(lpOffsetToPlanStepVariables + stepID) > occurrenceBounds[0].second) {
            lp->setColUpper(lpOffsetToPlanStepVariables + stepID, EpsilonResolutionTimestamp(occurrenceBounds[0].second,true).toDouble());
        }
        
        return;
    }
        
    if (onlyOneUserPerWindow && constraintsForOneUserPerOccurrence.empty()) {
        
        if (debug) {
            cout << "- Creating initial constraints for the " << occCount << " one-per-window outcomes\n";
        }
        
        constraintsForOneUserPerOccurrence.resize(occCount);
        outcomeWasUsed.resize(occCount);
        
        static const vector<pair<int,double> > emptyEntries;
        static vector<pair<int,double> > usedEntry(1);
        
        for (int occ = 0; occ < occCount; ++occ) {
            
            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
            
            if (nameLPElements) {
                ostringstream s;
                s << "usedAF" << factID << "oc" << occ;
                lp->setColName(lp->getNumCols() - 1, s.str());
            }
            
            outcomeWasUsed[occ] = lp->getNumCols() - 1;
            
            usedEntry[0] = make_pair(outcomeWasUsed[occ], -1.0);
            
            lp->addRow(usedEntry, 0.0, 0.0);
            constraintsForOneUserPerOccurrence[occ] = lp->getNumRows() - 1;
            
            if (nameLPElements) {
                ostringstream s;
                s << "limAF" << factID << "oc" << occ;
                lp->setRowName(lp->getNumRows() - 1, s.str());
            }
            
            if (debug) {
                cout << "  - Outcome " << occ << " limited by row " << constraintsForOneUserPerOccurrence[occ] << ", detect use with var " << outcomeWasUsed[occ] << endl;
            }
        }
        
        // now have an empty row ready to say <sum of users at that time> <= 1
    }
    
    static vector<pair<int,double> > oneEntry(1);   
        
    vector<pair<int,double> > exactlyOneUsed(occCount);
    
    vector<pair<int,double> > lowerBound;
    vector<pair<int,double> > upperBound;
    
    lowerBound.reserve(occCount + 1);
    upperBound.reserve(occCount + 1);    
        
    for (int occ = 0; occ < occCount; ++occ) {
        
        if (onlyOneUserPerWindow) {
            oneEntry[0].first = constraintsForOneUserPerOccurrence[occ];            
            oneEntry[0].second = 1.0;
            
            // add column, and update the <sum of users at that time> <= 1 constraint for outcome [occ]
            lp->addCol(oneEntry, 0.0, 1.0, MILPSolver::C_BOOL);
        } else {
            // if multiple users are allowed in the same window, we don't need to augment the <=1 constraints
            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);            
        } 
    
        const int currCol = lp->getNumCols() - 1;

        if (nameLPElements) {
            ostringstream s;
            s << "s" << stepID << "AF" << factID << "oc" << occ;
            lp->setColName(currCol, s.str());
        }
        exactlyOneUsed[occ] = make_pair(currCol, 1.0);

        if (debug) {
            cout << "* Have col for step " << stepID << " using outcome " << occ << endl;
        }
        
        if (occurrenceBounds[occ].first > 0.0) {       
            lowerBound.push_back(make_pair(currCol, -occurrenceBounds[occ].first));
            if (debug) {
                cout << "  - If 1, pushes lower bound up to " << occurrenceBounds[occ].first << endl;
            }
        }
        if (occ < occCount - 1) {
            upperBound.push_back(make_pair(currCol, (occurrenceBounds[occCount-1].second - occurrenceBounds[occ].second)));
            if (debug) {
                cout << "  - If 1, pushes upper bound down to " << occurrenceBounds[occ].second << endl;
            }
            
        }                
    }
    
    lowerBound.push_back(make_pair(stepID + lpOffsetToPlanStepVariables, 1.0));
    upperBound.push_back(make_pair(stepID + lpOffsetToPlanStepVariables, 1.0));
    
    lp->addRow(lowerBound, 0.0, LPinfinity);
    
    if (nameLPElements) {
        ostringstream s;
        s << "s" << stepID << "AF" << factID << "LB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }
    
    lp->addRow(upperBound, -LPinfinity, occurrenceBounds[occCount-1].second);

    if (nameLPElements) {
        ostringstream s;
        s << "s" << stepID << "AF" << factID << "UB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }    
    
    lp->addRow(exactlyOneUsed, 1.0, 1.0);
    
    if (nameLPElements) {
        ostringstream s;
        s << "s" << stepID << "AF" << factID << "sched";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }
    
    
}

void LPScheduler::AbstractFactConstraintBlock::addOverAllUser(const int & startStepID, const int & endStepID,
                                                              const double & startGap, const double & endGap)
{
    static const bool debug = (LPScheduler::lpDebug & 1);
    static const bool nameLPElements = true;
    
    const int occCount = occurrenceBounds.size();    
    
    if (debug) {
        cout << "Abstract fact " << *(RPGBuilder::getLiteral(factID)) << endl;
    }
    
    static const vector<pair<int,double> > emptyEntries;
    
    if (!onlyOneUserPerWindow && occCount == 1) {

        if (debug) {
            cout << "Only one window: simple re-bounding if needed\n";
        }
        
        {
            const double localOBFirst = occurrenceBounds[0].first - (startGap == EPSILON ? 0.0 : EPSILON);
                
            if (lp->getColLower(lpOffsetToPlanStepVariables + startStepID) < localOBFirst) {
                lp->setColLower(lpOffsetToPlanStepVariables + startStepID, EpsilonResolutionTimestamp(localOBFirst,true).toDouble());
            }
            
            if (lp->getColLower(lpOffsetToPlanStepVariables + endStepID) < localOBFirst + EPSILON) {
                lp->setColLower(lpOffsetToPlanStepVariables + endStepID, EpsilonResolutionTimestamp(localOBFirst + EPSILON,true).toDouble());
            }
        }
        
        {
            const double localOBSecond = occurrenceBounds[0].first + (endGap == EPSILON ? 0.0 : EPSILON);
        
            if (lp->getColUpper(lpOffsetToPlanStepVariables + endStepID) > localOBSecond) {
                lp->setColUpper(lpOffsetToPlanStepVariables + endStepID, EpsilonResolutionTimestamp(localOBSecond,true).toDouble());
            }
            
            if (lp->getColUpper(lpOffsetToPlanStepVariables + startStepID) > localOBSecond - EPSILON) {
                lp->setColUpper(lpOffsetToPlanStepVariables + startStepID, EpsilonResolutionTimestamp(localOBSecond - EPSILON,true).toDouble());
            }
        }
        
        return;
    }
        
    if (onlyOneUserPerWindow && constraintsForOneUserPerOccurrence.empty()) {
        
        if (debug) {
            cout << "- Creating initial constraints for the " << occCount << " one-per-window outcomes\n";
        }
        
        constraintsForOneUserPerOccurrence.resize(occCount);
        outcomeWasUsed.resize(occCount);
        
        static const vector<pair<int,double> > emptyEntries;
        static vector<pair<int,double> > usedEntry(1);
        
        for (int occ = 0; occ < occCount; ++occ) {
            
            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
            
            if (nameLPElements) {
                ostringstream s;
                s << "usedAF" << factID << "oc" << occ;
                lp->setColName(lp->getNumCols() - 1, s.str());
            }
            
            outcomeWasUsed[occ] = lp->getNumCols() - 1;
            
            usedEntry[0] = make_pair(outcomeWasUsed[occ], -1.0);
            
            lp->addRow(usedEntry, 0.0, 0.0);
            constraintsForOneUserPerOccurrence[occ] = lp->getNumRows() - 1;
            
            if (nameLPElements) {
                ostringstream s;
                s << "limAF" << factID << "oc" << occ;
                lp->setRowName(lp->getNumRows() - 1, s.str());
            }
            
            if (debug) {
                cout << "  - Outcome " << occ << " limited by row " << constraintsForOneUserPerOccurrence[occ] << ", detect use with var " << outcomeWasUsed[occ] << endl;
            }
        }
        
        // now have an empty row ready to say <sum of users at that time> <= 1
    }
    
    static vector<pair<int,double> > oneEntry(1);   
        
    vector<pair<int,double> > exactlyOneUsed(occCount);
    
    vector<pair<int,double> > lowerBound;
    vector<pair<int,double> > upperBound;
    
    lowerBound.reserve(occCount + 1);
    upperBound.reserve(occCount + 1);    

    for (int occ = 0; occ < occCount; ++occ) {
        
        if (onlyOneUserPerWindow) {
            oneEntry[0].first = constraintsForOneUserPerOccurrence[occ];            
            oneEntry[0].second = 1.0;
            
            // add column, and update the <sum of users at that time> <= 1 constraint for outcome [occ]
            lp->addCol(oneEntry, 0.0, 1.0, MILPSolver::C_BOOL);
        } else {
            // if multiple users are allowed in the same window, we don't need to augment the <=1 constraints
            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);            
        } 
    
        const int currCol = lp->getNumCols() - 1;

        if (nameLPElements) {
            ostringstream s;
            s << "soa" << startStepID << "AF" << factID << "oc" << occ;
            lp->setColName(currCol, s.str());
        }
        exactlyOneUsed[occ] = make_pair(currCol, 1.0);

        if (debug) {
            cout << "* Have col for over-all from step " << startStepID << " using outcome " << occ << endl;
        }
        
        const double localOBFirst = occurrenceBounds[occ].first - (startGap == EPSILON ? 0.0 : EPSILON);
        
        if (localOBFirst > 0.0) {       
            lowerBound.push_back(make_pair(currCol, -localOBFirst));
            if (debug) {
                cout << "  - If 1, pushes lower bound up to " << localOBFirst << endl;
            }
        }
        if (occ < occCount - 1) {
            // this is okay, we don't need the end gap check, as for zero end-gap we'd add EPSILON to both
            // terms before subtracting, which is equivalent
            upperBound.push_back(make_pair(currCol, (occurrenceBounds[occCount-1].second - occurrenceBounds[occ].second)));
            if (debug) {
                const double localOBSecond = occurrenceBounds[occ].second + (endGap == EPSILON ? 0.0 : EPSILON);
                cout << "  - If 1, pushes upper bound down to " << localOBSecond << endl;
            }
            
        }                
    }
    
    lowerBound.push_back(make_pair(startStepID + lpOffsetToPlanStepVariables, 1.0));
    upperBound.push_back(make_pair(startStepID + lpOffsetToPlanStepVariables, 1.0));
    
    lp->addRow(lowerBound, 0.0, LPinfinity);
    
    if (nameLPElements) {
        ostringstream s;
        s << "soa" << startStepID << "AF" << factID << "LB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }
    
    lowerBound.back().first = endStepID + lpOffsetToPlanStepVariables;
    
    lp->addRow(lowerBound, 0.0, LPinfinity);
    
    if (nameLPElements) {
        ostringstream s;
        s << "soa" << endStepID << "AF" << factID << "LB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }
    
    const double localOBSecond = occurrenceBounds[occCount - 1].second + (endGap == EPSILON ? 0.0 : EPSILON);
    lp->addRow(upperBound, -LPinfinity, localOBSecond);

    if (nameLPElements) {
        ostringstream s;
        s << "soa" << startStepID << "AF" << factID << "UB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }    
    
    upperBound.back().first = endStepID + lpOffsetToPlanStepVariables;
    
    lp->addRow(upperBound, -LPinfinity, localOBSecond);
    
    if (nameLPElements) {
        ostringstream s;
        s << "soa" << endStepID << "AF" << factID << "UB";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }    
    
    lp->addRow(exactlyOneUsed, 1.0, 1.0);
    
    if (nameLPElements) {
        ostringstream s;
        s << "soa" << startStepID << "AF" << factID << "sched";
        lp->setRowName(lp->getNumRows() - 1, s.str());
    }        
}

const vector<int> * LPScheduler::AbstractFactConstraintBlock::needToReviseBounds() const
{
    if (!onlyOneUserPerWindow || noLongerAvailable || constraintsForOneUserPerOccurrence.empty()) {        
        // leave the default bounds in place
        return 0;
    }

    assert(&outcomeWasUsed);
    
    return &outcomeWasUsed;
}

struct VarsForTrigger {
  
    int stepID;
    int satisfactionVar;
    int disjunctiveSatisfactionRow;
    
    VarsForTrigger(const int & s, const int & sv, const int & dsr)
        : stepID(s), satisfactionVar(sv), disjunctiveSatisfactionRow(dsr)
    {
    }
    
};

struct VarsForRequirement {
    
    int stepID;
       
    VarsForRequirement(const int & s)
        : stepID(s)
    {
    }
};

struct NNFDependencies {
    map<int, list<int> > literals;
    map<int, list<int> > negativeLiterals;
    map<int, set<int> > numerics;        
};

LPScheduler::LPScheduler(const MinimalState & theState,
                         vector<AutomatonPosition::Position> & preferenceStatus,
                         list<FFEvent> & header,
                         list<FFEvent> & now,
                         const int & justAppliedStep,
                         list<StartEvent> & startEventQueue,
                         ParentData * parentData,
                         map<int, list<list<StartEvent>::iterator > > & compulsaryEnds,
                         const vector<double> * secondMin,
                         const vector<double> * secondMax,
                         list<int> * tilComesBefore,
                         const bool & setObjectiveToMetric) : cd(0)
{

    if (!initialised) initialise();


    static vector<pair<int,double> > emptyEntries(0);

    static const bool optimised = true;

    assertions = true;

    static vector<vector<pair<double, double> > > & actionTSBounds = TemporalAnalysis::getActionTSBounds();

    includeMetricTrackingVariables = setObjectiveToMetric;    
    stableVariable = vector<bool>(numVars, true);

    tsVarCount = header.size() + now.size();

    planCostsWereCalculated = false;
    planCostsNeededAnLP = false;
    dummyVarForMakespan = -1;
    varForReachableCost = -1;
    
    bool shouldFail = false;
    bool shouldSucceed = false;

    bool paranoia = (Globals::paranoidScheduling || Globals::profileScheduling);

    if (tsVarCount == 0) {
        lp = 0; solved = true; return;
    }

    if (hybridBFLP && parentData) {

        cd = parentData->spawnChildData(startEventQueue, header, now, setObjectiveToMetric, theState.temporalConstraints, justAppliedStep);
        
        bool preferencesWereAsExpected = true;
        
        if (!cd || !cd->propagateNewEdges(preferenceStatus, theState.temporalConstraints, preferencesWereAsExpected)) {
            if (lpDebug & 1) cout << "STP proved LP unsolvable, skipping LP\n";
            //assert(!cd || cd->checkItContainsAllTheseEdges(theState.temporalConstraints));
            if (paranoia) {
                shouldSucceed = false;
                shouldFail = true;
            } else {
                lp = 0; solved = false; return;
            }
        } else if (!setObjectiveToMetric && !cd->doLPSolve()) {
            if (preferencesWereAsExpected) {
                if (lpDebug & 1) cout << "No need to solve LP - STP is sufficient\n";
                if (paranoia) {
                    #ifndef NDEBUG
                    if (Globals::paranoidScheduling) {
                        assert(!cd || cd->checkItContainsAllTheseEdges(theState.temporalConstraints));
                    }
                    #endif
                    shouldSucceed = true;
                    shouldFail = false;
                } else {
                    lp = 0; solved = true; return;
                }
            } else {
                if (lpDebug & 1) {
                    cout << "The STP could be scheduled, but not all preference dummy steps were necessarily supported as expected - using a MIP\n";
                    if (paranoia) {
                        shouldSucceed = true;
                        shouldFail = false;
                    }
                }
            }
        } else {
            #ifndef NDEBUG
            if (Globals::paranoidScheduling) {
                assert(!cd || cd->checkItContainsAllTheseEdges(theState.temporalConstraints));
            }
            #endif
        }

        if (cd) {                            
            if (!paranoia) {
                cd->distsToLPStamps();
                cd->distsToLPMinStamps();                
            }

            cd->letTheLPSetTimestamps();
        }
    }



    if (paranoia && lpDebug) {
        if (shouldSucceed) cout << "*** Should now succeed ***\n";
        if (shouldFail) cout << "*** Should now fail ***\n";
    }

    planAsAVector.resize(tsVarCount, (FFEvent*) 0);

    /* Number of remaining unvisited ancestors for each step */
    vector<int> fanIn(tsVarCount, 0);

    /* The steps that necessarily follow each step in the plan */
    vector<map<int, bool> > fanOut(tsVarCount);


    /* For each step in the plan, this records a mapping between state
     * variables, and the invariants involving that variable that begun at
     * that time step.  The idea, then, is if we are at a step that follows
     * I, and are changing variable v, we need to check any constraints
     * from this invariantsThisStepStartsOnVariableI[I][v].
     */
    vector<map<int, ConstraintSet > > invariantsThisStepStartsOnVariableI(tsVarCount);

    /* We use this to push forwards which active ancestors a given step has,
     * i.e. actions which have started but not yet finished.  For each of
     * these, we use the previous action starts (and the effects of the current
     * step) to determine which invariants we need to add as constraints
     * over the step's fluent vector.
     */
    vector<set<int> > activeAncestorsOfStep(tsVarCount);

    /* This is used to record whether the corresponding end of a start action
     * at the indexed step has been added to the LP.  If so, its invariants
     * have expired.  This is used in combination with the previous variable.
     */
    vector<bool> correspondEndHasBeenInserted(tsVarCount,false);
    
    /*
     * Step that comes after all future end actions.  -1 if we don't need this constraint
     * (i.e. we aren't imposing a strict total order.  @see TotalOrderTransformer
     */
    const int stepThatMustPrecedeFutureEnds = MinimalState::getTransformer()->stepThatMustPrecedeUnfinishedActions(theState.temporalConstraints);

    map<int, bool> fakeEdgeForThis;
    if (stepThatMustPrecedeFutureEnds != -1) {
        fakeEdgeForThis.insert(make_pair(stepThatMustPrecedeFutureEnds, true));
    }

    list<int> openList;
    int imaginaryEnds = 0;

    int mustVisit = 0;
    {
        int stepID = 0;
        for (int pass = 0; pass < 2; ++pass) {
            list<FFEvent> & currList = (pass ? now : header);

            list<FFEvent>::iterator citr = currList.begin();
            const list<FFEvent>::iterator cend = currList.end();

            for (; citr != cend; ++citr, ++stepID, ++mustVisit) {

                planAsAVector[stepID] = &(*citr);
                
                if (!(citr->time_spec == Planner::E_AT && citr->divisionID < 0)) {
                    if (citr->lpMaxTimestamp == DBL_MAX || citr->lpMaxTimestamp == -1.0) {
                        citr->lpMaxTimestamp = LPinfinity;
                    }
                    
                    if (citr->lpMinTimestamp < 0.0) {
                        citr->lpMinTimestamp = 0.0;
                    }
                }
                //if (citr->time_spec == Planner::E_AT_START && TemporalAnalysis::canSkipToEnd(citr->action->getID())) ++imaginaryEnds;

                if (pass && citr->isDummyStep()) {
                    newDummySteps.insert(make_pair(stepID,make_pair(-1, std::numeric_limits<double>::signaling_NaN() )));
                }                        
                
                const map<int, bool> * const stepsThatComeBeforeThisOne = theState.temporalConstraints->stepsBefore(stepID);

                if (stepsThatComeBeforeThisOne) {
                    assert(citr->time_spec != Planner::E_AT || citr->divisionID >= 0);
                    
                    fanIn[stepID] = stepsThatComeBeforeThisOne->size();
                    if (lpDebug & 512) {
                        cout << fanIn[stepID] << " recorded steps precede " << stepID << ": [";
                    }
                    map<int, bool>::const_iterator cbItr = stepsThatComeBeforeThisOne->begin();
                    const map<int, bool>::const_iterator cbEnd = stepsThatComeBeforeThisOne->end();
                    for (; cbItr != cbEnd; ++cbItr) {
                        if (lpDebug & 512) cout << " " << cbItr->first;
                        fanOut[cbItr->first].insert(make_pair(stepID, cbItr->second));
                    }
                    if (lpDebug & 512) cout << " ]\n";
                }

                /*if (citr->time_spec == Planner::E_AT_END) {
                    ++fanIn[stepID];
                    fanOut[citr->pairWithStep].insert(make_pair(stepID, false));
                }*/


                if (citr->time_spec == Planner::E_AT_END && !citr->getEffects
                        && stepThatMustPrecedeFutureEnds != -1
                        && citr->pairWithStep != stepThatMustPrecedeFutureEnds) {

                    // For the ends of all actions that have not yet finished - if we're using
                    // a total order, these must come after the step just added

                    if (fanOut[stepThatMustPrecedeFutureEnds].insert(make_pair(stepID, true)).second) {
                        if (lpDebug & 512) {
                            cout << "Additionally, the TO constraint means " << stepThatMustPrecedeFutureEnds << " precedes " << stepID << endl;
                        }

                        ++fanIn[stepID];
                    } else {
                        if (lpDebug & 512) {
                            cout << "The TO constraint means " << stepThatMustPrecedeFutureEnds << " precedes " << stepID << ", as it already was doing\n";
                        }                        
                    }
                    
                }

                if (!fanIn[stepID]) {
                    if (lpDebug & 512) cout << "No steps precede " << stepID << " - adding to open list\n";
                    openList.push_back(stepID);
                }

                if (   citr->time_spec == Planner::E_AT_END
                    && citr->getEffects == false
                    && RPGBuilder::getRPGDEs(citr->action->getID()).back()->fixed.empty()) {

                    ++imaginaryEnds;

                }
            }
        }
    }
    #ifndef NDEBUG

    {
        const int planLength = planAsAVector.size();
        for (int ps = 0; ps < planLength; ++ps) {
            if (!fanOut[ps].empty() && planAsAVector[ps]->time_spec == Planner::E_AT && planAsAVector[ps]->divisionID < 0) {
                std::cerr << "Error: edges go back into " << ps << ", an abstracted TIL on " << *(RPGBuilder::getLiteral(-1-planAsAVector[ps]->divisionID)) << endl;
                map<int,bool>::const_iterator foItr = fanOut[ps].begin();
                const map<int,bool>::const_iterator foEnd = fanOut[ps].end();
                
                for (; foItr != foEnd; ++foItr) {
                    cout << "- From step " << foItr->first << "\n";
                }
                assert(!(!fanOut[ps].empty() && planAsAVector[ps]->time_spec == Planner::E_AT && planAsAVector[ps]->divisionID < 0));
            }
                
        }
    }
    
    #endif
    
    if (lpDebug & 1) cout << "Making lp for " << tsVarCount << " events, " << imaginaryEnds << " future max events, and " << numVars << " variables\n";
    //if (lpDebug & 1) cout << "Making lp for " << tsVarCount << " events and " << numVars << " variables\n";

    lp = getNewSolver();
    lp->addEmptyRealCols(tsVarCount + numVars + imaginaryEnds);

    int nextImaginaryEndVar = tsVarCount + numVars;

    if (!(lpDebug & 4)) lp->hush();

    const int optVar = (justAppliedStep != -1 ? numVars + justAppliedStep : -1);

    if (optVar != -1) lp->setObjCoeff(optVar, 1.0);

    // make the last real action as early as possible

    if (lpDebug & 1) cout << "Objective function to minimise variable " << optVar << "\n";

    previousObjectiveVar = optVar;

    finalNumericVars = vector<FluentTracking>(numVars);

    for (int i = 0; i < numVars; ++i) {
        finalNumericVars[i] = FluentTracking(initialValues[i]);
        
        if (NumericAnalysis::getDominanceConstraints()[i] == NumericAnalysis::E_IRRELEVANT) {
            finalNumericVars[i].statusOfThisFluent = FluentTracking::FS_IGNORE;
        } else if (NumericAnalysis::getDominanceConstraints()[i] == NumericAnalysis::E_METRICTRACKING) {
            if (setObjectiveToMetric || Globals::optimiseSolutionQuality) {
                if (NumericAnalysis::getDataOnWhichVariablesHaveOrderIndependentEffects()[i] != NumericAnalysis::E_ORDER_DEPENDENT) {
                    finalNumericVars[i].statusOfThisFluent = FluentTracking::FS_ORDER_INDEPENDENT;
                    if (lpDebug & 1) {
                        cout << "Objective set to metric: keeping variable " << *(RPGBuilder::getPNE(i)) << ", but making it order-independent\n";
                    }                    
                } else {
                    if (lpDebug & 1) {
                        cout << "Objective set to metric: keeping variable " << *(RPGBuilder::getPNE(i)) << "\n";
                    }                    
                }
            } else {                
                finalNumericVars[i].statusOfThisFluent = FluentTracking::FS_IGNORE;
                if (lpDebug & 1) {
                    cout << "Objective not set to metric: ignoring metric-tracking variable " << *(RPGBuilder::getPNE(i)) << "\n";
                }                    
                
            }
        }

        if (finalNumericVars[i].statusOfThisFluent != FluentTracking::FS_IGNORE) {
            if (initialGradients[i] != 0.0) {
                ++(finalNumericVars[i].activeGradientCount);
                finalNumericVars[i].activeGradient += initialGradients[i];
                finalNumericVars[i].lastEffectTimestampVariable = -1;
                stableVariable[i] = false;
                    
                if (lpDebug & 1) {
                    cout << "Variable " << *(RPGBuilder::getPNE(i)) << " becomes unstable due to process; gradient is now " << initialGradients[i] << "\n";
                }

            }
        }
        
    }

    timestampVars.reserve(tsVarCount);

    vector<EndDetails> imaginaryMinMax(tsVarCount);

    vector<ValueOfVariablesAtSomeTime> fluentsAtStep(tsVarCount);

    vector<int> correspondingStart(tsVarCount);

//    endsOfSkippableActions = vector<int>(tsVarCount,-1);

    nameLPElements = (lpDebug || Globals::globalVerbosity & 32);

    for (int i = 0; i < numVars; ++i) {
        const double curr = initialValues[i];
        lp->setColLower(i, curr);
        lp->setColUpper(i, curr);

        if (nameLPElements) {
            ostringstream namestream;
            namestream << *(RPGBuilder::getPNE(i));
            namestream << "[0.000]";
            string asString = namestream.str();
            lp->setColName(i, asString);
        }
    }

    int nextTIL = 0;
//    double TILupbo = TILtimestamps[nextTIL];


    bool boundNow = false;


//    int stepID = 0;
//    int currVar = numVars;
//    map<int, pair<int, double> > activeGradients;
//    map<int, list<Constraint*>* > activeInvariants;

    map<int, int> outstandingCTS;

    list<int> stableNextTime;

    vector<double> unassignedLowerBounds(tsVarCount, 0.0);

    makespanVarMinimum = 0.0;

    timestampToUpdate = 0;
    timestampToUpdatePartner = 0;

    bool partnerIsEarlier = false;

    timestampToUpdateVar = -1;
    timestampToUpdateStep = -1;
    timestampToUpdatePartnerVar = -1;
    timestampToUpdatePartnerStep = -1;
    
    timestampToUpdateVarLB = -1.0;
    
    const vector<RPGBuilder::FakeTILAction*> & tilVec = RPGBuilder::getNonAbstractedTILVec();
    
    if (lpDebug & 1) {
        cout << "Building LP for " << tsVarCount << " step vars: a plan comprising " << header.size() << " header actions and " << now.size() << " new actions.\n";
    }
    
    int actuallyVisited = 0;

    vector<vector<int> > variablesCorrespondingToNNFNodesForDummyStep;
    vector<NNFDependencies> dummyStepDependencies;
    
    map<int, list<VarsForTrigger> > partOneOfPrefWasAtStep;
    map<int, list<VarsForRequirement> > partZeroOfPrefWasAtStep;
    
    const vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getPreferences();
    
    if (!prefs.empty()) {
        
        const list<int> & nonDefaults = PreferenceHandler::getPreferencesInNonDefaultPositionsInitially();
        
        list<int>::const_iterator ndItr = nonDefaults.begin();
        const list<int>::const_iterator ndEnd = nonDefaults.end();
        
        for (; ndItr != ndEnd; ++ndItr) {
            
            const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[*ndItr];   
            
            if (pref.cons == VAL::E_ALWAYSWITHIN || pref.cons == VAL::E_SOMETIMEAFTER) {
                if (PreferenceHandler::getInitialAutomataPositions()[*ndItr] == AutomatonPosition::triggered) {
                    
                    // the master column that says the sometime-after is currently unsatisfied if any of the instances of it are
                    lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                    const int currCol = lp->getNumCols() - 1;
                    const map<int, VarsForPreference>::iterator prefVars = varsForPreference.insert(make_pair(*ndItr,VarsForPreference(-1, currCol))).first;
                        
                    {
                        static vector<pair<int,double> > basicSometimeAfterConstraint(1);
                        basicSometimeAfterConstraint[0].first = currCol;
                        basicSometimeAfterConstraint[0].second = BIG;
                        lp->addRow(basicSometimeAfterConstraint, 0.0, LPinfinity);
                    }
                    
                    prefVars->second.committedRow = lp->getNumRows() - 1;
                    
                    const int & cr = prefVars->second.committedRow;
                                                
                    static vector<pair<int,double> > isThisTriggerClosed(1);
                    isThisTriggerClosed[0] = make_pair(cr, -1.0);
                    lp->addCol(isThisTriggerClosed, 0.0, -1.0, MILPSolver::C_BOOL);
                    
                    const int localCol = lp->getNumCols() - 1;

                    static vector<pair<int,double> > localPairOfEntries(2);
                    
                    localPairOfEntries[0] = make_pair(prefVars->second.committedCostVar, 1.0);
                    localPairOfEntries[1] = make_pair(localCol, -1.0);
                    lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                    
                    
                    // now add a disjunctive satisfaction row for this trigger
                    
                    static vector<pair<int,double> > basicSometimeAfterConstraint(1);
                    basicSometimeAfterConstraint[0] = make_pair(localCol, -1.0);                            
                    lp->addRow(basicSometimeAfterConstraint, -LPinfinity, -1.0);
                                                
                    
                    partOneOfPrefWasAtStep[*ndItr].push_back(VarsForTrigger(-1, localCol, lp->getNumRows() - 1));
                    
                }                
            }
            
        }
        
        variablesCorrespondingToNNFNodesForDummyStep.resize(tsVarCount);
        dummyStepDependencies.resize(tsVarCount);
        
        int stepID = 0;
        for (int pass = 0; pass < 2; ++pass) {
            list<FFEvent> & currList = (pass ? now : header);
            
            list<FFEvent>::iterator citr = currList.begin();
            const list<FFEvent>::iterator cend = currList.end();
            
            for (; citr != cend; ++citr, ++stepID) {
                
                if (!citr->isDummyStep()) {
                    continue;
                }
                
                if (citr->time_spec != Planner::E_DUMMY_PREFERENCE_PRECONDITION) {
                    if (preferenceStatus[citr->divisionID] == AutomatonPosition::unreachable) {
                        continue;
                    }
                }
                
                const int part = (citr->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE ? 1 : 0);                
                assert(citr->time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                
                if (!prefs[citr->divisionID].d->nodes[part].first) {                    
                    continue;                    
                }
                
                const bool wantToSatisfy = (    citr->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE
                                             || citr->time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION
                                             || citr->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE );
                
                assert(wantToSatisfy || prefs[citr->divisionID].cons == VAL::E_ATMOSTONCE);
                
                NNF_Flat * const currNNF = RPGBuilder::getPreferences()[citr->divisionID].d->flattened[part];
                assert(currNNF); // must be true, or else the NNF node check above would have called continue
                
                vector<int> & toUpdate = variablesCorrespondingToNNFNodesForDummyStep[stepID];                
                
                const int nodeCount = currNNF->getCellCount();
                toUpdate.resize(nodeCount);
                
                const NNF_Flat::Cell * const cells = currNNF->getCells();
                
                vector<int> constraintForSettingInnerNodeFromChildren(currNNF->getInteriorNodeCount());
                vector<int> constraintForSettingChildrenFromInnerNode(currNNF->getInteriorNodeCount());
                
                for (int c = 0; c < nodeCount; ++c) {

                    if (cells[c].isCell()) {
                        const int parentCell = currNNF->getParentIDs()[c];
                        
                        if (parentCell == -1) {
                            // special case: a single-fact NNF tree
                            // do nothing
                            
                            lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);                            
                            toUpdate[c] = lp->getNumCols() - 1;
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "s" << stepID << RPGBuilder::getPreferences()[citr->divisionID].name << "singleouter" << c;
                                lp->setColName(toUpdate[c], s.str());
                            }
                                                                                                                            
                        } else {                        
                            
                            if (cells[c].lit) {
                                if (cells[c].polarity == wantToSatisfy) {
                                    dummyStepDependencies[stepID].literals[cells[c].lit->getStateID()].push_back(c);
                                } else {
                                    dummyStepDependencies[stepID].negativeLiterals[cells[c].lit->getStateID()].push_back(c);
                                }
                            } else if (cells[c].num >= 0) {
                                
                                const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[cells[c].num];
                                
                                if (currPre.LHSVariable < RPGBuilder::getPNECount()) {
                                    dummyStepDependencies[stepID].numerics[currPre.LHSVariable].insert(c);
                                } else if (currPre.LHSVariable < 2 * RPGBuilder::getPNECount()) {
                                    dummyStepDependencies[stepID].numerics[currPre.LHSVariable - RPGBuilder::getPNECount()].insert(c);
                                } else {
                                    const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                                    
                                    for (int s = 0; s < currAV.size; ++s) {
                                        if (currAV.fluents[s] < RPGBuilder::getPNECount()) {
                                            dummyStepDependencies[stepID].numerics[currAV.fluents[s]].insert(c);
                                        } else {
                                            dummyStepDependencies[stepID].numerics[currAV.fluents[s] - RPGBuilder::getPNECount()].insert(c);
                                        }
                                    }
                                }
                                
                            }
                            
                            if (wantToSatisfy ? currNNF->cellIsAnAnd()[parentCell]
                                              : !currNNF->cellIsAnAnd()[parentCell]  ) {
                                
                                // for the and case, we have a constraint saying
                                // big * and-truth-value >= c1 + c2 + c3 + c4 + ...                                                                
                                // thus, if any child constraint is non-satisfied, the and must be registered as being non-satisfied
                                // i.e. big * and-truth-value - c1 - c2 .... >= 0
                                                                
                                // so, for this, we need to add an entry to the LHS of this constraint
                                vector<pair<int,double> > localEntries(2);
                                localEntries[0] = make_pair(constraintForSettingInnerNodeFromChildren[parentCell], -1.0);
                                
                                
                                // next, we have a constraint ensuring that if the and node is set to 1, at least one of its children is set to 1,
                                // thereby ensuring its falseness.  this constraint is of the form:
                                // c1 + c2 + c3 + c4 >= and-truth-value
                                
                                localEntries[1] = make_pair(constraintForSettingChildrenFromInnerNode[parentCell], 1.0);
                                
                                lp->addCol(localEntries, 0, 1, MILPSolver::C_BOOL);
                                toUpdate[c] = lp->getNumCols() - 1;
                            } else {
                                
                                // for the or case, second, we have a constraint saying
                                // (1 - or-truth-value) <= (1 - c1) + (1 - c2 )+ (1 - c3) + ...                                
                                // i.e. assuming the or holds (value 0) means at least one of the children holds
                                
                                // rewrite this as
                                // -or-truth-value <= -1 + number of children - c1 - c2 - c3 - c4 - ...
                                // c1 + c2 + c3 + c4 - or-truth-value <= number of children - 1
                                
                                // update LHS of inequality
                                vector<pair<int,double> > localEntries(1, make_pair(constraintForSettingInnerNodeFromChildren[parentCell], 1.0));
                                lp->addCol(localEntries, 0, 1, MILPSolver::C_BOOL);
                                toUpdate[c] = lp->getNumCols() - 1;
                                
                                // update RHS of inequality
                                const double newBound = lp->getRowUpper(constraintForSettingInnerNodeFromChildren[parentCell]) + 1.0;                                
                                lp->setRowUpper(constraintForSettingInnerNodeFromChildren[parentCell], newBound);
                                
                                // second, quite simply:
                                // child n >= or-truth-value
                                // so if the or is unsatisfied (1), the child is unsatisfied (1); otherwise, we don't care either way
                                
                                vector<pair<int,double> > simpleConstraint(2);
                                simpleConstraint[0] = make_pair(toUpdate[c], 1.0);
                                simpleConstraint[1] = make_pair(toUpdate[parentCell], -1.0);
                                lp->addRow(simpleConstraint, 0.0, LPinfinity);
                                
                                
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "s" << stepID << "orparent" << parentCell << "of" << c;
                                    lp->setRowName(lp->getNumRows() - 1, s.str());
                                }
                            }
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "s" << stepID << RPGBuilder::getPreferences()[citr->divisionID].name << "outer" << c;
                                lp->setColName(toUpdate[c], s.str());
                            }  
                        }
                        
                    } else {
                        
                        // it's an and node or an or node
                        // in both cases we need a variable to denote its truth value (0 = satisfied)
                        
                        lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);                      
                        toUpdate[c] = lp->getNumCols() - 1;
                        
                        if (nameLPElements) {
                            ostringstream s;
                            s << "s" << stepID << "inner" << c;
                            lp->setColName(toUpdate[c], s.str());
                        }
                        
                        if (wantToSatisfy ? currNNF->cellIsAnAnd()[c] : !currNNF->cellIsAnAnd()[c]) {                            
                            vector<pair<int,double> > localEntries(1, make_pair(toUpdate[c], nodeCount));
                            lp->addRow(localEntries, 0.0, LPinfinity);
                            constraintForSettingInnerNodeFromChildren[c] = lp->getNumRows() - 1;
                            
                            localEntries[0].second = -1.0;
                            
                            lp->addRow(localEntries, 0.0, LPinfinity);
                            constraintForSettingChildrenFromInnerNode[c] = lp->getNumRows() - 1;
                            
                            if (nameLPElements)  {
                                ostringstream s;
                                s << "s" << stepID << RPGBuilder::getPreferences()[citr->divisionID].name << "andconsone" << c << "b";
                                lp->setRowName(constraintForSettingChildrenFromInnerNode[c], s.str());
                            }
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "s" << stepID << RPGBuilder::getPreferences()[citr->divisionID].name << "andconstwo" << c;
                                lp->setRowName(constraintForSettingInnerNodeFromChildren[c], s.str());
                            }
                        } else {
                            vector<pair<int,double> > localEntries(1, make_pair(toUpdate[c], -1.0));
                            lp->addRow(localEntries,-LPinfinity, -1);
                            constraintForSettingInnerNodeFromChildren[c] = lp->getNumRows() - 1;                                                        
                            constraintForSettingChildrenFromInnerNode[c] = -1; // in the OR case, this has to be one constraint per OR--child relationship
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "s" << stepID << RPGBuilder::getPreferences()[citr->divisionID].name << "orcons" << c;
                                lp->setRowName(constraintForSettingInnerNodeFromChildren[c], s.str());
                            }
                        }
                        
                          
                    }
                    
                }
                

            }
            
        }
    }
    
    while (!openList.empty()) {

        ++actuallyVisited;

        const int stepID = openList.front();
        openList.pop_front();

        const int currVar = numVars + stepID;


        FFEvent & currEvent = *(planAsAVector[stepID]);

        
        const int actID = (currEvent.action ? currEvent.action->getID() : -1);
        const Planner::time_spec currTS = currEvent.time_spec;
        const int divisionID = currEvent.divisionID;

        if (currVar == optVar) {
            timestampToUpdate = &currEvent;
            timestampToUpdateVar = currVar;
            timestampToUpdateStep = stepID;

            if (actID != -1 && !RPGBuilder::getRPGDEs(actID).empty()) {
                if (currTS == Planner::E_AT_START) {
                    timestampToUpdatePartner = planAsAVector[stepID + 1];
                    timestampToUpdatePartnerStep = stepID + 1;
                    timestampToUpdatePartnerVar = numVars + stepID + 1;
                    partnerIsEarlier = false;
                } else {
                    timestampToUpdatePartner = planAsAVector[stepID - 1];
                    timestampToUpdatePartnerStep = stepID - 1;
                    timestampToUpdatePartnerVar = numVars + stepID - 1;
                    partnerIsEarlier = true;
                }
            }
        }
                                                
        if (currEvent.isDummyStep()) {
            map<int,pair<int,double> >::iterator ndsItr = newDummySteps.find(stepID);
            if (ndsItr != newDummySteps.end()) {
                ndsItr->second.first = currVar;
            }
        }

        const map<int, bool> * const stepsThatComeBeforeThisOne = theState.temporalConstraints->stepsBefore(stepID);

//        const bool implicitEnd = (currTS == Planner::E_AT_START && TemporalAnalysis::canSkipToEnd(actID));

        if (currTS == Planner::E_AT && divisionID < 0) {
            map<int, AbstractFactConstraintBlock>::iterator blockItr = planStepForAbstractFact.find(-1 - divisionID);
            if (blockItr == planStepForAbstractFact.end()) {
                blockItr = planStepForAbstractFact.insert(make_pair(-1 - divisionID, AbstractFactConstraintBlock(-1 - divisionID, lp, numVars, boundsForAbstractFactOccurrences.find(-1 - divisionID)->second))).first;
            }
            blockItr->second.setPlanStepBoundsAreDefinedAt(stepID, planAsAVector[stepID]->lpMinTimestamp == DBL_MAX);
            
        }

        if (lpDebug & 1) {
            cout << COLOUR_light_cyan << "Adding action ";
            if (currEvent.isDummyStep()) {
                if (currEvent.time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION) {
                    cout << "that is a dummy for a preference precondition " << RPGBuilder::getPreferences()[currEvent.divisionID].name  << " on step " << currEvent.divisionID << endl;
                } else if (currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE && RPGBuilder::getPreferences()[currEvent.divisionID].cons == VAL::E_ALWAYSWITHIN) {
                    cout << "that is a dummy corresponding to a triggering of always-within preference " << RPGBuilder::getPreferences()[currEvent.divisionID].name << ":" << currEvent.divisionID << " by step " << currEvent.pairWithStep << endl;
                } else if (currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                    cout << "that is a dummy for triggering preference " << RPGBuilder::getPreferences()[currEvent.divisionID].name << ":" << currEvent.divisionID << "\n";
                } else if (currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_FALSE) {
                    cout << "that is a dummy for unsatisfying preference " << RPGBuilder::getPreferences()[currEvent.divisionID].name << ":" << currEvent.divisionID << "\n";
                } else {
                    assert(currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE);
                    cout << "that is a dummy for satisfying preference " << RPGBuilder::getPreferences()[currEvent.divisionID].name << ":" << currEvent.divisionID << "\n";
                }
            } else if (actID != -1) {
                cout << *(currEvent.action) << " ";
                if (currTS == Planner::E_AT_START) {
                    cout << "start\n";
                } else if (currTS == Planner::E_AT_END) {
                    if (currEvent.getEffects) {
                        cout << "end\n";
                    } else {
                        cout << "end placeholder\n";
                    }
                } else {
                    cout << "intermediate point " << divisionID << "\n";
                }

            } else {
                if (divisionID >= 0) {
                    cout << " for TIL " << divisionID << "\n";
                } else {
                    cout << " as a placeholder for the lower bounds on when an abstracted fact " << *(RPGBuilder::getLiteral(-1 - divisionID))  << " can be obtained\n";
                }
            }
            cout << COLOUR_default;
        }

        if (nameLPElements) {
            ostringstream namestream;
            namestream << stepID << ": ";
            if (currEvent.isDummyStep()) {
                namestream << "dummy" << RPGBuilder::getPreferences()[currEvent.divisionID].name;
            } else if (actID != -1) {
                namestream << *(currEvent.action) << " ";
                if (currTS == Planner::E_AT_START) {
                    namestream << "S";
                } else if (currTS == Planner::E_AT_END) {
                    namestream << "E";
                } else {
                    namestream << "I" << divisionID;
                }
            } else {
                if (divisionID >= 0) {
                    namestream << "TIL" << divisionID;
                } else {
                    namestream << "AF" << -1 - divisionID;
                }             
            }

            string asString = namestream.str();
            lp->setColName(currVar, asString);
            if (lpDebug & 1) cout << "C" << currVar << " becomes " << asString << "\n";
        }


        if (!currEvent.isDummyStep() && currEvent.getEffects) {
            list<int>::iterator sntItr = stableNextTime.begin();
            const list<int>::iterator sntEnd = stableNextTime.end();

            for (; sntItr != sntEnd; ++sntItr) {
                if (lpDebug & 1) cout << "--- Variable " << *(RPGBuilder::getPNE(*sntItr)) << " becomes stable ---\n";
                stableVariable[*sntItr] = true;
                //durationalVary.erase(*sntItr);
            }

            stableNextTime.clear();

        }


        if (currTS == Planner::E_AT_START) {
            correspondingStart[stepID] = stepID;            
        } else if (currTS == Planner::E_AT_END) {
            correspondingStart[stepID] = correspondingStart[currEvent.pairWithStep];
            //correspondEndHasBeenInserted[currEvent.pairWithStep] = true;
        }

        if (currEvent.isDummyStep()) {

            if (currEvent.time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION || preferenceStatus[currEvent.divisionID] != AutomatonPosition::unreachable) {
                
                const vector<int> & varsForNNFCells = variablesCorrespondingToNNFNodesForDummyStep[stepID];
                
                const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[currEvent.divisionID];
                
                map<int,pair<int,bool> > factAfterStep;
                map<int,pair<int,bool> > negativeFactAfterStep;
                map<int,pair<int,bool> > fluentAfterStep;
                
                
                
                // time for some magic - look at the temporal constraints on this step, and figure out why they're there
                            
                if (stepsThatComeBeforeThisOne && (pref.cons != VAL::E_ALWAYSWITHIN || currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE)) {
                    
                    map<int, set<int> > fanOut;
                    map<int, int> fanIn;
                                    
                    list<pair<int,bool> > backList;
                    
                    {
                        map<int, bool>::const_iterator beforeItr = stepsThatComeBeforeThisOne->begin();
                        const map<int, bool>::const_iterator beforeEnd = stepsThatComeBeforeThisOne->end();
                        
                        for (; beforeItr != beforeEnd; ++beforeItr) {
                            fanOut.insert(make_pair(beforeItr->first, set<int>()));
                        }
                    }
                        
                        
                    list<int> visitForwards;
                    
                    backList.insert(backList.end(), stepsThatComeBeforeThisOne->begin(), stepsThatComeBeforeThisOne->end());
                    
                    while (!backList.empty()) {
                                            
                        const map<int, bool> * const currentPredecessors = theState.temporalConstraints->stepsBefore(backList.front().first);
                        
                        if (currentPredecessors) {
                            int & toIncrement = fanIn.insert(make_pair(backList.front().first, 0)).first->second;
                            
                            map<int, bool>::const_iterator beforeItr = currentPredecessors->begin();
                            const map<int, bool>::const_iterator beforeEnd = currentPredecessors->end();
                            
                            for (; beforeItr != beforeEnd; ++beforeItr) {
                                if (planAsAVector[beforeItr->first]->isDummyStep()) {
                                    continue;
                                }
                                pair<map<int, set<int> >::iterator,bool> insPair = fanOut.insert(make_pair(beforeItr->first, set<int>()));
                                if (insPair.second) {
                                    backList.push_back(*beforeItr);
                                }
                                insPair.first->second.insert(backList.front().first);
                                ++toIncrement;
                            }
                            
                            if (!toIncrement) {
                                visitForwards.push_back(backList.front().first);
                            }
                        } else {
                            fanIn.insert(make_pair(backList.front().first, 0));
                            visitForwards.push_back(backList.front().first);
                        }
                        
                        backList.pop_front();
                        
                    }
                    
                    // now recreate the available facts/find the most recent step to touch a given numeric variable
                    
                    while (!visitForwards.empty()) {
                        
                        const int effStep = visitForwards.front();
                        const FFEvent * const evt = planAsAVector[effStep];
                        
                        const list<Literal*> * adds = 0;
                        const list<Literal*> * dels = 0;
                        const list<int> * nums = 0;
                        
                        switch (evt->time_spec) {
                            case Planner::E_AT_START: {
                                adds = &(RPGBuilder::getStartPropositionAdds()[evt->action->getID()]);
                                dels = &(RPGBuilder::getStartPropositionDeletes()[evt->action->getID()]);
                                nums = &(RPGBuilder::getStartEffNumerics()[evt->action->getID()]);
                                break;
                            }
                            case Planner::E_AT_END: {
                                adds = &(RPGBuilder::getEndPropositionAdds()[evt->action->getID()]);
                                dels = &(RPGBuilder::getEndPropositionDeletes()[evt->action->getID()]);
                                nums = &(RPGBuilder::getEndEffNumerics()[evt->action->getID()]);
                                break;
                            }
                            case Planner::E_AT: {
                                adds = &(RPGBuilder::getNonAbstractedTILVec()[evt->divisionID]->addEffects);
                                dels = &(RPGBuilder::getNonAbstractedTILVec()[evt->divisionID]->delEffects);
                                nums = 0;
                                break;
                            }
                            default: {
                                // edge via a dummy step
                                assert(evt->isDummyStep());
                            }
                        }
                           
                        if (dels) {
                            list<Literal*>::const_iterator delItr = dels->begin();
                            const list<Literal*>::const_iterator delEnd = dels->end();

                            for (; delItr != delEnd; ++delItr) {

                                negativeFactAfterStep[(*delItr)->getStateID()] = make_pair(effStep, true);
                                factAfterStep.erase((*delItr)->getStateID());

                            }
                        }
                                                                                       
                        if (adds) {
                            list<Literal*>::const_iterator addItr = adds->begin();
                            const list<Literal*>::const_iterator addEnd = adds->end();
                            
                            for (; addItr != addEnd; ++addItr) {
                                
                                factAfterStep[(*addItr)->getStateID()] = make_pair(effStep, true);
                                negativeFactAfterStep.erase((*addItr)->getStateID());
                                
                            }
                        }
                        
                        if (nums) {
                            list<int>::const_iterator neItr = nums->begin();
                            const list<int>::const_iterator neEnd = nums->end();
                        
                        
                            for (; neItr != neEnd; ++neItr) {
                                fluentAfterStep[RPGBuilder::getNumericEff()[*neItr].fluentIndex] = make_pair(effStep, true);
                            }
                        }
                        
                        map<int, set<int> >::const_iterator foItr = fanOut.find(effStep);
                        if (foItr != fanOut.end()) {
                            
                            set<int>::const_iterator sItr = foItr->second.begin();
                            const set<int>::const_iterator sEnd = foItr->second.end();
                            
                            for (; sItr != sEnd; ++sItr) {
                                
                                if (!(--(fanIn[*sItr]))) {
                                    visitForwards.push_back(*sItr);
                                }
                                
                            }
                            
                        }
                        
                        visitForwards.pop_front();
                    }
                    
                }
                

                static const bool prefSupportDebug = (lpDebug & 1);
                            
                // now we have fact and numeric variable annotations, indicating after which step they should come
                // NB if a fact was never added or deleted, we must check if it was in the initial state
                
                const int part = (currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE ? 1 : 0);
                
                assert(currEvent.time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                
                const bool wantToSatisfy = (    currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE
                                             || currEvent.time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION
                                             || currEvent.time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE);
                
                assert(wantToSatisfy || prefs[currEvent.divisionID].cons == VAL::E_ATMOSTONCE);
                
                if (prefs[currEvent.divisionID].d->nodes[part].first) {                    
                    NNF_Flat * const currNNF = RPGBuilder::getPreferences()[currEvent.divisionID].d->flattened[part];
                    
                    assert(currNNF);
                    
                    const int nodeCount = currNNF->getCellCount();
                    const NNF_Flat::Cell * const cells = currNNF->getCells();
                    
                    for (int c = 0; c < nodeCount; ++c) {                
                    
                        bool canBeSatisfied = false;
                        set<int> satisfiedByOrderingAfter;
                        
                        if (cells[c].lit) {
                            const map<int, pair<int,bool> >::const_iterator factItr = factAfterStep.find(cells[c].lit->getStateID());
                            if (factItr != factAfterStep.end()) {
                                if (cells[c].polarity || !wantToSatisfy) {
                                    satisfiedByOrderingAfter.insert(factItr->second.first + numVars);
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << *(RPGBuilder::getLiteral(factItr->first)) << " can be";
                                        if (wantToSatisfy) {
                                            cout << " supported";
                                        } else {
                                            cout << " unsupported";
                                        }
                                        cout << " by ordering after " << lp->getColName(factItr->second.first + numVars) << COLOUR_default << endl;
                                    }
                                    canBeSatisfied = true;
                                } else {
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << "¬" << *(RPGBuilder::getLiteral(factItr->first)) << " cannot be ";
                                        if (wantToSatisfy) {
                                            cout << " supported";
                                        } else {
                                            cout << " unsupported";
                                        }                                    
                                        cout << " due to any deletors being before adder " << lp->getColName(factItr->second.first + numVars) << COLOUR_default << endl;
                                    }
                                }
                            } else {
                                const map<int, pair<int,bool> >::const_iterator negativeItr = negativeFactAfterStep.find(cells[c].lit->getStateID());
                               
                                if (negativeItr != negativeFactAfterStep.end()) {
                                    if (!cells[c].polarity || !wantToSatisfy) {
                                        satisfiedByOrderingAfter.insert(negativeItr->second.first + numVars);
                                        if (prefSupportDebug) {
                                            cout << COLOUR_yellow << "¬" << *(RPGBuilder::getLiteral(factItr->first)) << " can be ";
                                            if (wantToSatisfy) {
                                                cout << " supported";
                                            } else {
                                                cout << " unsupported";
                                            }                                        
                                            cout << " by ordering after " << lp->getColName(negativeItr->second.first + numVars) << COLOUR_default << endl;
                                        }
                                        
                                        canBeSatisfied = true;
                                    } else {
                                        if (prefSupportDebug) {
                                            cout << COLOUR_yellow << *(RPGBuilder::getLiteral(factItr->first)) << " cannot be ";
                                            if (wantToSatisfy) {
                                                cout << " supported";
                                            } else {
                                                cout << " unsupported";
                                            }                                        
                                            cout << " due to any adders being before deletor " << lp->getColName(negativeItr->second.first + numVars) << COLOUR_default << endl;
                                        }
                                    }
                                } else {
                                    
                                    // never been added, never been deleted - what about the initial state...

                                    if (initialFacts.find(cells[c].lit) != initialFacts.end()) {
                                        canBeSatisfied = (cells[c].polarity || !wantToSatisfy);                                    
                                        if (prefSupportDebug) {           
                                            if (cells[c].polarity) {
                                                cout << COLOUR_yellow << *(RPGBuilder::getLiteral(factItr->first));
                                                if (wantToSatisfy) {
                                                    cout << " supported:";
                                                } else {
                                                    cout << " unsupported:";
                                                }                                            
                                                cout << " not touched since initial state, and still true\n" << COLOUR_default;                                            
                                            } else {
                                                cout << COLOUR_yellow << "¬" << *(RPGBuilder::getLiteral(factItr->first)) << " cannot be";
                                                if (wantToSatisfy) {
                                                    cout << " supported:";
                                                } else {
                                                    cout << " unsupported:";
                                                }                                            
                                                cout << " true initially and not yet deleted\n" << COLOUR_default;                                            
                                            }
                                        }
                                            
                                    } else {
                                        canBeSatisfied = (!cells[c].polarity || !wantToSatisfy);                                    
                                        if (prefSupportDebug) {           
                                            if (!cells[c].polarity) {
                                                cout << COLOUR_yellow << "¬" << *(RPGBuilder::getLiteral(factItr->first));
                                                if (wantToSatisfy) {
                                                    cout << " supported:";
                                                } else {
                                                    cout << " unsupported:";
                                                }                                            
                                                cout << " not touched since initial state, and still false\n" << COLOUR_default;                                            
                                            } else {
                                                cout << COLOUR_yellow << *(RPGBuilder::getLiteral(factItr->first)) << " cannot be ";
                                                if (wantToSatisfy) {
                                                    cout << " supported:";
                                                } else {
                                                    cout << " unsupported:";
                                                }                                            
                                                cout << " false initially and not yet added\n" << COLOUR_default;                                            
                                            }
                                        }
                                    }

                                    
                                                                    
                                }
                                
                            } 
                        
                        } else if (cells[c].num != -1) {
                            const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[cells[c].num];
                            
                            if (prefSupportDebug) {
                                cout << COLOUR_yellow << "Finding support for " << currPre << COLOUR_default << endl;
                            }
                            double LHSvalue = 0.0;
                            
                            if (currPre.LHSVariable < RPGBuilder::getPNECount()) {
                                if (finalNumericVars[currPre.LHSVariable].lastEffectValueVariable != -1) {
                                    std::cerr << "Fatal internal error: using temporal preferences that depend on variable " << *(RPGBuilder::getPNE(currPre.LHSVariable));
                                    std::cerr << ", stored in column " << lp->getColName(finalNumericVars[currPre.LHSVariable].lastEffectValueVariable);
                                    std::cerr << ", so considered to be subject to continuous change\n";
                                    lp->writeLp("preference-continuous.lp");
                                    exit(1);
                                }
                                LHSvalue += finalNumericVars[currPre.LHSVariable].postLastEffectValue;                            
                                const int & vAfter = finalNumericVars[currPre.LHSVariable].lastEffectTimestampVariable;
                                if (vAfter != -1) {
                                    satisfiedByOrderingAfter.insert(vAfter);
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << *(RPGBuilder::getPNE(currPre.LHSVariable)) << " = " << finalNumericVars[currPre.LHSVariable].postLastEffectValue << ", ordered after " << lp->getColName(vAfter) << "\n" << COLOUR_default;
                                    }                                
                                } else {
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << *(RPGBuilder::getPNE(currPre.LHSVariable)) << " = " << finalNumericVars[currPre.LHSVariable].postLastEffectValue << ", and unchanged since the initial state\n" << COLOUR_default;
                                    }
                                }
                            } else if (currPre.LHSVariable < 2 * RPGBuilder::getPNECount()) {
                                if (finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].lastEffectValueVariable != -1) {
                                    std::cerr << "Fatal internal error: using temporal preferences that depend on variable " << *(RPGBuilder::getPNE(currPre.LHSVariable - RPGBuilder::getPNECount()));
                                    std::cerr << ", stored in column " << lp->getColName(finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].lastEffectValueVariable);
                                    std::cerr << ", which is subject to continuous change\n";
                                    lp->writeLp("preference-continuous.lp");
                                    exit(1);
                                }
                                LHSvalue -= finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].postLastEffectValue;
                                const int & vAfter = finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].lastEffectTimestampVariable;
                                if (vAfter != -1) {
                                    satisfiedByOrderingAfter.insert(vAfter);
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << *(RPGBuilder::getPNE(currPre.LHSVariable - RPGBuilder::getPNECount())) << " = " << finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].postLastEffectValue << ", ordered after " << lp->getColName(vAfter) << "\n" << COLOUR_default;
                                    }                                
                                } else {
                                    if (prefSupportDebug) {
                                        cout << COLOUR_yellow << *(RPGBuilder::getPNE(currPre.LHSVariable - RPGBuilder::getPNECount())) << " = " << finalNumericVars[currPre.LHSVariable - RPGBuilder::getPNECount()].postLastEffectValue << ", and unchanged since the initial state\n" << COLOUR_default << endl;
                                    }
                                }
                            } else {
                                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                                
                                LHSvalue += currAV.constant;
                                
                                for (int s = 0; s < currAV.size; ++s) {
                                    
                                    if (currAV.fluents[s] < RPGBuilder::getPNECount()) {
                                        if (finalNumericVars[currAV.fluents[s]].lastEffectValueVariable != -1) {
                                            std::cerr << "Fatal internal error: using temporal preferences that depend on variable " << *(RPGBuilder::getPNE(currAV.fluents[s])) << ", which is subject to continuous change\n";
                                            exit(1);
                                        }
                                        LHSvalue += finalNumericVars[currAV.fluents[s]].postLastEffectValue * currAV.weights[s];                            
                                        const int & vAfter = finalNumericVars[currAV.fluents[s]].lastEffectTimestampVariable;
                                        if (vAfter != -1) {
                                            satisfiedByOrderingAfter.insert(vAfter);
                                            if (prefSupportDebug) {
                                                cout << COLOUR_yellow << *(RPGBuilder::getPNE(currAV.fluents[s])) << " = " << finalNumericVars[currAV.fluents[s]].postLastEffectValue << ", ordered after " << lp->getColName(vAfter) << "\n" << COLOUR_default;
                                            }                                                                        
                                        } else {
                                            if (prefSupportDebug) {
                                                cout << COLOUR_yellow << *(RPGBuilder::getPNE(currAV.fluents[s])) << " = " << finalNumericVars[currAV.fluents[s]].postLastEffectValue << ", and unchanged since the initial state\n" << COLOUR_default;
                                            }                                
                                            
                                        }
                                    } else {
                                        if (finalNumericVars[currAV.fluents[s] - RPGBuilder::getPNECount()].lastEffectValueVariable != -1) {
                                            std::cerr << "Fatal internal error: using temporal preferences that depend on variable " << *(RPGBuilder::getPNE(currAV.fluents[s] - RPGBuilder::getPNECount())) << ", which is subject to continuous change\n";
                                            exit(1);
                                        }
                                        LHSvalue -= finalNumericVars[currAV.fluents[s] - RPGBuilder::getPNECount()].postLastEffectValue * currAV.weights[s];
                                        const int & vAfter = finalNumericVars[currAV.fluents[s] - RPGBuilder::getPNECount()].lastEffectTimestampVariable;
                                        if (vAfter != -1) {
                                            satisfiedByOrderingAfter.insert(vAfter);
                                            if (prefSupportDebug) {
                                                cout << COLOUR_yellow << *(RPGBuilder::getPNE(currAV.fluents[s] - RPGBuilder::getPNECount())) << " = " << finalNumericVars[currAV.fluents[s] - RPGBuilder::getPNECount()].postLastEffectValue << ", ordered after " << lp->getColName(vAfter) << "\n" << COLOUR_default;
                                            }                                
                                            
                                        } else {
                                            if (prefSupportDebug) {
                                                cout << COLOUR_yellow << *(RPGBuilder::getPNE(currAV.fluents[s] - RPGBuilder::getPNECount())) << " = " << finalNumericVars[currAV.fluents[s] - RPGBuilder::getPNECount()].postLastEffectValue << ", and unchanged since the initial state\n" << COLOUR_default;
                                            }                                
                                            
                                        }
                                            
                                    }
                                }
                               
                            }
                            
                            if (currPre.op == VAL::E_GREATEQ ? LHSvalue >= currPre.RHSConstant : LHSvalue > currPre.RHSConstant) {
                                if (prefSupportDebug) {
                                    if (wantToSatisfy) {                                    
                                        cout << COLOUR_light_green << " - Can be satisfied\n" << COLOUR_default;
                                    } else {
                                        cout << COLOUR_light_red << " - Must be satisfied\n" << COLOUR_default;
                                    }
                                }
                                canBeSatisfied = wantToSatisfy;                            
                            } else {
                                canBeSatisfied = !wantToSatisfy;                            
                                if (prefSupportDebug) {
                                    if (wantToSatisfy) {                                    
                                        cout << COLOUR_light_red << " - Cannot be satisfied\n" << COLOUR_default;
                                    } else {
                                        cout << COLOUR_light_green << " - Must be unsatisfied\n" << COLOUR_default;
                                    }
                                }
                            }
                            
                            if (!canBeSatisfied) {
                                satisfiedByOrderingAfter.clear();
                            }
                        } else {
                            // is an interior node
                            continue;
                        }
                        
                        
                        
                        if (canBeSatisfied) {                                            
                            
                            static vector<pair<int,double> > localEntries(3);
                            
                            if (!satisfiedByOrderingAfter.empty()) {
                                localEntries[0] = make_pair(currVar, 1.0);
                                localEntries[1] = make_pair(-1, -1.0);
                                localEntries[2] = make_pair(varsForNNFCells[c], BIG);
                                
                                set<int>::const_iterator afterItr = satisfiedByOrderingAfter.begin();
                                const set<int>::const_iterator afterEnd = satisfiedByOrderingAfter.end();
                            
                                for (; afterItr != afterEnd; ++afterItr) {
                                    
                                    localEntries[1].first = *afterItr; // the time-stamp var of that step                            
                                    lp->addRow(localEntries, EPSILON, LPinfinity);
                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        s << "ord" << stepID << "after" << *afterItr << "cell" << c;
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                }
                            }
                            
                        } else {
                            // force it to be unsatisfied: no actions in the past can support it
                            lp->setColLower(varsForNNFCells[c], 1.0);
                        }
                    
                    }
                }
                
                // now have soft back-edge if necessary
                
                static vector<pair<int,double> > localPairOfEntries(2);
                
                map<int,VarsForPreference>::iterator prefVars = varsForPreference.find(currEvent.divisionID);
                
                if (currEvent.time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION) {
                    
                    // bind this to be at the same point when the facts are being checked
                    
                    localPairOfEntries[0] = make_pair(currVar, 1.0);
                    localPairOfEntries[1] = make_pair(currEvent.pairWithStep + numVars, -1.0);
                    lp->addRow(localPairOfEntries, 0.0, 0.0); 

                    if (nameLPElements) {
                        ostringstream s;
                        s << "s" << stepID << "ppsameas" << currEvent.pairWithStep;
                        lp->setRowName(lp->getNumRows() - 1, s.str());
                    }
                    
                    varsForPreconditionPreference.insert(make_pair(currEvent.divisionID, list<int>())).first->second.push_back(varsForNNFCells[0]);
                    
                    // TODO: use the variable for the next step in the first place
                    
                } else {
                
                    const double isHardConstraint = (pref.cost == DBL_MAX ? 0.0 : 1.0);
                    
                    switch (pref.cons) {
                        
                        case VAL::E_ALWAYS: {
                            if (prefVars == varsForPreference.end()) {
                                lp->addCol(emptyEntries, 0.0, isHardConstraint, MILPSolver::C_BOOL);
                                if (nameLPElements) {
                                    ostringstream s;
                                    if (pref.cost == DBL_MAX) {
                                        s << "cons-always" << currEvent.divisionID;
                                    } else {
                                        s << "always" << pref.name << "i" << currEvent.divisionID;
                                    }
                                    lp->setColName(lp->getNumCols() - 1, s.str());
                                }
                                prefVars = varsForPreference.insert(make_pair(currEvent.divisionID,VarsForPreference(lp->getNumCols() - 1))).first;
                            }
                            
                            // var denoting the always is true >= var denoting this instance of the always is true
                            // therefore if this instance = 1, the always = 1
                            localPairOfEntries[0] = make_pair(prefVars->second.committedCostVar, 1.0);
                            localPairOfEntries[1] = make_pair(varsForNNFCells[0], -1.0);
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            break;
                        }
                        case VAL::E_ATEND:
                        {
                            std::cerr << "Fatal error: dummy steps should not be inserted for at-end preferences, it should only depend on whether they are true at the end or not\n";
                            exit(1);
                            break;
                        }
                        case VAL::E_SOMETIME:
                        {
                            if (prefVars == varsForPreference.end()) {
                                lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "sometime" << pref.name;
                                    lp->setColName(lp->getNumCols() - 1, s.str());
                                }
                                const int currCol = lp->getNumCols() - 1;
                                prefVars = varsForPreference.insert(make_pair(currEvent.divisionID,VarsForPreference(-1, currCol))).first;
                                
                                // create the initial basic constraint that this can only be true if any one of the instances of it are true
                                // c1 + c2 + c3 + c4 - sometime-truth-value <= number of children - 1
                                
                                static vector<pair<int,double> > basicSometimeConstraint(1);
                                basicSometimeConstraint[0].first = currCol;
                                basicSometimeConstraint[0].second = -1.0;
                                lp->addRow(basicSometimeConstraint, -LPinfinity, -1.0);
                                
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "sometimemet" << pref.name << "i" << currEvent.divisionID;
                                    lp->setRowName(lp->getNumRows() - 1, s.str());
                                }
                                
                                prefVars->second.committedRow = lp->getNumRows() - 1;
                            }
                            
                            // add to the constraint above
                            const int & cr = prefVars->second.committedRow;
                            lp->setMatrixEntry(cr, varsForNNFCells[0], 1.0);
                            lp->setRowUpper(cr, lp->getRowUpper(cr) + 1.0);
                            
                            
                            // and also force the sometime to be true if this NNF is
                            localPairOfEntries[0] = make_pair( varsForNNFCells[0], 1.0);
                            localPairOfEntries[1] = make_pair(prefVars->second.committedCostVar, -1.0);                        
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "sometime" << pref.name << "ifs" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            
                            break;
                        }
                        case VAL::E_ATMOSTONCE:
                        {
                            // for things we don't want to be true, we pessimistically force them to be true, and leave it to back-tracking to resolve
                            // either making it false, or making the STP feasible                                                                                                                                  
                            // for at-most-once, this means enforcing the entire trace
                            
                            lp->setColUpper(varsForNNFCells[0], 0.0);
                            break;
                        }
                        case VAL::E_SOMETIMEAFTER:
                        case VAL::E_ALWAYSWITHIN:
                        {
                            // part 1 is the a in (sometime-after a b)
                            
                            if (part == 1) {
                                
                                if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                    // must bind this dummy step to be at the same time as the one it's paired with, i.e. its direct trigger
                                    
                                    localPairOfEntries[0] = make_pair(currVar, 1.0);
                                    localPairOfEntries[1] = make_pair(currEvent.pairWithStep + numVars, -1.0);
                                    lp->addRow(localPairOfEntries, 0.0, 0.0); 
                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        s << "aw" << pref.name << "s" << stepID;
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                    
                                } else {
                                    
                                    // for things we don't want to be true, we pessimistically force them to be true, and leave it to back-tracking to resolve
                                    lp->setColUpper(varsForNNFCells[0], 0.0);
                                }
                                
                                if (prefVars == varsForPreference.end()) {
                                    
                                    // the master column that says the sometime-after is currently unsatisfied if any of the instances of it are
                                    lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                                    
                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                            s << "alwayswithin";
                                        } else {
                                            s << "sometimeafter";
                                        }                                    
                                        s << pref.name << "i" << currEvent.divisionID;;
                                        lp->setColName(lp->getNumCols() - 1, s.str());
                                    }
                                    
                                    
                                
                                    
                                    const int currCol = lp->getNumCols() - 1;
                                    prefVars = varsForPreference.insert(make_pair(currEvent.divisionID,VarsForPreference(-1, currCol))).first;
                                    
                                    static vector<pair<int,double> > basicSometimeAfterConstraint(1);
                                    basicSometimeAfterConstraint[0].first = currCol;
                                    basicSometimeAfterConstraint[0].second = BIG;
                                    lp->addRow(basicSometimeAfterConstraint, 0.0, LPinfinity);
                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                            s << "allofaw";
                                        } else {
                                            s << "allofsta";
                                        }                                    
                                        s << pref.name << "i" << currEvent.divisionID;
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                    
                                    prefVars->second.committedRow = lp->getNumRows() - 1;
                                    
                                    if (lpDebug & 1) {
                                        if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                            cout << "Now have a variable to track the truth value of always-within " << pref.name << endl;
                                        } else {
                                            cout << "Now have a variable to track the truth value of sometime-after " << pref.name << endl;
                                        } 
                                    }
                                }
                                
                                const int & cr = prefVars->second.committedRow;
                                                            
                                static vector<pair<int,double> > isThisTriggerClosed(1);
                                isThisTriggerClosed[0] = make_pair(cr, -1.0);
                                lp->addCol(isThisTriggerClosed, 0.0, 1.0, MILPSolver::C_BOOL);
                                
                                if (nameLPElements) {
                                    ostringstream s;
                                    if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                        s << "aw";
                                    } else {
                                        s << "sta";
                                    }                                    
                                    s << pref.name << "at" << stepID << "ok";
                                    lp->setColName(lp->getNumCols() - 1, s.str());
                                }
                                
                                
                                const int localCol = lp->getNumCols() - 1;
                                
                                localPairOfEntries[0] = make_pair(prefVars->second.committedCostVar, 1.0);
                                localPairOfEntries[1] = make_pair(localCol, -1.0);
                                lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                
                                if (nameLPElements) {
                                    ostringstream s;
                                    if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                        s << "aw";
                                    } else {
                                        s << "sta";
                                    }                                    
                                    s << pref.name;
                                    s << "brokenby" << stepID;
                                    lp->setRowName(lp->getNumRows() - 1, s.str());
                                }
                                
                                
                                // now add a disjunctive satisfaction row for this trigger
                                
                                static vector<pair<int,double> > basicSometimeAfterConstraint(1);
                                basicSometimeAfterConstraint[0] = make_pair(localCol, -1.0);                            
                                lp->addRow(basicSometimeAfterConstraint, -LPinfinity, -1.0);
                                                            
                                if (nameLPElements) {
                                    ostringstream s;
                                    if (pref.cons == VAL::E_ALWAYSWITHIN) {
                                        s << "aw";
                                    } else {
                                        s << "sta";
                                    }                                    
                                    s << pref.name;
                                    s << "t" << stepID << "met";
                                    lp->setRowName(lp->getNumRows() - 1, s.str());
                                }
                                
                                
                                partOneOfPrefWasAtStep[currEvent.divisionID].push_back(VarsForTrigger(stepID, localCol, lp->getNumRows() - 1));
                                
                                // for things we don't want to be true, we pessimistically force them to be true, and leave it to back-tracking to resolve
                                // either making it false, or making the STP feasible
                                
                                
                                
                            } else {
                                
                                // if this is satisfied, all previous part ones are satisfied
                                
                                map<int, list<VarsForTrigger> >::const_iterator emItr = partOneOfPrefWasAtStep.find(currEvent.divisionID);
                                
                                assert(emItr != partOneOfPrefWasAtStep.end());
                                
                                if (pref.cons == VAL::E_SOMETIMEAFTER) {
                                    list<VarsForTrigger>::const_iterator eItr = emItr->second.begin();
                                    const list<VarsForTrigger>::const_iterator eEnd = emItr->second.end();
                                    
                                    for (; eItr != eEnd; ++eItr) {
                                        // first, if the preference is presumed unsatisfied, force this to break
                                        localPairOfEntries[0] = make_pair(varsForNNFCells[0], 1.0);
                                        localPairOfEntries[1] = make_pair(eItr->satisfactionVar, -1.0);
                                        lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "sta" << pref.name;
                                            s << "mustbreak" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                        
                                        
                                        // second, if this is satisfied, force the preference as a whole to satisfied
                                        
                                        const int & cr = eItr->disjunctiveSatisfactionRow;
                                        lp->setMatrixEntry(cr, varsForNNFCells[0], 1.0);
                                        lp->setRowUpper(cr, lp->getRowUpper(cr) + 1.0);
                                    }
                                } else {
                                    list<VarsForTrigger>::const_iterator eItr = emItr->second.begin();
                                    const list<VarsForTrigger>::const_iterator eEnd = emItr->second.end();
                                    
                                    for (; eItr != eEnd; ++eItr) {
                                        
                                        // first, if the preference is presumed unsatisfied, force this to break
                                        localPairOfEntries[0] = make_pair(varsForNNFCells[0], 1.0);
                                        localPairOfEntries[1] = make_pair(eItr->satisfactionVar, -1.0);
                                        lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "aw" << pref.name;
                                            s << "mustbreak" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                                                            
                                        // (varsForCells[0] == 0) && (not too much time has elapsed) => eItr->satisfactionVar == 0
                                        
                                        lp->addCol(emptyEntries,0.0,1.0,MILPSolver::C_BOOL);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "aw" << pref.name << "s" << eItr->stepID << "e" << stepID << "intime";
                                            lp->setColName(lp->getNumCols() - 1, s.str());
                                        }

                                        const int appropriateTimeFrame = lp->getNumCols() - 1;
                                        
                                        static vector<pair<int,double> > conditionalPrecedence(3);
                                        conditionalPrecedence[0] = make_pair(currVar, 1.0);
                                        conditionalPrecedence[1] = make_pair(numVars + eItr->stepID, -1.0);
                                        conditionalPrecedence[2] = make_pair(appropriateTimeFrame, BIG);
                                        
                                        lp->addRow(conditionalPrecedence, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "aw" << pref.name << "g" << stepID << "aft" << eItr->stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                                                            

                                        conditionalPrecedence[0] = make_pair(numVars + eItr->stepID, 1.0);
                                        conditionalPrecedence[1] = make_pair(currVar, -1.0);
                                        conditionalPrecedence[2] = make_pair(appropriateTimeFrame, BIG);
                                        
                                        lp->addRow(conditionalPrecedence, -pref.deadline, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "aw" << pref.name << "g" << stepID << "ontime" << eItr->stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                        
                                        lp->addCol(emptyEntries,0.0,1.0,MILPSolver::C_BOOL);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "aw" << pref.name << "s" << eItr->stepID << "e" << stepID << "joint";
                                            lp->setColName(lp->getNumCols() - 1, s.str());
                                        }
                                        
                                        const int jointCol = lp->getNumCols() - 1;
                                        
                                        // first, if jointCol is 1, one of the other parts has to be 1
                                        
                                        
                                        static vector<pair<int,double> > jointConstraint(3);
                                        jointConstraint[0] = make_pair(jointCol, 1.0);
                                        jointConstraint[1] = make_pair(appropriateTimeFrame, -1.0);
                                        jointConstraint[2] = make_pair(varsForNNFCells[0], -1.0);
                                        lp->addRow(jointConstraint, -LPinfinity, 0.0);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "makenotaw" << pref.name << "s" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                                                
                                        
                                        // second, if either of the other parts is 1, jointCol is 1
                                        
                                        localPairOfEntries[0] = make_pair(jointCol, 1.0);
                                        localPairOfEntries[1] = make_pair(appropriateTimeFrame, -1.0);
                                        lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "jointnotmet" << pref.name << "s" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                        
                                        localPairOfEntries[1] = make_pair(varsForNNFCells[0], -1.0);
                                        lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "jointnottf" << pref.name << "s" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                        
                                        
                                        // finally, treat as sometime after, but with jointCol instead of varsForNNFCells[0]
                                        
                                        // first, if the preference is presumed unsatisfied, force this to break
                                        localPairOfEntries[0] = make_pair(jointCol, 1.0);
                                        localPairOfEntries[1] = make_pair(eItr->satisfactionVar, -1.0);
                                        lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                                        
                                        if (nameLPElements) {
                                            ostringstream s;
                                            s << "awi" << pref.name;
                                            s << "mustbreak" << stepID;
                                            lp->setRowName(lp->getNumRows() - 1, s.str());
                                        }
                                        
                                        
                                        // second, if this is satisfied, force the preference as a whole to satisfied
                                        
                                        const int & cr = eItr->disjunctiveSatisfactionRow;
                                        lp->setMatrixEntry(cr, jointCol, 1.0);
                                        lp->setRowUpper(cr, lp->getRowUpper(cr) + 1.0);
                                        
                                    }
                                    
                                    
                                }
                                
                            }
                                                       
                            
                            break;
                        }
                        
                        case VAL::E_SOMETIMEBEFORE:
                        {
                            // part 1 is the a in (sometime-before a b)
                            
                             if (prefVars == varsForPreference.end()) {
                                lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "sometimebefore" << pref.name << "i" << currEvent.divisionID;
                                    lp->setColName(lp->getNumCols() - 1, s.str());
                                }
                                prefVars = varsForPreference.insert(make_pair(currEvent.divisionID,VarsForPreference(lp->getNumCols() - 1))).first;
                            }
                            
                            if (part == 0) {
                                if (lpDebug & 1) {
                                    cout << COLOUR_yellow << "- Noting that step " << stepID << " is the requirement of sometime-before preference " << pref.name << COLOUR_default << endl;
                                }
                                partZeroOfPrefWasAtStep[currEvent.divisionID].push_back(VarsForRequirement(stepID));

                            } else {
                            
                                // one of the previous part zeros must be true if this is to be true
                                
                                map<int, list<VarsForRequirement> >::const_iterator vfrItr = partZeroOfPrefWasAtStep.find(currEvent.divisionID);
                                
                                if (vfrItr == partZeroOfPrefWasAtStep.end()) {
                                    // trivial case: 'b' was never seen, so this definitely violates it
                                    // force preference to be violated
                                    if (lpDebug & 1) {
                                        cout << COLOUR_yellow << "- Noting that step " << stepID << ", a trigger of sometime-before preference " << pref.name << ", comes after no requirements, so is definitely violated" << endl;
                                    }
                                    lp->setColLower(prefVars->second.committedCostVar, 1.0);
                                    
                                } else {
                                
                                    // c1 + c2 + c3 + c4 - sometime-before-truth-value <= number of earlier requirement opportunities - 1
                                    
                                    const int earlierRequirementOpportunities = vfrItr->second.size();
                                    
                                    vector<pair<int,double> > sometimeBeforeConstraint(earlierRequirementOpportunities + 1);
                                    
                                    sometimeBeforeConstraint[0] = make_pair(prefVars->second.committedCostVar, -1.0);
                                    
                                    list<VarsForRequirement>::const_iterator esItr = vfrItr->second.begin();
                                    const list<VarsForRequirement>::const_iterator esEnd = vfrItr->second.end();
                                    
                                    if (lpDebug & 1) {
                                        cout << COLOUR_yellow << "- Noting that step " << stepID << ", a trigger of sometime-before preference " << pref.name << ", must be after one of the earlier requirements to be satisfied [";
                                    }
                                    
                                    for (int col = 1; esItr != esEnd; ++esItr, ++col) {                                    
                                        sometimeBeforeConstraint[col] = make_pair(variablesCorrespondingToNNFNodesForDummyStep[esItr->stepID][0], 1.0);                                    
                                        if (lpDebug & 1) {
                                            cout << " " << esItr->stepID;
                                        }
                                    }
                                    
                                    if (lpDebug & 1)  {
                                        cout << " ]\n" << COLOUR_default;
                                    }
                                    
                                    lp->addRow(sometimeBeforeConstraint, -LPinfinity, earlierRequirementOpportunities - 1);
                                    

                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        s << "stb" << pref.name << "s" << stepID << "okay";
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                }
                            }                        
                            break;
                        }
                        
                        case VAL::E_WITHIN: {
                            
                            if (prefVars == varsForPreference.end()) {
                                lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "within" << pref.name << "i" << currEvent.divisionID;
                                    lp->setColName(lp->getNumCols() - 1, s.str());
                                }
                                const int currCol = lp->getNumCols() - 1;
                                prefVars = varsForPreference.insert(make_pair(currEvent.divisionID,VarsForPreference(-1, currCol))).first;
                                
                                // create the initial basic constraint that this can only be true if any one of the instances of it are true
                                // c1 + c2 + c3 + c4 - within-truth-value <= number of children - 1
                                
                                static vector<pair<int,double> > basicSometimeConstraint(1);
                                basicSometimeConstraint[0].first = currCol;
                                basicSometimeConstraint[0].second = -1.0;
                                lp->addRow(basicSometimeConstraint, -LPinfinity, -1.0);
                                
                                if (nameLPElements) {
                                    ostringstream s;
                                    s << "withinmet" << pref.name;
                                    lp->setRowName(lp->getNumRows() - 1, s.str());
                                }
                                
                                prefVars->second.committedRow = lp->getNumRows() - 1;
                            }
                            
                            // make a var that tests whether this step is soon enough
                            
                            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "twithin" << pref.name << "s" << stepID;
                                lp->setColName(lp->getNumCols() - 1, s.str());
                            }
                            
                            const int testCol = lp->getNumCols() - 1;
                            
                            // if current timestap after deadline, force testCol to 1
                            localPairOfEntries[0] = make_pair(currVar, 1.0);
                            localPairOfEntries[1] = make_pair(testCol, -BIG);
                            
                            lp->addRow(localPairOfEntries, -LPinfinity, pref.deadline);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "notelate" << pref.name << "s" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            
                            // if testCol is 1, force current timestamp to be after deadline
                            
                            localPairOfEntries[1] = make_pair(testCol, -pref.deadline);
                            
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "forcelate" << pref.name << "s" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            
                            // next, make a var that is 0 iff testCol == 0 and varsForNNFCells[0]
                            
                            lp->addCol(emptyEntries, 0.0, 1.0, MILPSolver::C_BOOL);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "metandontime" << pref.name << "s" << stepID;
                                lp->setColName(lp->getNumCols() - 1, s.str());
                            }
                                                    
                            
                            const int jointCol = lp->getNumCols() - 1;
                            
                            // first, if jointCol is 1, one of the other parts has to be 1
                            
                            static vector<pair<int,double> > jointConstraint(3);
                            jointConstraint[0] = make_pair(jointCol, 1.0);
                            jointConstraint[1] = make_pair(testCol, -1.0);
                            jointConstraint[2] = make_pair(varsForNNFCells[0], -1.0);
                            lp->addRow(jointConstraint, -LPinfinity, 0.0);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "makenotwithin" << pref.name << "s" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                                                    
                            
                            // second, if either of the other parts is 1, jointCol is 1
                            
                            localPairOfEntries[0] = make_pair(jointCol, 1.0);
                            localPairOfEntries[1] = make_pair(testCol, -1.0);
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "jointnotmet" << pref.name << "s" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            
                            localPairOfEntries[1] = make_pair(varsForNNFCells[0], -1.0);
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "jointtoolate" << pref.name << "s" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            
                            // we've now reduced it to a sometime constraint, only with jointCol instead of varsForNNFCells[0]
                            
                            // add to the constraint above
                            const int & cr = prefVars->second.committedRow;
                            lp->setMatrixEntry(cr, jointCol, 1.0);
                            lp->setRowUpper(cr, lp->getRowUpper(cr) + 1.0);
                            
                            
                            // and also force the within to be true if this NNF is
                            localPairOfEntries[0] = make_pair( jointCol, 1.0);
                            localPairOfEntries[1] = make_pair(prefVars->second.committedCostVar, -1.0);                        
                            lp->addRow(localPairOfEntries, 0.0, LPinfinity);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "within" << pref.name << "ifs" << stepID;
                                lp->setRowName(lp->getNumRows() - 1, s.str());
                            }
                            break;
                            
                        }
                    }
                }            
            }            
        } else if (currTS == Planner::E_AT && divisionID < 0) {

            /*lp->setColLower(currVar, currEvent.lpMinTimestamp);
            if (currEvent.lpMaxTimestamp != DBL_MAX) {
                lp->setColUpper(currVar, currEvent.lpMaxTimestamp);
            } else {
                lp->setColUpper(currVar, LPinfinity);
            }*/
            
        } else {
            
            bool printed = false;

            for (int predecessorPass = 0; predecessorPass < 2; ++predecessorPass) {
                const map<int, bool> * currentPredecessors;

                if (predecessorPass) {
                    if (currTS != Planner::E_AT_END || currEvent.getEffects) {
                        // if it's the end of an action in the past, we don't need the extra TO edge
                        break;
                    }
                    if (currEvent.pairWithStep == stepThatMustPrecedeFutureEnds) {
                        break;
                    }
                    currentPredecessors = &(fakeEdgeForThis);
                    if (lpDebug & 1) {
                        if (!fakeEdgeForThis.empty()) {
                            if (!printed) {
                                cout << "Steps before this one, only due to TO: [";
                                printed = true;
                            } else {
                                cout << "] + TO: [";
                            }
                        }
                    }

                } else {
                    currentPredecessors = stepsThatComeBeforeThisOne;
                }

                if (currentPredecessors) {

                    map<int, bool>::const_iterator beforeItr = currentPredecessors->begin();
                    const map<int, bool>::const_iterator beforeEnd = currentPredecessors->end();

                    for (; beforeItr != beforeEnd; ++beforeItr) {                        
                        if ((lpDebug & 1) && !printed) {
                            cout << "Steps before this one: [";
                            printed = true;
                        }
                        if (lpDebug & 1) cout << " " << beforeItr->first;
                        const int prevVar = beforeItr->first + numVars;

                        if (planAsAVector[beforeItr->first]->isDummyStep()) {
                            
                            if (planAsAVector[beforeItr->first]->time_spec == Planner::E_DUMMY_PREFERENCE_PRECONDITION
                                || preferenceStatus[planAsAVector[beforeItr->first]->divisionID] != AutomatonPosition::unreachable) {
                                // back edge to a dummy step
                                if (lpDebug & 1) cout << "d";
                                
                                const list<Literal*> * adds;
                                const list<Literal*> * dels;
                                const list<int> * nums;
                                
                                switch (currEvent.time_spec) {
                                    case Planner::E_AT_START: {
                                        adds = &(RPGBuilder::getStartPropositionAdds()[currEvent.action->getID()]);
                                        dels = &(RPGBuilder::getStartPropositionDeletes()[currEvent.action->getID()]);
                                        nums = &(RPGBuilder::getStartEffNumerics()[currEvent.action->getID()]);
                                        break;
                                    }
                                    case Planner::E_AT_END: {
                                        adds = &(RPGBuilder::getEndPropositionAdds()[currEvent.action->getID()]);
                                        dels = &(RPGBuilder::getEndPropositionDeletes()[currEvent.action->getID()]);
                                        nums = &(RPGBuilder::getEndEffNumerics()[currEvent.action->getID()]);
                                        break;
                                    }
                                    case Planner::E_AT: {
                                        adds = &(RPGBuilder::getNonAbstractedTILVec()[currEvent.divisionID]->addEffects);
                                        dels = &(RPGBuilder::getNonAbstractedTILVec()[currEvent.divisionID]->delEffects);
                                        nums = 0;
                                        break;
                                    }
                                    default: {
                                        std::cerr << "Fatal internal error: should not have time specifier " << currEvent.time_spec << " at this point\n";
                                        exit(1);
                                    }
                                }
                                
                                static vector<pair<int,double> > conditionalPrecedence(3);
                                   
                                conditionalPrecedence[0] = make_pair(currVar, 1.0);
                                conditionalPrecedence[1] = make_pair(prevVar, -1.0);
                                
                                set<int> cpCells;
                                
                                for (int apass = 0; apass < 2; ++apass) {
                                    list<Literal*>::const_iterator delItr = (apass ? adds->begin() : dels->begin());
                                    const list<Literal*>::const_iterator delEnd = (apass ? adds->end() : dels->end());

                                    for (; delItr != delEnd; ++delItr) {

                                        const map<int, list<int> >::const_iterator depItr = dummyStepDependencies[beforeItr->first].literals.find((*delItr)->getStateID());
                                        
                                        if (depItr != dummyStepDependencies[beforeItr->first].literals.end()) {                                        
                                            cpCells.insert(depItr->second.begin(), depItr->second.end());                                        
                                        }
                                    }
                                }
                                                                                               
                                if (nums) {
                                    list<int>::const_iterator neItr = nums->begin();
                                    const list<int>::const_iterator neEnd = nums->end();
                                
                                
                                    for (; neItr != neEnd; ++neItr) {
                                        
                                        const map<int, set<int> >::const_iterator depItr = dummyStepDependencies[beforeItr->first].numerics.find(RPGBuilder::getNumericEff()[*neItr].fluentIndex);
                                        if (depItr != dummyStepDependencies[beforeItr->first].numerics.end()) {                                        
                                            cpCells.insert(depItr->second.begin(), depItr->second.end());                                        
                                        }
                                    }
                                }
                                 
                                set<int>::const_iterator cellItr = cpCells.begin();
                                const set<int>::const_iterator cellEnd = cpCells.end();
                                
                                for (; cellItr != cellEnd; ++cellItr) {
                                    conditionalPrecedence[2] = make_pair(variablesCorrespondingToNNFNodesForDummyStep[beforeItr->first][*cellItr], BIG);
                                    lp->addRow(conditionalPrecedence, 0.0, LPinfinity);
                                    
                                    if (nameLPElements) {
                                        ostringstream s;
                                        s << "ord" << stepID << "after" << beforeItr->first << "cell" << *cellItr;
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                }
                            }
                           
                        } else {
                        
                            if (currTS != Planner::E_AT_END || prevVar != currVar - 1) {

                                static vector<pair<int,double> > entries(2);
                                entries[0].second = 1.0;
                                entries[1].second = -1.0;
                                
                                entries[0].first = currVar;
                                entries[1].first = prevVar;

                                lp->addRow(entries, (beforeItr->second ? EPSILON : 0.0), LPinfinity); // syntax for '>= 0 or EPSILON'

                                if (nameLPElements) {
                                    int constrIdx = lp->getNumRows() - 1;
                                    ostringstream namestream;
                                    if (beforeItr->second) {
                                        namestream << "t" << beforeItr->first << "_l_t" << stepID;
                                    } else {
                                        namestream << "t" << beforeItr->first << "_le_t" << stepID;
                                    }
                                    string asString = namestream.str();
                                    lp->setRowName(constrIdx, asString);
                                }
                            } else {
                                if (lpDebug & 1) cout << " <start>";
                            }
                        }
                    }                    
                }
            }


            if (lpDebug & 1 && printed) cout << " ]\n";

        }

        if (lpDebug & 1) {
            if (!activeAncestorsOfStep[stepID].empty()) {
                cout << "Active ancestors:";
                set<int>::const_iterator aaItr = activeAncestorsOfStep[stepID].begin();
                const set<int>::const_iterator aaEnd = activeAncestorsOfStep[stepID].end();
                for (; aaItr != aaEnd; ++aaItr) {
                    if (!correspondEndHasBeenInserted[*aaItr]) cout << " " << *aaItr;
                }
                cout << endl;
            }
        }

        timestampVars[stepID] = currVar;

        {
            double boundForSuccessors = unassignedLowerBounds[stepID];

            if (currEvent.isDummyStep()) {
                if (optimised) {
                    if (currEvent.lpMinTimestamp != -1.0) {
                        if (boundForSuccessors < currEvent.lpMinTimestamp) {
                            boundForSuccessors = currEvent.lpMinTimestamp;
                        }
                    }
                }
                lp->setColLower(currVar, EpsilonResolutionTimestamp(boundForSuccessors,true).toDouble());
            } else if (currTS == Planner::E_AT) {
                
                if (divisionID >= 0) {
                    const double thisTIL = TILtimestamps[divisionID];

                    lp->setColLower(currVar, thisTIL);
                    lp->setColUpper(currVar, thisTIL);
                    if (lpDebug & 1) cout << "- As it's a TIL, fixing column bounds of " << currVar << " to " << thisTIL << endl;
                    nextTIL = divisionID + 1;
    //                TILupbo = TILtimestamps[nextTIL];
                    if (boundForSuccessors < thisTIL) {
                        boundForSuccessors = thisTIL;
                    }
                }

            } else {


                if (optimised) {
                    if (currEvent.lpMinTimestamp != -1.0) {
                        if (boundForSuccessors < currEvent.lpMinTimestamp) {
                            boundForSuccessors = currEvent.lpMinTimestamp;
                        }
                    }
                } 
               
                const double initialWorkingLower = actionTSBounds[actID][currTS == Planner::E_AT_START ? 0 : 1].first;
                
                if (boundForSuccessors < initialWorkingLower) {
                    boundForSuccessors = initialWorkingLower;
                }
                
                if (optimised) {
                    if (currTS == Planner::E_AT_END) {
                        double startPlusMin = planAsAVector[stepID-1]->lpMinTimestamp;
                        if (startPlusMin != -1.0) {
                            startPlusMin += RPGBuilder::getOpMinDuration(actID,-1);
                            if (boundForSuccessors < startPlusMin) {
                                boundForSuccessors = startPlusMin;
                            }
                        }
                    }
                }
                 
                double overallWorkingUpper = DBL_MAX;
                                  
                                               
                if (currTS == Planner::E_AT_END && !currEvent.getEffects) {
                    
                    {
                        // see if it has any end conditions on time-elapsed
                        
                        const list<const Constraint*> & endConstraints = constraints[actID][2];
                        
                        list<const Constraint*>::const_iterator ecItr = endConstraints.begin();
                        const list<const Constraint*>::const_iterator ecEnd = endConstraints.end();
                        
                        for (int ecID = 0; ecItr != ecEnd; ++ecItr, ++ecID) {

                            const int size = (*ecItr)->weights.size();
                            
                            pair<double,double> boundsOnRest(0.0, 0.0);

                            bool canBeBounded = true;
                            
                            bool foundTime = false;
                            double timeWeight;

                            for (int s = 0; s < size; ++s) {
                                if ((*ecItr)->variables[s] == -4) {
                                    timeWeight = (*ecItr)->weights[s];
                                    foundTime = true;
                                } else {
                                    map<int, set<int> >::const_iterator guardItr = NumericAnalysis::getFactsThatDefineAndFixVariables().find((*ecItr)->variables[s]);
                                    if (guardItr != NumericAnalysis::getFactsThatDefineAndFixVariables().end()) {
                                        set<int>::const_iterator gItr = guardItr->second.begin();
                                        const set<int>::const_iterator gEnd = guardItr->second.end();
                                        for (; gItr != gEnd; ++gItr) {
                                            if (theState.first.find(*gItr) != theState.first.end()) {
                                                break;
                                            }
                                        }
                                        if (gItr == gEnd) {
                                            canBeBounded = false;
                                            break;
                                        } else {
                                            
                                            const double outcomeA = theState.secondMin[(*ecItr)->variables[s]] * (*ecItr)->weights[s];
                                            const double outcomeB = theState.secondMax[(*ecItr)->variables[s]] * (*ecItr)->weights[s];
                                            
                                            if (outcomeA < outcomeB) {
                                                boundsOnRest.first += outcomeA;
                                                boundsOnRest.second += outcomeB;
                                            } else {
                                                boundsOnRest.first += outcomeB;
                                                boundsOnRest.second += outcomeA;
                                            }
                                            
                                        }
                                    } else {
                                        canBeBounded = false;
                                        break;
                                    }
                                }
                            }
                            
                            if (canBeBounded && foundTime) {
                                
                                                            
                                vector<pair<int,double> > constraintOnOpenEnd;
                                constraintOnOpenEnd.reserve(size);
                                
                                double fixed = 0.0;
                                for (int s = 0; s < size; ++s) {
                                    if ((*ecItr)->variables[s] == -4) {
                                        constraintOnOpenEnd.push_back(make_pair(currVar, timeWeight));
                                    } else {
                                        const int col = finalNumericVars[(*ecItr)->variables[s]].lastEffectValueVariable;
                                        
                                        if (col == -1) {
                                            fixed += finalNumericVars[(*ecItr)->variables[s]].postLastEffectValue * (*ecItr)->weights[s];
                                        } else {
                                            constraintOnOpenEnd.push_back(make_pair(col, (*ecItr)->weights[s]));
                                        }
                                    }
                                }
                                
                                if (constraintOnOpenEnd.size() > 1) {
                                    bool added = false;
                                    if ((*ecItr)->lower == -DBL_MAX && (*ecItr)->upper != DBL_MAX) {
                                        lp->addRow(constraintOnOpenEnd, -LPinfinity, (*ecItr)->upper - fixed);
                                        added = true;
                                    } else if ((*ecItr)->lower != -DBL_MAX && (*ecItr)->upper == DBL_MAX) {
                                        lp->addRow(constraintOnOpenEnd, (*ecItr)->lower - fixed, LPinfinity);
                                        added = true;
                                    } else {
                                        assert((*ecItr)->lower != DBL_MAX && (*ecItr)->upper != DBL_MAX);
                                        lp->addRow(constraintOnOpenEnd, (*ecItr)->lower - fixed, (*ecItr)->upper - fixed);
                                        added = true;
                                    }
                                    if (added && nameLPElements) {
                                        ostringstream s;
                                        s << "oe" << stepID << "ex" << ecID;
                                        lp->setRowName(lp->getNumRows() - 1, s.str());
                                    }
                                }
                                
                                if (timeWeight > 0.0) {
                                    
                                    if ((*ecItr)->lower != -DBL_MAX) {
                                        
                                        double forcedTBound = ((*ecItr)->lower - boundsOnRest.second) / timeWeight;
                                        
                                        if (forcedTBound > boundForSuccessors) {
                                            boundForSuccessors = forcedTBound;
                                            if (lpDebug & 1) {
                                                cout << "Pushed lower bound up to " << forcedTBound << " due to a time-dependent precondition\n";
                                            }
                                        }
                                    }
                                    
                                    if ((*ecItr)->upper != DBL_MAX) {
                                        
                                        double forcedTBound = ((*ecItr)->upper - boundsOnRest.first) / timeWeight;
                                        
                                        if (forcedTBound < overallWorkingUpper) {
                                            overallWorkingUpper = forcedTBound;
                                            if (lpDebug & 1) {
                                                cout << "Pushed upper bound down to " << forcedTBound << " due to a time-dependent precondition\n";
                                            }
                                        }
                                    }
                                    
                                } else if (timeWeight < 0.0) {
                                    
                                    if ((*ecItr)->lower != -DBL_MAX) {
                                        
                                        double forcedTBound = (-(*ecItr)->lower + boundsOnRest.second) / -timeWeight;
                                        
                                        if (forcedTBound < overallWorkingUpper) {
                                            overallWorkingUpper = forcedTBound;
                                            if (lpDebug & 1) {
                                                cout << "Pushed upper bound down to " << forcedTBound << " due to a time-dependent precondition\n";
                                            }
                                        }
                                    }
                                    
                                    if ((*ecItr)->upper != DBL_MAX) {
                                        
                                        double forcedTBound = (-(*ecItr)->upper + boundsOnRest.first) / -timeWeight;
                                        
                                        if (forcedTBound > boundForSuccessors) {
                                            boundForSuccessors = forcedTBound;
                                            if (lpDebug & 1) {
                                                cout << "Pushed lower bound up to " << forcedTBound << " due to a time-dependent precondition\n";
                                            }
                                        }
                                    }
                                    
                                }
                                
                            }
                            
                        }
                        
                    }
                    
                    if (!tilVec.empty()) {
                    
                        // the end of an action that has been started but not yet finished
                        // see if its end preconditions depend on any TILs

                        const list<Literal*> & instantPres = RPGBuilder::getEndPropositionalPreconditions()[actID];
                    
                        list<pair<TILTimeline::const_iterator, TILTimeline::const_iterator> > relevantTimelinePointsAndTheirEnds;
                        
                        bool pushedForwards = false;
                        
                        list<Literal*>::const_iterator pItr = instantPres.begin();
                        const list<Literal*>::const_iterator pEnd = instantPres.end();                                        
                        
                        for (; pItr != pEnd; ++pItr) {
                            
                            if (TemporalAnalysis::getFactIsAbstract()[(*pItr)->getStateID()]) {
                                continue;
                            }
                            
                            const TILTimeline * const currTimeline = TemporalAnalysis::timelineOnTILFact((*pItr)->getStateID());
                            
                            if (!currTimeline) {
                                continue;
                            }
                            
                            if (!currTimeline->isOnlyEverAddedByTILs()) {
                                continue;
                            }
                            
                            {
                                TILTimeline::const_iterator ub = currTimeline->getLastDeletor();
                                if (ub != currTimeline->end() && ub->first - EPSILON < overallWorkingUpper) {
                                    if (lpDebug & 1) {
                                        cout << "- " << *(*pItr) << " pushes upper bound down to " << ub->first - EPSILON << ", i.e. before the last TIL deletor\n";
                                    }
                                    overallWorkingUpper = ub->first - EPSILON;
                                    
                                    if (overallWorkingUpper < boundForSuccessors) {
                                        if (lpDebug & 1) {
                                            cout << "- This is before the lower bound of " << boundForSuccessors << ", so the LP would be unsolvable\n";
                                        }
                                        solved = false; return;                                                                                                                
                                    }
                                }
                            }
                            
                            TILTimeline::const_iterator adder = currTimeline->firstAdderSuitableForTime(boundForSuccessors);

                            if (adder == currTimeline->end()) {
                                if (lpDebug & 1) {
                                    cout << "- " << *(*pItr) << " means that the LP cannot ever be solved: there is no true-TIL-window that can contain " << boundForSuccessors << endl;
                                }
                                solved = false; return;                            
                            }
                            
                            if (adder->first + EPSILON > boundForSuccessors) {
                                if (lpDebug & 1) {
                                    cout << "- " << *(*pItr) << " leads to pushing lower-bound of end point up to " << adder->first + EPSILON << endl;
                                }
                                
                                pushedForwards = !relevantTimelinePointsAndTheirEnds.empty();
                                boundForSuccessors = adder->first + EPSILON;
                                if (overallWorkingUpper < boundForSuccessors) {
                                    if (lpDebug & 1) {
                                        cout << "- This is after the upper bound of " << overallWorkingUpper << ", so the LP would be unsolvable\n";
                                    }
                                    solved = false; return;                                                                                                                
                                }
                            } else {
                                if (lpDebug & 1) {
                                    cout << "- " << *(*pItr) << " is okay for now: " << adder->first << " is below the known lower bound\n";
                                }
                            }
                            
                            relevantTimelinePointsAndTheirEnds.push_back(make_pair(adder, currTimeline->end()));                                                
                            
                        }
                        
                        for (int iCounter = 0; pushedForwards; ++iCounter) {
                                
                                
                            pushedForwards = false;
                            
                            if (lpDebug & 1) {
                                cout << "- Revisiting TIL timelines from " << boundForSuccessors << ", pass " << iCounter << endl;
                            }
                                
                            list<pair<TILTimeline::const_iterator, TILTimeline::const_iterator> >::iterator rtItr = relevantTimelinePointsAndTheirEnds.begin();
                            const list<pair<TILTimeline::const_iterator, TILTimeline::const_iterator> >::iterator rtEnd = relevantTimelinePointsAndTheirEnds.end();
                            
                            for (; rtItr != rtEnd; ++rtItr) {
                                
                                TILTimeline::const_iterator next = rtItr->first;
                                ++next;
                                
                                
                                if (next == rtItr->second) {
                                    // the last thing on the TIL timeline is an add
                                    continue;
                                }
                                
                                TILTimeline::const_iterator lastDeletorBeforeBoundForSuccessors = rtItr->second;

                                TILTimeline::const_iterator curr = rtItr->first;
                                
                                while (next != rtItr->second && next->first <= boundForSuccessors) {
                                    if (curr->second.deleted) {
                                        lastDeletorBeforeBoundForSuccessors = curr;
                                    }
                                    ++curr; ++next;                                    
                                }
                                
                                // curr points to the happening before the 'boundForSuccessors' time
                                
                                if (lastDeletorBeforeBoundForSuccessors != rtItr->second) {
                                    // some deletor has occurred between the previously relied upon TIL and now
                                    // thus, the next adder must precede nowAfter - push forwards the last deletor until we find an adding happening
                                    
                                    for (; lastDeletorBeforeBoundForSuccessors != rtItr->second && !lastDeletorBeforeBoundForSuccessors->second.added; ++lastDeletorBeforeBoundForSuccessors) ;
                                                                    
                                    if (lastDeletorBeforeBoundForSuccessors == rtItr->second) {
                                        // no new adder exists
                                        if (lpDebug & 1) {
                                            cout << "- There is no adder after a now-past deletor on this timeline\n";
                                        }
                                        solved = false;
                                        return;
                                    }
                                    
                                    rtItr->first = lastDeletorBeforeBoundForSuccessors;
                                    
                                    if (rtItr->first->first + EPSILON> boundForSuccessors) {
                                        boundForSuccessors = rtItr->first->first + EPSILON;
                                        if (lpDebug & 1) {
                                            cout << "- To get past a deletor on this timeline, and then be added again, the lower bound is pushed to " << boundForSuccessors << endl;
                                        }
                                        if (overallWorkingUpper < boundForSuccessors) {
                                            if (lpDebug & 1) {
                                                cout << "- This is after the upper bound of " << overallWorkingUpper << ", so the LP would be unsolvable\n";
                                            }
                                            solved = false; return;                                                                                                                
                                        }
                                        pushedForwards = true;
                                    }
                                    
                                } else {
                                    if (lpDebug & 1) {
                                        cout << "- Can keep pre-existing adder on this timeline\n";
                                    }
                                }
                                
                            }
                            
                        }
                    }
                }
                                               
                
                lp->setColLower(currVar, EpsilonResolutionTimestamp(boundForSuccessors,true).toDouble());

                /* if (implicitEnd) {
                    lp->setColLower(endsOfSkippableActions[stepID], unassignedLowerBound + EPSILON);
                }*/

                if (currEvent.getEffects && !tilVec.empty() && theState.nextTIL < tilVec.size()) {
                    // check for conflict with future TILs                    
                    
                    {
                        if (lpDebug & 1) {
                            cout << "Looking at preconditions attached to snap action\n";
                        }
                        const list<Literal*> & instantPres = (currTS == Planner::E_AT_START ? RPGBuilder::getStartPropositionalPreconditions()[actID] : RPGBuilder::getEndPropositionalPreconditions()[actID]);
                    
                        list<Literal*>::const_iterator pItr = instantPres.begin();
                        const list<Literal*>::const_iterator pEnd = instantPres.end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            
                            if (TemporalAnalysis::getFactIsAbstract()[(*pItr)->getStateID()]) {
                                continue;
                            }
                            
                            double local;
                            double workingUpper = DBL_MAX;
                                                
                            bool allTILs = true;
                            const list<pair<int, Planner::time_spec> > & deletors = RPGBuilder::getNegativeEffectsToActions()[(*pItr)->getStateID()];
                            list<pair<int, Planner::time_spec> >::const_iterator dItr = deletors.begin();
                            const list<pair<int, Planner::time_spec> >::const_iterator dEnd = deletors.end();
                            
                            for (; dItr != dEnd; ++dItr) {
                                if (dItr->second == Planner::E_AT) {
                                    #ifndef NDEBUG
                                    list<Literal*>::const_iterator delItr = tilVec[dItr->first]->delEffects.begin();
                                    const list<Literal*>::const_iterator delEnd = tilVec[dItr->first]->delEffects.end();
                                    
                                    for (; delItr != delEnd; ++delItr) {
                                        if ((*delItr)->getStateID() == (*pItr)->getStateID()) {
                                            break;
                                        }
                                    }
                                    
                                    if (delItr == delEnd) {
                                        std::cerr << "Fatal error: TIL " << dItr->first << " does not delete fact " << *(pItr) << ", as claimed\n";
                                        assert(delItr != delEnd);
                                    }
                                    #endif
                                    if (dItr->first >= theState.nextTIL) {
                                        local = tilVec[dItr->first]->duration - EPSILON;
                                        if (local < workingUpper) {
                                            workingUpper = local;
                                        }
                                    }
                                } else {                                    
                                    allTILs = false;
                                    break;
                                }
                            }
                            if (allTILs) {
                                if (lpDebug & 1) {
                                    if (workingUpper == DBL_MAX) {
                                        cout << "- " << *(*pItr) << " does not limit the latest point at which the action can occur\n";
                                    } else {
                                        cout << "- " << *(*pItr) << " limits it to " << workingUpper << endl;
                                    }
                                }

                                if (workingUpper < overallWorkingUpper) {
                                    overallWorkingUpper = workingUpper;
                                }
                            }
                        }
                    }
                    
                    
                    
                    if (currTS == Planner::E_AT_END) {
                        const list<Literal*> & invs = RPGBuilder::getInvariantPropositionalPreconditions()[actID];

                        list<Literal*>::const_iterator pItr = invs.begin();
                        const list<Literal*>::const_iterator pEnd = invs.end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            if (TemporalAnalysis::getFactIsAbstract()[(*pItr)->getStateID()]) {
                                continue;
                            }
                            
                            double local;
                            double workingUpper = DBL_MAX;

                            bool allTILs = true;
                            const list<pair<int, Planner::time_spec> > & deletors = RPGBuilder::getNegativeEffectsToActions()[(*pItr)->getStateID()];
                            list<pair<int, Planner::time_spec> >::const_iterator dItr = deletors.begin();
                            const list<pair<int, Planner::time_spec> >::const_iterator dEnd = deletors.end();
                            
                            for (; dItr != dEnd; ++dItr) {
                                if (dItr->second == Planner::E_AT) {
                                    if (dItr->first >= theState.nextTIL) {
                                        local = tilVec[dItr->first]->duration;
                                        if (local < workingUpper) {
                                            workingUpper = local;
                                        }
                                    }
                                } else {
                                    allTILs = false;
                                    break;
                                }
                            }
                            if (allTILs) {
                                if (workingUpper < overallWorkingUpper) {
                                    overallWorkingUpper = workingUpper;
                                }
                            }
                            
                        }
                    }
                    
                    if (lpDebug & 1 && overallWorkingUpper < DBL_MAX) {
                        cout << "Looking at negative TIL effects got working upper bound down to " << overallWorkingUpper << endl;
                    }
                    
                }
                
                if (optimised) {
                    double workingUpper = actionTSBounds[actID][currTS == Planner::E_AT_START ? 0 : 1].second;
//                    if (TILupbo < DBL_MAX) {
//                        if (workingUpper > TILupbo - EPSILON) workingUpper = TILupbo - EPSILON;
//                    }
                                        
                    if (overallWorkingUpper < workingUpper) {
                        workingUpper = overallWorkingUpper;
                    }

                    if (currEvent.lpMaxTimestamp < LPinfinity) {
                        if (workingUpper > currEvent.lpMaxTimestamp) workingUpper = currEvent.lpMaxTimestamp;
                    }

                    if (workingUpper < DBL_MAX) {
                        if (workingUpper != LPinfinity) {
                            if (workingUpper < boundForSuccessors) {
                                solved = false; return;
                            }
                            lp->setColUpper(currVar, EpsilonResolutionTimestamp(workingUpper,true).toDouble());
                        }
                    }
                } else {
                    if (overallWorkingUpper < DBL_MAX) {
                        if (overallWorkingUpper < boundForSuccessors) {
                            solved = false; return;
                        }
                        lp->setColUpper(currVar, EpsilonResolutionTimestamp(overallWorkingUpper,true).toDouble());
                    }
                }

            }

            const double plusEpsilon = boundForSuccessors + EPSILON;

            map<int, bool> & succs = fanOut[stepID];

            assert(!(currTS == Planner::E_AT && divisionID < 0 && !succs.empty()));
            
            map<int, bool>::iterator succItr = succs.begin();
            const map<int, bool>::iterator succEnd = succs.end();

            for (; succItr != succEnd; ++succItr) {
                double & toUpdate = unassignedLowerBounds[succItr->first];
                if (succItr->second) {
                    if (toUpdate < plusEpsilon) {
                        toUpdate = plusEpsilon;
                    }
                } else {
                    if (toUpdate < boundForSuccessors) {
                        toUpdate = boundForSuccessors;
                    }
                }
            }

            if (!currEvent.isDummyStep() && currEvent.time_spec != Planner::E_AT && boundForSuccessors > makespanVarMinimum) {
                makespanVarMinimum = boundForSuccessors;
            }
        }


        if (!currEvent.isDummyStep() && currTS != Planner::E_AT) {
            addConstraintsForTILMutexes(currVar, pointsThatWouldBeMutexWithOptimisationTILs[actID][currTS == Planner::E_AT_START ? 0 : 1]);
        }

        if (!boundsForAbstractFactOccurrences.empty() && (currTS == Planner::E_AT_START || currTS == Planner::E_AT_END)) {
            
            set<int> mergedWithOverAll;
            
            {
            
                const map<int,list<int> > & lookIn = TemporalAnalysis::getAbstractFactsUsedByActionOverAll();
                const map<int,list<int> >::const_iterator depItr = lookIn.find(actID);
            
                if (depItr != lookIn.end()) {
                    mergedWithOverAll.insert(depItr->second.begin(), depItr->second.end());
                    if (currTS == Planner::E_AT_START) {
                        // actually add the ordering constraints to the start--end pair
                        const map<int,list<int> > & lookInStart = TemporalAnalysis::getAbstractFactsUsedByActionStart();
                        const map<int,list<int> > & lookInEnd = TemporalAnalysis::getAbstractFactsUsedByActionEnd();
                        
                        map<int, pair<double,double> > offsets;                        
                        map<int, pair<double,double> >::iterator offsetItr = offsets.end();
                        
                        {
                            list<int>::const_iterator fItr = depItr->second.begin();
                            const list<int>::const_iterator fEnd = depItr->second.end();
                            
                            for (; fItr != fEnd; ++fItr) {
                                offsetItr = offsets.insert(offsetItr, make_pair(*fItr, make_pair(0.0,0.0)));
                            }
                        }

                        map<int, pair<double,double> >::iterator offsetEnd = offsets.end();
                        
                        {
                            const map<int,list<int> >::const_iterator startDepItr = lookInStart.find(actID);
                                
                            if (startDepItr != lookInStart.end()) {
                                list<int>::const_iterator fItr = startDepItr->second.begin();
                                const list<int>::const_iterator fEnd = startDepItr->second.end();
                                
                                for (; fItr != fEnd; ++fItr) {
                                    offsetItr = offsets.find(*fItr);
                                    if (offsetItr != offsetEnd) {
                                        offsetItr->second.first = EPSILON;
                                    }
                                }
                            }
                        }

                        {
                            const map<int,list<int> >::const_iterator endDepItr = lookInEnd.find(actID);
                                                        
                            if (endDepItr != lookInEnd.end()) {
                                list<int>::const_iterator fItr = endDepItr->second.begin();
                                const list<int>::const_iterator fEnd = endDepItr->second.end();
                                
                                for (; fItr != fEnd; ++fItr) {
                                    offsetItr = offsets.find(*fItr);
                                    if (offsetItr != offsetEnd) {
                                        offsetItr->second.second = EPSILON;
                                    }
                                }
                            }
                        }
                                                
                        offsetItr = offsets.begin();
                        
                        for (; offsetItr != offsetEnd; ++offsetItr) {
                            map<int, AbstractFactConstraintBlock>::iterator blockItr = planStepForAbstractFact.find(offsetItr->first);
                            if (blockItr == planStepForAbstractFact.end()) {
                                blockItr = planStepForAbstractFact.insert(make_pair(offsetItr->first, AbstractFactConstraintBlock(offsetItr->first, lp, numVars, boundsForAbstractFactOccurrences.find(-1 - divisionID)->second))).first;
                            }
                            if (lpDebug & 1) {
                                cout << COLOUR_light_magenta << "Registering step as over-all user of abstract fact " << *(RPGBuilder::getLiteral(offsetItr->first)) << COLOUR_default << endl;
                            }
                            blockItr->second.addOverAllUser(stepID, currEvent.pairWithStep, offsetItr->second.first, offsetItr->second.second);
                                                                            
                        }
                    } 
                
                }
            }
            
            {
                
                const map<int,list<int> > & lookIn = (currTS == Planner::E_AT_START ? TemporalAnalysis::getAbstractFactsUsedByActionStart()
                                                                                    : TemporalAnalysis::getAbstractFactsUsedByActionEnd());
                
                const map<int,list<int> >::const_iterator depItr = lookIn.find(actID);
                
                if (depItr != lookIn.end()) {
                    list<int>::const_iterator fItr = depItr->second.begin();
                    const list<int>::const_iterator fEnd = depItr->second.end();
                    
                    for (; fItr != fEnd; ++fItr) {
                        if (mergedWithOverAll.find(*fItr) != mergedWithOverAll.end()) {
                            continue;
                        }
                        map<int, AbstractFactConstraintBlock>::iterator blockItr = planStepForAbstractFact.find(*fItr);
                        if (blockItr == planStepForAbstractFact.end()) {
                            blockItr = planStepForAbstractFact.insert(make_pair(*fItr, AbstractFactConstraintBlock(*fItr, lp, numVars, boundsForAbstractFactOccurrences.find(-1 - divisionID)->second))).first;
                        }
                        if (lpDebug & 1) {
                            cout << COLOUR_light_magenta << "Registering step as a user of abstract fact " << *(RPGBuilder::getLiteral(*fItr)) << COLOUR_default << endl;
                        }
                        blockItr->second.addUser(stepID);
                    }
                }
            }
        }

        if (!currEvent.isDummyStep() && currEvent.getEffects) {

            InterestingMap currInterest;
            CountedConstraintSet activeInvariants;

            collateRelevantVariablesAndInvariants(currInterest, activeInvariants, stepID, currTS, actID,
                                                  activeAncestorsOfStep, correspondEndHasBeenInserted,
                                                  invariantsThisStepStartsOnVariableI);

            ValueOfVariablesAtSomeTime atStep;
            ValueOfVariablesAtSomeTime & beforeStep = fluentsAtStep[stepID];

            addConstraintsToGetValuesOfVariablesNow(currInterest, stepID, currVar, beforeStep);


            
            if (optimised && boundNow) {
                boundNow = false;

                if (secondMin || secondMax) {

                    ValueOfVariablesAtSomeTime::const_iterator bsItr = beforeStep.begin();
                    const ValueOfVariablesAtSomeTime::const_iterator bsEnd = beforeStep.end();

                    for (int v = 0; v < numVars; ++v) {

                        if (bsItr != bsEnd && (v == bsItr->first)) {
                            if (bsItr->second.first != -1) {
                                if (secondMin) lp->setColLower(bsItr->second.first, (*secondMin)[v]);
                                if (secondMax) lp->setColUpper(bsItr->second.first, (*secondMax)[v]);
                            } else {
                                assert(!secondMin || bsItr->second.second >= (*secondMin)[v]);
                                assert(!secondMax || bsItr->second.second <= (*secondMax)[v]);
                            }
                            ++bsItr;
                        } else {
                            const int update = finalNumericVars[v].lastEffectValueVariable;

                            if (update != -1) {
                                if (secondMin) lp->setColLower(update, (*secondMin)[v]);
                                if (secondMax) lp->setColUpper(update, (*secondMax)[v]);
                            } else {
                                assert(!secondMin || finalNumericVars[v].postLastEffectValue >= (*secondMin)[v]);
                                assert(!secondMax || finalNumericVars[v].postLastEffectValue <= (*secondMax)[v]);
                            }
                        }

                    }

                }
            }

            ValueOfVariablesAtSomeTime * constrsOver = &beforeStep;
            /*const int dummyEnd = */ generateEndDetails(currTS, actID, stepID, currEvent, planAsAVector, nextImaginaryEndVar, imaginaryMinMax);

            ConstraintAdder adder(this, currEvent, "inv@t", stepID, beforeStep);

            const map<int, list<vector<pair<const Constraint*, const Constraint*> > > >::const_iterator iceConds = (currTS != Planner::E_AT ? instantIntegralConstraints.find(actID)
                                                                                                                                            : instantIntegralConstraints.end());
            

            const list<vector<list<RPGBuilder::RPGNumericEffect* > > > * ice = 0;
            list<int> iceVars;
            
            if (iceConds != instantIntegralConstraints.end()) {
                map<int, list<vector<list<RPGBuilder::RPGNumericEffect* > > > >::const_iterator iceEffs = instantIntegralConditionalEffects.find(actID);
                assert(iceEffs != instantIntegralConditionalEffects.end());
                ice = &(iceEffs->second);
            }
            
            if (currTS == Planner::E_AT_START || currTS == Planner::E_AT_END) {

                constrsOver = &atStep;

                for_each(activeInvariants.begin(), activeInvariants.end(), adder);

                if (adder.wereConstraintsBroken()) {
                    solved = false;
                    return;
                }
                
                {

                    const int iPass = (currTS == Planner::E_AT_START ? 0 : 2);
                    list<const Constraint*> & currList = constraints[actID][iPass];

                    adder.changeLabel("pre@t");
                    for_each(currList.begin(), currList.end(), adder);
            
                    if (adder.wereConstraintsBroken()) {
                        solved = false;
                        return;
                    }
                    
                    
                    if (ice) {
                        
                        map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator defMapItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(actID);
                        
                        adder.changeLabel("icepre@t");
                        
                        list<RPGBuilder::IntegralContinuousEffect>::const_iterator defItr = defMapItr->second.begin();
                        list<vector<pair<const Constraint*, const Constraint*> > >::const_iterator icItr = iceConds->second.begin();
                        const list<vector<pair<const Constraint*, const Constraint*> > >::const_iterator icEnd = iceConds->second.end();
                        
                        for (; icItr != icEnd; ++icItr, ++defItr) {
                            if (defItr->getTS() != currTS) {
                                continue;
                            }
                            
                            const int lb = defItr->getIntegerLB();
                            if (lb == -1) {
                                continue;
                            }
                            
                            lp->addCol(emptyEntries, lb, defItr->getIntegerUB(), MILPSolver::C_INT);
                            
                            iceVars.push_back(lp->getNumCols() - 1);
                            
                            if (nameLPElements) {
                                ostringstream s;
                                s << "ice" << stepID;                                
                                lp->setColName(iceVars.back(), s.str());
                            }
                            
                            if (lpDebug & 1) {
                                cout << COLOUR_yellow << "Created integer conditional effect variable " << lp->getColName(iceVars.back()) << " with range [" << lp->getColLower(iceVars.back()) << "," << lp->getColUpper(iceVars.back()) << "]\n" << COLOUR_default;
                            }
                            
                            adder.setRHSModifier(iceVars.back(), defItr->getLeftPreconditionDifference());
                            adder.operator()((*icItr)[iPass].first);
                            
                            adder.setRHSModifier(iceVars.back(), defItr->getRightPreconditionDifference());
                            adder.operator()((*icItr)[iPass].second);
                            
                            adder.clearRHSModifier();
                            
                        }
                    }


                    adder.changeLabel("inv@t");
                    
                }


                InterestingMap untouched(currInterest);
                list<int> unstableNextTime;

                list<RPGBuilder::RPGNumericEffect* > & currEffs = instantEffects[actID][(currTS == Planner::E_AT_START ? 0 : 1)];

                adder.supplyEffectData(atStep, untouched, stableNextTime, unstableNextTime);

                for_each(currEffs.begin(), currEffs.end(), adder);

                if (ice) {
                    map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator defMapItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(actID);                    
                    assert(defMapItr != RPGBuilder::getActionsToIntegralConditionalEffects().end());
                    
                    list<int>::const_iterator ivItr = iceVars.begin();
                    
                    list<RPGBuilder::IntegralContinuousEffect>::const_iterator icItr = defMapItr->second.begin();
                    const list<RPGBuilder::IntegralContinuousEffect>::const_iterator icEnd = defMapItr->second.end();
                    
                    for (; icItr != icEnd; ++icItr) {
                        if (icItr->getTS() != currTS) {
                            continue;
                        }
                        
                        const list<pair<int,double> > & effs = (currTS == Planner::E_AT_START ? icItr->getLeftStartEffects() : icItr->getLeftEndEffects());
            
                        list<pair<int,double> >::const_iterator effItr = effs.begin();
                        const list<pair<int,double> >::const_iterator effEnd = effs.end();
                        
                        for (; effItr != effEnd; ++effItr) {
                            adder.setRHSModifier(*ivItr, effItr->second);
                            adder.operator()(&(RPGBuilder::getNumericEff()[effItr->first]));
                        }
                        
                        ++ivItr;
                    }
                    
                    adder.clearRHSModifier();
                }
 
                if (workOutFactLayerZeroBoundsStraightAfterRecentAction) {
                
                    list<Literal*> & currPropEffs = (currTS == Planner::E_AT_START ? RPGBuilder::getStartPropositionAdds()[actID]  : RPGBuilder::getEndPropositionAdds()[actID]);

                    for_each(currPropEffs.begin(), currPropEffs.end(), adder);
                    
                    if (adder.wereConstraintsBroken()) {
                        solved = false;
                        return;
                    }
                    
                }
                
                {
                    list<int>::iterator unstItr = unstableNextTime.begin();
                    const list<int>::iterator unstEnd = unstableNextTime.end();

                    for (; unstItr != unstEnd; ++unstItr) {
                        if (lpDebug & 1) cout << "Variable " << *(RPGBuilder::getPNE(*unstItr)) << " becomes unstable after an instantaneous effect\n";
                        stableVariable[*unstItr] = false;
                    }
                }


                {
                    int colIdx = lp->getNumCols();
                    int constrIdx = lp->getNumRows();
                    InterestingMap::iterator sItr = untouched.begin();
                    const InterestingMap::iterator sItrEnd = untouched.end();

                    for (; sItr != sItrEnd; ++sItr, ++colIdx, ++constrIdx) {
                        
                        if (finalNumericVars[sItr->first].statusOfThisFluent != FluentTracking::FS_NORMAL) {
                            --colIdx;
                            --constrIdx;
                            continue;
                        }
                        
                        #ifndef NDEBUG
                        bool foundCTS = false;
                        if (sItr->second) {
                            list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > & geList = gradientEffects[actID][0];
                            list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geItr = geList.begin();
                            const list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geEnd = geList.end();

                            for (; geItr != geEnd; ++geItr) {
                                if (geItr->first == sItr->first) {
                                    foundCTS = true;
                                    break;
                                }
                            }
                        }
                        assert(!sItr->second || foundCTS);
                        #endif

                        atStep.copyVRecordFrom(sItr->first, beforeStep);
                        
                        /*static vector<pair<int,double> > entries(2);

                        entries[0].second = 1.0;
                        entries[1].second = -1.0;

                        entries[0].first = colIdx;
                        entries[1].first = beforeStep[sItr->first];

                        assert(lp->getNumCols() == colIdx);
                        
                        lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);

                        assert((lp->getNumCols() -1) == colIdx);
                        
                        if (nameLPElements) {
                            ostringstream namestream;
                            namestream << *(RPGBuilder::getPNE(sItr->first));
                            namestream << "a" << stepID;
                            string asString = namestream.str();
                            lp->setColName(colIdx, asString);
                        }


                        lp->addRow(entries, 0.0, 0.0);

                        if (nameLPElements) {
                            ostringstream namestream;
                            namestream << "no-eff@" << stepID << "n" << constrIdx;
                            string asString = namestream.str();
                            lp->setRowName(constrIdx, asString);
                        }

                        atStep[sItr->first] = colIdx;*/
                    }
                }
            }

            if (currTS == Planner::E_AT_START) {
                activeInvariants.insert(constraints[actID][1].begin(), constraints[actID][1].end());
                if (lpDebug & 1024) {
                    cout << COLOUR_light_green << "Recording invariants started at " << stepID << COLOUR_default << endl;
                }
                recordVariablesInvolvedInThisStepsInvariants(constraints[actID][1], invariantsThisStepStartsOnVariableI[stepID]);
                
            } else if (currTS == Planner::E_AT_END) {
                activeInvariants.erase(constraints[actID][1].begin(), constraints[actID][1].end());
                correspondEndHasBeenInserted[currEvent.pairWithStep] = true;               
            }

            adder.applyTo = constrsOver;

            for_each(activeInvariants.begin(), activeInvariants.end(), adder);

            bool durationIsFixed = true;
            
            if (currTS == Planner::E_AT_START && !RPGBuilder::getRPGDEs(actID).empty()) {


                DurationAdder durAdder(this, currEvent, stepID, beforeStep, stableVariable);

                RPGBuilder::RPGDuration* const currDuration = RPGBuilder::getRPGDEs(actID).back();

                if (!currDuration->fixed.empty()) {

                    durAdder.setStartEnd(currVar, imaginaryMinMax[stepID].imaginaryMin, VAL::E_EQUALS);
                    for_each(currDuration->fixed.begin(), currDuration->fixed.end(), durAdder);
                }

                if (!currDuration->min.empty()) {

                    durAdder.setStartEnd(currVar, imaginaryMinMax[stepID].imaginaryMin, VAL::E_GREATEQ);
                    for_each(currDuration->min.begin(), currDuration->min.end(), durAdder);

                }

                if (!currDuration->max.empty()) {

                    durAdder.setStartEnd(currVar, (currDuration->fixed.empty() ? imaginaryMinMax[stepID].imaginaryMax : imaginaryMinMax[stepID].imaginaryMin), VAL::E_LESSEQ);
                    for_each(currDuration->max.begin(), currDuration->max.end(), durAdder);

                }
                
                durationIsFixed = durAdder.durationIsFixed;

            }

            if (currTS == Planner::E_AT_START) {
                list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > & geList = gradientEffects[actID][0];
                list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geItr = geList.begin();
                const list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geEnd = geList.end();
                for (; geItr != geEnd; ++geItr) {
                    FluentTracking & currTracker = finalNumericVars[geItr->first];

                    if (currTracker.statusOfThisFluent != FluentTracking::FS_NORMAL) {
                        if (lpDebug & 1) {
                            cout << "Ignoring order-independent CTS effect on " << *(RPGBuilder::getPNE(geItr->first)) << endl;
                        }
                        // If the status is FS_IGNORE, we should ignore it;
                        // If the status is FS_ORDER_INDEPENDENT, we can just take
                        // the integral of the change at the end
                        continue;
                    }
                    ++(currTracker.activeGradientCount);
                    currTracker.activeGradient += geItr->second.constant;
                    currTracker.lastEffectTimestampVariable = timestampVars[stepID];
                    const ValueOfVariablesAtSomeTime::const_iterator valItr = constrsOver->find(geItr->first);
                    assert(valItr != constrsOver->end());
                    
                    currTracker.lastEffectValueVariable = valItr->second.first;
                    currTracker.postLastEffectValue = valItr->second.second;

                    stableVariable[geItr->first] = false;
                    
                    if (!durationIsFixed) {
                        
                        // If an action has a non-constant-valued duration AND a cts effect on a variable, then we need to
                        // mark that that variable is subject to duration-dependent change.  Otherwise, it will be considered
                        // stable once the action has ended; whereas, really, the time it ends at (and hence the
                        // cumulative effect) can vary.
                        if (lpDebug & 1) cout << "Variable " << *(RPGBuilder::getPNE(geItr->first)) << " becomes duration-dependent\n";
                        finalNumericVars[geItr->first].everHadADurationDependentEffect = true;
                    }
                    
                    if (lpDebug & 1) {
                        cout << "Variable " << *(RPGBuilder::getPNE(geItr->first)) << " becomes unstable due to CTS effect; gradient is now " << currTracker.activeGradient << "\n";
                    }
                }

            } else if (currTS == Planner::E_AT_END) {

                list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > & geList = gradientEffects[actID].back();
                list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geItr = geList.begin();
                const list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geEnd = geList.end();
                for (; geItr != geEnd; ++geItr) {

                    FluentTracking & currTracker = finalNumericVars[geItr->first];
                    
                    if (currTracker.statusOfThisFluent == FluentTracking::FS_NORMAL) {
                        if (!--(currTracker.activeGradientCount)) {
                            currTracker.activeGradient = 0.0;
                            if (!finalNumericVars[geItr->first].everHadADurationDependentEffect) {
                                stableNextTime.push_back(geItr->first);
                                if (lpDebug & 1) cout << "Variable " << *(RPGBuilder::getPNE(geItr->first)) << " becomes stable next time: " << currTracker.activeGradientCount << " active gradients on it, and never a duration-dependent effect\n";
                            }
                        } else {
                            currTracker.activeGradient -= geItr->second.constant;
                        }
                        
                    } else if (currTracker.statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT) {
                        
                        // For order-independent change, we integrate the effect that has just finished -
                        // add gradient * (end - start) to the terms
                        
                        currTracker.orderIndependentValueTerms.insert(make_pair(timestampVars[stepID], 0.0)).first->second += geItr->second.constant;
                        currTracker.orderIndependentValueTerms.insert(make_pair(timestampVars[correspondingStart[stepID]], 0.0)).first->second -= geItr->second.constant;
                        
                        if (lpDebug & 1) {
                            cout << "Noting order-independent CTS effect on " << *(RPGBuilder::getPNE(geItr->first)) << endl;
                            cout << " = " << geItr->second.constant << " * (" << lp->getColName(timestampVars[stepID]);
                            cout << " - " << lp->getColName(timestampVars[correspondingStart[stepID]]) << ")\n";
                                 
                        }
                        
                        
                    }
                }

            }

            {

                InterestingMap::iterator ciItr = currInterest.begin();
                const InterestingMap::iterator ciEnd = currInterest.end();

                for (; ciItr != ciEnd; ++ciItr) {
                    if (ciItr->second) {
                        const int effVar = ciItr->first;
                        FluentTracking & currTracker = finalNumericVars[effVar];

                        if (currTracker.statusOfThisFluent == FluentTracking::FS_NORMAL) {
                            currTracker.lastEffectTimestampVariable = timestampVars[stepID];
                            
                            const ValueOfVariablesAtSomeTime::const_iterator valItr = constrsOver->find(effVar);
                            assert(valItr != constrsOver->end());
                            
                            currTracker.lastEffectValueVariable = valItr->second.first;
                            currTracker.postLastEffectValue = valItr->second.second;
                            
                        }
                    }
                }

            }

        }




        {

            set<int> ancestorsToPassOn = activeAncestorsOfStep[stepID];
            if (currEvent.time_spec == Planner::E_AT_START) {
                if (!constraints[actID][1].empty()) {
                    ancestorsToPassOn.insert(stepID);
                }
            } else if (currEvent.time_spec == Planner::E_AT_END) {
                ancestorsToPassOn.erase(currEvent.pairWithStep);
            }

            // Finally, handle ordering constraints

            bool tilSwitch = false;

            map<int, bool>::iterator foItr = fanOut[stepID].begin();
            const map<int, bool>::iterator foEnd = fanOut[stepID].end();

            if (foItr == foEnd) {
                if (currEvent.time_spec != Planner::E_AT) endsOfThreads.push_back(timestampVars[stepID]);
            } else {
                for (; foItr != foEnd; ++foItr) {
                    const int succ = foItr->first;
                    if (!(--(fanIn[succ]))) {
                        openList.push_back(succ);
                        if (lpDebug & 512) {
                            cout << "No predecessors remaining for " << succ << " - placing it on the open list\n";
                        }
                    } else {
                        if (lpDebug & 512) {
                            cout << "Now only " << fanIn[succ] << " predecessors for step " << succ << endl;
                        }
                    }

                    // remembering to push forwards which invariants need to be checked at each successor step

                    activeAncestorsOfStep[succ].insert(ancestorsToPassOn.begin(), ancestorsToPassOn.end());

                    if (currEvent.time_spec != Planner::E_AT) {
                        if (planAsAVector[succ]->time_spec == Planner::E_AT) {
                            if (!tilSwitch) {
                                endsOfThreads.push_back(timestampVars[stepID]);
                                tilSwitch = true;
                            }
                        }
                    }
                }
            }
        }

    }

    if (actuallyVisited < mustVisit) {
        if (lpDebug & 2) {
            cout << "Never visited:\n";
            
            {
                int stepID = 0;
                for (int pass = 0; pass < 2; ++pass) {
                    list<FFEvent> & currList = (pass ? now : header);
                    
                    list<FFEvent>::iterator citr = currList.begin();
                    const list<FFEvent>::iterator cend = currList.end();
                    
                    for (; citr != cend; ++citr, ++stepID, ++mustVisit) {
                        
                        if (fanIn[stepID]) {
                            cout << stepID << ": ";
                            if (planAsAVector[stepID]->isDummyStep()) {
                                cout << "\tDummy";
                            } else if (planAsAVector[stepID]->action) {
                                if (planAsAVector[stepID]->time_spec == Planner::E_AT_START) {
                                    cout << "\t" << *(planAsAVector[stepID]->action) << ", start";
                                } else {
                                    cout << "\t" << *(planAsAVector[stepID]->action) << ", end";
                                }
                            }
                            cout << endl;
                        }
                        
                    }
                }
            }
        
        }
        solved = false;
        return;
    }

    // Now to sort out 'now'.
    // First, find which variables are undergoing continuous change, and make a pair of placeholder variables:
    // - one for the time at which we are going to read their value
    // - one containing the value itself
    //
    // This loop will add constraints for the latter, linking its value to the last thing that changed it, and scheduling it after that
    // After that, we add constraints to the former scheduling it before the ends of open actions who are changing this variable

    // The timestamp of 'now', if doing total order search
    int totalOrderNowTimestamp = -1;

    static const double bigLimitOnTimes = 10000000.0;
    
    for (int varID = 0; varID < numVars; ++varID) {
        FluentTracking & currTracker = finalNumericVars[varID];

        // for fluents we are ignoring, or putting straight into the metric, we can skip this
        if (currTracker.statusOfThisFluent != FluentTracking::FS_NORMAL) continue;
        
        // if no gradients are active, 'lastEffectValueVariable' is adequate as it can't have changed since then        
        if (!currTracker.activeGradientCount) continue;

        lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);

        const int nowValueIdx = lp->getNumCols() - 1;

        if (nameLPElements) {
            ostringstream namestream;
            namestream << *(RPGBuilder::getPNE(varID));
            namestream << "-now-v";
            string asString = namestream.str();
            lp->setColName(nowValueIdx, asString);
        }
        
        if (Globals::totalOrder) {
            
            if (totalOrderNowTimestamp == -1) {
                lp->addCol(emptyEntries, 0.0, bigLimitOnTimes, MILPSolver::C_REAL);                
                totalOrderNowTimestamp = lp->getNumCols() - 1;
                
                if (nameLPElements) {
                    lp->setColName(totalOrderNowTimestamp, "now-to");
                }
                
                static vector<pair<int,double> > entries(2);
                
                entries[0].first = totalOrderNowTimestamp;
                
                assert(timestampToUpdateVar != -1);
                
                entries[1].first = timestampToUpdateVar;
                entries[0].second = 1.0;
                entries[1].second = -1.0;
                
                // 'now' must come no sooner than epsilon after the most recent step
                lp->addRow(entries, EPSILON, LPinfinity);
                
                if (nameLPElements) {
                    const int constrIdx = lp->getNumRows() - 1;
                    lp->setRowName(constrIdx, "last-before-now-t");
                }
                
            }
        }
        int nowTimeIdx;
            
        {

            lp->addCol(emptyEntries, 0.0, bigLimitOnTimes, MILPSolver::C_REAL);

            nowTimeIdx = lp->getNumCols() - 1;

            if (nameLPElements) {
                ostringstream namestream;
                namestream << *(RPGBuilder::getPNE(varID));
                namestream << "-now-t";
                string asString = namestream.str();
                lp->setColName(nowTimeIdx, asString);
            }

            // now need to encode tnow >= tlast
            // i.e. tnow - tlast >= 0

            if (currTracker.lastEffectTimestampVariable == -1) {
            
                // special case: ongoing effect is due to a process rather than action
                // so previous time-step doesn't exist: it's just time zero
                // hence, we can do nothing: this step is at least after zero
                
                if (Globals::totalOrder) {
                    static vector<pair<int,double> > entries(2);
                
                    entries[0].first = nowTimeIdx;                
                    entries[1].first = totalOrderNowTimestamp;
                    entries[0].second = 1.0;
                    entries[1].second = -1.0;

                    lp->addRow(entries, 0.0, LPinfinity);

                    if (nameLPElements) {
                        const int constrIdx = lp->getNumRows() - 1;
                        ostringstream namestream;
                        namestream << *(RPGBuilder::getPNE(varID));
                        namestream << "-process-now-t";
                        string asString = namestream.str();
                        lp->setRowName(constrIdx, asString);
                    }
                    
                    if (lpDebug & 1) {                        
                        cout << "now for " << *(RPGBuilder::getPNE(varID)) << " must follow " << lp->getColName(totalOrderNowTimestamp) << endl;
                    }

                }
                
            } else {
                static vector<pair<int,double> > entries(2);
                
                if (!Globals::totalOrder) {
                    entries[0].first = nowTimeIdx;                
                    entries[1].first = currTracker.lastEffectTimestampVariable;
                    entries[0].second = 1.0;
                    entries[1].second = -1.0;

                    lp->addRow(entries, 0.0, LPinfinity);

                    if (nameLPElements) {
                        const int constrIdx = lp->getNumRows() - 1;
                        ostringstream namestream;
                        namestream << *(RPGBuilder::getPNE(varID));
                        namestream << "-last-now-t";
                        string asString = namestream.str();
                        lp->setRowName(constrIdx, asString);
                    }
                    
                    if (lpDebug & 1) {                        
                        cout << "now for " << *(RPGBuilder::getPNE(varID)) << " must follow " << lp->getColName(currTracker.lastEffectTimestampVariable);
                    }
                    
                } else {
                    
                    entries[0].first = nowTimeIdx;                
                    entries[1].first = totalOrderNowTimestamp;
                    entries[0].second = 1.0;
                    entries[1].second = -1.0;

                    lp->addRow(entries, 0.0, LPinfinity);

                    if (nameLPElements) {
                        const int constrIdx = lp->getNumRows() - 1;
                        ostringstream namestream;
                        namestream << *(RPGBuilder::getPNE(varID));
                        namestream << "-last-now-t";
                        string asString = namestream.str();
                        lp->setRowName(constrIdx, asString);
                    }
                    
                    if (lpDebug & 1) {                        
                        cout << "now for " << *(RPGBuilder::getPNE(varID)) << " must follow " << lp->getColName(totalOrderNowTimestamp);
                    }
                    
                    set<int>::const_iterator pcolItr = currTracker.nowMustFollowCols.begin();
                    const set<int>::const_iterator pcolEnd = currTracker.nowMustFollowCols.end();
                    
                    for (; pcolItr != pcolEnd; ++pcolItr) {
                        if (*pcolItr == totalOrderNowTimestamp) {
                            continue;
                        }
                        entries[0].first = nowTimeIdx;                
                        entries[1].first = *pcolItr;
                        entries[0].second = 1.0;
                        entries[1].second = -1.0;

                        lp->addRow(entries, 0.0, LPinfinity);

                        if (nameLPElements) {
                            const int constrIdx = lp->getNumRows() - 1;
                            ostringstream namestream;
                            namestream << *(RPGBuilder::getPNE(varID));
                            namestream << "-last-now-to" << *pcolItr;
                            string asString = namestream.str();
                            lp->setRowName(constrIdx, asString);
                        }
                        
                        if (lpDebug & 1) {                        
                            cout << " and " << lp->getColName(totalOrderNowTimestamp);
                        }

                    }                    
                }
                if (lpDebug & 1) {
                    cout << endl;
                }
            }
        }
        
        if (currTracker.lastEffectTimestampVariable == -1) {
            
            // now need to encode v(now) = 0 + grad * (tnow)
            // i.e. v(now) - grad * tnow  = 0
                        
            static vector<pair<int,double> > entries(2);
            
            entries[0].first = nowValueIdx;
            entries[1].first = nowTimeIdx;
            
            entries[0].second = 1.0;
            entries[1].second = -currTracker.activeGradient;
            
            lp->addRow(entries, 0.0, 0.0);
            
            if (nameLPElements) {
                const int constrIdx = lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << *(RPGBuilder::getPNE(varID));
                namestream << "-now";
                string asString = namestream.str();
                lp->setRowName(constrIdx, asString);
            }
        } else {
        
            // now need to encode v(now) = v(last) + grad * (tnow - tlast)
            // i.e. v(now) - v(last) - grad * tnow + grad * tlast = 0
            static vector<pair<int,double> > entries(4);
            
            entries[0].first = nowValueIdx;
            entries[1].first = currTracker.lastEffectValueVariable;
            entries[2].first = nowTimeIdx;
            entries[3].first = currTracker.lastEffectTimestampVariable;

            entries[0].second = 1.0;
            entries[1].second = -1.0;
            entries[2].second = -currTracker.activeGradient;
            entries[3].second = currTracker.activeGradient;

            lp->addRow(entries, 0.0, 0.0);

            if (nameLPElements) {
                const int constrIdx = lp->getNumRows() - 1;
                ostringstream namestream;
                namestream << *(RPGBuilder::getPNE(varID));
                namestream << "-now";
                string asString = namestream.str();
                lp->setRowName(constrIdx, asString);
            }
        }

        // this specific now then becomes the latest thing to establish a value for this variable

        currTracker.lastEffectTimestampVariable = nowTimeIdx;
        currTracker.lastEffectValueVariable = nowValueIdx;

    }

    for (int stepID = 0; stepID < tsVarCount; ++stepID) {

        FFEvent & currEvent = *(planAsAVector[stepID]);

        if (currEvent.isDummyStep()) continue;
        if (currEvent.time_spec != Planner::E_AT_END) continue;
        if (currEvent.getEffects) continue; // if we don't get its effects yet, it must be the end of an open action

        const int actID = currEvent.action->getID();
        
        list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > & geList = gradientEffects[actID][0];

        list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geItr = geList.begin();
        const list<pair<int, RPGBuilder::LinearEffects::EffectExpression> >::iterator geEnd = geList.end();

        for (; geItr != geEnd; ++geItr) {
            FluentTracking & currTracker = finalNumericVars[geItr->first];

            // skip for fluents we are ignoring, or adding straight to the objective
            if (currTracker.statusOfThisFluent != FluentTracking::FS_NORMAL) continue;
            
            
            // now need to encode tend >= tnow
            // i.e. tend - tnow >= 0
            {
                static vector<pair<int,double> > entries(2);
                
                entries[0].first = timestampVars[stepID];
                entries[1].first = currTracker.lastEffectTimestampVariable;
                entries[0].second = 1.0;
                entries[1].second = -1.0;

                lp->addRow(entries, 0.0, LPinfinity);

                if (nameLPElements) {
                    const int constrIdx = lp->getNumRows() - 1;
                    ostringstream namestream;
                    namestream << "tnow" << *(RPGBuilder::getPNE(geItr->first)) << " <= t" << stepID;
                    string asString = namestream.str();
                    lp->setRowName(constrIdx, asString);
                }
            }

        }
    }

    {


        map<int, list<list<StartEvent>::iterator > >::iterator ceItr = compulsaryEnds.begin();
        const map<int, list<list<StartEvent>::iterator > >::iterator ceEnd = compulsaryEnds.end();

        for (; ceItr != ceEnd; ++ceItr) {
            list<list<StartEvent>::iterator >::iterator matchItr = ceItr->second.begin();
            const list<list<StartEvent>::iterator >::iterator matchEnd = ceItr->second.end();

            for (; matchItr != matchEnd; ++matchItr) {
                if ((*matchItr)->ignore) continue;
                
                int suffix = 0;
                // add invariants from this action
                
                const list<const Constraint*> & invs = constraints[(*matchItr)->actID][1];
                
                {
                    list<const Constraint*>::const_iterator invItr = invs.begin();
                    const list<const Constraint*>::const_iterator invEnd = invs.end();
                    
                    for (; invItr != invEnd; ++invItr) {
                        
                        
                        const int cSize = (*invItr)->weights.size();

                        vector<pair<int,double> > entries;
                        entries.reserve(cSize + 2);
                        
                        if (LPScheduler::lpDebug & 1024) {
                            cout << "Adding constraint: ";
                            for (int s = 0 ; s < cSize; ++s) {
                                if (s) cout << " + ";                
                                cout << (*invItr)->weights[s] << "*";
                                if ((*invItr)->variables[s] == -3) {
                                    cout << "?duration";
                                } else if ((*invItr)->variables[s] == -4) {
                                    cout << "total-time";
                                } else {                
                                    cout << lp->getColName(finalNumericVars[(*invItr)->variables[s]].lastEffectValueVariable);
                                }

                            }
                            if ((*invItr)->lower != -DBL_MAX) {
                                cout << ", >= " << (*invItr)->lower;
                            }
                            if ((*invItr)->upper != DBL_MAX) {
                                cout << ", <= " << (*invItr)->upper;
                            }
                            cout << std::endl;
                        }

                        int lastVar;
                        double fixedLHS = 0.0;
                        
                        for (int s = 0 ; s < cSize; ++s) {
                            if ((*invItr)->variables[s] < 0) {
                                if ((*invItr)->variables[s] == -3) {
                                    int startStep = timestampVars[(*matchItr)->stepID];
                                    int endStep = timestampVars[(*matchItr)->stepID + 1];
                                    
                                    entries.push_back(make_pair(endStep, (*invItr)->weights[s]));
                                    entries.push_back(make_pair(startStep, -(*invItr)->weights[s]));
                                    
                                } else {
                                    std::cerr << "Fatal internal error: variable index " << (*invItr)->variables[s] << " used\n";
                                    exit(1);
                                }
                            } else {
                                lastVar = finalNumericVars[(*invItr)->variables[s]].lastEffectValueVariable;
                                if (lastVar >= 0) {
                                    entries.push_back(make_pair(lastVar, (*invItr)->weights[s]));
                                    if (assertions) assert(entries.back().second != 0.0);
                                } else {
                                    fixedLHS += (*invItr)->weights[s] * finalNumericVars[(*invItr)->variables[s]].postLastEffectValue;
                                }

                            }
                        }

                        lp->addRow(entries,
                                   ((*invItr)->lower != -DBL_MAX ? (*invItr)->lower - fixedLHS : -LPinfinity),
                                   ((*invItr)->upper != DBL_MAX  ? (*invItr)->upper - fixedLHS : LPinfinity ) );

                        if (nameLPElements) {
                            const int constrIdx = lp->getNumRows() - 1;
                            ostringstream namestream;
                            namestream << "nowinv" << (*matchItr)->stepID << "n" << suffix;
                            string asString = namestream.str();
                            lp->setRowName(constrIdx, asString);
                            ++suffix;
                        }                    
                        
                    }
                }
                
                /*if (!RPGBuilder::getSemaphoreFacts().empty() && !(constraints[(*matchItr)->actID][1].empty() && constraints[(*matchItr)->actID][2].empty())) {
                
                    set<int> blockedOtherEffectsOnVar;
                    
                    {
                        const list<Literal*> & endAdds = RPGBuilder::getEndPropositionAdds()[(*matchItr)->actID];
                        
                        list<Literal*>::const_iterator aItr = endAdds.begin();
                        const list<Literal*>::const_iterator aEnd = endAdds.end();
                        
                        for (int fID; aItr != aEnd; ++aItr) {
                            fID = (*aItr)->getStateID();
                            if (theState.first.find(fID) != theState.first.end()) {
                                continue;
                            }
                            
                            const map<int, RPGBuilder::Guarded>::const_iterator gItr = RPGBuilder::getSemaphoreFacts().find(fID);
                            if (gItr != RPGBuilder::getSemaphoreFacts().end()) {
                                
                                // the end of this action will restore the ability to change to the given variable
                                // until then, any active gradients will persist
                                
                                blockedOtherEffectsOnVar.insert(gItr->second.guardedEffectVars.begin(),gItr->second.guardedEffectVars.end());
                                
                            }
                        }
                    }
                    
                    if (!blockedOtherEffectsOnVar.empty()) {
                        
                        if (lpDebug & 1) {
                            cout << COLOUR_yellow << "The execution of " << *(RPGBuilder::getInstantiatedOp((*matchItr)->actID)) << " is blocking access to some vars\n" << COLOUR_default;
                        }
                        // now see how many invariants or end conditions we can write in terms of variables this action has exclusive effect-access to
                        ConstraintSet checkInvs;
                        map<int,int> needVars;
                        
                        for (int ppass = 1; ppass < 3; ++ppass) {
                            list<const Constraint*>::const_iterator invItr = constraints[(*matchItr)->actID][ppass].begin();
                            const list<const Constraint*>::const_iterator invEnd = constraints[(*matchItr)->actID][ppass].end();
                            
                            for (; invItr != invEnd; ++invItr) {
                                int s = 0;
                                const int cSize = (*invItr)->weights.size();
                                for (; s < cSize; ++s) {
                                    if (blockedOtherEffectsOnVar.find((*invItr)->variables[s]) == blockedOtherEffectsOnVar.end()) {
                                        break;
                                    }
                                }
                                if (s == cSize) {
                                    // all the mentioned variables are locked by the current action
                                    checkInvs.insert((*invItr));

                                    for (s = 0; s < cSize; ++s) {
                                        if ((*invItr)->variables[s] >= 0) {
                                            needVars.insert(make_pair((*invItr)->variables[s],-1));
                                        }
                                    }
                                }
                            }
                        }
                        
                        {
                            map<int,int>::iterator nvItr = needVars.begin();
                            const map<int,int>::iterator nvEnd = needVars.end();
                            
                            for (; nvItr != nvEnd; ++nvItr) {
                                FluentTracking & currTracker = finalNumericVars[nvItr->first];
                                if (currTracker.activeGradientCount == 0 || fabs(currTracker.activeGradient) < 0.00001 ) {
                                    // if there are no gradients active, just take the var holding its previous value
                                    nvItr->second = currTracker.lastEffectValueVariable; 
                                                                            
                                    if (lpDebug & 1) {
                                        cout << "Future value of " << *(RPGBuilder::getPNE(nvItr->first)) << " is the same as the last value\n";
                                    }

                                } else {
                                                                            
                                    if (lpDebug & 1) {
                                        cout << "Extrapolating future value of " << *(RPGBuilder::getPNE(nvItr->first)) << " based on active gradients\n";
                                    }

                                    // need to add a constraint to extrapolate the value of the variable at the end of the action
                                    
                                    lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);                                                                        
                                    
                                    nvItr->second = lp->getNumCols() - 1;
                                    
                                    if (nameLPElements) {
                                        ostringstream namestream;
                                        namestream << *(RPGBuilder::getPNE(nvItr->first));
                                        namestream << "guarded" << (*matchItr)->stepID + 1;
                                        string asString = namestream.str();
                                        lp->setColName(nvItr->second, asString);
                                    }
                                    
                                    if (currTracker.lastEffectValueVariable != -1) {

                                        static vector<pair<int,double> > entries(4);
                                        
                                        entries[0].second = 1.0;
                                        entries[1].second = -1.0;
                                        entries[2].second = -currTracker.activeGradient;
                                        entries[3].second = currTracker.activeGradient;

                                        if (assertions) assert(entries[3].second != 0.0);
                                        if (assertions) assert(entries[2].second != 0.0);

                                        entries[0].first = nvItr->second;
                                        entries[1].first = currTracker.lastEffectValueVariable;
                                        entries[2].first = timestampVars[(*matchItr)->stepID + 1];
                                        entries[3].first = currTracker.lastEffectTimestampVariable;

                                        lp->addRow(entries, 0.0, 0.0);

                                    } else {
                                        static vector<pair<int,double> > entries(3);
                                        
                                        entries[0].second = 1.0;
                                        entries[1].second = -currTracker.activeGradient;
                                        entries[2].second = currTracker.activeGradient;

                                        if (assertions) assert(entries[2].second != 0.0);
                                        if (assertions) assert(entries[1].second != 0.0);

                                        entries[0].first = nvItr->second;
                                        entries[1].first = timestampVars[(*matchItr)->stepID + 1];
                                        entries[2].first = currTracker.lastEffectTimestampVariable;

                                        lp->addRow(entries, currTracker.postLastEffectValue, currTracker.postLastEffectValue); // syntax for EQ prev

                                    }

                                    if (nameLPElements) {
                                        ostringstream namestream;
                                        namestream << "guard" <<  (*matchItr)->stepID + 1 << "delta-" << *(RPGBuilder::getPNE(nvItr->first));
                                        string asString = namestream.str();
                                        lp->setRowName(lp->getNumRows() - 1 , asString);
                                    }
                                }
                            }
                        }
                        
                        {
                            
                            ConstraintSet::const_iterator invItr = checkInvs.begin();
                            const ConstraintSet::const_iterator invEnd = checkInvs.end();
                            
                            for (int gi = 0; invItr != invEnd; ++invItr, ++gi) {
                                
                                
                                const int cSize = (*invItr)->weights.size();

                                vector<pair<int,double> > entries;
                                entries.reserve(cSize + 2);
                                
                                if (LPScheduler::lpDebug & 1024) {
                                    cout << "Adding constraint: ";
                                    for (int s = 0 ; s < cSize; ++s) {
                                        if (s) cout << " + ";                
                                        cout << (*invItr)->weights[s] << "*";
                                        if ((*invItr)->variables[s] == -3) {
                                            cout << "?duration";
                                        } else if ((*invItr)->variables[s] == -4) {
                                            cout << "total-time";
                                        } else {                
                                            cout << lp->getColName(needVars.find((*invItr)->variables[s])->second);
                                        }

                                    }
                                    if ((*invItr)->lower != -DBL_MAX) {
                                        cout << ", >= " << (*invItr)->lower;
                                    }
                                    if ((*invItr)->upper != DBL_MAX) {
                                        cout << ", <= " << (*invItr)->upper;
                                    }
                                    cout << std::endl;
                                }

                                double extraForLHS = 0.0;

                                for (int s = 0 ; s < cSize; ++s) {
                                    if ((*invItr)->variables[s] < 0) {
                                        if ((*invItr)->variables[s] == -3) {
                                            int startStep = timestampVars[(*matchItr)->stepID];
                                            int endStep = timestampVars[(*matchItr)->stepID + 1];
                                            
                                            entries.push_back(make_pair(endStep, (*invItr)->weights[s]));
                                            entries.push_back(make_pair(startStep, -(*invItr)->weights[s]));
                                            
                                        } else {
                                            std::cerr << "Fatal internal error: variable index " << (*invItr)->variables[s] << " used\n";
                                            exit(1);
                                        }
                                    } else {
                                        const map<int,int>::const_iterator nvItr = needVars.find((*invItr)->variables[s]);
                                        
                                        assert(nvItr != needVars.end());
                                        
                                        if (nvItr->second == -1) {
                                            extraForLHS = (*invItr)->weights[s] * finalNumericVars[(*invItr)->variables[s]].postLastEffectValue;
                                        } else {                                        
                                            entries.push_back(make_pair(nvItr->second, (*invItr)->weights[s]));
                                            if (assertions) assert(entries.back().second != 0.0);
                                        }
                                    }
                                }

                                lp->addRow(entries,
                                           ((*invItr)->lower != -DBL_MAX ? (*invItr)->lower - extraForLHS : -LPinfinity),
                                           ((*invItr)->upper != DBL_MAX  ? (*invItr)->upper - extraForLHS : LPinfinity ) );

                                if (nameLPElements) {
                                    const int constrIdx = lp->getNumRows() - 1;
                                    ostringstream namestream;
                                    namestream << "gi" << (*matchItr)->stepID << "n" << gi;
                                    string asString = namestream.str();
                                    lp->setRowName(constrIdx, asString);
                                }                    
                                
                            }
                            
                        }
                    }
                    
                }*/
                
            }
        }
    }


    { // now add the movable 'now' timestamp



        {
            map<int, list<list<StartEvent>::iterator > >::iterator ceItr = compulsaryEnds.begin();
            const map<int, list<list<StartEvent>::iterator > >::iterator ceEnd = compulsaryEnds.end();

            for (; ceItr != ceEnd; ++ceItr) {
                //const int actID = ceItr->first;
                //list<EndDetails> & destList = openDurationConstraints[actID];
                list<list<StartEvent>::iterator >::iterator matchItr = ceItr->second.begin();
                const list<list<StartEvent>::iterator >::iterator matchEnd = ceItr->second.end();

                for (; matchItr != matchEnd; ++matchItr) {
                    if ((*matchItr)->ignore) continue;
                    //EndDetails & currEndDetails = imaginaryMinMax[(*matchItr)->stepID];

                    /*if (optimised) {
                        const double localMin = (*matchItr)->lpMinTimestamp;
                        const double localMax = (*matchItr)->lpMaxTimestamp;
                        if (localMax < COIN_DBL_MAX) {
                            {
                                double exUp = lp->getColUpper()[currEndDetails.imaginaryMax];
                                if (exUp > localMax) {
                                    lp->setColUpper(currEndDetails.imaginaryMax, localMax);
                                }
                            }
                            {
                                double exUp = lp->getColUpper()[currEndDetails.imaginaryMin];
                                if (exUp > localMax) {
                                    lp->setColUpper(currEndDetails.imaginaryMin, localMax);
                                }
                            }
                        }
                        {
                            double exLow = lp->getColLower()[currEndDetails.imaginaryMax];
                            if (exLow < localMin) {
                                lp->setColLower(currEndDetails.imaginaryMax, localMin);
                            }
                        }
                        {
                            double exLow = lp->getColLower()[currEndDetails.imaginaryMin];
                            if (exLow < localMin) {
                                lp->setColLower(currEndDetails.imaginaryMin, localMin);
                            }
                        }


                    }*/

                    /*{

                        weightScratch[0] = -1.0;
                        weightScratch[1] = 1.0;

                        varScratch[0] = currVar;
                        varScratch[1] = currEndDetails.imaginaryMax;

                        lp->addRow(2, varScratch, weightScratch, 0.0, COIN_DBL_MAX);

                        currEndDetails.first = *matchItr;

                        destList.push_back(currEndDetails);

                                                if (nameLPElements) {
                            int constrIdx = lp->getNumRows() - 1;
                            ostringstream namestream;
                            namestream << "tnow < iEnd" << (*matchItr)->stepID;
                            string asString = namestream.str();
                            lp->setRowName(constrIdx, asString);
                        }

                    }*/

                    /*if (orderOptimised) {
                        set<int>::iterator orderItr = (*matchItr)->getEndComesBefore().begin();
                        const set<int>::iterator orderEnd = (*matchItr)->getEndComesBefore().end();

                        for (; orderItr != orderEnd; ++orderItr) {

                            if (*orderItr == -1) {
                                const int colIdx = imaginaryMinMax[(*matchItr)->stepID].imaginaryMin;
                                if (lp->getColUpper()[colIdx] < TILupbo) lp->setColUpper(colIdx, TILupbo);
                            } else {
                                weightScratch[0] = -1.0;
                                weightScratch[1] = 1.0;

                                varScratch[0] = imaginaryMinMax[(*matchItr)->stepID].imaginaryMin;
                                varScratch[1] = imaginaryMinMax[*orderItr].imaginaryMin;

                                lp->addRow(2, varScratch, weightScratch, 0.001, DBL_MAX);

                                if (nameLPElements) {
                                    int constrIdx = lp->getNumRows() - 1;
                                    ostringstream namestream;
                                    namestream << imaginaryMinMax[(*matchItr)->stepID].imaginaryMin << " ecb " << imaginaryMinMax[*orderItr].imaginaryMin;
                                    string asString = namestream.str();
                                    lp->setRowName(constrIdx, asString);
                                }
                            }
                        }
                    }*/

                    /*if (orderOptimised) {
                        set<int>::iterator orderItr = (*matchItr)->getEndComesAfter().begin();
                        const set<int>::iterator orderEnd = (*matchItr)->getEndComesAfter().end();

                        for (; orderItr != orderEnd; ++orderItr) {
                            weightScratch[0] = 1.0;
                            weightScratch[1] = -1.0;

                            varScratch[0] = imaginaryMinMax[(*matchItr)->stepID].imaginaryMin;
                            varScratch[1] = imaginaryMinMax[*orderItr].imaginaryMin;

                            lp->addRow(2, varScratch, weightScratch, 0.001, DBL_MAX);

                            if (nameLPElements) {
                                int constrIdx = lp->getNumRows() - 1;
                                ostringstream namestream;
                                namestream << imaginaryMinMax[(*matchItr)->stepID].imaginaryMin << " eca " << imaginaryMinMax[*orderItr].imaginaryMin;
                                string asString = namestream.str();
                                lp->setRowName(constrIdx, asString);
                            }

                        }
                    }*/


                    /*if (prevVar != -1) {
                        weightScratch[0] = -1.0;
                        weightScratch[1] = 1.0;

                        varScratch[0] = prevVar;
                        varScratch[1] = currEndDetails.imaginaryMin;

                        lp->addRow(2, varScratch, weightScratch, 0.001, COIN_DBL_MAX);

                                                if (nameLPElements) {
                            int constrIdx = lp->getNumRows() - 1;
                            ostringstream namestream;
                            namestream << "iend" << (*matchItr)->stepID << " tprev";
                            string asString = namestream.str();
                            lp->setRowName(constrIdx, asString);
                        }
                    }*/


                    /*                    RPGBuilder::RPGDuration* currDuration = RPGBuilder::getRPGDEs(actID)[(*matchItr)->divisionsApplied];

                                        if (currDuration->fixed) {
                                            varScratch[0] = currVar;
                                            varScratch[1] = timestampVars[(*matchItr)->stepID];

                                            RPGBuilder::DurationExpr * const currDE = currDuration->fixed;
                                            const int vSize = currDE->weights.size();
                                            for (int v = 0; v < vSize; ++v) {
                                                weightScratch[2+v] = currDE->weights[v];
                                                if (assertions) assert(weightScratch[2+v] != 0.0);
                                                varScratch[2+v] = fluentsAtStep[(*matchItr)->stepID][currDE->variables[v]];
                                            }
                                            weightScratch[0] = -1.0;
                                            weightScratch[1] = 1.0;

                                            const double rTerm = (currDE->constant == 0.0 ? 0.0 : -currDE->constant);
                                            add_constraintex(lp, 2 + vSize, weightScratch, varScratch, GE, rTerm);
                                            ++constrIdx;
                                            destList.push_back(pair<list<StartEvent>::iterator, int>(*matchItr, constrIdx));

                                        } else if (currDuration->max) {
                                            varScratch[0] = currVar;
                                            varScratch[1] = timestampVars[(*matchItr)->stepID];

                                            RPGBuilder::DurationExpr * const currDE = currDuration->max;

                                            const int vSize = currDE->weights.size();
                                            for (int v = 0; v < vSize; ++v) {
                                                weightScratch[2+v] = currDE->weights[v];
                                                if (assertions) assert(weightScratch[2+v] != 0.0);
                                                varScratch[2+v] = fluentsAtStep[(*matchItr)->stepID][currDE->variables[v]];
                                            }
                                            weightScratch[0] = -1.0;
                                            weightScratch[1] = 1.0;

                                            const double rTerm = (currDE->constant == 0.0 ? 0.0 : -currDE->constant);

                                            add_constraintex(lp, 2 + vSize, weightScratch, varScratch, GE, rTerm);
                                            ++constrIdx;
                                            destList.push_back(pair<list<StartEvent>::iterator, int>(*matchItr, constrIdx));
                                        } else {
                                            destList.push_back(pair<list<StartEvent>::iterator, int>(*matchItr, -1));
                                        }
                    */

                }
            }

        }

    }

    if (Globals::optimiseSolutionQuality) {
        getVarForReachableCost(preferenceStatus, theState.prefPreconditionViolations);
    }
    
    if (lpDebug & 1) cout << "LP complete, " << lp->getNumCols() << " columns, " << lp->getNumRows() << " rows\n";

    if (setObjectiveToMetric) {
        if (!scheduleToMetric()) {
            solved = false;
            return;
        }
    }
    


//    if (lpDebug & 2) print_lp(lp);
    if (lpDebug & 4) nicerLPPrint(lp);
    if (lpDebug & 8) checkForZeroRows(lp);

    if (optVar == -1) {
        assert(newDummySteps.empty());
        timestampToUpdateVarLB = 0.0;
        solved = true;
        recalculateAbstractFactBounds();
        return;
    } else {
        
        previousObjectiveVar = optVar;                
        lp->setObjCoeff(optVar, 1.0);
    }

    solved = true;
    
    if (!newDummySteps.empty()) {
        if (lpDebug & 1) cout << "Doing minimisations for dummy steps\n";
        
        lp->setObjCoeff(previousObjectiveVar, 0.0);
        
        map<int, pair<int, double> >::iterator dsItr = newDummySteps.begin();
        const map<int, pair<int, double> >::iterator dsEnd = newDummySteps.end();
        
        for (; dsItr != dsEnd; ++dsItr) {
     
            previousObjectiveVar = dsItr->second.first;
            
            lp->setObjCoeff(previousObjectiveVar, 1.0);
            
            if (lpDebug & 8) {
                lp->writeLp("stateevaluationdummy.lp");
            }
            if (lpDebug & 1) {
                cout << "About to call solve, optimising " << lp->getColName(previousObjectiveVar) << ":";
                cout.flush();
            }
            
            solved = lp->solve(false);

            if (solved) {
                dsItr->second.second = lp->getObjValue();
                
                if (lpDebug & 1) {
                    cout << dsItr->second.second << endl;
                }
                    
            } else {
                if (lpDebug & 1) {
                    cout << "LP unsolvable" << endl;
                }
            }
            
            lp->setObjCoeff(previousObjectiveVar, 0.0);

            
            if (!solved) {
                break;
            }
        }
        
        previousObjectiveVar = optVar;
                
        lp->setObjCoeff(optVar, 1.0);
        
    }

    if (solved && planAsAVector[justAppliedStep]->time_spec == Planner::E_AT_START
               && TemporalAnalysis::canSkipToEnd(planAsAVector[justAppliedStep]->action->getID())) {

        if (lpDebug & 1) cout << "Doing minimisation for compression-safe end\n";
        
        lp->setObjCoeff(previousObjectiveVar, 0.0);
        
        previousObjectiveVar = optVar + 1;
            
        lp->setObjCoeff(previousObjectiveVar, 1.0);
            
        if (lpDebug & 8) {
            lp->writeLp("stateevaluationcs.lp");
        }
        if (lpDebug & 1) {
            cout << "About to call solve, optimising " << lp->getColName(previousObjectiveVar) << ":";
            cout.flush();
        }
            
        solved = lp->solve(false);

        if (solved) {
            timestampToUpdateVarEndLB.insert(make_pair(previousObjectiveVar - numVars, lp->getObjValue()));
            
            if (lpDebug & 1) {
                cout << "- Earliest time is " << timestampToUpdateVarEndLB.find(optVar-numVars)->second << ", recording as bound on " << lp->getColName(previousObjectiveVar) <<  endl;
            }
                
        } else {
            if (lpDebug & 1) {
                cout << "LP unsolvable" << endl;
            }
        }
        
        lp->setObjCoeff(previousObjectiveVar, 0.0);

            
        previousObjectiveVar = optVar;
                
        lp->setObjCoeff(optVar, 1.0);

        
    }
    
    if (solved) {
        map<int, list<list<StartEvent>::iterator > >::iterator ceItr = compulsaryEnds.begin();
        const map<int, list<list<StartEvent>::iterator > >::iterator ceEnd = compulsaryEnds.end();

        for (; ceItr != ceEnd; ++ceItr) {
            list<list<StartEvent>::iterator >::iterator matchItr = ceItr->second.begin();
            const list<list<StartEvent>::iterator >::iterator matchEnd = ceItr->second.end();
            
            for (; matchItr != matchEnd; ++matchItr) {
                assert(!TemporalAnalysis::canSkipToEnd((*matchItr)->actID));
            
                if (lpDebug & 1) cout << "Doing minimisation for unfinished end of " << *(RPGBuilder::getInstantiatedOp((*matchItr)->actID)) << endl;
            
                lp->setObjCoeff(previousObjectiveVar, 0.0);
                
                previousObjectiveVar = numVars + ((*matchItr)->stepID + 1);
                    
                lp->setObjCoeff(previousObjectiveVar, 1.0);
                    
                if (lpDebug & 8) {
                    lp->writeLp("stateevaluationcs.lp");
                }
                if (lpDebug & 1) {
                    cout << "About to call solve, optimising " << lp->getColName(previousObjectiveVar) << ":";
                    cout.flush();
                }
                    
                solved = lp->solve(false);

                if (solved) {
                    timestampToUpdateVarEndLB.insert(make_pair(((*matchItr)->stepID + 1), lp->getObjValue()));
            
                    if (lpDebug & 1) {
                        cout << "- Earliest time is " << timestampToUpdateVarEndLB.find(((*matchItr)->stepID + 1))->second << ", recording as bound on " << lp->getColName((*matchItr)->stepID + 1 + numVars) <<  endl;
                    }
                        
                } else {
                    if (lpDebug & 1) {
                        cout << "LP unsolvable" << endl;
                    }
                }
                
                lp->setObjCoeff(previousObjectiveVar, 0.0);

                    
                previousObjectiveVar = optVar;
                        
                lp->setObjCoeff(optVar, 1.0);
            }
        }
    }
    
    if (solved) {

        if (lpDebug & 8) {
            lp->writeLp("stateevaluation.lp");
            cout << "About to call solve, optimising " << lp->getColName(previousObjectiveVar) << "\n";
        }

        solved = lp->solve(false);
        
        if (lpDebug & 8) {
            if (solved) {
                cout << "Solve called succeeded\n";
            } else {
                cout << "Solve called failed\n";
            }
        }
    }
    
    if (solved) {
        if (shouldFail) {
            if (cd) cd->printDotFile(cout);
        }
        assert(!shouldFail);
        
        timestampToUpdateVarLB = lp->getObjValue();
        static const map<int,double> rpLowerBounds;
        sortOutTheSolution(setObjectiveToMetric, justAppliedStep, preferenceStatus, theState.prefPreconditionViolations, rpLowerBounds);
        
    } else {
        if (lpDebug) {
            if (shouldSucceed) {
                cout << "According to STP, LP call should have succeeded\n";
                if (cd) cd->printDotFile(cout);
            }
        }
        if (Globals::paranoidScheduling) {
            assert(!shouldSucceed);
        }
    }
};

int LPScheduler::getVarForReachableCost(vector<AutomatonPosition::Position> & preferenceStatus, const double & preconditionPrefViolations)
{
    if (varForReachableCost != -1) {
        return varForReachableCost;
    }

    if (!NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
        return -1;
    }            
    
    static const bool localDebug = (lpDebug & 1);
    
    const RPGBuilder::Metric * metric = RPGBuilder::getMetric();
        
    double currentCostFromNonPreferenceParts = 0.0;
        
    const vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getPreferences();
        
    list<double>::const_iterator wItr = metric->weights.begin();
    const list<double>::const_iterator wEnd = metric->weights.end();
        
    list<int>::const_iterator vItr = metric->variables.begin();
    
    static int metricLastTime = 10;
    
    map<int,double> entries;
    
    for (; wItr != wEnd; ++wItr, ++vItr) {
        
        if (*vItr < 0) {
            assert(*vItr == -4); // :makespan
            entries.insert(make_pair(getDummyVarForMakespan(), 0.0)).first->second += *wItr;
            continue;
        }
            
        assert(*vItr >= 0 && *vItr < RPGBuilder::getPNECount());
        const FluentTracking & currFT = finalNumericVars[*vItr];
        
        if (currFT.statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT) {
            
            currentCostFromNonPreferenceParts += currFT.orderIndependentValueConstant * *wItr;
            
           
            if (!currFT.orderIndependentValueTerms.empty()) {
                if (lpDebug & 1) {
                    cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.orderIndependentValueConstant * *wItr << " + some weighted sum\n";
                }
                                    
                map<int,double>::const_iterator oiTerms = currFT.orderIndependentValueTerms.begin();
                const map<int,double>::const_iterator oiTermsEnd = currFT.orderIndependentValueTerms.end();
                
                for (; oiTerms != oiTermsEnd; ++oiTerms) {
                    entries.insert(make_pair(oiTerms->first,0.0)).first->second += oiTerms->second * *wItr;
                    if (lpDebug & 1) {
                        cout << "\t\t+ " << lp->getColName(oiTerms->first) << " * " << oiTerms->second * *wItr << endl;
                    }
                }
            } else {
                if (lpDebug & 1) {
                    cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.orderIndependentValueConstant * *wItr << endl;
                }                                            
            }
        } else {
        
            if (currFT.lastEffectValueVariable == -1) {
                currentCostFromNonPreferenceParts += currFT.postLastEffectValue * *wItr;
                if (lpDebug & 1) {
                    cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.postLastEffectValue * *wItr << endl;
                } 
            } else {
                entries.insert(make_pair(currFT.lastEffectValueVariable,0.0)).first->second += *wItr;
                if (lpDebug & 1) {
                    cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " is determined by variable " << currFT.lastEffectValueVariable << endl;
                } 
            }
        }
    }
        
                                        
    double baselinePrefReachable = preconditionPrefViolations;
    if (!RPGBuilder::getPreferences().empty()) {
        map<int, list<int> >::const_iterator ppMapItr = varsForPreconditionPreference.begin();
        const map<int, list<int> >::const_iterator ppMapEnd = varsForPreconditionPreference.end();
        
        for (; ppMapItr != ppMapEnd; ++ppMapItr) {
            const double weight = prefs[ppMapItr->first].cost;
            
            list<int>::const_iterator ppVar = ppMapItr->second.begin();
            const list<int>::const_iterator ppEnd = ppMapItr->second.end();
            
            for (; ppVar != ppEnd; ++ppVar) {
                entries.insert(make_pair(*ppVar, 0.0)).first->second += weight;

            }                
            
        }    
            
                            
        {
            map<int, VarsForPreference>::const_iterator prefItr = varsForPreference.begin();
            const map<int, VarsForPreference>::const_iterator prefEnd = varsForPreference.end();
            
            const int prefCount = PreferenceHandler::getInitialAutomataPositions().size();
            int prefID = 0;
            double currPrefCost;
            for (; prefID < prefCount && prefItr != prefEnd; ++prefID) {
                
                currPrefCost = prefs[prefID].cost;
                
                if (currPrefCost == DBL_MAX) {
                    
                    if (prefID < prefItr->first) {
                        if (PreferenceHandler::preferenceDebug && lpDebug & 1) {
                            cout << "Constraint " << prefID << " excluded from contributing to cost: the plan has not interacted with it\n";
                        }
                    } else {
                        ++prefID;
                    }
                } else {
                    if (prefID < prefItr->first) {
                        if (PreferenceHandler::preferenceDebug && lpDebug & 1) {
                            cout << "Contribution to baseline current pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getCurrentCost(prefID, preferenceStatus) << endl;
                        }
                        baselinePrefReachable += PreferenceHandler::getReachableCost(prefID, preferenceStatus);
                    } else {
                        if (prefItr->second.reachableCostVar >= 0) { // some preferences have zero reachable cost
                            entries.insert(make_pair(prefItr->second.reachableCostVar,0.0)).first->second += currPrefCost;
                        }
                        ++prefItr;
                    }
                }
            }
            
            for (; prefID < prefCount; ++prefID) {
                currPrefCost = prefs[prefID].cost;
                
                if (currPrefCost != DBL_MAX) {
                    if (PreferenceHandler::preferenceDebug && lpDebug & 1) {
                        cout << "Contribution to baseline current pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getCurrentCost(prefID, preferenceStatus) << endl;
                    }
                    baselinePrefReachable += PreferenceHandler::getReachableCost(prefID, preferenceStatus);
                }
            }
            
        }
    }

    unavoidableReachablePlanCost = currentCostFromNonPreferenceParts + metric->constant + RPGBuilder::getPermanentViolationCost() + baselinePrefReachable;
    
    if (entries.empty()) {        
        varForReachableCost = -2;
        return varForReachableCost;
    }
    
    static const vector<pair<int,double> > emptyEntries;

    static const double tolerance = 1.0/1000.0;
    
    double roundedUnavoidablePlanCost = unavoidableReachablePlanCost;
    
    if (Globals::optimiseSolutionQuality && Globals::bestSolutionQuality > -DBL_MAX) {
        
        if (metric->minimise) {
            int roundedUp = ceil(-Globals::bestSolutionQuality / tolerance);
            lp->addCol(emptyEntries, -LPinfinity, roundedUp * tolerance, MILPSolver::C_REAL);
            roundedUnavoidablePlanCost = floor(unavoidableReachablePlanCost / tolerance) * tolerance;
        } else {
            int roundedUp = floor(Globals::bestSolutionQuality / tolerance);
            lp->addCol(emptyEntries, roundedUp * tolerance, LPinfinity, MILPSolver::C_REAL);
            roundedUnavoidablePlanCost = ceil(unavoidableReachablePlanCost / tolerance) * tolerance;
        }
        
    } else {
        lp->addCol(emptyEntries, -LPinfinity, LPinfinity, MILPSolver::C_REAL);
    }
    
    {
        lp->setColName(lp->getNumCols() - 1, "flexiblecost");
    }
    
    varForReachableCost = lp->getNumCols() - 1;
    
    if (localDebug) {
        cout << "Unavoidable plan cost, rounded = " << roundedUnavoidablePlanCost << endl;
        cout << "Upper limit on cost variable = " << lp->getColUpper(varForReachableCost) << endl;
    }
    
    entries.insert(make_pair(varForReachableCost, -1.0));
    
    vector<pair<int,double> > entriesVec;
    entriesVec.insert(entriesVec.end(), entries.begin(), entries.end());
    
    
    lp->addRow(entriesVec, -roundedUnavoidablePlanCost, -roundedUnavoidablePlanCost);

    {
        lp->setRowName(lp->getNumRows() - 1, "reachablecost");
    }
    
    return varForReachableCost;
    
}

void LPScheduler::recalculateAbstractFactBounds()
{
    {
        const int restoreVar = previousObjectiveVar;
        
        map<int, AbstractFactConstraintBlock>::iterator factItr = planStepForAbstractFact.begin();
        const map<int, AbstractFactConstraintBlock>::iterator factEnd = planStepForAbstractFact.end();
        
        for (; factItr != factEnd; ++factItr) {
            
            const vector<int> * wasUsed = factItr->second.needToReviseBounds();
            
            if (!wasUsed) {
                if (lpDebug & 1) {
                    cout << COLOUR_yellow << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << " - never used, so LB stays at ";
                    cout << planAsAVector[factItr->second.getBoundsStep()]->lpMinTimestamp;
                    cout << COLOUR_default << endl;
                }
                
                continue;
            }
            
            if (previousObjectiveVar != -1) {
                lp->setObjCoeff(previousObjectiveVar, 0.0);
                previousObjectiveVar = -1;
            }
            
            if (lpDebug & 1) {
                cout << COLOUR_yellow << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << " - calculating LB:";
                cout.flush();
            }
            
            const int outcomeCount = wasUsed->size();
            
            int occ = 0;
            for (; occ < outcomeCount; ++occ) {
                
                lp->setObjCoeff((*wasUsed)[occ], 1.0);                
                const bool available = lp->solve(true);
                lp->setObjCoeff((*wasUsed)[occ], 0.0);
                
                if (lpDebug & 1) {
                    if (available) { 
                        cout << " " << occ << ", yes.";
                        cout.flush();
                    } else {
                        cout << " " << occ << ", no;";
                        cout.flush();
                    }
                }
                
                
                if (available) {                    
                    break;
                }                                
            }
            
            if (occ == outcomeCount) {
                if (lpDebug & 1) {
                    cout << " has expired.\n";
                }
                planAsAVector[factItr->second.getBoundsStep()]->lpMinTimestamp = DBL_MAX;
                planAsAVector[factItr->second.getBoundsStep()]->lpTimestamp = DBL_MAX;
                factItr->second.markAsNoLongerAvailable();
            } else {
                planAsAVector[factItr->second.getBoundsStep()]->lpMinTimestamp = factItr->second.getOccurrenceBounds()[occ].first;
                planAsAVector[factItr->second.getBoundsStep()]->lpTimestamp = factItr->second.getOccurrenceBounds()[occ].first;
                
                if (lpDebug & 1) {
                    cout << " so available from " << planAsAVector[factItr->second.getBoundsStep()]->lpMinTimestamp << endl;
                }
            }
            
            if (lpDebug & 1) {
                cout << COLOUR_default;
            }
        }
        
        if (previousObjectiveVar == -1 && restoreVar != -1) {
            lp->setObjCoeff(restoreVar, 1.0);
            previousObjectiveVar = restoreVar;
        }
        
    }

}


void LPScheduler::sortOutTheSolution(const bool & setObjectiveToMetric, const int & justAppliedStep, vector<AutomatonPosition::Position> & preferenceStatus, const double & preconditionPrefViolations, const map<int,double> & rpLowerBounds)
{
    const int loopLim = planAsAVector.size();

    static const bool optimised = true;
    {
        const double * const partialSoln = lp->getPartialSolution(numVars, numVars + loopLim);        

        assert(!cd || !cd->willSetTimestamps());
        
        for (int stepID = 0; stepID < loopLim; ++stepID) {
            FFEvent * const itr = planAsAVector[stepID];
            if (itr->time_spec == Planner::E_AT) {
                if (itr->divisionID >= 0) {
                    itr->lpTimestamp = TILtimestamps[itr->divisionID];
                }
                continue;
            }
            itr->lpTimestamp = partialSoln[timestampVars[stepID] - numVars];
            if (lpDebug & 2 && !itr->isDummyStep()) {
                cout << "Timestamp of " << *(itr->action) << " (var " << timestampVars[stepID] << ") ";
                if (itr->time_spec == Planner::E_AT_START) cout << " start = "; else cout << "end = ";
                cout << itr->lpTimestamp << "\n";                
            }
        }
    }

    if (!setObjectiveToMetric) {
        
        if (Globals::paranoidScheduling && cd && !cd->doLPSolve()) {
            cd->distsToLPMinStampsAndCheck(planAsAVector);
        }
        
        if (optimised) {
            if (timestampToUpdate || !newDummySteps.empty()) {
                pushTimestampToMin(preferenceStatus, timestampToUpdateVarEndLB, rpLowerBounds);
            }
        }                                        
                            

        if (Globals::paranoidScheduling && cd && !cd->doLPSolve()) {
            cd->distsToLPStamps(justAppliedStep);
        }
    }

    /*if (lpDebug & 8 && !mutexCols.empty()) {
        cout << "Values of TIL mutex column variables:\n";
        {
            list<int>::const_iterator mcItr = mutexCols.begin();
            const list<int>::const_iterator mcEnd = mutexCols.end();
            for (; mcItr != mcEnd; ++mcItr) {
                cout << "\t" << lp->getColName(*mcItr) << " = " << lp->getSingleSolutionVariableValue(*mcItr) << endl;
                assert(lp->isColumnBinary(*mcItr));
            }
        }
        
        cout << "Values of TIL mutex rows:\n";
        {
            list<int>::const_iterator mcItr = mutexRows.begin();
            const list<int>::const_iterator mcEnd = mutexRows.end();
            for (; mcItr != mcEnd; ++mcItr) {
                printRow(lp, *mcItr, *mcItr+1);
                cout << "\t" << lp->getRowName(*mcItr) << " = " << lp->getSingleSolutionRowValue(*mcItr) << endl;
            }
        }
    }*/

    recalculateAbstractFactBounds();
    
    if (Globals::optimiseSolutionQuality && RPGBuilder::getMetric()) {                        
        
        planCostsNeededAnLP = false;
        const int restoreVar = previousObjectiveVar;
        
        const RPGBuilder::Metric * metric = RPGBuilder::getMetric();
        
        double currentCostFromNonPreferenceParts = 0.0;
        
        const vector<RPGBuilder::Constraint> & prefs = RPGBuilder::getPreferences();

        list<double>::const_iterator wItr = metric->weights.begin();
        const list<double>::const_iterator wEnd = metric->weights.end();
        
        list<int>::const_iterator vItr = metric->variables.begin();
        
        for (; wItr != wEnd; ++wItr, ++vItr) {
            
            if (*vItr < 0) {
                assert(*vItr == -4); // :makespan
                if (!planCostsNeededAnLP) {                        
                    planCostsNeededAnLP = true;
                    if (previousObjectiveVar != -1) {
                        lp->setObjCoeff(previousObjectiveVar, 0.0);
                        previousObjectiveVar = -1;
                    }
                }
                lp->setObjCoeff(getDummyVarForMakespan(), *wItr);
                continue;
            }
            
            assert(*vItr >= 0 && *vItr < RPGBuilder::getPNECount());
            const FluentTracking & currFT = finalNumericVars[*vItr];
            
            if (currFT.statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT) {
                
                currentCostFromNonPreferenceParts += currFT.orderIndependentValueConstant * *wItr;
                
               
                if (!currFT.orderIndependentValueTerms.empty()) {
                    if (lpDebug & 1) {
                        cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.orderIndependentValueConstant * *wItr << " + some weighted sum\n";
                    }
                                        
                    if (!planCostsNeededAnLP) {                        
                        planCostsNeededAnLP = true;
                        if (previousObjectiveVar != -1) {
                            lp->setObjCoeff(previousObjectiveVar, 0.0);
                            previousObjectiveVar = -1;
                        }
                    }
                    
                    map<int,double>::const_iterator oiTerms = currFT.orderIndependentValueTerms.begin();
                    const map<int,double>::const_iterator oiTermsEnd = currFT.orderIndependentValueTerms.end();
                    
                    for (; oiTerms != oiTermsEnd; ++oiTerms) {
                        lp->setObjCoeff(oiTerms->first, oiTerms->second * *wItr);
                        if (lpDebug & 1) {
                            cout << "\t\t+ " << lp->getColName(oiTerms->first) << " * " << oiTerms->second * *wItr << endl;
                        }
                    }
                } else {
                    if (lpDebug & 1) {
                        cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.orderIndependentValueConstant * *wItr << endl;
                    }                                            
                }
            } else {
            
                if (currFT.lastEffectValueVariable == -1) {
                    currentCostFromNonPreferenceParts += currFT.postLastEffectValue * *wItr;
                    if (lpDebug & 1) {
                        cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " = " << currFT.postLastEffectValue * *wItr << endl;
                    } 
                } else {
                    if (!planCostsNeededAnLP) {                        
                        planCostsNeededAnLP = true;
                        if (previousObjectiveVar != -1) {
                            lp->setObjCoeff(previousObjectiveVar, 0.0);
                            previousObjectiveVar = -1;
                        }
                    }
                    lp->setObjCoeff(currFT.lastEffectValueVariable, *wItr);
                    if (lpDebug & 1) {
                        cout << "Contribution to baseline current cost by " << *(RPGBuilder::getPNE(*vItr)) << " is determined by variable " << currFT.lastEffectValueVariable << endl;
                    } 
                }
            }
        }
        
                                        
        double baselinePrefReachable = preconditionPrefViolations;
        double baselinePrefCurrent = preconditionPrefViolations;

        static const bool prefTermDebug = false;
        
        if (!RPGBuilder::getPreferences().empty()) {
            
            
            map<int, list<int> >::const_iterator ppMapItr = varsForPreconditionPreference.begin();
            const map<int, list<int> >::const_iterator ppMapEnd = varsForPreconditionPreference.end();
            
            for (; ppMapItr != ppMapEnd; ++ppMapItr) {
                const double weight = prefs[ppMapItr->first].cost;
                
                list<int>::const_iterator ppVar = ppMapItr->second.begin();
                const list<int>::const_iterator ppEnd = ppMapItr->second.end();
                
                for (; ppVar != ppEnd; ++ppVar) {
                    if (!planCostsNeededAnLP) {                        
                        planCostsNeededAnLP = true;
                        if (previousObjectiveVar != -1) {
                            lp->setObjCoeff(previousObjectiveVar, 0.0);
                            previousObjectiveVar = -1;
                        }
                    }
                    lp->setObjCoeff(*ppVar, weight);                        
                    if (prefTermDebug) {
                        cout << "Set objective weight on " << lp->getColName(*ppVar) << " to " << weight << " due to precondition preference " << RPGBuilder::getPreferences()[ppMapItr->first].name << endl;
                    }
                }                
                
            }    
            
            // first minimise reachable cost, and collect cost of non-mentioned preferences

                                
            {
                map<int, VarsForPreference>::const_iterator prefItr = varsForPreference.begin();
                const map<int, VarsForPreference>::const_iterator prefEnd = varsForPreference.end();
                
                const int prefCount = PreferenceHandler::getInitialAutomataPositions().size();
                int prefID = 0;
                double currPrefCost;
                for (; prefID < prefCount && prefItr != prefEnd; ++prefID) {
                    currPrefCost = prefs[prefID].cost;
                    if (currPrefCost == DBL_MAX) {
                        if (prefID < prefItr->first) {
                             if (prefTermDebug || (PreferenceHandler::preferenceDebug && lpDebug & 1)) {
                                 cout << "Constraint " << prefID << " does not influence cost - the plan has not interacted with it\n";
                             }
                        } else {
                            ++prefItr;
                        }
                    } else {
                        if (prefID < prefItr->first) {
                            if (prefTermDebug || (PreferenceHandler::preferenceDebug && lpDebug & 1)) {
                                cout << "Contribution to baseline current pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getCurrentCost(prefID, preferenceStatus) << endl;
                                cout << "Contribution to baseline reachable pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getReachableCost(prefID, preferenceStatus) << endl;
                            }
                            baselinePrefReachable += PreferenceHandler::getReachableCost(prefID, preferenceStatus);
                            baselinePrefCurrent += PreferenceHandler::getCurrentCost(prefID, preferenceStatus);
                        } else {
                            if (prefItr->second.reachableCostVar >= 0) { // some preferences have zero reachable cost
                                if (!planCostsNeededAnLP) {                        
                                    planCostsNeededAnLP = true;
                                    if (previousObjectiveVar != -1) {
                                        lp->setObjCoeff(previousObjectiveVar, 0.0);
                                        previousObjectiveVar = -1;
                                    }
                                }                
                                lp->setObjCoeff(prefItr->second.reachableCostVar, currPrefCost);
                                if (prefTermDebug) {
                                    cout << "Set objective weight on " << lp->getColName(prefItr->second.reachableCostVar) << " to " << prefs[prefID].cost << " due to preference " << prefs[prefID].name << ":" << prefID << endl;
                                }                            
                            }
                            ++prefItr;
                        }
                    }
                }
                
                for (; prefID < prefCount; ++prefID) {
                    currPrefCost = prefs[prefID].cost;
                    if (currPrefCost != DBL_MAX) {
                        if (prefTermDebug || (PreferenceHandler::preferenceDebug && lpDebug & 1)) {
                            cout << "Contribution to baseline current pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getCurrentCost(prefID, preferenceStatus) << endl;
                            cout << "Contribution to baseline reachable pref cost by " << prefs[prefID].name << ":" << prefID << " = " << PreferenceHandler::getReachableCost(prefID, preferenceStatus) << endl;
                        }
                        baselinePrefReachable += PreferenceHandler::getReachableCost(prefID, preferenceStatus);
                        baselinePrefCurrent += PreferenceHandler::getCurrentCost(prefID, preferenceStatus);
                    }
                }
                
            }
        }
        
        if (!NumericAnalysis::theMetricIsMonotonicallyWorsening()) {
            reachablePlanCost = std::numeric_limits< double >::signaling_NaN();
        } else {
            reachablePlanCost = currentCostFromNonPreferenceParts + metric->constant + RPGBuilder::getPermanentViolationCost() + baselinePrefReachable;
            if (planCostsNeededAnLP) {                    
                
                if (metric->minimise) {
                    lp->setMaximiseObjective(false);
                } else {
                    lp->setMaximiseObjective(true);
                }
            
                if (lpDebug & 8) {
                    lp->writeLp("reachablecost.lp");
                }
                
                lp->mustSolve(true); // we've only changed the objective
                
                reachablePlanCost += lp->getObjValue();
            }
            
            if (lpDebug & 1) {
                cout << COLOUR_light_cyan << "Calculated reachable plan cost as " << reachablePlanCost << endl << COLOUR_default;
            }
                                    
        }
        
        if (!RPGBuilder::getPreferences().empty()) {
            map<int, VarsForPreference>::const_iterator prefItr = varsForPreference.begin();
            const map<int, VarsForPreference>::const_iterator prefEnd = varsForPreference.end();
            
            double currPrefCost;
            for (; prefItr != prefEnd; ++prefItr) {
                currPrefCost = prefs[prefItr->first].cost;
                
                if (currPrefCost == DBL_MAX) {
                    // exclude constraints (not preferences)
                    continue;
                }
                
                if (prefItr->second.reachableCostVar >= 0) { // some preferences have zero reachable cost
                    lp->setObjCoeff(prefItr->second.reachableCostVar,0);
                }                    
                if (prefItr->second.committedCostVar >= 0) {
                    if (!planCostsNeededAnLP) {                        
                        planCostsNeededAnLP = true;
                        if (previousObjectiveVar != -1) {
                            lp->setObjCoeff(previousObjectiveVar, 0.0);
                            previousObjectiveVar = -1;
                        }
                        if (metric->minimise) {
                            lp->setMaximiseObjective(false);
                        } else {
                            lp->setMaximiseObjective(true);
                        }

                    }   
                    lp->setObjCoeff(prefItr->second.committedCostVar, prefs[prefItr->first].cost);
                    if (prefTermDebug) {
                        cout << "Set objective weight on " << lp->getColName(prefItr->second.committedCostVar) << " to " << prefs[prefItr->first].cost << " due to preference " << prefs[prefItr->first].name << ":" << prefItr->first << endl;
                    }
                }
            }
        }
        
        if (!planCostsNeededAnLP) {
            
            currentChoosablePlanCost = 0.0;
            
        } else {
        
            if (lpDebug & 8) {
                lp->writeLp("currentcost.lp");
            }
                        
            
            lp->mustSolve(true); // we've only changed the objective
                        
            currentChoosablePlanCost = lp->getObjValue();
            
            const double * const partialSoln = lp->getPartialSolution(numVars, numVars + loopLim);     
        
            for (int stepID = 0; stepID < loopLim; ++stepID) {
                FFEvent * const itr = planAsAVector[stepID];
                if (itr->time_spec == Planner::E_AT_START || itr->time_spec == Planner::E_AT_END) {
                    itr->lpTimestamp = partialSoln[timestampVars[stepID] - numVars];
                    if (lpDebug & 2) {
                        cout << "Timestamp of " << *(itr->action) << " (var " << timestampVars[stepID] << ") ";
                        if (itr->time_spec == Planner::E_AT_START) cout << " start = "; else cout << "end = ";
                        cout << itr->lpTimestamp << ", when attaining current plan cost\n";                
                    }                    
                }
            }
            
            lp->clearObjective();
            if (restoreVar != -1) {
                lp->setObjCoeff(restoreVar, 1.0);
                previousObjectiveVar = restoreVar;
                lp->setMaximiseObjective(false);
            }
        }
        
        currentPlanCost = currentChoosablePlanCost + currentCostFromNonPreferenceParts + RPGBuilder::getMetric()->constant + RPGBuilder::getPermanentViolationCost() + baselinePrefCurrent;
        
        if (lpDebug & 1) {
            cout << COLOUR_light_cyan << "Calculated current plan cost as " << currentPlanCost << endl << COLOUR_default;
        }
        
        planCostsWereCalculated = true;
    }
}

LPScheduler::~LPScheduler()
{

    delete lp;
    delete cd;
};

void LPScheduler::removeExpiredAbstractFacts(StateFacts & facts)
{
    
    map<int, AbstractFactConstraintBlock>::iterator factItr = planStepForAbstractFact.begin();
    const map<int, AbstractFactConstraintBlock>::iterator factEnd = planStepForAbstractFact.end();
    
    for (; factItr != factEnd; ++factItr) {
        
        if (factItr->second.isNoLongerAvailable()) {
            
            if (lpDebug & 1) {
                cout << COLOUR_light_red << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << " is no longer available, removing from state\n" << COLOUR_default;
            }
            facts.erase(factItr->first);
        } else {
            
            if (lpDebug & 1) {
                cout << COLOUR_light_green << "Abstract fact " << *(RPGBuilder::getLiteral(factItr->first)) << " stays in the state\n" << COLOUR_default;
            }
            assert(facts.find(factItr->first) != facts.end());
        }
        
    }
    
}

const LPScheduler::Constraint* LPScheduler::buildConstraint(RPGBuilder::RPGNumericPrecondition & pre)
{

    if (lpDebug & 4) cout << pre << " with op " << pre.op << " becomes:";

    Constraint toReturn;

    switch (pre.op) {
    case VAL::E_GREATER: {
        toReturn.upper = DBL_MAX;
        toReturn.lower = pre.RHSConstant + 0.0001; // HACK - some small value to fake greater-than using a GE
        if (lpDebug & 4) cout << " >= " << toReturn.lower;
        break;
    }
    case VAL::E_GREATEQ: {
        toReturn.upper = DBL_MAX;
        toReturn.lower = pre.RHSConstant;
        if (lpDebug & 4) cout << " >= " << toReturn.lower;
        break;
    }
    case VAL::E_LESS: {
        toReturn.lower = -DBL_MAX;
        toReturn.upper = pre.RHSConstant - 0.0001; // HACK - some small value to fake less-than using a LE
        if (lpDebug & 4) cout << " <= " << toReturn.upper;
        break;
    }
    case VAL::E_LESSEQ: {
        toReturn.lower = -DBL_MAX;
        toReturn.upper = pre.RHSConstant;
        if (lpDebug & 4) cout << " <= " << toReturn.upper;
        break;
    }
    case VAL::E_EQUALS: {
        toReturn.lower = toReturn.upper = pre.RHSConstant;
        break;
    }
    };

    int v = pre.LHSVariable;
    if (v < numVars) { // simple variable or duration &c
        toReturn.weights = vector<double>(1);
        toReturn.variables = vector<int>(1);

        toReturn.weights[0] = pre.LHSConstant;
        toReturn.variables[0] = pre.LHSVariable;
        if (lpDebug & 4) cout << "Constraint on simple variable: \n";
    } else {
        v -= numVars;

        if (v < numVars) { // negative variable

            if (lpDebug & 4) cout << "Constraint on negative variable: \n";
            toReturn.weights = vector<double>(1);
            toReturn.variables = vector<int>(1);

            toReturn.weights[0] = -1 * pre.LHSConstant;
            toReturn.variables[0] = pre.LHSVariable;
        } else {
            if (lpDebug & 4) cout << "Constraint on AV: \n";
            
            RPGBuilder::ArtificialVariable & av = RPGBuilder::getArtificialVariable(pre.LHSVariable);
            const int loopLim = av.size;
            toReturn.weights = vector<double>(loopLim);
            toReturn.variables = vector<int>(loopLim);

            for (int s = 0; s < loopLim; ++s) {
                toReturn.weights[s] = av.weights[s];
                int lv = av.fluents[s];
                if (lv >= numVars) {
                    lv -= numVars;
                    toReturn.weights[s] *= -1;
                }
                toReturn.variables[s] = lv;
            }

            if (pre.op == VAL::E_GREATER || pre.op == VAL::E_GREATEQ) {
                toReturn.lower -= av.constant; // constant term from the AV
            } else if (pre.op == VAL::E_EQUALS) {
                toReturn.lower -= av.constant;
                toReturn.upper -= av.constant;
            } else {
                toReturn.upper += av.constant; // constant term from the AV
            }

        }
    }
    
    // now post-filter to replace tickers with the appropriate weight times total-time
    
    const map<int,double> & tickerVars = NumericAnalysis::getVariablesThatAreTickers();
    
    map<int,double>::const_iterator tvItr;
    int Slim = toReturn.weights.size();
    for (int i = 0; i < Slim; ++i) {
        tvItr = tickerVars.find(toReturn.variables[i]);
        if (tvItr != tickerVars.end()) {
            toReturn.weights[i] *= tvItr->second;
            toReturn.variables[i] = -4; // total-time variable
        }
    }
    
    if (lpDebug & 4) {
        for (int i = 0; i < Slim; ++i) {
            if (i) cout << " + ";
            cout << toReturn.weights[i] << ".";
            if (toReturn.variables[i] < 0) {
                switch (toReturn.variables[i]) {
                    case -3: {
                        cout << "?duration";
                        break;
                    }
                    case -4: {
                        cout << "total-time";
                        break;
                    }
                    case -19: {
                        cout << "-?duration";
                        break;
                    }
                    default:
                    {
                        cout << "Internal error: should be a normal variable, ?duration, or a ticker\n";
                        exit(1);
                    }
                }
            } else {
                cout << *(RPGBuilder::getPNE(toReturn.variables[i]));
            }
        }

        cout << " in [";

        if (toReturn.lower != -DBL_MAX) {
            cout << toReturn.lower << ",";
        } else {
            cout << "-inf,";
        }

        if (toReturn.upper != DBL_MAX) {
            cout << toReturn.upper << "]\n";
        } else {
            cout << "inf]\n";
        }

    }

    return Constraint::requestConstraint(toReturn);


};

void LPScheduler::initialise()
{

    initialised = true;

    const bool initDebug = false;

    numVars = RPGBuilder::getPNECount();
    const int actCount = RPGBuilder::getFixedDEs().size();

    gradientEffects .resize(actCount);
    instantEffects.resize(actCount);
    constraints.resize(actCount);
    interesting.resize(actCount);
    boringAct.resize(actCount, vector<pair<bool,bool> >(2, pair<bool,bool>(true,true)));
    pointsThatWouldBeMutexWithOptimisationTILs.resize(actCount, vector<vector<double> >(2));
    initialGradients.resize(numVars,0.0); // set all initial gradients to zero, but have a look at processes to refine that

    const map<int,double> & tickerVars = NumericAnalysis::getVariablesThatAreTickers();
    
    if (initDebug) cout << "Initialising LP lookups for " << actCount << " actions\n";

    for (int a = 0; a < actCount; ++a) {

        if (initDebug) {
            cout << "[" << a << "] ";
            cout.flush();
        }

        if (RPGBuilder::rogueActions[a] != RPGBuilder::OT_INVALID_ACTION) {

            interesting[a] = vector<InterestingMap>(3);

            RPGBuilder::LinearEffects* const discretisation = RPGBuilder::getLinearDiscretisation()[a];

            if (discretisation) {
                const int divisions = discretisation->divisions;

                bool allMetricTracking = true;
                {
                    vector<list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > > & toFill = gradientEffects[a] = vector<list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > >(divisions);
                    const int varCount = discretisation->vars.size();
                    for (int v = 0; v < varCount; ++v) {
                        const int currVar = (discretisation->vars)[v];
                        if (currVar < 0) continue;
                        interesting[a][0].insertEffect(currVar);
                        interesting[a][1].insertEffect(currVar);
                        interesting[a][2].insertEffect(currVar);
                        for (int d = 0; d < divisions; ++d) {
                            toFill[d].push_back(pair<int, RPGBuilder::LinearEffects::EffectExpression>(currVar, discretisation->effects[d][v]));
                            if (RPGBuilder::rogueActions[a] == RPGBuilder::OT_PROCESS) {
                                initialGradients[currVar] += discretisation->effects[d][v].constant;
                            }
                        }
                        if (   NumericAnalysis::getDominanceConstraints()[currVar] != NumericAnalysis::E_METRICTRACKING
                            && NumericAnalysis::getDominanceConstraints()[currVar] != NumericAnalysis::E_IRRELEVANT) {
                            allMetricTracking = false;
                        }
                    }
                }

                boringAct[a][0].first = allMetricTracking;
                boringAct[a][1].first = allMetricTracking;
                
                boringAct[a][0].second = false;
                boringAct[a][1].second = false;


            } else {
                gradientEffects[a] = vector<list<pair<int, RPGBuilder::LinearEffects::EffectExpression> > >(1);
            }
        }
        
        if (RPGBuilder::rogueActions[a] == RPGBuilder::OT_NORMAL_ACTION) {
            {

                vector<list<RPGBuilder::RPGNumericEffect* > > & toFill = instantEffects[a] = vector<list<RPGBuilder::RPGNumericEffect* > >(2);

                for (int pass = 0; pass < 2; ++pass) {
                    list<int> & currList = (pass ? RPGBuilder::getEndEffNumerics()[a] : RPGBuilder::getStartEffNumerics()[a]);

                    list<int>::iterator clItr = currList.begin();
                    const list<int>::iterator clEnd = currList.end();

                    const int iPoint = (pass ? 2 : 0);

                    for (; clItr != clEnd; ++clItr) {

                        RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*clItr];
                        
                        toFill[pass].push_back(&currEff);

                        interesting[a][iPoint].insertEffect(currEff.fluentIndex);

                        if (initDebug) {
                            if (iPoint == 2) {
                                cout << *(RPGBuilder::getInstantiatedOp(a)) << " end writes to " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                            } else {
                                cout << *(RPGBuilder::getInstantiatedOp(a)) << " start writes to " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                            }
                            assert(interesting[a][iPoint].find(currEff.fluentIndex)->second);
                        }

                        for (int s = 0; s < currEff.size; ++s) {
                            int vv = currEff.variables[s];
                            if (vv >= 0) {
                                if (vv >= numVars) vv -= numVars;
                                if (tickerVars.find(vv) == tickerVars.end()) {
                                    interesting[a][iPoint].insertPrecondition(vv);
                                }
                            } else if (vv <= -2) {
                                boringAct[a][pass].second = false;
                                if (   NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_IRRELEVANT
                                    && NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] != NumericAnalysis::E_METRICTRACKING) {
                                    boringAct[a][pass].first = false;
                                }
                            }
                        }
                    }
                }
            }

            const map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceItr = RPGBuilder::getActionsToIntegralConditionalEffects().find(a);

            
                
            if (iceItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {
                
                // these actions need a MIP to be resolved
                
                boringAct[a][0] = make_pair(false,false);
                boringAct[a][1] = make_pair(false,false);
                
                list<vector<list<RPGBuilder::RPGNumericEffect* > > > & toFillOuter = instantIntegralConditionalEffects[a];
            
                list<RPGBuilder::IntegralContinuousEffect>::const_iterator icItr = iceItr->second.begin();
                const list<RPGBuilder::IntegralContinuousEffect>::const_iterator icEnd = iceItr->second.end();
                
                for (; icItr != icEnd; ++icItr) {
                    
                    toFillOuter.push_back(vector<list<RPGBuilder::RPGNumericEffect* > >(2));
                    
                    vector<list<RPGBuilder::RPGNumericEffect* > > & toFill = toFillOuter.back();
                    
                    for (int pass = 0; pass < 2; ++pass) {
                        const list<pair<int,double> > & currList = (pass ? icItr->getLeftEndEffects() : icItr->getLeftStartEffects());
                            
                        list<pair<int,double> >::const_iterator clItr = currList.begin();
                        const list<pair<int,double> >::const_iterator clEnd = currList.end();

                        const int iPoint = (pass ? 2 : 0);

                        for (; clItr != clEnd; ++clItr) {
                            RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[clItr->first];
                        
                            toFill[pass].push_back(&currEff);

                            interesting[a][iPoint].insertEffect(currEff.fluentIndex);

                            if (initDebug) {
                                if (iPoint == 2) {
                                    cout << *(RPGBuilder::getInstantiatedOp(a)) << " end ICE writes to " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                                } else {
                                    cout << *(RPGBuilder::getInstantiatedOp(a)) << " start ICE writes to " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << "\n";
                                }
                                assert(interesting[a][iPoint].find(currEff.fluentIndex)->second);
                            }

                            for (int s = 0; s < currEff.size; ++s) {
                                int vv = currEff.variables[s];
                                if (vv >= 0) {
                                    if (vv >= numVars) vv -= numVars;
                                    if (tickerVars.find(vv) == tickerVars.end()) {
                                        interesting[a][iPoint].insertPrecondition(vv);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            {
                vector<list<const Constraint*> > & toFill = constraints[a] = vector<list<const Constraint*> >(3);

                for (int pass = 0; pass < 3; ++pass) {
                    list<int> & currList = (pass ? (pass == 2 ? RPGBuilder::getEndPreNumerics()[a] : RPGBuilder::getInvariantNumerics()[a]) : RPGBuilder::getStartPreNumerics()[a]);
                    
                    
                    /*if (pass == 1) {
                        cout << "In LP: " << *(RPGBuilder::getInstantiatedOp(a)) << " has " << currList.size() << " numeric invariants\n";
                    }*/
                    list<int>::iterator clItr = currList.begin();
                    const list<int>::iterator clEnd = currList.end();

                    for (; clItr != clEnd; ++clItr) {
                        toFill[pass].push_back(buildConstraint(RPGBuilder::getNumericPreTable()[*clItr]));

                        const Constraint * const curr = toFill[pass].back();
                        vector<int>::const_iterator itr = curr->variables.begin();
                        const vector<int>::const_iterator itrEnd = curr->variables.end();

                        for (; itr != itrEnd; ++itr) {
                            if (*itr >= 0) {
                                interesting[a][pass].insertPrecondition(*itr);
                            } else if (*itr <= -2) {
                                // effects that depend on a ticker or ?duration are non-boring
                                boringAct[a][0] = make_pair(false,false);
                                boringAct[a][1] = make_pair(false,false);
                            }
                        }

                    }
                }

            }
            
            if (iceItr != RPGBuilder::getActionsToIntegralConditionalEffects().end()) {
                                                
                list<vector<pair<const Constraint*, const Constraint*> > > & toFillOuter = instantIntegralConstraints[a];
                
                list<RPGBuilder::IntegralContinuousEffect>::const_iterator icItr = iceItr->second.begin();
                const list<RPGBuilder::IntegralContinuousEffect>::const_iterator icEnd = iceItr->second.end();
                
                for (; icItr != icEnd; ++icItr) {
                    toFillOuter.push_back(vector<pair<const Constraint*, const Constraint*> >(3));
                    
                    vector<pair<const Constraint*, const Constraint*> > & toFill = toFillOuter.back();
                
                    const int pass = (icItr->getTS() == Planner::E_AT_START ? 0 : 2);                                        
                    
                    toFill[pass].first = buildConstraint(RPGBuilder::getNumericPreTable()[icItr->getLeftPrecondition()]);
                    toFill[pass].second = buildConstraint(RPGBuilder::getNumericPreTable()[icItr->getRightPrecondition()]);
                    
                    for (int fp = 0; fp < 2; ++fp) {
                        const Constraint * const curr = (fp ? toFill[pass].second : toFill[pass].first);
                        vector<int>::const_iterator itr = curr->variables.begin();
                        const vector<int>::const_iterator itrEnd = curr->variables.end();

                        for (; itr != itrEnd; ++itr) {
                            if (*itr >= 0) {
                                interesting[a][pass].insertPrecondition(*itr);
                            }
                        }
                        
                    }
                }
                
            }
            
            if (!RPGBuilder::getRPGDEs(a).empty()) {
                RPGBuilder::RPGDuration* const currDuration = RPGBuilder::getRPGDEs(a).back();
                for (int pass = 0; pass < 3; ++pass) {
                    const list<RPGBuilder::DurationExpr*> & currDurs = (*currDuration)[pass];
                    
                    list<RPGBuilder::DurationExpr*>::const_iterator dItr = currDurs.begin();
                    const list<RPGBuilder::DurationExpr*>::const_iterator dEnd = currDurs.end();
                    
                    for (; dItr != dEnd; ++dItr) {
                        const int vCount = (*dItr)->variables.size();
                        
                        int vv;
                        for (int i = 0; i < vCount; ++i) {
                            vv = (*dItr)->variables[i];
                            if (vv >= 0) {
                                if (vv >= numVars) vv -= numVars;
                                interesting[a][0].insertPrecondition(vv);
                            }
                        }
                    }
                }
            }
            
            
            {
                pointsThatWouldBeMutexWithOptimisationTILs[a].resize(2);
                
                const list<RPGBuilder::ConditionalEffect> & ceffs = RPGBuilder::getActionsToConditionalEffects()[a];

                list<RPGBuilder::ConditionalEffect>::const_iterator ceffItr = ceffs.begin();
                const list<RPGBuilder::ConditionalEffect>::const_iterator ceffEnd = ceffs.end();
                
                for (; ceffItr != ceffEnd; ++ceffItr) {
                    
                    const list<pair<Literal*, Planner::time_spec> > & conds = ceffItr->getPropositionalConditions();
                    
                    list<pair<Literal*, Planner::time_spec> >::const_iterator condItr = conds.begin();
                    const list<pair<Literal*, Planner::time_spec> >::const_iterator condEnd = conds.end();
                    
                    for (; condItr != condEnd; ++condItr) {
                        const list<pair<double,double> > * windows = TemporalAnalysis::factIsVisibleInWindows(condItr->first);
                        
                        if (!windows) {
                            continue;
                        }
                        
                        list<pair<double,double> >::const_iterator wItr = windows->begin();
                        const list<pair<double,double> >::const_iterator wEnd = windows->end();
                        
                        for (; wItr != wEnd; ++wItr) {
                            if (wItr->second == DBL_MAX) break;
                            if (condItr->second == Planner::E_AT_START) {
                                pointsThatWouldBeMutexWithOptimisationTILs[a][0].push_back(wItr->second); // start points cannot coincide with start conditions being deleted
                            } else if (condItr->second == Planner::E_AT_END) {
                                pointsThatWouldBeMutexWithOptimisationTILs[a][1].push_back(wItr->second); // end points cannot coincide with end conditions being deleted
                            }
                        }
                    }
                }
            }

        }


    }


    /*{
        map<int, set<int> >::const_iterator sfItr = RPGBuilder::getSemaphoreFacts().begin();
        const map<int, set<int> >::const_iterator sfEnd = RPGBuilder::getSemaphoreFacts().end();
        
        for (; sfItr != sfEnd; ++sfItr) {
            
            set<int>::const_iterator vItr = sfItr->second.begin();
            const set<int>::const_iterator vEnd = sfItr->second.end();
            
            for (; vItr != vEnd; ++vItr) {
              list<pair<int, Planner::time_spec> >::const_iterator pItr = RPGBuilder::getEffectsToActions(sfItr->first).begin();
              const list<pair<int, Planner::time_spec> >::const_iterator pEnd = RPGBuilder::getEffectsToActions(sfItr->first).end();
              
              for (; pItr != pEnd; ++pItr) {
                  if (pItr->second == Planner::E_AT_START) {
                      interesting[pItr->first][0].insertEffect(*vItr);
                  } else if (pItr->second == Planner::E_AT_END) {
                      interesting[pItr->first][2].insertEffect(*vItr);
                  } else {
                      std::cerr << "Fatal internal error: semaphores should only be manipulated by actions\n";
                      exit(1);
                  }
              }
            }
        }
    }*/

    if (initDebug) cout << "\n";

    {
        list<pair<int, int> > & goals = RPGBuilder::getNumericRPGGoals();
        list<pair<int, int> >::iterator gItr = goals.begin();
        const list<pair<int, int> >::iterator gEnd = goals.end();

        for (; gItr != gEnd; ++gItr) {
            if (gItr->first != -1) goalConstraints.push_back(buildConstraint(RPGBuilder::getNumericPreTable()[gItr->first]));
            if (gItr->second != -1) goalConstraints.push_back(buildConstraint(RPGBuilder::getNumericPreTable()[gItr->second]));
        }
    }


    {
        RPGBuilder::getInitialState(initialFacts, initialValues);
    }

    {

        vector<RPGBuilder::FakeTILAction*> & TILs = RPGBuilder::getNonAbstractedTILVec();
        const int tilCount = TILs.size();
        TILtimestamps = vector<double>(tilCount + 1);

        int t = 0;

        for (; t < tilCount; ++t) {
            TILtimestamps[t] = TILs[t]->duration;
        }

        TILtimestamps[t] = DBL_MAX;

    }

    
    {
        
        //map<int, vector<pair<double,double> > > LPScheduler::boundsForAbstractFactOccurrences;
        
        const map<int, TILTimeline> & tilTimelines = TemporalAnalysis::getTILTimelines();
                    
        map<int, TILTimeline>::const_iterator tilItr = tilTimelines.begin();
        const map<int, TILTimeline>::const_iterator tilEnd = tilTimelines.end();
        
        for (; tilItr != tilEnd; ++tilItr) {
            if (TemporalAnalysis::getFactIsAbstract()[tilItr->first]) {
                vector<pair<double,double> > & toFill = boundsForAbstractFactOccurrences[tilItr->first];
                
                TILTimeline::const_iterator tlItr = tilItr->second.begin();
                const TILTimeline::const_iterator tlEnd = tilItr->second.end();
                
                double lastDeletedAt = -1.0;
                double lastAddedAt = -1.0;
                
                for (; tlItr != tlEnd; ++tlItr) {
                    if (tlItr->second.deleted) {
                        if (lastAddedAt != -1.0) {
                            toFill.push_back(make_pair(lastAddedAt, tlItr->first - EPSILON));
                        }
                        lastAddedAt = -1.0;
                        lastDeletedAt = tlItr->first;
                    }
                    if (tlItr->second.added) {
                        if (lastAddedAt != -1.0) {
                            toFill.push_back(make_pair(lastAddedAt, tlItr->first - EPSILON));
                        }
                        lastAddedAt = tlItr->first + EPSILON;                        
                    }
                }
                
                assert(lastAddedAt == -1.0);
            }
        }
        
    }

};

void LPScheduler::addConstraintsForTILMutexes(const int & timestampVar, const vector<double> & mutexTimestamps)
{
    
    if (mutexTimestamps.empty()) return;
        
    static const vector<pair<int,double> > emptyEntries;
    
    static vector<pair<int,double> > binaryConstraint(2);
    
    const int mtCount = mutexTimestamps.size();
    
    const pair<double,double> tsBounds = make_pair(lp->getColLower(timestampVar), lp->getColUpper(timestampVar));
    
    for (int mt = 0; mt < mtCount; ++mt) {
        if (mutexTimestamps[mt] < tsBounds.first || mutexTimestamps[mt] > tsBounds.second) {
            // no need to forbid the variable from taking a value which it could not anyway
            continue;
        }
        
        
        // make a variable that takes the value 1 if timestampVar falls after mutexTimestamps[mt],
        // or 0 if it falls before
        
        lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
        
        const int beforeOrAfter = lp->getNumCols() - 1;
        
        //mutexCols.push_back(beforeOrAfter);
        
        if (nameLPElements) {
            ostringstream n;
            n << "col" << timestampVar << "neq" << mutexTimestamps[mt];
            const string cname(n.str());
            lp->setColName(beforeOrAfter, cname);
        }
        
        // First, make the setting of this variable force upper and lower bounds
        
        binaryConstraint[0].first = timestampVar;
        binaryConstraint[0].second = 1.0;
        
        binaryConstraint[1].first = beforeOrAfter;
        binaryConstraint[1].second = -N;
        
        lp->addRow(binaryConstraint, -LPinfinity, mutexTimestamps[mt] - SAFE);
        
        //mutexRows.push_back(lp->getNumRows() - 1);
        
        if (nameLPElements) {
            ostringstream n;
            n << "set" << timestampVar << "lt" << mutexTimestamps[mt];
            const string cname(n.str());
            lp->setRowName(lp->getNumRows() - 1, cname);
        }
        
        binaryConstraint[0].first = timestampVar;
        binaryConstraint[0].second = 1.0;
        
        binaryConstraint[1].first = beforeOrAfter;
        binaryConstraint[1].second = -(mutexTimestamps[mt] + SAFE);
        
        lp->addRow(binaryConstraint, 0, LPinfinity);
        
        //mutexRows.push_back(lp->getNumRows() - 1);
        
        if (nameLPElements) {
            ostringstream n;
            n << "set" << timestampVar << "gt" << mutexTimestamps[mt];
            const string cname(n.str());
            lp->setRowName(lp->getNumRows() - 1, cname);
        }
        
        // Second, make the setting of the timestamp force the correct value of this variable
        
        binaryConstraint[0].first = timestampVar;
        binaryConstraint[0].second = -1.0;
        
        binaryConstraint[1].first = beforeOrAfter;
        binaryConstraint[1].second = N;
        
        lp->addRow(binaryConstraint, -(mutexTimestamps[mt] - SAFE), LPinfinity);
        
        //mutexRows.push_back(lp->getNumRows() - 1);
        
        if (nameLPElements) {
            ostringstream n;
            n << "if" << timestampVar << "gt" << mutexTimestamps[mt];
            const string cname(n.str());
            lp->setRowName(lp->getNumRows() - 1, cname);
        }
        
        binaryConstraint[0].first = timestampVar;
        binaryConstraint[0].second = 1.0;
        
        binaryConstraint[1].first = beforeOrAfter;
        binaryConstraint[1].second = -N;
        
        lp->addRow(binaryConstraint, mutexTimestamps[mt] + SAFE - N, LPinfinity);
        
        //mutexRows.push_back(lp->getNumRows() - 1);
        
        if (nameLPElements) {
            ostringstream n;
            n << "if" << timestampVar << "lt" << mutexTimestamps[mt];
            const string cname(n.str());
            lp->setRowName(lp->getNumRows() - 1, cname);
        }
        
    }
}



void LPScheduler::updateStateFluents(vector<double> & min, vector<double> & max, vector<double> & timeAtWhichValueIsDefined)
{

    if (!lp) return;
    /*if (previousObjectiveVar == -1) {
        return;
    }
    if (timestampToUpdateVar == -1) {
        return;        
    }*/
        
    assert(solved);

    if (lpDebug & 16) {
        lp->mustSolve(false);
    }
    
    if (lpDebug & 1) {
        cout << "Finding bounds on state fluents\n";
    }
    
    if (workOutFactLayerZeroBoundsStraightAfterRecentAction) {
        timeAtWhichValueIsDefined.resize(min.size(), -1.0);
    }
    
    map<int,double> knownMinValueOfColumn;
    
    if (timestampToUpdateVar != -1) {
        knownMinValueOfColumn.insert(make_pair(timestampToUpdateVar,timestampToUpdateVarLB));
    }
    
    static const bool optimised = true;
    
    static const double tolerance = 0.001;
    
    int numberOfCalls = 0;
    
    const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
    
    for (int s = 0; s < numVars; ++s) {
        
        if (tickers.find(s) != tickers.end()) {
            if (lpDebug & 1) cout << "New bounds on " << *(RPGBuilder::getPNE(s)) << ": it's a ticker, so bounded in the range 0 to infinity\n";
            min[s] = 0.0;
            max[s] = DBL_MAX;
            continue;
        }
        
        if (finalNumericVars[s].statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT) {
        
            if (finalNumericVars[s].orderIndependentValueTerms.empty()) {
                if (lpDebug & 1) cout << "New bounds on " << *(RPGBuilder::getPNE(s)) << ", an order-independent variable are constant: " << finalNumericVars[s].orderIndependentValueConstant << endl;
                
                min[s] = finalNumericVars[s].orderIndependentValueConstant;
                max[s] = finalNumericVars[s].orderIndependentValueConstant;                                
                
            } else {
                    
                if (lpDebug & 1) cout << "New bounds on " << *(RPGBuilder::getPNE(s)) << ", an order-independent variable, evaluate to: ";
                
                if (previousObjectiveVar != -1) {
                    lp->setObjCoeff(previousObjectiveVar, 0.0);
                    previousObjectiveVar = -1;
                }
                        
                map<int,double>::const_iterator oiTerms = finalNumericVars[s].orderIndependentValueTerms.begin();
                const map<int,double>::const_iterator oiTermsEnd = finalNumericVars[s].orderIndependentValueTerms.end();
                
                for (; oiTerms != oiTermsEnd; ++oiTerms) {
                    lp->setObjCoeff(oiTerms->first, oiTerms->second);
                }
                
                lp->setMaximiseObjective(true);
            
                if (lpDebug & 16) {
                    ostringstream fns;
                    fns << "bound-" << numberOfCalls << ".lp";
                    lp->writeLp(fns.str());
                }
            
                lp->mustSolve(false);
                ++numberOfCalls;
                
                const double mv = lp->getObjValue();
                max[s] = mv + finalNumericVars[s].orderIndependentValueConstant + tolerance;

                
                lp->setMaximiseObjective(false);
            
                if (lpDebug & 16) {
                    ostringstream fns;
                    fns << "bound-" << numberOfCalls << ".lp";
                    lp->writeLp(fns.str());
                }
                
                lp->mustSolve(false);
                ++numberOfCalls;
                
                const double mvTwo = lp->getObjValue();
                min[s] = mvTwo + finalNumericVars[s].orderIndependentValueConstant - tolerance;
                
                if (lpDebug & 1) cout << " [" << min[s] << "," << max[s] << "]\n";                            
                
                lp->clearObjective();
            } 
        
            
        } else if (   !stableVariable[s]
            && (finalNumericVars[s].statusOfThisFluent == FluentTracking::FS_NORMAL) ) {

            if (lpDebug & 1) cout << "New bounds on " << *(RPGBuilder::getPNE(s)) << ", column " << lp->getColName(finalNumericVars[s].lastEffectValueVariable) << " were [" << min[s] << "," << max[s] << "] now:";

            if (previousObjectiveVar != -1) lp->setObjCoeff(previousObjectiveVar, 0.0);

            bool nonDDAmethod = false;
            double oldColUpper;
        
            if (workOutFactLayerZeroBoundsStraightAfterRecentAction) {
                if (!finalNumericVars[s].everHadADurationDependentEffect) {
                    const int relevantTSVar = finalNumericVars[s].lastEffectTimestampVariable;
                    oldColUpper = lp->getColUpper(relevantTSVar);
                    nonDDAmethod = true;
                    
                    pair<map<int,double>::iterator,bool> knownMin = knownMinValueOfColumn.insert(make_pair(relevantTSVar,0.0));
                    
                    if (knownMin.second) {
                        if (lpDebug & 16) {
                            cout << "No known min value of " << lp->getColName(relevantTSVar) << endl;
                        }
                        previousObjectiveVar = relevantTSVar;
                        lp->setObjCoeff(previousObjectiveVar, 1.0);
                        lp->setMaximiseObjective(false);
                        if (lpDebug & 16) {
                            cout << "First, minimising " << lp->getColName(previousObjectiveVar) << "; old col upper was " << oldColUpper << endl;
                        }
                            
                        lp->mustSolve(false);
                        ++numberOfCalls;
                        
                        knownMin.first->second = lp->getSingleSolutionVariableValue(previousObjectiveVar);
                        lp->setObjCoeff(previousObjectiveVar, 0.0);
                        
                        if (optimised) {
                            // since we minimised the value of this variable, we can use this as its lower bound from hereon
                            lp->setColLower(previousObjectiveVar, EpsilonResolutionTimestamp(knownMin.first->second,true).toDouble());
                        }
                    } else {
                        if (lpDebug & 16) {
                            cout << "Known min value of " << lp->getColName(relevantTSVar) << endl;
                        }

                    }
                    
                    timeAtWhichValueIsDefined[s] = EpsilonResolutionTimestamp(knownMin.first->second,true).toDouble();
                    
                    // temporary additional constraint to make sure now is as early as it can be
                    if (lpDebug & 16) {
                        cout << "Never had a duration-dependent effect on variable, so using new method - limiting " << lp->getColName(relevantTSVar) << " to " << knownMin.first->second << " instead of " << oldColUpper << endl;
                    }

                    lp->setColUpper(relevantTSVar, timeAtWhichValueIsDefined[s] + 0.0005);
                    
                                                                
                }                
            }
            
            
            previousObjectiveVar = finalNumericVars[s].lastEffectValueVariable;
            lp->setObjCoeff(previousObjectiveVar, 1.0);
            lp->setMaximiseObjective(true);
            
            if (lpDebug & 16) {
                cout << "Maximising " << lp->getColName(previousObjectiveVar) << " gets ";
                cout.flush();                
                ostringstream fns;
                fns << "bound-" << numberOfCalls << ".lp";
                lp->writeLp(fns.str());
            }
            
            lp->mustSolve(false);
            ++numberOfCalls;
            
            if (lpDebug & 16) {
                cout << lp->getObjValue() << endl;
                cout << "Minimising " << lp->getColName(previousObjectiveVar) << " gets ";
                cout.flush();                
            }

            static const double tolerance = 0.001;
            
            const double mv = lp->getSingleSolutionVariableValue(previousObjectiveVar);
            max[s] = mv + tolerance;

            if (!nonDDAmethod && optimised) {
                //lp->setColUpper(previousObjectiveVar, mv + 0.005);
            }

            lp->setMaximiseObjective(false);
            
            if (lpDebug & 16) {
                ostringstream fns;
                fns << "bound-" << numberOfCalls << ".lp";
                lp->writeLp(fns.str());
            }
            
            lp->mustSolve(false);
            ++numberOfCalls;
            
            if (lpDebug & 16) {
                cout << lp->getObjValue() << endl;
            }
            
            const double mvTwo = lp->getSingleSolutionVariableValue(previousObjectiveVar);
            min[s] = mvTwo - tolerance;
            if (!nonDDAmethod && optimised) {
                //lp->setColLower(previousObjectiveVar, mvTwo - 0.005);
            }
            
            if (nonDDAmethod) {
                
                // restore previous upper bound rather than the tighter one used
                lp->setColUpper(finalNumericVars[s].lastEffectTimestampVariable, oldColUpper);
                if (lpDebug & 16) {
                    cout << "Reset upper on " << lp->getColName(finalNumericVars[s].lastEffectTimestampVariable) << " to " << oldColUpper << endl;
                }
                if (lpDebug & 16) {
                    ostringstream fns;
                    fns << "boundr-" << numberOfCalls - 1<< ".lp";
                    lp->writeLp(fns.str());
                }
                if (lpDebug & 1) cout << " [" << mvTwo << "," << mv << "] from t=" << timeAtWhichValueIsDefined[s] << " onwards\n";
                
                if (Globals::totalOrder) {
                    timeAtWhichValueIsDefined[s] = lp->getColLower(timestampToUpdateVar);
                    if (lpDebug & 1) cout << " ** Using a total-order, so pretending is defined from " << timeAtWhichValueIsDefined[s] << endl;
                }
                                            
            } else {
                if (lpDebug & 1) cout << " [" << mvTwo << "," << mv << "]\n";                            
            }

        } else {
            if (lpDebug & 1) cout << "Skipping updating bounds on " << *(RPGBuilder::getPNE(s)) << ", remain at [" << min[s] << "," << max[s] << "]\n";
        }
    }

};

void LPScheduler::extrapolateBoundsAfterRecentAction(const list<StartEvent> * startEventQueue, vector<double> & min, vector<double> & max, const vector<double> & timeAtWhichValueIsDefined)
{
    if (!lp) return;
    if (previousObjectiveVar == -1) {
        return;
    }
    if (timestampToUpdateVar == -1) {
        return;        
    }
    if (timeAtWhichValueIsDefined.empty()) {
        return;
    }
            
    assert(solved);
       
    vector<RPGBuilder::LinearEffects*> & LD = RPGBuilder::getLinearDiscretisation();
    
    list<StartEvent>::const_iterator evItr = startEventQueue->begin();
    const list<StartEvent>::const_iterator evEnd = startEventQueue->end();
    
    for (; evItr != evEnd; ++evItr) {
        
        const RPGBuilder::LinearEffects* currLD = LD[evItr->actID];
        if (!currLD) continue;
                               
        const double multiplier = evItr->maxDuration - evItr->elapsed;
        
        const vector<int> & varList = currLD->vars;
        const vector<RPGBuilder::LinearEffects::EffectExpression> & changeList = currLD->effects[0];
        
        const int effCount = varList.size();
        
        for (int e = 0; e < effCount; ++e) {
            if (timeAtWhichValueIsDefined[varList[e]] < 0.0) {
                // ignore effects upon variables where the -/ method wasn't used anyway
                continue;                
            }
            if (changeList[e].constant > 0.0) {
                max[varList[e]] += changeList[e].constant * multiplier;
                //cout << "Boosted upper bound on " << *(RPGBuilder::getPNE(varList[e])) << endl;
            }
            if (changeList[e].constant < 0.0) {
                min[varList[e]] += changeList[e].constant * multiplier;
                //cout << "Boosted lower bound on " << *(RPGBuilder::getPNE(varList[e])) << endl;
            }
        }        
    }
}

int LPScheduler::getDummyVarForMakespan() {
    
    if (dummyVarForMakespan != -1) {
        return dummyVarForMakespan;
    }
    
    static const vector<pair<int,double> > emptyEntries;
    static vector<pair<int,double> > entries(2);

    lp->addCol(emptyEntries, makespanVarMinimum, LPinfinity, MILPSolver::C_REAL);
    
    dummyVarForMakespan = lp->getNumCols() - 1;
    
    
    if (nameLPElements) {
        lp->setColName(dummyVarForMakespan, "makespan");
    }

    
    entries[0].second = 1.0;
    entries[1].second = -1.0;
    
    entries[0].first = dummyVarForMakespan;
        
    const int stepCount = planAsAVector.size();
    
    for (int s = 0; s < stepCount; ++s) {
        
        if (!planAsAVector[s]->isDummyStep() && ((planAsAVector[s]->time_spec == Planner::E_AT_START) || (planAsAVector[s]->time_spec == Planner::E_AT_END))) {
            entries[1].first = numVars + s; // the variable of step s
            lp->addRow(entries, 0.0, LPinfinity);
            if (nameLPElements) {
                ostringstream str;
                str << "msafter" << s;
                lp->setRowName(lp->getNumRows() - 1, str.str());
            }
        }                        
    }
    
    return dummyVarForMakespan;
}

bool LPScheduler::isSolution(const MinimalState & state, list<FFEvent> & header, list<FFEvent> & now)
{
    static const vector<pair<int,double> > emptyEntries;

    if (!PreferenceHandler::constraintsAreSatisfied(state.preferenceStatus)) {
        return false;
    }
    
    if (!lp) {
        static list<pair<int, int> > & numGoals = RPGBuilder::getNumericRPGGoals();

        list<pair<int, int> >::iterator ngItr = numGoals.begin();
        const list<pair<int, int> >::iterator ngEnd = numGoals.end();

        for (; ngItr != ngEnd; ++ngItr) {
            if (ngItr->first != -1) {
                const RPGBuilder::RPGNumericPrecondition & currNP = RPGBuilder::getNumericPreTable()[ngItr->first];
                if (!currNP.isSatisfiedWCalculate(state.secondMin, state.secondMax)) return false;
            }

            if (ngItr->second != -1) {
                const RPGBuilder::RPGNumericPrecondition & currNP = RPGBuilder::getNumericPreTable()[ngItr->second];
                if (!currNP.isSatisfiedWCalculate(state.secondMin, state.secondMax)) return false;
            }

        }

        {
            list<FFEvent>::iterator itr = header.begin();
            list<FFEvent>::iterator endPt = header.end();
            for (; itr != endPt; ++itr) {
                itr->lpTimestamp = itr->lpMinTimestamp;
            }
        }

        {
            list<FFEvent>::iterator itr = now.begin();
            list<FFEvent>::iterator endPt = now.end();
            for (; itr != endPt; ++itr) {
                itr->lpTimestamp = itr->lpMinTimestamp;
            }
        }


        return true;

    }


    if (lpDebug & 1) {
        cout << "Extending model to do goal checking\n";
    }
    
    
   

//    const int rowCount = lp->getNumRows();
//    const int colCount = lp->getNumCols();
//    const int goalCount = goalConstraints.size();

//    lp->resize(rowCount + goalCount, colCount);

    list<const Constraint*>::iterator gItr = goalConstraints.begin();
    const list<const Constraint*>::iterator gEnd = goalConstraints.end();

    for (; gItr != gEnd; ++gItr) {
        const int cSize = (*gItr)->weights.size();

        vector<pair<int,double> > entries;
        entries.reserve(cSize);
        
        double offset = 0.0;
        int v;
        for (int s = 0 ; s < cSize; ++s) {
            v = finalNumericVars[(*gItr)->variables[s]].lastEffectValueVariable;
            if (v != -1) {
                if (lpDebug & 1) {
                    cout << "Value of " << (*gItr)->variables[s] << " is column " << v << endl;
                }
                entries.push_back(make_pair(v, (*gItr)->weights[s]));
            } else {
                if (lpDebug & 1) {
                    cout << "Value of " << (*gItr)->variables[s] << " is constant: " << finalNumericVars[(*gItr)->variables[s]].postLastEffectValue << endl;
                }
                
                offset += ((*gItr)->weights[s] * finalNumericVars[(*gItr)->variables[s]].postLastEffectValue);
            }
        }
        if (entries.empty()) {
            if ((offset < (*gItr)->lower) || (offset > (*gItr)->upper)) {
                if (lpDebug & 1) {
                    cout << "A goal constraint is not in range\n";
                }
                return false;
            } else {
                if (lpDebug & 1) {
                    cout << "Goal constraint evaluates to " << offset << ", which is in range [" << (*gItr)->lower << "..\n";
                }
            }
        } else {
            lp->addRow(entries, (*gItr)->lower - offset, (*gItr)->upper - offset);
        }
    }

    if (previousObjectiveVar != -1) {
        lp->setObjCoeff(previousObjectiveVar, 0.0);
        previousObjectiveVar = -1;
    }
    

    int resetRow = -1;
    
    bool mustSucceed = false;
    
    if (Globals::optimiseSolutionQuality && RPGBuilder::getMetric()) {

        // first, optimise solution cost - we can skip this if costs don't need an LP

        if (planCostsWereCalculated && planCostsNeededAnLP) {
            
            if (lpDebug & 1) {
                cout << COLOUR_light_magenta << "Plan costs were calculated, and needed an LP - first solve to minimise cost\n" << COLOUR_default;
            }
            
            map<int,double> objective;
            
            const RPGBuilder::Metric * const metric = RPGBuilder::getMetric();
            
            list<double>::const_iterator wItr = metric->weights.begin();
            const list<double>::const_iterator wEnd = metric->weights.end();
            
            list<int>::const_iterator vItr = metric->variables.begin();
            
            for (; wItr != wEnd; ++wItr, ++vItr) {
                
                if (*vItr < 0) {
                    assert(*vItr == -4); // :makespan
                    objective.insert(make_pair(getDummyVarForMakespan(), 0)).first->second += *wItr;
                    continue;
                }
                
                assert(*vItr >= 0 && *vItr < RPGBuilder::getPNECount());
                const FluentTracking & currFT = finalNumericVars[*vItr];
                
                if (currFT.statusOfThisFluent == FluentTracking::FS_ORDER_INDEPENDENT) {
                                    
                    map<int,double>::const_iterator oiTerms = currFT.orderIndependentValueTerms.begin();
                    const map<int,double>::const_iterator oiTermsEnd = currFT.orderIndependentValueTerms.end();
                    
                    for (; oiTerms != oiTermsEnd; ++oiTerms) {
                        objective.insert(make_pair(oiTerms->first, 0.0)).first->second += oiTerms->second * *wItr;
                    }
                    
                } else if (currFT.lastEffectValueVariable != -1) {    
                    objective.insert(make_pair(currFT.lastEffectValueVariable, 0.0)).first->second += *wItr;
                }
            }        
            
            map<int, list<int> >::const_iterator ppMapItr = varsForPreconditionPreference.begin();
            const map<int, list<int> >::const_iterator ppMapEnd = varsForPreconditionPreference.end();
            
            for (; ppMapItr != ppMapEnd; ++ppMapItr) {
                const double weight = RPGBuilder::getPreferences()[ppMapItr->first].cost;
                
                list<int>::const_iterator ppVar = ppMapItr->second.begin();
                const list<int>::const_iterator ppEnd = ppMapItr->second.end();
                
                for (; ppVar != ppEnd; ++ppVar) {
                    objective.insert(make_pair(*ppVar, 0.0)).first->second += weight;
                }                
                                
            }  
            
            {
                map<int, VarsForPreference>::const_iterator prefItr = varsForPreference.begin();
                const map<int, VarsForPreference>::const_iterator prefEnd = varsForPreference.end();
                
                for (; prefItr != prefEnd; ++prefItr) {
                    if (prefItr->second.committedCostVar >= 0) {
                        objective.insert(make_pair(prefItr->second.committedCostVar, 0.0)).first->second += RPGBuilder::getPreferences()[prefItr->first].cost;
                    }
                }
            }
            
            assert(!objective.empty());
            
            lp->setObjCoeffs(objective.begin(), objective.end());
            
            if (lpDebug & 8) {
                lp->writeLp("goalcostchecking.lp");
            }
            const bool success = lp->solve(false);

            if (success) {

                const int loopLim = planAsAVector.size();
                
                const double * const partialSoln = lp->getPartialSolution(numVars, numVars + loopLim);
                
                for (int stepID = 0; stepID < loopLim; ++stepID) {
                    FFEvent * const itr = planAsAVector[stepID];
                    if (itr->time_spec == Planner::E_AT_START || itr->time_spec == Planner::E_AT_END) {
                        itr->lpTimestamp = partialSoln[timestampVars[stepID] - numVars];
                        if (lpDebug & 2) {
                            cout << "Timestamp of " << *(itr->action) << " (var " << timestampVars[stepID] << ") ";
                            if (itr->time_spec == Planner::E_AT_START) cout << " start = "; else cout << "end = ";
                             cout << itr->lpTimestamp << ", when reaching optimal cost\n";                
                        }                    
                    }
                }                        
                
                
                const double costLimit = lp->getObjValue();
                
                lp->clearObjective();
                
                currentPlanCost = currentPlanCost - currentChoosablePlanCost + costLimit;
                
                currentChoosablePlanCost = costLimit;
                
                vector<pair<int,double> > primaryObjectiveRow;
                primaryObjectiveRow.insert(primaryObjectiveRow.end(), objective.begin(), objective.end());
                
                if (metric->minimise) {
                    lp->addRow(primaryObjectiveRow, -LPinfinity, (ceil(costLimit / Globals::numericTolerance) + 100) * Globals::numericTolerance);
                } else {
                    lp->addRow(primaryObjectiveRow, (floor(costLimit / Globals::numericTolerance) - 100) * Globals::numericTolerance, LPinfinity);
                }
                resetRow = lp->getNumRows() - 1;
                
                mustSucceed = true;
                
            } else {
                if (lpDebug & 1) cout << "Goal not reached\n";
                lp->clearObjective();    
                return false;
            }

        } else {
            
            if (!planCostsWereCalculated) {
                if (lpDebug & 1) {
                    cout << COLOUR_light_magenta << "Plan costs were not calculated earlier\n" << COLOUR_default;
                }
            } else {            
                if (!planCostsNeededAnLP) {
                    if (lpDebug & 1) {
                        cout << COLOUR_light_magenta << "Plan costs do not need an LP\n" << COLOUR_default;
                    }
                }
            }
        }
        
    }
                
                        
    const int makespanVar = getDummyVarForMakespan();

    lp->setObjCoeff(makespanVar, 1.0);
    previousObjectiveVar = makespanVar;


    //cout << "Optimising makespan, lower bound is " << makespanVarMinimum << "\n";

    if (lpDebug & 8) {
        lp->writeLp("goalchecking.lp");
    }
    bool success = lp->solve(false);

    bool toReturn = success;
    
    if (!success) {
        if (mustSucceed) {
            std::cerr << "Warning: numeric precision issues with the LP when optimising the cost of a goal state\n";
            std::cerr << "Plan will not be cost-then-makespan-optimal\n";            
            if (lpDebug & 1) cout << COLOUR_light_red << "Goal not reached, but pretending it was due to precision\n" << COLOUR_default;
            toReturn = true;
        } else {
            if (lpDebug & 1) cout << "Goal not reached\n";
        }
    } else {
        if (lpDebug & 1) cout << "Goal reached by " << header.size() << " header steps along with " << now.size() << " more\n";
        //        if (lpDebug & 2) print_solution(lp, timestampVars.back());
        
        //const double * lpvars = lp->getSolution();
        
        const int loopLim = planAsAVector.size();
        
        const double * const partialSoln = lp->getPartialSolution(numVars, numVars + loopLim);
        
        for (int stepID = 0; stepID < loopLim; ++stepID) {
            FFEvent * const itr = planAsAVector[stepID];
            if (itr->time_spec == Planner::E_AT_START || itr->time_spec == Planner::E_AT_END) {
                itr->lpTimestamp = partialSoln[timestampVars[stepID] - numVars];
                if (lpDebug & 2) {
                    cout << "Timestamp of " << *(itr->action) << " (var " << timestampVars[stepID] << ") ";
                    if (itr->time_spec == Planner::E_AT_START) cout << " start = "; else cout << "end = ";
                    cout << itr->lpTimestamp << ", when reaching goals\n";                
                }                    
            }
        }                        
    }
    
    if (resetRow != -1) {  
        if (RPGBuilder::getMetric()->minimise) {
            lp->setRowUpper(resetRow, LPinfinity);
        } else {
            lp->setRowLower(resetRow, -LPinfinity);
        }
    }
    
    return toReturn;


};

bool LPScheduler::addAnyNumericConstraints(const list<pair<int, Planner::time_spec > > & numericConditions,
                                           const int & actStartAt, const int & actEndAt, list<int> & conditionVars)
{
    static const vector<pair<int,double> > emptyEntries(0);
    static const bool debug = (Globals::globalVerbosity & 32);    
    static const int pneCount = RPGBuilder::getPNECount();
    
    if (debug) {
        cout << "Conditional effect has " << numericConditions.size() << " numeric conditions\n";
    }
    
    const map<int,double> & tickerVars = NumericAnalysis::getVariablesThatAreTickers();
        
    list<pair<int, Planner::time_spec > >::const_iterator condItr = numericConditions.begin();
    const list<pair<int, Planner::time_spec > >::const_iterator condEnd = numericConditions.end();
    
    for (; condItr != condEnd; ++condItr) {
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[condItr->first];
        
        /// TODO extend to variables other than ?duration
        
        double threshold = currPre.RHSConstant;
        VAL::comparison_op op = currPre.op;

        bool isDurationVar = false;
        bool isTimestampVar = false;
        double tickerMultipler = 1.0;
        
        bool negativeVar = false;
        

        int localVar = currPre.LHSVariable;
        
        if (localVar >= 2 * pneCount) {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
            
            if (currAV.size != 1) {
                cout << "Ignoring conditional effect dependent on " << currPre << " for now, as is size other than 1\n";
                return false;
            }
            
            localVar = currAV.fluents[0];
            threshold = currPre.RHSConstant - currAV.constant;
        }
        
        if (currPre.LHSVariable < 0) {
            switch (currPre.LHSVariable) {
                case -3: {
                    isDurationVar = true;
                    break;
                }
                case -4: {
                    isTimestampVar = true;
                    break;
                }
                case -19: {
                    isDurationVar = true;
                    negativeVar = true;
                    break;
                }
                case -20: {
                    isTimestampVar = true;
                    negativeVar = true;
                    break;
                }
                default: {
                    cout << "Ignoring conditional effect dependent on special var " << currPre << " for now\n";
                    return false;
                }
            }
                    
        } else {
            assert(localVar < 2 * pneCount);
                
            if (localVar < pneCount) {
                const map<int,double>::const_iterator tvItr = tickerVars.find(localVar);
                if (tvItr != tickerVars.end()) {
                    isTimestampVar = true;
                    tickerMultipler = tvItr->second;
                } else {
                    cout << "Ignoring conditional effect dependent on " << currPre << " for now, as " << localVar << " isn't a ticker\n";
                    return false;                        
                }
            } else {
                const map<int,double>::const_iterator tvItr = tickerVars.find(localVar - pneCount);
                if (tvItr != tickerVars.end()) {
                    isTimestampVar = true;
                    tickerMultipler = tvItr->second;
                    negativeVar = true;
                } else {
                    cout << "Ignoring conditional effect dependent on " << currPre << " for now, as " << localVar - pneCount << " isn't a ticker\n";
                    return false;                        
                }
            }
        }
               
        if (negativeVar) {
            if (op == VAL::E_GREATEQ) {
                op = VAL::E_LESSEQ;
            } else if (op == VAL::E_GREATER) {
                op = VAL::E_LESS;
            }
            if (threshold != 0.0) {
                threshold = -threshold;
            }
            
        }
        
        assert(isDurationVar || isTimestampVar);
        assert(!isDurationVar || !isTimestampVar);
                
        lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
        
        const int switchVar = lp->getNumCols() - 1;
        
        if (nameLPElements) {
            ostringstream s;
            if (isDurationVar) {
                s << "dur" << actStartAt;
            } else {
                s << "ts";
                if (condItr->second == Planner::E_AT_START) {                    
                    s << actStartAt;
                } else {
                    s << actEndAt;
                }
            }
            if (op == VAL::E_LESS) {
               s << "lt";
            } else if (op == VAL::E_LESSEQ) {
                s << "leq";
            }if (op == VAL::E_GREATER) {
                s << "gt";
            } else if (op == VAL::E_GREATEQ) {
                s << "geq";
            }
            s << threshold;
            string cname = s.str();
            lp->setColName(switchVar, cname);
        }

        if (debug) {
            cout << "Adding switch var " << lp->getColName(switchVar) << " for constraint ";
            if (isDurationVar) {
                cout << "(?duration ";
            } else {
                cout << "(time-elapsed ";
            }
            switch (op) {
                case VAL::E_GREATER:
                {
                    cout << ">";
                    break;
                }
                case VAL::E_GREATEQ:
                {
                    cout << ">=";
                    break;
                }
                case VAL::E_LESS:
                {
                    cout << "<";
                    break;
                }
                case VAL::E_LESSEQ:
                {
                    cout << "<=";
                    break;
                }
                default:
                {
                    cout << " - Error, = constraint should have been preprocessed into a <= and a >=\n";
                    exit(1);
                }
            }
            cout << " " << threshold << ")" << endl;                    
        }
        

        {
            vector<pair<int,double> > durConstraint;
            durConstraint.reserve(3);
            
            // first, we construct a constraint that enforces the bound on ?duration if switchVar = 1

            if (isDurationVar) {
                durConstraint.push_back(make_pair(actEndAt,1.0));
                durConstraint.push_back(make_pair(actStartAt,-1.0));
            } else {
                if (condItr->second == Planner::E_AT_START) {
                    durConstraint.push_back(make_pair(actStartAt,1.0));
                } else {
                    durConstraint.push_back(make_pair(actEndAt,1.0));
                }
            }
            
            switch (op) {
                case VAL::E_GREATER:
                {
                    durConstraint.push_back(make_pair(switchVar, -(threshold + EPSILON)));
                    lp->addRow(durConstraint, 0.0, LPinfinity);
                    break;
                }
                case VAL::E_GREATEQ:
                {
                    durConstraint.push_back(make_pair(switchVar, -threshold));
                    lp->addRow(durConstraint, 0.0, LPinfinity);
                    break;
                }
                case VAL::E_LESS:
                {
                    durConstraint.push_back(make_pair(switchVar, (N - (threshold - EPSILON))));
                    lp->addRow(durConstraint, -LPinfinity, N);
                    break;
                }
                case VAL::E_LESSEQ:
                {
                    durConstraint.push_back(make_pair(switchVar, (N - threshold)));
                    lp->addRow(durConstraint, -LPinfinity, N);
                    break;
                }
                default:
                {
                    std::cerr << "Internal error: = precondition should have been preprocessed into a >=, <= pair\n";
                    exit(1);
                }
                
            }
            if (nameLPElements) {
                ostringstream s;
                s << "sw" << switchVar;
                if (isDurationVar) {
                    s << "impldur";
                } else {
                    s << "implts";
                }
                string cname = s.str();
                lp->setRowName(lp->getNumRows() - 1, cname);
            }
        }
                
        // next, we construct a constraint that means switchVar = 1 if the bound on ?duration is met
        
        {
            vector<pair<int,double> > durConstraint;
            durConstraint.reserve(3);
            
            switch (op) {
                case VAL::E_GREATER:
                case VAL::E_GREATEQ:
                {
                    
                    if (isDurationVar) {
                        durConstraint.push_back(make_pair(actEndAt,-1.0));                    
                        durConstraint.push_back(make_pair(actStartAt,1.0));                    
                    } else {
                        if (condItr->second == Planner::E_AT_START) {
                            durConstraint.push_back(make_pair(actStartAt,-1.0));
                        } else {
                            durConstraint.push_back(make_pair(actEndAt,-1.0));
                        }                                                
                    }
                    
                    
                    durConstraint.push_back(make_pair(switchVar,N));
                    
                    if (op == VAL::E_GREATER) {
                        lp->addRow(durConstraint, -threshold, LPinfinity);
                    } else {
                        lp->addRow(durConstraint, -(threshold - EPSILON), LPinfinity);
                    }
                    
                    break;
                }
                
                case VAL::E_LESS:
                case VAL::E_LESSEQ:
                {
                    
                    
                    if (isDurationVar) {
                        durConstraint.push_back(make_pair(actEndAt,1.0));
                        durConstraint.push_back(make_pair(actStartAt,-1.0));
                    } else {
                        if (condItr->second == Planner::E_AT_START) {
                            durConstraint.push_back(make_pair(actStartAt,1.0));
                        } else {
                            durConstraint.push_back(make_pair(actEndAt,1.0));
                        }
                    }
                    

                    durConstraint.push_back(make_pair(switchVar,N));
                                        
                    if (op == VAL::E_LESS) {
                        lp->addRow(durConstraint, threshold, LPinfinity);
                    } else {
                        lp->addRow(durConstraint, threshold + EPSILON, LPinfinity);
                    }
                    
                    break;
                }
                default:
                {
                    std::cerr << "Internal error: = precondition should have been preprocessed into a >=, <= pair\n";
                    exit(1);
                }
                
                
            }

        }
                
        if (nameLPElements) {
            ostringstream s;
            if (isDurationVar) {
                s << "durimplsv";
            } else {
                s << "tsimplsv";
            }
            s << switchVar;
            string cname = s.str();
            lp->setRowName(lp->getNumRows() - 1, cname);
        }
        
        conditionVars.push_back(switchVar);
    }
    
    return true;
}


bool LPScheduler::addAnyTimeWindowConstraints(const list<pair<Literal*, Planner::time_spec > > & propositionalConditions,
                                              const int & actStartAt, const int & actEndAt, list<int> & conditionVars)
{
    
    static const vector<pair<int,double> > emptyEntries(0);
    static const bool debug = (Globals::globalVerbosity & 32);    
    
    list<pair<Literal*, Planner::time_spec > >::const_iterator condItr = propositionalConditions.begin();
    const list<pair<Literal*, Planner::time_spec > >::const_iterator condEnd = propositionalConditions.end();
    
    for (int cep = 0; condItr != condEnd; ++condItr, ++cep) {
        const Literal* const currLit = condItr->first;
    
        const list<pair<double,double> > * windows = TemporalAnalysis::factIsVisibleInWindows(currLit);
        
        if (!windows) {
            if (debug) {
                cout << *currLit << " does not form TIL windows\n";
            }
            return false;
        }

        if (debug) {
            cout << *currLit << " forms TIL windows\n";
        }            
        
        vector<int> boundVars(2,-1);
        
        if (condItr->second != Planner::E_AT_END) {
            if (debug) {
                cout << lp->getColName(actStartAt) << " needs to fall within a window\n";
            }            
            boundVars[0] = actStartAt;
        }        
        if (condItr->second != Planner::E_AT_START) {
            if (debug) {
                cout << lp->getColName(actEndAt) << " needs to fall within a window\n";
            }                        
            boundVars[1] = actEndAt;
        }
        
        list<pair<double,double> >::const_iterator wItr = windows->begin();
        const list<pair<double,double> >::const_iterator wEnd = windows->end();
        
        list<int> windowSwitches;
        
        for (; wItr != wEnd; ++wItr) {
            int startAndEndVar = -1;
            for (int vi = 0; vi < 2; ++vi) {            
                if (boundVars[vi] == -1) continue;
                
                lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
                const int switchAB = lp->getNumCols() - 1;
                
                if (nameLPElements) {
                    ostringstream s;
                    s << boundVars[vi]<< "in" << wItr->first << "to";
                    if (wItr->second == DBL_MAX) {
                        s << "inf";
                    } else {
                        s << wItr->second;
                    }
                    string cname = s.str();
                    lp->setColName(switchAB, cname);
                }
                
                static vector<pair<int,double> > binaryConstraint(2);
                
                if (wItr->first == 0.0) {
                    
                    // if switchAB is set to 1, upper bound on boundVars[vi] is wItr->second
                    binaryConstraint[0].second = 1.0;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = (N - wItr->second - SAFE);
                    binaryConstraint[1].first = switchAB;                    
                    lp->addRow(binaryConstraint, 0.0, N);
                    
                    // if boundVars[i] < wItr->second, then switchAB must be = 1
                    binaryConstraint[0].second = 1.0;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = N;
                    binaryConstraint[1].first = switchAB;                    
                    lp->addRow(binaryConstraint, wItr->second, LPinfinity);
                    
                } else if (wItr->second == DBL_MAX) {

                    // if switchAB is set to 1, lower bound on boundVars[vi] is wItr->first
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = -(wItr->first + SAFE);
                    binaryConstraint[1].first = switchAB;                    
                    lp->addRow(binaryConstraint, 0.0, LPinfinity);
                    
                    // if boundVars[i] > wItr->first, then switchAB must be = 1
                    binaryConstraint[0].second = -1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = N;
                    binaryConstraint[1].first = switchAB;                    
                    lp->addRow(binaryConstraint, -wItr->first, LPinfinity);
                    
                } else {
                    
                    lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
                    const int lb = lp->getNumCols() - 1;
                    
                    if (nameLPElements) {
                        ostringstream s;
                        s << boundVars[vi]<< "bef" << wItr->second;
                        string cname(s.str());
                        lp->setColName(lb, cname);
                    }
                    
                    // if lb is set to 1, upper bound on boundVars[vi] is wItr->second
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = (N - wItr->second - SAFE);
                    binaryConstraint[1].first = lb;                    
                    lp->addRow(binaryConstraint, 0.0, N);
                    
                    // if boundVars[i] < wItr->second, then lb must be = 1
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = N;
                    binaryConstraint[1].first = lb;                    
                    lp->addRow(binaryConstraint, wItr->second, LPinfinity);

                    
                    lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
                    const int ga = lp->getNumCols() - 1;

                    if (nameLPElements) {
                        ostringstream s;
                        s << boundVars[vi]<< "aft" << wItr->first;
                        string cname(s.str());
                        lp->setColName(ga, cname);
                    }
                    
                    // if ga is set to 1, lower bound on boundVars[vi] is wItr->first
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = -(wItr->first + SAFE);
                    binaryConstraint[1].first = ga;                    
                    lp->addRow(binaryConstraint, 0.0, LPinfinity);
                    
                    // if boundVars[i] > wItr->first, then ga must be = 1
                    binaryConstraint[0].second = -1;
                    binaryConstraint[0].first = boundVars[vi];                    
                    binaryConstraint[1].second = N;
                    binaryConstraint[1].first = ga;                    
                    lp->addRow(binaryConstraint, -wItr->first, LPinfinity);
                    
                    // if switchAB = 1, lb = 1
                    binaryConstraint[0].second = -1;
                    binaryConstraint[0].first = switchAB;                    
                    binaryConstraint[1].second = 1;
                    binaryConstraint[1].first = lb;                    
                    lp->addRow(binaryConstraint, 0, LPinfinity);

                    // if switchAB = 1, ga = 1
                    binaryConstraint[0].second = -1;
                    binaryConstraint[0].first = switchAB;                    
                    binaryConstraint[1].second = 1;
                    binaryConstraint[1].first = ga;                    
                    lp->addRow(binaryConstraint, 0, LPinfinity);
                                      
                    static vector<pair<int,double> > bothForceAB(3);
                    // if ga =1 and lb = 1, switchAB = 1
                    bothForceAB[0].second = 1;
                    bothForceAB[0].first = switchAB;
                    bothForceAB[1].second = -1;
                    bothForceAB[1].first = ga;
                    bothForceAB[2].second = -1;
                    bothForceAB[2].first = lb;
                    lp->addRow(bothForceAB, -1, LPinfinity);                    
                }
                
                if (startAndEndVar == -1) {
                    startAndEndVar = switchAB;
                } else {
                    const int switchAB2 = startAndEndVar;
                    
                    lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
                    const int switchABBoth = lp->getNumCols() - 1;
                    
                    static vector<pair<int,double> > bothForceOverall(3);
                    // If both the start and the end are in, then over all is in
                    bothForceOverall[0].second = 1;
                    bothForceOverall[0].first = switchABBoth;
                    bothForceOverall[1].second = -1;
                    bothForceOverall[1].first = switchAB;
                    bothForceOverall[2].second = -1;
                    bothForceOverall[2].first = switchAB2;
                    lp->addRow(bothForceOverall, -1, LPinfinity);                    
                    
                    static vector<pair<int,double> > binaryConstraint(2);
                    
                    // if overall is in, then the end must be in
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = switchAB;
                    binaryConstraint[1].second = -1;
                    binaryConstraint[1].first = switchABBoth;
                    lp->addRow(binaryConstraint, 0.0, LPinfinity);

                    // if overall is in, then the start must be in
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = switchAB2;
                    binaryConstraint[1].second = -1;
                    binaryConstraint[1].first = switchABBoth;
                    lp->addRow(binaryConstraint, 0.0, LPinfinity);
                    
                }
            }
            
            windowSwitches.push_back(startAndEndVar);
        }
        
        const int wCount = windowSwitches.size();
        if (wCount == 1) {
            conditionVars.push_back(windowSwitches.front());
        } else {
            lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);
            const int switchOverall = lp->getNumCols() - 1;
            
            if (nameLPElements) {
                ostringstream s;
                s << actStartAt << "c" << cep << "met";
                string cname(s.str());
                lp->setColName(switchOverall, cname);
                
            }
            conditionVars.push_back(switchOverall);
            
            {
                static vector<pair<int,double> > binaryConstraint(2);
                
                list<int>::const_iterator swItr = windowSwitches.begin();
                const list<int>::const_iterator swEnd = windowSwitches.end();
                
                for (; swItr != swEnd; ++swItr) {
                    // if one window's switch is true, the overall switch must be true
                    binaryConstraint[0].second = 1;
                    binaryConstraint[0].first = switchOverall;
                    binaryConstraint[1].second = -1;
                    binaryConstraint[1].first = *swItr;
                    lp->addRow(binaryConstraint, 0.0, LPinfinity);
                }
            }
            
            vector<pair<int,double> > entries(wCount + 1);
            
            {
                list<int>::const_iterator swItr = windowSwitches.begin();
                const list<int>::const_iterator swEnd = windowSwitches.end();
                
                for (int vi = 0; swItr != swEnd; ++swItr, ++vi) {
                    entries[vi].first = *swItr;
                    entries[vi].second = 1.0;
                }
            }
            entries[wCount].first = switchOverall;
            entries[wCount].second = -1.0;
            
            // if the overall switch is 1, then at least one of the window
            // switches must also be 1
            lp->addRow(entries, 0.0, LPinfinity);

        }
    }
    
    return true;
}


bool LPScheduler::scheduleToMetric()
{   
    static const vector<pair<int,double> > emptyEntries(0);
    
    int variableForRecentStep = -1;
    if (previousObjectiveVar != -1) {
        variableForRecentStep = previousObjectiveVar;
        lp->setObjCoeff(previousObjectiveVar, 0.0);
        previousObjectiveVar = -1;
    }

    // First, make sure that in scheduling to the metric, we don't break the goals
    
    list<const Constraint*>::iterator gItr = goalConstraints.begin();
    const list<const Constraint*>::iterator gEnd = goalConstraints.end();
    
    for (; gItr != gEnd; ++gItr) {
        const int cSize = (*gItr)->weights.size();
        
        vector<pair<int,double> > entries(cSize);
        
        for (int s = 0 ; s < cSize; ++s) {
            entries[s].second = (*gItr)->weights[s];
            if (assertions) assert(entries[s].second != 0.0);
            entries[s].first = finalNumericVars[(*gItr)->variables[s]].lastEffectValueVariable;
        }
        lp->addRow(entries, (*gItr)->lower, (*gItr)->upper);
    }
    
    // ... and make a term for makespan, in case it appears in the objective
    // (or, after that, to find a good makespan within the best-quality solutions)
    
    
    lp->addCol(emptyEntries, makespanVarMinimum, LPinfinity, MILPSolver::C_REAL);

    const int variableForMakespan = lp->getNumCols() - 1;

    {
        list<int>::iterator comesAfter = endsOfThreads.begin();
        const list<int>::iterator comesAfterEnd = endsOfThreads.end();

        for (; comesAfter != comesAfterEnd; ++comesAfter) {
            static vector<pair<int,double> > entries(2);
            
            entries[0].second = 1.0;
            entries[1].second = -1.0;

            entries[0].first = variableForMakespan;
            entries[1].first = *comesAfter;

            lp->addRow(entries, 0.0, LPinfinity);

        }
    }

    
    const RPGBuilder::Metric * const metric = RPGBuilder::getMetric();
    
    MILPSolver::Objective newObjective(!metric->minimise);
    
    const int termCount = metric->variables.size();
    
    /* For each metric variable, specifies its weight in the objective function */
    map<int, double> mapVariableToObjectiveWeight;
    
    /* For each metric term, the LP column containing its value. */
    vector<int> columnForTerm(termCount);
    
    if (termCount == 1 && metric->variables.front() < 0) {
        cout << "; Warning: metric is just to optimise makespan, so post-hoc optimisation is redundant unless being used as a partial-order lifter\n";
    }
    
    list<double>::const_iterator wItr = metric->weights.begin();
    list<int>::const_iterator vItr = metric->variables.begin();
    
    for (int t = 0; t < termCount; ++t, ++vItr, ++wItr) {
        const int currVar = *vItr;

        mapVariableToObjectiveWeight.insert(make_pair(currVar, *wItr));
        
        if (currVar < 0) {
            columnForTerm[t] = variableForMakespan;
            if (variableForMakespan != -1) {
                newObjective.getTerm(variableForMakespan).linearCoefficient = *wItr;
            }
            continue;
        }
        
        FluentTracking & varInfo = finalNumericVars[currVar];
        
        if (varInfo.statusOfThisFluent == FluentTracking::FS_IGNORE) continue;
        
        if (varInfo.statusOfThisFluent == FluentTracking::FS_NORMAL) {
            if (lpDebug & 1) {
                cout << *(RPGBuilder::getPNE(currVar)) << " is a normal variable, adding " << *wItr << " times it to the objective\n";
            }
            columnForTerm[t] = varInfo.lastEffectTimestampVariable;

            if (varInfo.lastEffectTimestampVariable != -1) {
                newObjective.getTerm(varInfo.lastEffectTimestampVariable).linearCoefficient = *wItr;
            }                
            
        } else {

            if (lpDebug & 1) {
                cout << *(RPGBuilder::getPNE(currVar)) << " is an order-independent metric variable, adding terms to objective:\n\t";
            }
            
            map<int,double>::const_iterator termItr = varInfo.orderIndependentValueTerms.begin();
            const map<int,double>::const_iterator termEnd = varInfo.orderIndependentValueTerms.end();
            
            for (bool plus=false; termItr != termEnd; ++termItr) {
                newObjective.getTerm(termItr->first).linearCoefficient += (*wItr * termItr->second);
                if (lpDebug & 1) {
                    if (plus) {
                        cout << " + ";
                    }
                    cout << (*wItr * termItr->second) << " * " << lp->getColName(termItr->first);
                    plus = true;
                }
            }
            if (lpDebug & 1) {
                cout << endl;
            }
                
            
        }
    }

    const map<int,double> & tickerVars = NumericAnalysis::getVariablesThatAreTickers();
    static const int pneCount = RPGBuilder::getPNECount();
    
    const int actCount = planAsAVector.size();
    
    for (int act = 0; act < actCount; ++act) {
        FFEvent * const currEvent = planAsAVector[act];        
        if (currEvent->time_spec == Planner::E_AT) continue;
        if (currEvent->time_spec == Planner::E_AT_END) continue;
        
        const list<RPGBuilder::ConditionalEffect> & condEffs = RPGBuilder::getActionsToConditionalEffects()[currEvent->action->getID()];
        if (condEffs.empty()) continue;
        
        const int actStartAt = timestampVars[act];
        const int actEndAt = (RPGBuilder::getRPGDEs(currEvent->action->getID()).empty() ? -1 : timestampVars[currEvent->pairWithStep]);
        
        list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs.begin();
        const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs.end();
        
        for (int cep = 0; ceItr != ceEnd; ++ceItr, ++cep) {
            list<int> conditionVars;
            
            if (lpDebug & 1) {
                cout << "Considering conditional effect " << cep << " on step " << act << ", " << *(currEvent->action) << " start\n";
                cout << "Start step var: " << actStartAt << ", end var: " << actEndAt << endl;
            }
            const bool success = addAnyTimeWindowConstraints(ceItr->getPropositionalConditions(), actStartAt, actEndAt, conditionVars);

            if (!success) continue;
            
            const bool success2 = addAnyNumericConstraints(ceItr->getNumericPreconditions(), actStartAt, actEndAt, conditionVars);
            
            if (!success2) continue;

            if (conditionVars.empty()) {
                if (lpDebug & 1) {
                    cout << "No metric effects recognised, ignoring it\n";
                }
                continue;
            }
            
            int colRepresentingAllConstraintsSatisfied = -1;
            
            const int cvCount = conditionVars.size();
            
            if (cvCount == 1) {                
                colRepresentingAllConstraintsSatisfied = conditionVars.front();
            } else if (cvCount > 1) {
                lp->addCol(emptyEntries, 0, 1, MILPSolver::C_BOOL);            
                colRepresentingAllConstraintsSatisfied = lp->getNumCols() - 1;

                if (nameLPElements) {
                    ostringstream s;
                    s << "s" << act << "ce" << cep << "satisfied";
                    string cname(s.str());
                    lp->setColName(colRepresentingAllConstraintsSatisfied, cname);
                }
                
                static vector<pair<int,double> > binaryConstraint(2);
                {
                    list<int>::const_iterator cvItr = conditionVars.begin();
                    const list<int>::const_iterator cvEnd = conditionVars.end();
                    
                    for (; cvItr != cvEnd; ++cvItr) {
                        // if all constraints are considered satisfied, each must be
                        binaryConstraint[0].second = 1;
                        binaryConstraint[0].first  = *cvItr;
                        binaryConstraint[1].second = -1;
                        binaryConstraint[1].first  = colRepresentingAllConstraintsSatisfied;
                        lp->addRow(binaryConstraint, 0.0, LPinfinity);
                    }
                }
                
                vector<pair<int,double> > entries(cvCount + 1);
                                                
                {
                    list<int>::const_iterator cvItr = conditionVars.begin();
                    const list<int>::const_iterator cvEnd = conditionVars.end();
 
                    for (int cvi = 0; cvItr != cvEnd; ++cvItr, ++cvi) {
                        entries[cvi].second = -1;
                        entries[cvi].first = *cvItr;
                    }
                                                
                }

                entries[cvCount].first = colRepresentingAllConstraintsSatisfied;
                entries[cvCount].second = 1.0;
                
                // if all the condition switches are set to 1, the overall switch must be also
            
                lp->addRow(entries, 1-cvCount, LPinfinity);
                                                  
            }
            
            assert(colRepresentingAllConstraintsSatisfied >= 0 && colRepresentingAllConstraintsSatisfied < lp->getNumCols());
            // now, using the variable 'colRepresentingAllConstraintsSatisfied' we need to
            // add the conditional effects
            
             const list<pair<int, Planner::time_spec> > & effs = ceItr->getNumericEffects();
            list<pair<int, Planner::time_spec> >::const_iterator effItr = effs.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator effEnd = effs.end();
            
            /* The sum effect on the objective if all conditions are met. */
            
            MILPSolver::Objective::Coefficient & overallObjectiveWeightOfEffect = newObjective.getTerm(colRepresentingAllConstraintsSatisfied);
            
            for (; effItr != effEnd; ++effItr) {
                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[effItr->first];

                assert(effItr->second == Planner::E_AT_START || actEndAt != -1);
                
                if (lpDebug & 1) {
                    if (effItr->second == Planner::E_AT_START) {
                        cout << "Has a cond eff at the start\n";
                    } else {
                        cout << "Has a cond eff at the end\n";
                    }
                }
                
                map<int,double>::const_iterator wItr = mapVariableToObjectiveWeight.find(currEff.fluentIndex);
                
                if (wItr == mapVariableToObjectiveWeight.end()) {
                    // has no weight (or a 0 weight) in the :metric
                    continue;
                }
                
                if (currEff.isAssignment) {
                    cout << "Warning: ignoring conditional metric effect " << currEff << ", as for now only increase/decrease metric conditional effects are supported\n";
                    continue;
                }
                
                {
                    int s = 0;
                    map<int,double>::const_iterator tvItr;
                    for (; s < currEff.size; ++s) {
                        if (currEff.variables[s] == -3 || currEff.variables[s] == -19) {
                            continue;
                        }
                        if (currEff.variables[s] == -4 || currEff.variables[s] == -20) {
                            continue;
                        }                                                   
                        tvItr = tickerVars.find(currEff.variables[s]);       
                        if (tvItr != tickerVars.end()) {
                            continue;
                        }
                        tvItr = tickerVars.find(currEff.variables[s] - pneCount);       
                        if (tvItr != tickerVars.end()) {
                            continue;
                        }
                    }
                    if (s != currEff.size) {
                        cout << "Warning: ignoring conditional metric effect " << currEff << ", as for now the conditional effects can only be in terms of constants, ?duration, or tickers\n";
                        continue;
                    }
                }
                                                
                overallObjectiveWeightOfEffect.linearCoefficient += wItr->second * currEff.constant;
                
                for (int s = 0; s < currEff.size; ++s) {
                    switch (currEff.variables[s]) {
                        case -3: {
                            overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second += (currEff.weights[s] * wItr->second);
                            overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second);
                            break;
                        }
                        case -19: {
                            overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second);
                            overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second += (currEff.weights[s] * wItr->second);
                            break;
                        }
                        case -4: {
                            if (effItr->second == Planner::E_AT_START) {
                                overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second += (currEff.weights[s] * wItr->second);
                            } else {
                                overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second += (currEff.weights[s] * wItr->second);
                            }                            
                            break;
                        }
                        case -20: {
                            if (effItr->second == Planner::E_AT_START) {
                                overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second);
                            } else {
                                overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second);
                            }                            
                            break;
                        }
                                                
                        default: {
                            if (currEff.variables[s] < pneCount) {
                                const map<int,double>::const_iterator tvItr = tickerVars.find(currEff.variables[s]);       
                                assert(tvItr != tickerVars.end());
                                if (effItr->second == Planner::E_AT_START) {
                                    overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second += (currEff.weights[s] * wItr->second) * tvItr->second;
                                } else {
                                    overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second += (currEff.weights[s] * wItr->second) * tvItr->second;
                                }
                            } else {
                                const map<int,double>::const_iterator tvItr = tickerVars.find(currEff.variables[s] - pneCount);       
                                assert(tvItr != tickerVars.end());
                                if (effItr->second == Planner::E_AT_START) {
                                    overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actStartAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second) * tvItr->second;
                                } else {
                                    overallObjectiveWeightOfEffect.nonLinearCoefficients.insert(make_pair(actEndAt, 0.0)).first->second -= (currEff.weights[s] * wItr->second) * tvItr->second;
                                }                                                                
                            }
                        }
                    }
                }
                
                
            }
     
            if (colRepresentingAllConstraintsSatisfied != -1) {
                if (Globals::globalVerbosity & 32) {
                    cout << "Adding term to objective: " << overallObjectiveWeightOfEffect.linearCoefficient << "*" << lp->getColName(colRepresentingAllConstraintsSatisfied) << endl;
                }
                if (!overallObjectiveWeightOfEffect.nonLinearCoefficients.empty()) {
                    if (Globals::globalVerbosity & 32) {
                        cout << "Adding quadratic terms to objective: " << lp->getColName(colRepresentingAllConstraintsSatisfied) << " * (";
                        map<int,double>::const_iterator qtItr = overallObjectiveWeightOfEffect.nonLinearCoefficients.begin();
                        const map<int,double>::const_iterator qtEnd = overallObjectiveWeightOfEffect.nonLinearCoefficients.end();
                        
                        for (bool plus = false; qtItr != qtEnd; ++qtItr, plus = true) {
                            if (plus) {
                                cout << " + ";
                            }
                            if (qtItr->second != 1.0) {
                                cout << qtItr->second << " * ";
                            }
                            cout << lp->getColName(qtItr->first);
                        }
                        cout << ")\n";
                    }
                }
            }
        }
    }
    
    if (Globals::globalVerbosity & 32) {
        MILPSolver::debug = true;
    }
    
    lp->setQuadraticObjective(newObjective);
    if (!lp->quadraticPreSolve()) {
        if (Globals::globalVerbosity & 32) {
            cout << "Could not solve problem with objective set to problem metric\n";
        }
        return false;
    }
    
    lp->setMaximiseObjective(false);
    lp->setObjCoeff(variableForMakespan, 1);

    if (Globals::globalVerbosity & 32) {
        cout << "Set objective to minimise makespan variable " << lp->getColName(variableForMakespan) << endl;
        lp->writeLp("final.lp");
    }
    
    return true;
    // all done - the actual (final) solving is done back in the calling method (the constructor)
    
}

void LPScheduler::pushTimestampToMin(vector<AutomatonPosition::Position> & preferenceStatus, const map<int,double> & csEndLowerBound, const map<int,double> & rpLowerBounds)
{
    if (lpDebug & 1) {
        cout << COLOUR_light_red << "Min timestamp of new step is now " << timestampToUpdate->lpTimestamp << ", rather than " << timestampToUpdate->lpMinTimestamp << COLOUR_default << endl;
    }                                                                
    
    if (cd) {
        
        {
            map<int,pair<int,double> >::const_iterator dsItr = newDummySteps.begin();
            const map<int,pair<int,double> >::const_iterator dsEnd = newDummySteps.end();
            
            for (; dsItr != dsEnd; ++dsItr) {
                if (!cd->updateLPMinTimestamp(dsItr->second.second, dsItr->first)) {
                    std::cerr << "Internal error: the solution found by the LP should not violate the temporal constraints used by BF\n";
                    exit(1);
                }
            }
        }
        
        for (int pass = 0; pass < 2; ++pass) {
            
            const map<int,double> & loopOver = (pass ? rpLowerBounds : csEndLowerBound);
            map<int,double>::const_iterator rplItr = loopOver.begin();
            const map<int,double>::const_iterator rplEnd = loopOver.end();
             
            for (; rplItr != rplEnd; ++rplItr) {
                if (!cd->updateLPMinTimestamp(rplItr->second, rplItr->first)) {
                    std::cerr << "Internal error: the solution found by the LP should not violate the temporal constraints used by BF\n";
                    exit(1);
                }
            }
        }
  
        if (!cd->updateLPMinTimestamp(timestampToUpdate->lpTimestamp, timestampToUpdateStep)) {
            std::cerr << "Internal error: the solution found by the LP should not violate the temporal constraints used by BF\n";
            exit(1);
        }
        
        if (lpDebug & 1) {
            cout << "Pushed lower bound on CD: Got min timestamps from BF again" << endl;
        }

        if (!Globals::profileScheduling) {
            if (lpDebug & 1) {
                cout << "CD: Got min timestamps from BF again" << endl;
            }
            cd->distsToLPMinStamps();
        }

        lp->setColLower(timestampToUpdateVar, EpsilonResolutionTimestamp(timestampToUpdate->lpMinTimestamp,true).toDouble());

        if (lpDebug & 1) {
            cout << "CD: Set lower bound on " << lp->getColName(timestampToUpdateVar) << " to " << timestampToUpdate->lpMinTimestamp << ", is now " << lp->getColLower(timestampToUpdateVar) << endl;
        }

        
        if (timestampToUpdatePartner) {
            lp->setColLower(timestampToUpdatePartnerVar, EpsilonResolutionTimestamp(timestampToUpdatePartner->lpMinTimestamp,true).toDouble());
        }

        {
            map<int,pair<int,double> >::iterator dsItr = newDummySteps.begin();
            const map<int,pair<int,double> >::iterator dsEnd = newDummySteps.end();
            
            for (; dsItr != dsEnd; ++dsItr) {
                const EpsilonResolutionTimestamp rounded(planAsAVector[dsItr->first]->lpMinTimestamp,true);
                lp->setColLower(dsItr->second.first, rounded.toDouble());
                dsItr->second.second = rounded.toDouble();
                
                if (lpDebug & 1) {
                    cout << "CD: Set lower bound on " << lp->getColName(dsItr->second.first) << " to " << planAsAVector[dsItr->first]->lpMinTimestamp << ", is now " << lp->getColLower(dsItr->second.first) << endl;
                }
            }
        }
        
       for (int pass = 0; pass < 2; ++pass) {
            
            const map<int,double> & loopOver = (pass ? rpLowerBounds : csEndLowerBound);
            map<int,double>::const_iterator rplItr = loopOver.begin();
            const map<int,double>::const_iterator rplEnd = loopOver.end();
             
            for (; rplItr != rplEnd; ++rplItr) {
                const EpsilonResolutionTimestamp rounded(planAsAVector[rplItr->first]->lpMinTimestamp,true);
                lp->setColLower(rplItr->first + numVars, rounded.toDouble());
                
                if (lpDebug & 1) {
                    cout << "CD: Set lower bound on " << lp->getColName(rplItr->first + numVars) << " to " << planAsAVector[rplItr->first]->lpMinTimestamp << ", is now " << lp->getColLower(rplItr->first + numVars) << endl;
                }
            }
        }
        
    } else {
        timestampToUpdate->lpMinTimestamp = timestampToUpdate->lpTimestamp;
        lp->setColLower(timestampToUpdateVar, timestampToUpdate->lpMinTimestamp);
        
        if (lpDebug & 1) {
            cout << "Set lower bound on " << lp->getColName(timestampToUpdateVar) << " to " << timestampToUpdate->lpMinTimestamp << endl;
        }

        if (timestampToUpdatePartner) {
            if (timestampToUpdate->time_spec == Planner::E_AT_END) {
                EpsilonResolutionTimestamp newMin(timestampToUpdate->lpMinTimestamp, true);
                EpsilonResolutionTimestamp maxDur(timestampToUpdate->maxDuration, true);
                if (maxDur < newMin) {
                    newMin -= maxDur;
                    double & oldMin = timestampToUpdatePartner->lpMinTimestamp;
                    if (newMin.toDouble() > oldMin + 0.0005) {
                        if (lpDebug & 1) {
                            cout << COLOUR_light_red << "Min timestamp of corresponding start is now " << newMin << " rather than " << oldMin << COLOUR_default << endl;
                        }                            
                        
                        oldMin = newMin.toDouble();
                        lp->setColLower(timestampToUpdatePartnerVar,newMin.toDouble());
                    }
                }
            } else {
                EpsilonResolutionTimestamp newMin(timestampToUpdate->lpMinTimestamp, true);
                newMin += EpsilonResolutionTimestamp(timestampToUpdate->minDuration, true);
                double & oldMin = timestampToUpdatePartner->lpMinTimestamp;
                if (newMin.toDouble() > oldMin + 0.0005) {
                    if (lpDebug & 1) {
                        cout << COLOUR_light_red << "Min timestamp of corresponding end is now " << newMin << " rather than " << oldMin << COLOUR_default << endl;
                    }                            
                    
                    oldMin = newMin.toDouble();
                    lp->setColLower(timestampToUpdatePartnerVar, newMin.toDouble());
                }
            }
        }
        
        {
            map<int,pair<int,double> >::const_iterator dsItr = newDummySteps.begin();
            const map<int,pair<int,double> >::const_iterator dsEnd = newDummySteps.end();
            
            for (; dsItr != dsEnd; ++dsItr) {
                const EpsilonResolutionTimestamp rounded(dsItr->second.second,true);
                planAsAVector[dsItr->first]->lpMinTimestamp = rounded.toDouble();
                lp->setColLower(dsItr->second.first, planAsAVector[dsItr->first]->lpMinTimestamp);
                
                if (lpDebug & 1) {
                    cout << "DS: Set lower bound on " << lp->getColName(dsItr->second.first) << " to " << planAsAVector[dsItr->first]->lpMinTimestamp << ", is now " << lp->getColLower(dsItr->second.first) << endl;
                }
            }
        }

        for (int pass = 0; pass < 2; ++pass) {
            
            const map<int,double> & loopOver = (pass ? rpLowerBounds : csEndLowerBound);
            map<int,double>::const_iterator rplItr = loopOver.begin();
            const map<int,double>::const_iterator rplEnd = loopOver.end();
             
            for (; rplItr != rplEnd; ++rplItr) {
 
                const EpsilonResolutionTimestamp rounded(rplItr->second,true);
                planAsAVector[rplItr->first]->lpMinTimestamp = rounded.toDouble();
                lp->setColLower(rplItr->first + numVars, planAsAVector[rplItr->first]->lpMinTimestamp);
                if (lpDebug & 1) {
                    cout << "(csrp:" << pass << ") Set lower bound on " << lp->getColName(rplItr->first + numVars) << " to " << planAsAVector[rplItr->first]->lpMinTimestamp << endl;
                }
                
                if (planAsAVector[rplItr->first]->action) {
                    const int actID = planAsAVector[rplItr->first]->action->getID();
                    if (!RPGBuilder::getRPGDEs(actID).empty()) {
                        // is a temporal action
                        
                        if (planAsAVector[rplItr->first]->time_spec == Planner::E_AT_END) {
                            EpsilonResolutionTimestamp newMin(planAsAVector[rplItr->first]->lpMinTimestamp, true);
                            EpsilonResolutionTimestamp maxDur(planAsAVector[rplItr->first]->maxDuration, true);
                            if (maxDur < newMin) {
                                newMin -= maxDur;
                                double & oldMin = planAsAVector[rplItr->first - 1]->lpMinTimestamp;
                                if (newMin.toDouble() > oldMin + 0.0005) {
                                    if (lpDebug & 1) {
                                        cout << COLOUR_light_red << "Min timestamp of corresponding start is now " << newMin << " rather than " << oldMin << COLOUR_default << endl;
                                    }                            
                                    
                                    oldMin = newMin.toDouble();
                                    lp->setColLower(rplItr->first - 1 + numVars, newMin.toDouble());
                                }
                            }
                        } else {
                            EpsilonResolutionTimestamp newMin(planAsAVector[rplItr->first]->lpMinTimestamp, true);
                            newMin += EpsilonResolutionTimestamp(planAsAVector[rplItr->first]->minDuration, true);
                            double & oldMin = planAsAVector[rplItr->first + 1]->lpMinTimestamp;
                            if (newMin.toDouble() > oldMin + 0.0005) {
                                if (lpDebug & 1) {
                                    cout << COLOUR_light_red << "Min timestamp of corresponding end is now " << newMin << " rather than " << oldMin << COLOUR_default << endl;
                                }                            
                                
                                oldMin = newMin.toDouble();
                                lp->setColLower(rplItr->first + 1 + numVars, newMin.toDouble());
                            }
                        }
                    }
                    
                }
                
            }
            
        }
    }            
}

bool LPScheduler::addRelaxedPlan(const list<StartEvent> & seq, vector<AutomatonPosition::Position> & preferenceStatus, double & preconditionPrefViolations, list<FFEvent> & header, list<FFEvent> & now, const list<pair<double, list<ActionSegment> > > & relaxedPlan, const int & justAppliedStep)
{

    static const bool localDebug = (lpDebug & 1);
    
    if (!lp) {
        if (localDebug) {
            cout << "addRelaxedPlan(): No LP, so doing nothing with the refined bounds on action ends\n";
        }
        return true;
    }

    if (timestampToUpdateVar == -1) {
        if (localDebug) {
            cout << "addRelaxedPlan(): No timestamp to update var, so doing nothing with the refined bounds on action ends\n";
        }
        return true;
    }
    
    static const bool optimised = true;
    
    
    bool recalculate = false;
    map<int,double> rpLowerBounds;
    
    if (RPGBuilder::modifiedRPG) {
        
        if (!seq.empty()) {
                        
            if (localDebug) {
                cout << "addRelaxedPlan(): Collating open ends and comparing to relaxed plan\n";
            }
            
            
            map<int,double> actEndsAt;
            list<pair<double, list<ActionSegment> > >::const_iterator rpItr = relaxedPlan.begin();
            const list<pair<double, list<ActionSegment> > >::const_iterator rpEnd = relaxedPlan.end();

            for (; rpItr != rpEnd; ++rpItr) {
                
                list<ActionSegment>::const_iterator asItr = rpItr->second.begin();
                const list<ActionSegment>::const_iterator asEnd = rpItr->second.end();

                for (; asItr != asEnd; ++asItr) {
                    if (asItr->second == Planner::E_AT_END) {
                        actEndsAt.insert(make_pair(asItr->first->getID(), rpItr->first));
                    }
                }
                
            }
            
            list<StartEvent>::const_iterator seqItr = seq.begin();
            const list<StartEvent>::const_iterator seqEnd = seq.end();
            
            for (; seqItr != seqEnd; ++seqItr) {
                if (TemporalAnalysis::canSkipToEnd(seqItr->actID)) {
                    continue;
                }
                map<int,double>::const_iterator endTime = actEndsAt.find(seqItr->actID);
                assert(endTime != actEndsAt.end());
                const int actEndVar = numVars + seqItr->stepID + 1;
                
                const EpsilonResolutionTimestamp rounded(endTime->second,true);
                
                if (lp->getColLower(actEndVar) < rounded.toDouble()) {
                    if (localDebug) {
                        cout << "\tExisting bound of " << lp->getColLower(actEndVar) << " on " << *(RPGBuilder::getInstantiatedOp(seqItr->actID)) << " is increased by the RP bound of " << endTime->second << endl;
                    }
                    lp->setColLower(actEndVar, rounded.toDouble());
                    rpLowerBounds.insert(make_pair(seqItr->stepID + 1, rounded.toDouble()));
                    recalculate = true;
                } else {
                    if (localDebug) {
                        cout << "\tExisting bound of " << lp->getColLower(actEndVar) << " on " << *(RPGBuilder::getInstantiatedOp(seqItr->actID)) << " is no worse than the RP bound of " << endTime->second << endl;
                    }
                }
            }
        } else {
            if (localDebug) {
                cout << "addRelaxedPlan(): Returning - no actions currently executing in the state\n";
            }
            
        }
        
    } else {

        if (localDebug) {
            cout << "addRelaxedPlan(): Branch for the non-POPF TRPG\n";
        }
        
        map<int, list<EndDetails> > compulsaryEnds(openDurationConstraints);

        bool recalculate = false;

        {
            list<pair<double, list<ActionSegment> > >::const_iterator rpItr = relaxedPlan.begin();
            const list<pair<double, list<ActionSegment> > >::const_iterator rpEnd = relaxedPlan.end();

            for (; rpItr != rpEnd; ++rpItr) {
                double offset = 0.0;
                bool changeFlag = false;
                if (rpItr->first > EPSILON) {
                    changeFlag = true;
                    offset = rpItr->first - EPSILON;
                }

                list<ActionSegment>::const_iterator asItr = rpItr->second.begin();
                const list<ActionSegment>::const_iterator asEnd = rpItr->second.end();

                for (; asItr != asEnd; ++asItr) {
                    if (asItr->second != Planner::E_AT_START) {
                        const int actID = asItr->first->getID();
                        const int divMatch = (asItr->second == Planner::E_OVER_ALL ? asItr->divisionID : gradientEffects[actID].size() - 1);

                        map<int, list<EndDetails> >::iterator ceItr = compulsaryEnds.find(actID);

                        RPGBuilder::RPGDuration* currDuration = RPGBuilder::getRPGDEs(actID)[divMatch];

                        if (currDuration->min.empty()) {

                            map<int, list<EndDetails> >::iterator ceItr = compulsaryEnds.find(actID);
                            if (ceItr != compulsaryEnds.end()) {

                                list<EndDetails>::iterator matchItr = ceItr->second.begin();
                                const list<EndDetails>::iterator matchEnd = ceItr->second.end();

                                for (; matchItr != matchEnd; ++matchItr) {
                                    if (matchItr->first->divisionsApplied == divMatch) {

                                        int * secItr = &(matchItr->lastToMin);

                                        double tmp = lp->getRowLower(*secItr);

                                        if (lpDebug & 1) cout << "Changed RHS of timestamp for " << *(asItr->first) << " from " << tmp << " to " << tmp + offset << "\n";

                                        tmp += offset;
                                        lp->setRowLower(*secItr, tmp);

                                        recalculate = (recalculate || changeFlag);



                                        ceItr->second.erase(matchItr);
                                        if (ceItr->second.empty()) {
                                            compulsaryEnds.erase(ceItr);
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
    }
    
    if (recalculate && timestampToUpdateVar != -1) {
        if (lpDebug & 1) cout << "Recalculating timestamps following relaxed plan\n";


        if (previousObjectiveVar != -1) lp->setObjCoeff(previousObjectiveVar, 0.0);

        lp->setObjCoeff(timestampToUpdateVar, 1.0);

        previousObjectiveVar = timestampToUpdateVar;

        const bool success = lp->solve(false);


        if (success) {

            sortOutTheSolution(false, justAppliedStep, preferenceStatus, preconditionPrefViolations, rpLowerBounds);
            
        }

    } else {
        if (lpDebug & 1) cout << "No need to recalculate timestamps following relaxed plan\n";
    }

    return solved;

}


ParentData * LPScheduler::prime(list<FFEvent> & header, const TemporalConstraints * const cons, list<StartEvent> & open, const bool & includeMetric)
{

    if (!hybridBFLP) return 0;
    const bool primeDebug = (Globals::globalVerbosity & 4096);

    const int qSize = header.size() + 5;

    ParentData * const toReturn = new ParentData(qSize, &header, 0);

    bool needLP = false;

    list<FFEvent>::iterator hItr = header.begin();
    const list<FFEvent>::iterator hEnd = header.end();

    map<int, pair<double, double> > rememberDurs;

    int i = 0;

    for (; hItr != hEnd; ++hItr, ++i) {
        double m = hItr->lpMinTimestamp;
        if (m != 0.0) m = -m;
        toReturn->setRawDistToFromZero(i, m, hItr->lpMaxTimestamp);

        if (hItr->isDummyStep()) {
            toReturn->setNonTemporal(i);
            if (hItr->getEffects) {
                toReturn->nonSoftEdges(i,remapPreferenceEdge(*hItr,i,cons));
            }
        } else {
            toReturn->nonSoftEdges(i,i);
            if (hItr->action) {
                if (RPGBuilder::getRPGDEs(hItr->action->getID()).empty()) {
                    toReturn->setNonTemporal(i);
                } else {
                    if (hItr->pairWithStep == -1) {
                        rememberDurs[i] = make_pair(hItr->minDuration, hItr->maxDuration);
                    } else {
                        toReturn->setPairWith(i, hItr->pairWithStep);
                    }
                }
            } else {
                assert(hItr->time_spec == Planner::E_AT);
                toReturn->setTIL(i);
            }
            instantiatedOp * const act = hItr->action;
            if (act) {
                if (hItr->time_spec == Planner::E_AT_START) {
                    needLP = needLP || (!isBoring(act->getID(), 0, includeMetric));
                } else {
                    needLP = needLP || (!isBoring(act->getID(), 1, includeMetric));
                }
            }
        }
    }

    toReturn->setWhetherNeedsLP(needLP);


//    const double minAtLeast = (i > 0 ? toReturn->getDistToZero()[i] - 0.001 : 0.0);


    if (primeDebug) {
        cout << "Parent nodes 0 to " << i - 1 << ": events [";
        
        for (int p = 0; p < i; ++p) {
            if (p) cout << ",";
            cout << -toReturn->getDistToZero()[p];
        }
        cout << "]\n";
        cout << "Parent node " << i << ": gaps for new actions\n";
    }

    // leave a gap in case a start event (or TIL) needs to go in later
    toReturn->startGapIsStep(i);
    ++i;

    // leave a gap in case an end event needs to go in later
    toReturn->endGapIsStep(i);
    ++i;
    
    // leave a gap for preferences met after the start of an action
    toReturn->postStartGapIsStep(i);
    ++i;
    
    // leave a gap for preferences met after the end of an action
    toReturn->postEndGapIsStep(i);
    
    {
        list<FFEvent>::iterator hItr = header.begin();
        const list<FFEvent>::iterator hEnd = header.end();

        for (i = 0; hItr != hEnd; ++hItr, ++i) {
  
            const int hardEdgesForVertex = toReturn->edgesAreNonSoft(i);
            
            if (hItr->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                if (hItr->pairWithStep >= 0) {
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[hItr->divisionID];
                    if (pref.cons == VAL::E_ALWAYSWITHIN) {                    
                        if (hardEdgesForVertex == -1) {
                            toReturn->makeSoftEdgeListFor(i).addPredecessor(hItr->pairWithStep, false, -pref.deadline);
                            toReturn->makeSoftEdgeListFor(hItr->pairWithStep).addFollower(i, false, -pref.deadline);
                        } else {
                            toReturn->makeEdgeListFor(hardEdgesForVertex).addPredecessor(hItr->pairWithStep, false, -pref.deadline);
                            toReturn->makeEdgeListFor(hItr->pairWithStep).addFollower(hardEdgesForVertex, false, -pref.deadline);
                        }                                     
                    }
                }
            } else if (hItr->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE) {
                const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[hItr->divisionID];
                if (pref.cons == VAL::E_WITHIN) {                    
                    if (hardEdgesForVertex == -1) {
                        toReturn->makeSoftEdgeListFor(-1).addPredecessor(i, false, -pref.deadline);
                        toReturn->makeSoftEdgeListFor(i).addFollower(-1, false, -pref.deadline);
                    }                                     
                }
            }
                        
            const map<int, bool> * stepCons = cons->stepsBefore(i);
            if (!stepCons) {
                continue;
            }
                        
            int localEdgesForVertex = hardEdgesForVertex;
            
            IncomingAndOutgoing * forThisStep;
            IncomingAndOutgoing * forThisStepSoft;
            
            if (hardEdgesForVertex == -1) {
                localEdgesForVertex = i;
                forThisStep = &(toReturn->makeSoftEdgeListFor(localEdgesForVertex));
                forThisStepSoft = forThisStep;
            } else {
                forThisStep = &(toReturn->makeEdgeListFor(hardEdgesForVertex));
                forThisStepSoft = 0;
            }
            
            //toReturn->makeEdgeListFor(i).initialisePredecessors(*stepCons);

            int exclude = -1;

            if (hItr->time_spec == Planner::E_AT_END) {
                exclude = hItr->pairWithStep;
            }

            map<int, bool>::const_iterator ntfItr = stepCons->begin();
            const map<int, bool>::const_iterator ntfEnd = stepCons->end();

            int earlier;
            for (; ntfItr != ntfEnd; ++ntfItr) {
                if (ntfItr->first == exclude) continue;
                if (ntfItr->first == localEdgesForVertex) continue;
                if ((earlier = toReturn->edgesAreNonSoft(ntfItr->first)) != -1) {
                    if (hardEdgesForVertex == -1) {
                        if (primeDebug) cout << "\t\tStep " << localEdgesForVertex << " soft-needs to start after step " << earlier << "\n";
                        toReturn->makeSoftEdgeListFor(earlier).addFollower(localEdgesForVertex, ntfItr->second, (ntfItr->second ? EPSILON : 0.0));                        
                    } else {
                        if (primeDebug) cout << "\t\tStep " << hardEdgesForVertex << " needs to start after step " << earlier << "\n";
                        toReturn->makeEdgeListFor(earlier).addFollower(hardEdgesForVertex, ntfItr->second, (ntfItr->second ? EPSILON : 0.0));                        
                    }
                    forThisStep->addPredecessor(earlier, ntfItr->second, (ntfItr->second ? EPSILON : 0.0));
                } else {
                    if (!forThisStepSoft) {
                        forThisStepSoft = &(toReturn->makeSoftEdgeListFor(hardEdgesForVertex));
                    }
                    if (primeDebug) cout << "\t\tStep " << localEdgesForVertex << " soft-needs to start after step " << ntfItr->first << "\n";
                                                                    
                    toReturn->makeSoftEdgeListFor(ntfItr->first).addFollower(localEdgesForVertex, ntfItr->second, (ntfItr->second ? EPSILON : 0.0));                        
                    forThisStepSoft->addPredecessor(ntfItr->first, ntfItr->second, (ntfItr->second ? EPSILON : 0.0));
                    
                }
            }
        }
    }

    const int mostRecentStep = MinimalState::getTransformer()->stepThatMustPrecedeUnfinishedActions(cons);

    list<StartEvent>::iterator seqItr = open.begin();
    const list<StartEvent>::iterator seqEnd = open.end();

    for (; seqItr != seqEnd; ++seqItr) {
        if (seqItr->ignore) {
            continue;
        }
        const int startWasAt = seqItr->stepID;
        i = toReturn->getPairWith()[startWasAt];

        IncomingAndOutgoing & myEdgeList = toReturn->makeEdgeListFor(i);

        if (mostRecentStep != -1) {
            if (mostRecentStep != startWasAt) {
                if (primeDebug) {
                    cout << "TO: Insisting that an unfinished action at " << i << " must follow " << mostRecentStep << ", the most recent step\n";
                }
                myEdgeList.addPredecessor(mostRecentStep, true, EPSILON);
                toReturn->makeEdgeListFor(mostRecentStep).addFollower(i, true, EPSILON);
            }
        }

        if (!ignoreABedges) {

            {
                set<int>::iterator ecaItr = seqItr->getEndComesAfter().begin();
                const set<int>::iterator ecaEnd = seqItr->getEndComesAfter().end();

                for (; ecaItr != ecaEnd; ++ecaItr) {
                    const int af = *ecaItr;

                    if (af >= 0) {
                        if (primeDebug) cout << "\t\tEnd of " << seqItr->stepID << " comes after end of " << af << ", therefore...\n";
                        const int afw = toReturn->getPairWith()[af];
                        myEdgeList.addPredecessor(afw, true, EPSILON);
                        toReturn->makeEdgeListFor(afw).addFollower(i, true, EPSILON);
                        if (primeDebug) cout << "\t\t" << afw << " before " << i << "\n";
                    }
                }
            }

            {
                set<int>::iterator ecbItr = seqItr->getEndComesBefore().begin();
                const set<int>::iterator ecbEnd = seqItr->getEndComesBefore().end();

                for (; ecbItr != ecbEnd; ++ecbItr) {
                    const int af = *ecbItr;

                    if (af >= 0) {
                        if (primeDebug) cout << "\t\tEnd of " << seqItr->stepID << " comes before end of " << af << ", therefore...\n";
                        const int afw = toReturn->getPairWith()[af];
                        myEdgeList.addFollower(afw, true, EPSILON);
                        toReturn->makeEdgeListFor(afw).addPredecessor(i, true, EPSILON);
                        if (primeDebug) cout << "\t\t" << i << " before " << afw << "\n";

                    }
                }
            }

        }

    }

    if (checkSanity) toReturn->sanityCheck();

    if (Globals::paranoidScheduling) {
        // should, here, be consistent
        const bool noisy = Globals::globalVerbosity & 4096;
        
        const int mSize = header.size() + 1;

        vector<FFEvent*> eventsWithFakes(mSize - 1, (FFEvent*)0);
        
        vector<vector<double> > matrix(mSize, vector<double>(mSize, DBL_MAX));

        for (int m = 0; m < mSize; ++m) {
            matrix[m][m] = 0.0;
        }


        list<FFEvent>::iterator hItr = header.begin();
        const list<FFEvent>::iterator hEnd = header.end();
        
        for (int m = 1; hItr != hEnd; ++hItr, ++m) {
            matrix[m][0] = 0.0;
            eventsWithFakes[m-1] = &(*hItr);
            if (hItr->isDummyStep()) {
                matrix[m][0] = 0.0;
                matrix[0][m] = DBL_MAX;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << 0.0 << ", as it's a dummy pref step\n";
                
            } else if (hItr->time_spec == Planner::E_AT_START) {
                const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[hItr->action->getID()];
                const double startMin = tsBounds[0].first;
                const double startMax = tsBounds[0].second;

                matrix[m][0] = -1 * startMin;
                matrix[0][m] = startMax;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -startMin << " due to earliest RPG start point of action\n";
            } else if (hItr->time_spec == Planner::E_AT_END) {
                const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[hItr->action->getID()];
                const double endMin = tsBounds[1].first;
                const double endMax = tsBounds[1].second;

                matrix[m][0] = -1 * endMin;
                matrix[0][m] = endMax;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -endMin << " due to earliest RPG end point of action\n";

            }
        }

        for (int m = 1; m < mSize; ++m) {
            if (!eventsWithFakes[m-1]) continue;

            if (!eventsWithFakes[m-1]->isDummyStep()) {
                const int & thisPair = eventsWithFakes[m-1]->pairWithStep;
                if (thisPair >= 0) {
                    if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_START) {
                        matrix[m][thisPair + 1] = eventsWithFakes[m-1]->maxDuration;
                        if (noisy) cout << "Edge from " << m - 1 << " to " << thisPair << " - " << eventsWithFakes[m-1]->maxDuration << " due to max duration" << endl;
                    } else {
                        matrix[m][thisPair + 1] = -1 * eventsWithFakes[m-1]->minDuration;
                        if (noisy) cout << "Edge from " << m - 1 << " to " << thisPair << " - " << -eventsWithFakes[m-1]->minDuration << " due to min duration" << endl;
                    }
                } else if (thisPair == -2) {
                    const double tilTime = LPScheduler::getTILTimestamp(eventsWithFakes[m-1]->divisionID);
                    matrix[0][m] = tilTime;
                    matrix[m][0] = -1 * tilTime;
                }
            }

            if (eventsWithFakes[m-1]->lpMinTimestamp != -1.0) {
                const double backEdge = (eventsWithFakes[m-1]->lpMinTimestamp == 0.0 ? 0.0 : -(eventsWithFakes[m-1]->lpMinTimestamp));
                if (backEdge < matrix[m][0]) {
                    matrix[m][0] = backEdge;
                    if (noisy) cout << "Changing edge from " << m - 1 << " to time zero - " << backEdge << " due to known minimum timestamp for action\n";
                } else {
                    if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
                }
            } else {
                if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
            }
            
            if (eventsWithFakes[m-1]->lpMaxTimestamp != -1.0) {
                if (eventsWithFakes[m-1]->lpMaxTimestamp < matrix[0][m]) {
                    matrix[0][m] = eventsWithFakes[m-1]->lpMaxTimestamp;
                    if (noisy) cout << "Changing edge from time zero to " << m - 1 << " to " << matrix[0][m] << " due to known maximum timestamp for action\n";
                } else {
                    if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
                }
            } else {
                if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
            }

            map<int, IncomingAndOutgoing>::const_iterator eItr = toReturn->getTemporaryEdges().find(m - 1);
            if (eItr != toReturn->getTemporaryEdges().end()) {
                map<int, pair<bool,double> >::const_iterator pItr = eItr->second.mustPrecedeThis().begin();
                const map<int, pair<bool,double> >::const_iterator pEnd = eItr->second.mustPrecedeThis().end();

                for (; pItr != pEnd; ++pItr) {
                    if (pItr->second.second == 0.0) {
                        matrix[m][pItr->first + 1] = 0.0;
                    } else {
                        matrix[m][pItr->first + 1] = -pItr->second.second;
                    }
                    if (noisy) cout << "Edge from " << m - 1 << " to " << pItr->first << " - " << -pItr->second.second << " due to recorded predecessors" << endl;
                }
            }
        }


        int k, i, j;
        double distIK, distKJ;

        for (k = 0; k < mSize; ++k) {
            for (i = 0; i < mSize; ++i) {
                distIK = matrix[i][k];
                if (distIK == DBL_MAX) continue;
                for (j = 0; j < mSize; ++j) {
                    distKJ = matrix[k][j];

                    if (distKJ != DBL_MAX) {
                        double & distIJ = matrix[i][j];
                        if ((distIK + distKJ) - distIJ < -0.00001) {
                            distIJ = distIK + distKJ;
                        }
                    }
                }
            }
        }

        for (int m = 0; m < mSize; ++m) {
            assert(fabs(matrix[m][m]) < 0.000000001);
        }

        if (noisy) {
            cout << "Floyd gives pre-child-generation timestamps of: [";
            for (int m = 1; m < mSize; ++m) {
                if (!eventsWithFakes[m-1]) continue;
                if (m >= 2) cout << ",";
                cout << -(matrix[m][0]);
            }
            cout << "]\n";
        }
    }

    
    return toReturn;
}

void mergeEdges(map<int,bool> & mergedEdges, const list<const map<int,bool> * > & extraPrecedenceSets, const int & exclude, const set<int> & ignoreEdgesBackTo) {

    list<const map<int,bool>* >::const_iterator psItr = extraPrecedenceSets.begin();
    const list<const map<int,bool>* >::const_iterator psEnd = extraPrecedenceSets.end();
    
    for (; psItr != psEnd; ++psItr) {
        map<int,bool>::iterator insItr = mergedEdges.end();
        
        map<int,bool>::const_iterator precItr = (*psItr)->begin();
        const map<int,bool>::const_iterator precEnd = (*psItr)->end();
        
        for (; precItr != precEnd; ++precItr) {
            if (precItr->first != exclude) {
                insItr = mergedEdges.insert(insItr, *precItr);
                insItr->second = (insItr->second || precItr->second);
            }
        }
    }
                        
    set<int>::const_iterator igItr = ignoreEdgesBackTo.begin();
    const set<int>::const_iterator igEnd = ignoreEdgesBackTo.end();
    
    for (; igItr != igEnd; ++igItr) {
        mergedEdges.erase(*igItr);
    }
}


ChildData * ParentData::spawnChildData(list<StartEvent> & seq,
                                       list<FFEvent> & header, list<FFEvent> & newActs,
                                       const bool & includeMetric,
                                       const TemporalConstraints * const cons, const int & stepID)
{

    const bool spawnDebug = (Globals::globalVerbosity & 4096);

    const int newActCount = newActs.size();
    if (spawnDebug) {
        cout << "Spawning child data for ";
        if (newActCount) {
            if (newActCount == 1) {
                cout << "1 new step\n";
            } else {
                cout << newActCount << " new steps\n";
            }
        } else {
            cout << "Spawning child data by ending the action at step " << stepID << endl;
        }
    }

    if (spawnDebug) {
        list<FFEvent>::iterator hItr = header.begin();
        const list<FFEvent>::iterator hEnd = header.end();

        list<FFEvent>::iterator ppItr = parentPlan->begin();
        const list<FFEvent>::iterator ppEnd = parentPlan->end();

        for (int i = 0; hItr != hEnd; ++hItr, ++i, ++ppItr) {
            assert(ppItr != ppEnd);
            if (hItr->isDummyStep()) {
                assert(ppItr->isDummyStep());
            } else {
                assert(hItr->action == ppItr->action);
                assert(hItr->time_spec == ppItr->time_spec);
                assert(hItr->time_spec != Planner::E_AT || hItr->divisionID == ppItr->divisionID);
                assert(hItr->time_spec != Planner::E_AT || pairWith[i] == -2);
            }
        }
    }

    const int mustComeBeforeOpenEnds = MinimalState::getTransformer()->stepThatMustPrecedeUnfinishedActions(cons);
        
        
    double TILupbo = MinimalState::getTransformer()->latestTimePointOfActionsStartedHere(nextTIL);

    ChildData * toReturn = 0;

    if (startGap > stepID) { // if we're only triggering an existing action within the plan

        if (spawnDebug) cout << "Is an end action\n";
        assert(RPGBuilder::getPreferences().empty() ? newActs.empty() : true);

        // in this case, the end was already assigned an event, so we need to nuke the old one

        list<FFEvent>::iterator findIt = header.begin();
        for (int i = 0; i < stepID; ++i, ++findIt) ;

        FFEvent & s = *findIt;

        toReturn = new ChildData(&Q, distFromZero, distToZero, pairWith, eventsWithFakes, softEdges, temporaryEdges, temporarySoftEdges, needsLP);

        toReturn->updateLPNeed(!LPScheduler::isBoring(s.action->getID(), 1, includeMetric));

        const int startLocation = s.pairWithStep;
        const int endLocation = stepID;

        const double endMax = toReturn->getDistFromZero()[endLocation];
        double endMin = toReturn->getDistToZero()[endLocation];
        if (endMin != 0.0) endMin = -endMin;

        s.lpMinTimestamp = endMin;
        s.lpMaxTimestamp = endMax;

        // fortunately, we left gaps in the event sequence
        vector<FFEvent*> & childEvents = toReturn->getEventsWithFakes();

        int i = 0;

        {
            list<FFEvent>::iterator hItr = header.begin();
            const list<FFEvent>::iterator hEnd = header.end();

            for (; hItr != hEnd; ++hItr, ++i) {
                childEvents[i] = &(*hItr);
            }
        }
        
        list<int> gapsUsed;
        list<const map<int,bool>* > extraPrecedenceSets;
        set<int> ignoreEdgesBackTo;
        
        if (!newActs.empty()) {
            
            list<int> spareGaps;
            spareGaps.push_back(startGap);
            spareGaps.push_back(endGap);
            spareGaps.push_back(postStartGap);
            spareGaps.push_back(postEndGap);
            
            const int naSize = newActs.size();
            
            if (naSize > 4) {
                toReturn->addMoreGaps(spareGaps, naSize - 4);
            }
            
            list<FFEvent>::iterator newStep = newActs.begin();
            const list<FFEvent>::iterator newEnd = newActs.end();
                        
            for (; newStep != newEnd; ++newStep) {
            
                const int dummyGap = spareGaps.front();
                spareGaps.pop_front();
                
                gapsUsed.push_back(dummyGap);
                
                childEvents[dummyGap] = &(*newStep);
                toReturn->setNonTemporal(dummyGap);
                
                if (newStep->getEffects) {
                    const int remapTo = remapPreferenceEdge(*newStep,dummyGap,cons);
                    toReturn->nonSoftEdges(dummyGap, remapTo);
                    
                    const map<int,bool> * const prec = cons->stepsBefore(dummyGap);
                    if (prec && remapTo != dummyGap && remapTo == endLocation) {
                        extraPrecedenceSets.push_back(prec);
                        ignoreEdgesBackTo.insert(dummyGap);
                    }
                }
                
                toReturn->makeEdgeListFor(dummyGap);
            }
        }


        assert(i == startGap);

        //toReturn->pairEventWith(startLocation, endLocation);

        IncomingAndOutgoing & edgesForTheEndAction = toReturn->makeEdgeListFor(endLocation);

        map<int, pair<bool,double> > nowAfter(edgesForTheEndAction.mustFollowThis());

        if (mustComeBeforeOpenEnds != -1) {
            assert(mustComeBeforeOpenEnds == endLocation);

            if (spawnDebug) {
                cout << "This step, " << endLocation<< ", must come before all open ends\n";
            }
            
            list<StartEvent>::iterator seqFillItr = seq.begin();
            const list<StartEvent>::iterator seqFillEnd = seq.end();

            for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                if (seqFillItr->stepID == startLocation) continue;
                const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                map<int, pair<bool,double> >::const_iterator oldEdge = edgesForTheEndAction.mustPrecedeThis().find(cbf);
                if (oldEdge != edgesForTheEndAction.mustPrecedeThis().end() && oldEdge->second.second > 0.0) {
                    if (spawnDebug) {
                        cout << "Previously required this action to end strictly after another that hasn't finished yet - STP inconsistent\n";
                    }
                    delete toReturn;
                    toReturn = 0;
                    return toReturn;
                }

                const pair<map<int, pair<bool,double> >::iterator, bool> insPair = nowAfter.insert(make_pair(cbf, make_pair(true, EPSILON)));
                bool tightened = false;
                if (insPair.second) {
                    tightened = true;
                } else {
                    if (   insPair.first->second.second == 0.0
                        || EPSILON > insPair.first->second.second) {
                        
                        insPair.first->second.first = true;
                        insPair.first->second.second = EPSILON;
                        tightened = true;
                    }
                }
                if (tightened) {
                    if (spawnDebug) cout << "Adding epsilon separation edge from " << endLocation << " to some future end event " << cbf << "\n";
                    toReturn->addNewEdge(BFEdge(endLocation, cbf, 0.001, DBL_MAX));
                }
            }
        }

        {// now see if any new edges are in cons that weren't present before

            const map<int, bool> * eventsBeforeEndAction = cons->stepsBefore(endLocation);

            map<int,bool> mergedEdges;
            
            if (!extraPrecedenceSets.empty()) {
                mergedEdges = *eventsBeforeEndAction;
                eventsBeforeEndAction = &mergedEdges;
                
                mergeEdges(mergedEdges, extraPrecedenceSets, endLocation, ignoreEdgesBackTo);
            }
            

            // first, things that used to come before this - any extras?
            if (eventsBeforeEndAction) {
                map<int, pair<bool,double> >::const_iterator oldCbf = edgesForTheEndAction.mustPrecedeThis().begin();
                const map<int, pair<bool,double> >::const_iterator oldCbfEnd = edgesForTheEndAction.mustPrecedeThis().end();

                map<int, bool>::const_iterator newCbf = eventsBeforeEndAction->begin();
                const map<int, bool>::const_iterator newCbfEnd = eventsBeforeEndAction->end();

                int earlier;
                
                while (oldCbf != oldCbfEnd && newCbf != newCbfEnd) {
                    if (newCbf->first < oldCbf->first) {
                        if (newCbf->first != startLocation) {
                            if ((earlier = toReturn->edgesAreNonSoft(newCbf->first)) != -1) {
                                if (spawnDebug) {
                                    if (newCbf->second) {
                                        cout << "New 'before' edge: adding epsilon separation edge from " << earlier << " to the end snap-action that has been applied\n";
                                    } else {
                                        cout << "New 'before' edge: adding zero separation edge from " << earlier << " to the end snap-action that has been applied\n";
                                    }
                                }
                                toReturn->addNewEdge(BFEdge(earlier, endLocation, (newCbf->second ? 0.001 : 0.0), DBL_MAX));
                            } else {
                                toReturn->makeSoftEdgeListFor(endLocation).addPredecessor(newCbf->first, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(newCbf->first).addFollower(endLocation, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                            }
                        }
                        ++newCbf;
                    } else {
                        assert(newCbf->first == oldCbf->first); // or else edges have disappeared....
                        //assert(!oldCbf->second || newCbf->second);
                        if (newCbf->first != startLocation) {
                            if ((earlier = toReturn->edgesAreNonSoft(newCbf->first)) != -1) {
                                const double newValue = (newCbf->second ? EPSILON : 0.0);
                                if (newValue > oldCbf->second.second) {
                                    if (spawnDebug) {
                                        cout << "Changed cost from " << -oldCbf->second.second << " to -epsilon on the separation edge from " << earlier << " to the end snap-action that has been applied\n";
                                    }
                                    toReturn->addNewEdge(BFEdge(earlier, endLocation, 0.001, DBL_MAX));
                                }
                            } else {
                                toReturn->makeSoftEdgeListFor(endLocation).addPredecessor(newCbf->first, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(newCbf->first).addFollower(endLocation, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                            }
                        }
                        ++oldCbf;
                        ++newCbf;
                    }
                }

                for (; newCbf != newCbfEnd; ++newCbf) {
                    if (newCbf->first != startLocation) {
                        if ((earlier = toReturn->edgesAreNonSoft(newCbf->first)) != -1) {
                            if (spawnDebug) {
                                if (newCbf->second) {
                                    cout << "New 'before' edge: adding epsilon separation edge from " << newCbf->first << " to the end snap-action that has been applied\n";
                                } else {
                                    cout << "New 'before' edge: adding zero separation edge from " << newCbf->first << " to the end snap-action that has been applied\n";
                                }
                            }
                            toReturn->addNewEdge(BFEdge(earlier, endLocation, (newCbf->second ? 0.001 : 0.0), DBL_MAX));
                        } else {
                            toReturn->makeSoftEdgeListFor(endLocation).addPredecessor(newCbf->first, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(newCbf->first).addFollower(endLocation, newCbf->second, (newCbf->second ? 0.001 : 0.0));
                        }
                    }
                }
            }


            // then, things this has to come before - necessarily must be ends of actions yet to have been applied
            // but, better check...

            if (Globals::paranoidScheduling) {
                const int consSize = cons->size();
                for (int cs = 0; cs < consSize; ++cs) {
                    if (!cons->stepsBefore(cs)) continue;
                    if (!toReturn->getEventsWithFakes()[cs]) {
                        cout << "Warning: event at step " << cs << " is null\n";
                        continue;
                    }
                    if (!toReturn->getEventsWithFakes()[cs]->getEffects) continue;

                    assert(cons->stepsBefore(cs)->find(endLocation) == cons->stepsBefore(cs)->end());
                }
            }

            {
                list<StartEvent>::iterator seqFillItr = seq.begin();
                const list<StartEvent>::iterator seqFillEnd = seq.end();

                for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                    const int cbf = toReturn->getPairWith()[seqFillItr->stepID];

                    const map<int, bool> * const eventsBeforeFutureAction = cons->stepsBefore(cbf);
                    if (!eventsBeforeFutureAction) {
                        continue;
                    }

                    map<int, bool>::const_iterator toThisItr = eventsBeforeFutureAction->find(endLocation);

                    if (toThisItr != eventsBeforeFutureAction->end()) {
                        const double localValue = (toThisItr->second ? EPSILON : 0.0);
                        const pair<map<int, pair<bool,double> >::iterator, bool> insPair = nowAfter.insert(make_pair(cbf, make_pair(toThisItr->second, localValue)));

                        bool tightened = false;
                        if (insPair.second) {
                            tightened = true;
                        } else {
                            if (localValue > insPair.first->second.second) {
                                if (toThisItr->second) {
                                    insPair.first->second.first = true;
                                    insPair.first->second.second = EPSILON;
                                } else {
                                    insPair.first->second.first = false;
                                    insPair.first->second.second = 0.0;
                                }
                                tightened = true;
                            }
                        }
                        
                        if (tightened) {
                            if (spawnDebug) {
                                if (toThisItr->second) {
                                    cout << "Adding epsilon separation edge to the end snap-action " << cbf << " that has yet to be applied\n";
                                } else {
                                    cout << "Adding zero separation edge to the end snap-action " << cbf << " that has yet to be applied\n";
                                }
                            }
                            toReturn->addNewEdge(BFEdge(endLocation, cbf, localValue, DBL_MAX));
                        }
                    }

                }

            }

        }

        if (!newActs.empty()) {
            
            list<int>::const_iterator gapItr = gapsUsed.begin();
            
            list<FFEvent>::iterator newStep = newActs.begin();
            const list<FFEvent>::iterator newEnd = newActs.end();
                        
            for (; newStep != newEnd; ++newStep, ++gapItr) {
            
                const int dummyGap = *gapItr;
                
                const int applyEdgesTo = toReturn->edgesAreNonSoft(*gapItr);
                
                double localMin = 0.0;
                double localMax = DBL_MAX;

                if (applyEdgesTo == *gapItr) {
                    const map<int, bool> * const preceding = cons->stepsBefore(dummyGap);
                    
                    if (preceding) {
                        int earlier;
                        map<int, bool>::const_iterator pItr = preceding->begin();
                        const map<int, bool>::const_iterator pEnd = preceding->end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) == -1) {
                                continue;
                            }
                            const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                            if (localMin < w) localMin = w;
                        }
                    }
                }
                
                if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                    if (newStep->pairWithStep >= 0) {
                        const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                        if (pref.cons == VAL::E_ALWAYSWITHIN) {                    
                            if (applyEdgesTo == -1) {
                                toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(newStep->pairWithStep, false, -pref.deadline);
                                toReturn->makeSoftEdgeListFor(newStep->pairWithStep).addFollower(dummyGap, false, -pref.deadline);
                            } else {
                                assert(applyEdgesTo != dummyGap);
                                assert(newStep->getEffects);
                                toReturn->addNewEdge(BFEdge(applyEdgesTo, newStep->pairWithStep, 0.001, pref.deadline));
                            }                                     
                        }
                    }
                } else if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE) {
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                    if (pref.cons == VAL::E_WITHIN) {
                        if (newStep->getEffects) {
                            assert(applyEdgesTo == dummyGap);                        
                            localMax = pref.deadline;
                        } else {
                            assert(applyEdgesTo == -1);
                            toReturn->makeSoftEdgeListFor(-1).addPredecessor(dummyGap, false, -pref.deadline);
                            toReturn->makeSoftEdgeListFor(dummyGap).addFollower(-1, false, -pref.deadline);
                        }
                    }
                }
                
                if (localMin > localMax) {
                    delete toReturn;
                    return 0;
                }
                
                toReturn->autoMinima[dummyGap] = localMin;
                
                if (localMax < DBL_MAX) {
                    toReturn->setDFZ(dummyGap, localMax);
                }
                    
                if (localMin > 0.0) {
                    toReturn->setDTZ(dummyGap, -localMin);
                }
                    
                if (Globals::paranoidScheduling || Globals::profileScheduling) {
                    childEvents[dummyGap]->lpMinTimestamp = 0.0;
                    childEvents[dummyGap]->lpMaxTimestamp = DBL_MAX;
                } else {
                    childEvents[dummyGap]->lpMinTimestamp = localMin;
                    childEvents[dummyGap]->lpMaxTimestamp = localMax;
                }

                if (applyEdgesTo == dummyGap) {
                    const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);

                    if (beforeDummyStep) {
                        
                        map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                        const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();

                        int earlier;
                        
                        for (; ecaItr != ecaEnd; ++ecaItr) {
                            const int afR = ecaItr->first;

                            if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                                if (spawnDebug) {
                                    if (ecaItr->second) {
                                        cout << "Due to recorded constraints: adding edge to denote that the first preference checking step comes at least epsilon after step " << earlier << endl;                                
                                    } else {
                                        cout << "Due to recorded constraints: adding edge to denote that the first preference checking step comes after (or alongside) step " << earlier << endl;
                                    }
                                }

                                toReturn->addNewEdge(BFEdge(earlier, dummyGap, (ecaItr->second ? 0.001 : 0.0), DBL_MAX));
                            } else {
                                
                                toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            } 
                        
                        }
                        
                    } else {
                        if (spawnDebug) {
                            cout << "No steps must come before the end just added\n";
                        }
                    }
                } else if (applyEdgesTo == -1) {
                    const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);
                    
                    if (beforeDummyStep) {
                        
                        map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                        const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();
                        
                        for (; ecaItr != ecaEnd; ++ecaItr) {
                            const int afR = ecaItr->first;
                            toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        }
                    }
                }
                
                {
                    
                    list<StartEvent>::iterator seqFillItr = seq.begin();
                    const list<StartEvent>::iterator seqFillEnd = seq.end();
                    
                    for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                        const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                        const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                        if (!beforeFutureStep) continue;
                        
                        map<int, bool>::const_iterator toThisItr = beforeFutureStep->find(dummyGap);
                        if (toThisItr != beforeFutureStep->end()) {
                            if (applyEdgesTo != -1) {
                                if (spawnDebug) {
                                    if (toThisItr->second) {
                                        cout << "Constraint to future step: adding epsilon separation edge from " << applyEdgesTo << " to some future end event " << cbf << "\n";
                                    } else {
                                        cout << "Constraint to future step: adding zero separation edge from " << applyEdgesTo << " to some future end event " << cbf << "\n";
                                    }
                                }
                            
                                toReturn->addNewEdge(BFEdge(applyEdgesTo, cbf, (toThisItr->second ? 0.001 : 0.0), DBL_MAX));
                            } else {
                                toReturn->makeSoftEdgeListFor(cbf).addPredecessor(dummyGap, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(dummyGap).addFollower(cbf, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                            }
                                
                        }
                        
                    }
                } 
            
            }
            
        }

        return toReturn;

    }

    assert(newActCount);

    FFEvent & s = newActs.front();

    assert(newActs.front().time_spec == Planner::E_AT_START || newActs.front().time_spec == Planner::E_AT);

    if (s.time_spec == Planner::E_AT_START) {
        const bool nonTemporal = RPGBuilder::getRPGDEs(s.action->getID()).empty();

        if (spawnDebug) {
            if (!nonTemporal) {
                cout << "Is a start action - start goes at " << startGap << ", end goes at " << endGap << "\n";
                cout << "Duration in the range [" << s.minDuration << "," << s.maxDuration << "]";

                if (LPScheduler::isBoring(s.action->getID(), 0, includeMetric)) {
                    cout << ", and start is numerically boring\n";
                } else {
                    cout << ", and start is numerically interesting\n";
                }

            } else {
                if (spawnDebug) cout << "Is an instantaneous action, goes at " << startGap << "\n";
                if (LPScheduler::isBoring(s.action->getID(), 0, includeMetric)) {
                    cout << ", and is numerically boring\n";
                } else {
                    cout << ", and is numerically interesting\n";
                }
            }
        }

        toReturn = new ChildData(&Q, distFromZero, distToZero, pairWith, eventsWithFakes, softEdges, temporaryEdges, temporarySoftEdges, needsLP);

        toReturn->updateLPNeed(!LPScheduler::isBoring(s.action->getID(), 0, includeMetric));

        if (spawnDebug) {
            if (toReturn->doLPSolve()) {
                cout << "We need to solve an LP if the STP is solvable\n";
            } else {
                cout << "We don't need the LP so far\n";
            }
        }

        const int endLocation = endGap;
        const int startLocation = startGap;
        // fortunately, we left gaps in the event sequence
        vector<FFEvent*> & childEvents = toReturn->getEventsWithFakes();


        {
            int i = 0;

            list<FFEvent>::iterator hItr = header.begin();
            const list<FFEvent>::iterator hEnd = header.end();

            for (; hItr != hEnd; ++hItr, ++i) {
                childEvents[i] = &(*hItr);
            }
        }

        list<FFEvent>::iterator newStep = newActs.begin();
        ++newStep;
        
        childEvents[startLocation] = &s;
        
        toReturn->nonSoftEdges(startLocation, startLocation);
        
        list<int> spareGaps;
        spareGaps.push_back(endGap);
        spareGaps.push_back(postStartGap);
        spareGaps.push_back(postEndGap);
                    
        if (!nonTemporal) {

            assert(newStep != newActs.end());
            assert(newStep->time_spec == Planner::E_AT_END);

            FFEvent & s2 = *newStep;
            childEvents[endLocation] = &s2;

            toReturn->nonSoftEdges(endLocation, endLocation);
            
            toReturn->pairEventWith(startLocation, endLocation);

            ++newStep;
            spareGaps.pop_front();
        } else {
            toReturn->setNonTemporal(startGap);
        }

        list<int> gapsUsed;
        list<const map<int,bool>* > extraStartPrecedenceSets;
        set<int> ignoreStartEdgesBackTo;
        
        list<const map<int,bool>* > extraEndPrecedenceSets;
        set<int> ignoreEndEdgesBackTo;
        
        if (newStep != newActs.end()) { // if we have dummy steps
            
            const int naSize = newActs.size() - (nonTemporal ? 1 : 2);
            const int sgSize = spareGaps.size();
            
            if (naSize > sgSize) {
                // this ensures that there are enough gaps defined, with timestamps given the default range of [0..inf]
                toReturn->addMoreGaps(spareGaps, naSize - sgSize);
            }            
            
            const list<FFEvent>::iterator newStepBefore = newStep;
            
            for (; newStep != newActs.end(); ++newStep) {
                
                const int dummyGap = spareGaps.front();
                spareGaps.pop_front();
                
                if (spawnDebug) {
                    cout << "Allocating gap " << dummyGap << " to dummy step for " << RPGBuilder::getPreferences()[newStep->divisionID].name << endl;
                }
                
                childEvents[dummyGap] = &(*newStep);
                toReturn->setNonTemporal(dummyGap);
                
                gapsUsed.push_back(dummyGap);
                                
                if (newStep->getEffects) {                        
                    const int remapTo = remapPreferenceEdge(*newStep,dummyGap,cons);                    
                    toReturn->nonSoftEdges(dummyGap, remapTo);
                    
                    const map<int, bool> * const preceding = cons->stepsBefore(dummyGap);
                    
                    if (preceding && remapTo != dummyGap) {
                        
                        if (remapTo == startLocation) {
                            extraStartPrecedenceSets.push_back(preceding);
                            ignoreStartEdgesBackTo.insert(dummyGap);
                        } else if (remapTo == endLocation) {
                            extraEndPrecedenceSets.push_back(preceding);
                            ignoreEndEdgesBackTo.insert(dummyGap);
                        }
                    }
                }
                
                toReturn->makeEdgeListFor(dummyGap);
            }
            
            newStep = newStepBefore;
        }
        
        const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[s.action->getID()];

        double startMin = tsBounds[0].first;
        double endMin = tsBounds[1].first;

        double startMax = tsBounds[0].second;
        double endMax = tsBounds[1].second;


        {
            const map<int, bool> * const preceding = cons->stepsBefore(startLocation);            
            if (preceding) {
                int earlier;
                map<int, bool>::const_iterator pItr = preceding->begin();
                const map<int, bool>::const_iterator pEnd = preceding->end();

                for (; pItr != pEnd; ++pItr) {
                    if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) != -1) {
                        if (ignoreStartEdgesBackTo.find(earlier) == ignoreStartEdgesBackTo.end()) {
                            const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                            if (startMin < w) startMin = w;
                        }
                    }
                }
            }
        }
        
        {
            list<const map<int,bool>* >::const_iterator psItr = extraStartPrecedenceSets.begin();
            const list<const map<int,bool>* >::const_iterator psEnd = extraStartPrecedenceSets.end();
            
            int earlier;
            for (; psItr != psEnd; ++psItr) {
                map<int, bool>::const_iterator pItr = (*psItr)->begin();
                const map<int, bool>::const_iterator pEnd = (*psItr)->end();

                for (; pItr != pEnd; ++pItr) {
                    if (pItr->first == startLocation) {
                        continue;
                    }
                    if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) != -1) {
                        if (earlier != startLocation && ignoreStartEdgesBackTo.find(earlier) == ignoreStartEdgesBackTo.end()) {
                            const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                            if (startMin < w) startMin = w;
                        }
                    }
                }
            }
        }

        if (startMax > TILupbo) startMax = TILupbo;

        if (nonTemporal) {
            if (spawnDebug) cout << "Edges back to previous steps give earliest start position " << startMin << " vs " << tsBounds[0].first << " from RPG\n";

            toReturn->autoMinima[startLocation] = startMin;

            if (startMax < startMin) {
                delete toReturn;
                return 0;
            }
        } else {

            {
                const map<int, bool> * const preceding = cons->stepsBefore(endLocation);
                if (preceding) {
                    map<int, bool>::const_iterator pItr = preceding->begin();
                    const map<int, bool>::const_iterator pEnd = preceding->end();
                    
                    int earlier;
                    for (; pItr != pEnd; ++pItr) {
                        if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) != -1) {                            
                            if (earlier != startLocation && ignoreEndEdgesBackTo.find(earlier) == ignoreEndEdgesBackTo.end()) {
                                const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                                if (endMin < w) endMin = w;                    
                            }   
                        }
                    }
                }
            }            
            
            {
                list<const map<int,bool>* >::const_iterator psItr = extraEndPrecedenceSets.begin();
                const list<const map<int,bool>* >::const_iterator psEnd = extraEndPrecedenceSets.end();
                
                int earlier;
                for (; psItr != psEnd; ++psItr) {
                    map<int, bool>::const_iterator pItr = (*psItr)->begin();
                    const map<int, bool>::const_iterator pEnd = (*psItr)->end();

                    for (; pItr != pEnd; ++pItr) {
                        if (pItr->first == endLocation) {
                            continue;
                        }
                        if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) != -1) {
                            if (earlier != endLocation && earlier != startLocation && ignoreEndEdgesBackTo.find(earlier) == ignoreEndEdgesBackTo.end()) {
                                const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                                if (endMin < w) endMin = w;
                            }
                        }
                    }
                }
            }            
            
            {
                const double sEndMin = startMin + s.minDuration;
                if (sEndMin > endMin) endMin = sEndMin;
            }

            {
                const double sStartMin = endMin - s.maxDuration;
                if (sStartMin > startMin) startMin = sStartMin;
            }

            if (startMax != DBL_MAX && s.maxDuration != DBL_MAX) {
                const double sEndMax = startMax + s.maxDuration;
                if (sEndMax < endMax) endMax = sEndMax;
            }

            if (endMax != DBL_MAX) {
                const double sStartMax = endMax - s.minDuration;
                if (sStartMax < startMax) startMax = sStartMax;
            }

            if (spawnDebug) {
                cout << "Edges back to previous steps give earliest positions " << startMin << ";" << endMin << " vs " << tsBounds[0].first << ";" << tsBounds[1].first << " from RPG\n";
            }

            toReturn->autoMinima[startLocation] = startMin;
            toReturn->autoMinima[endLocation] = endMin;

            if (startMax < startMin || endMax < endMin) {
                delete toReturn;
                return 0;
            }
        }

        if (startMax < DBL_MAX) {
            toReturn->setDFZ(startLocation, startMax);
        }

        if (startMin > 0.0) {
            toReturn->setDTZ(startLocation, -startMin);
        }

        if (Globals::paranoidScheduling || Globals::profileScheduling) {
            childEvents[startLocation]->lpMinTimestamp = 0.0;
            childEvents[startLocation]->lpMaxTimestamp = DBL_MAX;
        } else {
            childEvents[startLocation]->lpMinTimestamp = startMin;        
            childEvents[startLocation]->lpMaxTimestamp = startMax;            
        }

        if (spawnDebug) cout << "Initially putting at " << startMin;

        if (!nonTemporal) {
            if (endMax < DBL_MAX) {
                toReturn->setDFZ(endLocation, endMax);
            }


            if (endMin > 0.0) {
                toReturn->setDTZ(endLocation, -endMin);
            }


            if (Globals::paranoidScheduling || Globals::profileScheduling) {
                childEvents[endLocation]->lpMinTimestamp = 0.0;
                childEvents[endLocation]->lpMaxTimestamp = DBL_MAX;
            } else {
                childEvents[endLocation]->lpMinTimestamp = endMin;
                childEvents[endLocation]->lpMaxTimestamp = endMax;
            } 
        
            if (spawnDebug) {
                cout << " ; " << endMin << "\n";
            }

        } else {
            if (spawnDebug) cout << "\n";
        }

        const int mustComeBeforeOpenEnds = MinimalState::getTransformer()->stepThatMustPrecedeUnfinishedActions(cons);

        if (mustComeBeforeOpenEnds != -1) {
            assert(mustComeBeforeOpenEnds == startLocation);

            list<StartEvent>::iterator seqFillItr = seq.begin();
            const list<StartEvent>::iterator seqFillEnd = seq.end();

            for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                if (seqFillItr->stepID == startLocation) continue;
                const int cbf = toReturn->getPairWith()[seqFillItr->stepID];

                // The edge is definitely new, as it's from a start (an event that wasn't in before)

                if (spawnDebug) cout << "Adding total-order epsilon separation edge from " << startLocation << " to some future end event " << cbf << "\n";
                toReturn->addNewEdge(BFEdge(startLocation, cbf, 0.001, DBL_MAX));
            }
        } else {
            list<StartEvent>::iterator seqFillItr = seq.begin();
            const list<StartEvent>::iterator seqFillEnd = seq.end();

            for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                if (seqFillItr->stepID == startLocation) continue;
                const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                if (!beforeFutureStep) continue;

                map<int, bool>::const_iterator toThisItr = beforeFutureStep->find(startLocation);
                if (toThisItr != beforeFutureStep->end()) {
                    if (spawnDebug) {
                        if (toThisItr->second) {
                            cout << "Adding epsilon separation edge from " << startLocation << " to some future end event " << cbf << ", due to recorded constraints\n";
                        } else {
                            cout << "Adding zero separation edge from " << startLocation << " to some future end event " << cbf << ", due to recorded constraints\n";
                        }
                    }
                    toReturn->addNewEdge(BFEdge(startLocation, cbf, (toThisItr->second ? 0.001 : 0.0), DBL_MAX));
                }
            }
        }

        {
            const map<int, bool> * beforeNewStep = cons->stepsBefore(startLocation);

            map<int,bool> mergedEdges;
            
            if (!extraStartPrecedenceSets.empty()) {
                if (beforeNewStep) {
                    mergedEdges = *beforeNewStep;
                }
                beforeNewStep = &mergedEdges;
                
                mergeEdges(mergedEdges, extraStartPrecedenceSets, startLocation, ignoreStartEdgesBackTo);
            }
            
            
            if (beforeNewStep) {
                map<int, bool>::const_iterator ecaItr = beforeNewStep->begin();
                const map<int, bool>::const_iterator ecaEnd = beforeNewStep->end();

                int earlier;
                for (; ecaItr != ecaEnd; ++ecaItr) {
                    const int afR = ecaItr->first;

                    if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                        if (spawnDebug) {
                            if (ecaItr->second) {
                                cout << "Recorded constraints: adding edge to denote that the start of the new action comes at least epsilon after step " << earlier << endl;
                            } else {
                                cout << "Recorded constraints: adding edge to denote that the start of the new action comes after (or alongside) step " << earlier << endl;
                            }
                        }

                        toReturn->addNewEdge(BFEdge(earlier, startLocation, (ecaItr->second ? 0.001 : 0.0), DBL_MAX));
                    } else {
                        toReturn->makeSoftEdgeListFor(startLocation).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        toReturn->makeSoftEdgeListFor(afR).addFollower(startLocation, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                    }
                }
            }
        }
        
        if (!nonTemporal) {
            toReturn->makeEdgeListFor(endLocation);

            {
                const map<int, bool> * beforeNewEndStep = cons->stepsBefore(endLocation);

                map<int,bool> mergedEdges;
            
                if (!extraEndPrecedenceSets.empty()) {
                    if (beforeNewEndStep) {
                        mergedEdges = *beforeNewEndStep;
                    }
                    beforeNewEndStep = &mergedEdges;
                    
                    mergeEdges(mergedEdges, extraEndPrecedenceSets, endLocation, ignoreEndEdgesBackTo);
                }

                
                if (beforeNewEndStep) {
                    map<int, bool>::const_iterator ecaItr = beforeNewEndStep->begin();
                    const map<int, bool>::const_iterator ecaEnd = beforeNewEndStep->end();

                    int earlier;
                    for (; ecaItr != ecaEnd; ++ecaItr) {
                        const int afR = ecaItr->first;
                        if (afR == startLocation) continue;

                        if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                        
                            if (earlier == startLocation) {
                                continue;
                            }
                                                    
                            if (spawnDebug) {
                                if (ecaItr->second) {
                                    cout << "Due to recorded constraints: adding edge to denote that the end of the new action comes at least epsilon after step " << earlier << endl;
                                } else {
                                    cout << "Due to recorded constraints: adding edge to denote that the end of the new action comes after (or alongside) step " << earlier << endl;
                                }
                            }

                            toReturn->addNewEdge(BFEdge(earlier, endLocation, (ecaItr->second ? 0.001 : 0.0), DBL_MAX));
                        } else {
                            toReturn->makeSoftEdgeListFor(endLocation).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(afR).addFollower(endLocation, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        }
                    }
                } else {
                    if (spawnDebug) {
                        cout << "No steps must come before the end just added\n";
                    }
                }
            }
            
            {

                list<StartEvent>::iterator seqFillItr = seq.begin();
                const list<StartEvent>::iterator seqFillEnd = seq.end();

                for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                    if (seqFillItr->stepID == startLocation) continue;

                    const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                    const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                    if (!beforeFutureStep) continue;

                    map<int, bool>::const_iterator toThisItr = beforeFutureStep->find(endLocation);
                    if (toThisItr != beforeFutureStep->end()) {
                        if (spawnDebug) {
                            if (toThisItr->second) {
                                cout << "Constraint to future step: adding epsilon separation edge from " << endLocation << " to some future end event " << cbf << "\n";
                            } else {
                                cout << "Constraint to future step: adding zero separation edge from " << endLocation << " to some future end event " << cbf << "\n";
                            }
                        }
                        toReturn->addNewEdge(BFEdge(endLocation, cbf, (toThisItr->second ? 0.001 : 0.0), DBL_MAX));
                    }

                }
            }

            /*
            StartEvent & ev = seq.back();

            if (!ignoreABedges) {


                {
                    set<int>::iterator ecaItr = ev.getEndComesAfter().begin();
                    const set<int>::iterator ecaEnd = ev.getEndComesAfter().end();

                    for (; ecaItr != ecaEnd; ++ecaItr) {
                        const int af = *ecaItr;

                        if (af >= 0) {
                            if (spawnDebug) cout << "Adding edge to denote that the end of the new action comes after the end of that starting at " << af << ", i.e. after node " << toReturn->getPairWith()[af] << "\n";
                            toReturn->addNewEdge(BFEdge(toReturn->getPairWith()[af], endLocation, 0.001, DBL_MAX));
                        }
                    }
                }

                {
                    set<int>::iterator ecbItr = ev.getEndComesAfterPair().begin();
                    const set<int>::iterator ecbEnd = ev.getEndComesAfterPair().end();

                    for (; ecbItr != ecbEnd; ++ecbItr) {
                        const int af = *ecbItr;

                        if (af >= 0) {
                            if (spawnDebug) cout << "Adding edge to denote that the end of the action comes before the end of that starting at " << af << ", i.e. before node " << toReturn->getPairWith()[af] << ", due to eca pair\n";
                            toReturn->addNewEdge(BFEdge(endLocation, toReturn->getPairWith()[af], 0.001, DBL_MAX));
                        }
                    }
                }


                {
                    set<int>::iterator ecbItr = ev.getEndComesBefore().begin();
                    const set<int>::iterator ecbEnd = ev.getEndComesBefore().end();

                    for (; ecbItr != ecbEnd; ++ecbItr) {
                        const int af = *ecbItr;

                        if (af >= 0) {
                            if (spawnDebug) cout << "Adding edge to denote that the end action comes before the end of that starting at node " << af << ", i.e. node " << toReturn->getPairWith()[af] << "\n";
                            toReturn->addNewEdge(BFEdge(endLocation, toReturn->getPairWith()[af], 0.001, DBL_MAX));
                        }
                    }
                }

                int workingFanIn = ev.fanIn;
                if (workingFanIn) {
                    set<int>::iterator ecaItr = ev.getEndComesBeforePair().begin();
                    const set<int>::iterator ecaEnd = ev.getEndComesBeforePair().end();

                    for (; ecaItr != ecaEnd; ++ecaItr) {
                        const int af = *ecaItr;

                        if (af >= 0) {
                            if (spawnDebug) cout << "Adding edge to denote that the end of the action comes after that which started at node " << *ecaItr << ", i.e. " << toReturn->getPairWith()[*ecaItr] << ", due to it being on the back-end of an end-comes-before\n";
                            toReturn->addNewEdge(BFEdge(toReturn->getPairWith()[*ecaItr], endLocation, 0.001, DBL_MAX));
                        }
                    }
                }
            }*/
        }

        list<int>::const_iterator gapItr = gapsUsed.begin();
        for (; newStep != newActs.end(); ++newStep, ++gapItr) {
            const int dummyGap = *gapItr;
            const int applyEdgesTo = toReturn->edgesAreNonSoft(dummyGap);
            
            double localMin = 0.0;
            double localMax = DBL_MAX;
            
            if (applyEdgesTo == *gapItr) {
                
                const map<int, bool> * const preceding = cons->stepsBefore(dummyGap);
                
                if (preceding) {
                    int earlier;
                    map<int, bool>::const_iterator pItr = preceding->begin();
                    const map<int, bool>::const_iterator pEnd = preceding->end();
                    
                    for (; pItr != pEnd; ++pItr) {
                        if ((earlier = toReturn->edgesAreNonSoft(pItr->first)) != -1) {
                            const double w = -(toReturn->getDistToZero()[earlier] - (pItr->second ? 0.001 : 0.0));
                            if (localMin < w) localMin = w;
                        }
                    }
                }
            }
            
            if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                if (newStep->pairWithStep >= 0) {
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                    if (pref.cons == VAL::E_ALWAYSWITHIN) {                    
                        if (applyEdgesTo == -1) {
                            toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(newStep->pairWithStep, false, -pref.deadline);
                            toReturn->makeSoftEdgeListFor(newStep->pairWithStep).addFollower(dummyGap, false, -pref.deadline);
                        } else {
                            assert(applyEdgesTo != dummyGap);
                            assert(newStep->getEffects);
                            toReturn->addNewEdge(BFEdge(applyEdgesTo, newStep->pairWithStep, 0.001, pref.deadline));
                        }                                     
                    }
                }
            } else if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE) {
                const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                if (pref.cons == VAL::E_WITHIN) {
                    if (newStep->getEffects) {
                        assert(applyEdgesTo == dummyGap);                        
                        localMax = pref.deadline;
                    } else {
                        assert(applyEdgesTo == -1);
                        toReturn->makeSoftEdgeListFor(-1).addPredecessor(dummyGap, false, -pref.deadline);
                        toReturn->makeSoftEdgeListFor(dummyGap).addFollower(-1, false, -pref.deadline);
                    }
                }
            }
            

            if (localMin > localMax) {
                delete toReturn;
                return 0;
            }
            
                                    
            toReturn->autoMinima[dummyGap] = localMin;
            if (localMax < DBL_MAX) {
                toReturn->setDFZ(dummyGap, localMax);
            }
                
            if (localMin > 0.0) {
                toReturn->setDTZ(dummyGap, -localMin);
            }
                
            if (Globals::paranoidScheduling || Globals::profileScheduling) {
                childEvents[dummyGap]->lpMinTimestamp = 0.0;
                childEvents[dummyGap]->lpMaxTimestamp = DBL_MAX;
            } else {
                childEvents[dummyGap]->lpMinTimestamp = localMin;
                childEvents[dummyGap]->lpMaxTimestamp = localMax;
            }
                
            if (applyEdgesTo == dummyGap) {
                const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);

                if (beforeDummyStep) {
                    map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                    const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();

                    int earlier;
                    for (; ecaItr != ecaEnd; ++ecaItr) {
                        const int afR = ecaItr->first;

                        if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                            if (spawnDebug) {
                                if (ecaItr->second) {
                                    cout << "Due to recorded constraints: adding edge to denote that preference checking step " << dummyGap << " comes at least epsilon after step " << earlier << endl;                                
                                } else {
                                    cout << "Due to recorded constraints: adding edge to denote that preference checking step " << dummyGap << " comes after (or alongside) step " << earlier << endl;                                
                                }
                            }

                            toReturn->addNewEdge(BFEdge(earlier, dummyGap, (ecaItr->second ? 0.001 : 0.0), DBL_MAX));
                        } else {
                            toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        }
                    }
                } else {
                    if (spawnDebug) {
                        cout << "No steps must come before the end just added\n";
                    }
                }
            } else if (applyEdgesTo == -1) {
                const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);
                
                if (beforeDummyStep) {
                    map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                    const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();
                    
                    for (; ecaItr != ecaEnd; ++ecaItr) {
                        const int afR = ecaItr->first;
                        toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                    }
                }
            }
            
            
            {
                
                list<StartEvent>::iterator seqFillItr = seq.begin();
                const list<StartEvent>::iterator seqFillEnd = seq.end();
                
                for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                    const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                    const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                    if (!beforeFutureStep) continue;
                    
                    map<int, bool>::const_iterator toThisItr = beforeFutureStep->find(dummyGap);
                    if (toThisItr != beforeFutureStep->end()) {
                        if (applyEdgesTo != -1) {
                            if (spawnDebug) {
                                if (toThisItr->second) {
                                    cout << "Constraint to future step: adding epsilon separation edge from " << dummyGap << " to some future end event " << cbf << "\n";
                                } else {
                                    cout << "Constraint to future step: adding zero separation edge from " << dummyGap << " to some future end event " << cbf << "\n";
                                }
                            }
                            toReturn->addNewEdge(BFEdge(dummyGap, cbf, (toThisItr->second ? 0.001 : 0.0), DBL_MAX));
                        } else {
                            toReturn->makeSoftEdgeListFor(cbf).addPredecessor(dummyGap, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(dummyGap).addFollower(cbf, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                        }
                    }
                    
                }
            }
            
        }

    } else {
        if (spawnDebug) cout << "Is a TIL\n";

        assert(newActCount == 1);

        FFEvent & s = newActs.front();

        toReturn = new ChildData(&Q, distFromZero, distToZero, pairWith, eventsWithFakes, softEdges, temporaryEdges, temporarySoftEdges, needsLP);

        vector<FFEvent*> & childEvents = toReturn->getEventsWithFakes();

        int i = 0;

        {
            list<FFEvent>::iterator hItr = header.begin();
            const list<FFEvent>::iterator hEnd = header.end();

            for (; hItr != hEnd; ++hItr, ++i) {
                childEvents[i] = &(*hItr);
            }
        }
        ++i;

        childEvents[startGap] = &s;
        toReturn->setTil(startGap);

        const double tilTime = LPScheduler::getTILTimestamp(s.divisionID);

        s.lpMinTimestamp = tilTime;
        s.lpMaxTimestamp = tilTime;

        toReturn->setDFZ(startGap, tilTime);
        if (tilTime != 0.0) {
            toReturn->setDTZ(startGap, -tilTime);
        } else {
            toReturn->setDTZ(startGap, 0.0);
        }

        toReturn->autoMinima[startGap] = tilTime;
        
        list<int> gapsUsed;
        
        list<const map<int,bool> * > extraPrecedenceSets;
        set<int> ignoreEdgesBackTo;
        
        const int naSize = newActs.size();
        if (naSize > 1) {
            
            list<int> spareGaps;
            spareGaps.push_back(endGap);
            spareGaps.push_back(postStartGap);
            spareGaps.push_back(postEndGap);
            
            if (naSize > 4) {
                toReturn->addMoreGaps(spareGaps, naSize - 4);
            }
            
            list<FFEvent>::iterator newStep = newActs.begin();
            const list<FFEvent>::iterator newEnd = newActs.end();            
            
            ++newStep;
            
            for (; newStep != newEnd; ++newStep) {
                const int dummyGap = spareGaps.front();
                spareGaps.pop_front();
                
                gapsUsed.push_back(dummyGap);
                
                childEvents[dummyGap] = &(*newStep);
                toReturn->setNonTemporal(dummyGap);
                
                if (newStep->getEffects) {
                    const int remapTo = remapPreferenceEdge(*newStep,dummyGap,cons);
                    toReturn->nonSoftEdges(dummyGap, remapTo);
                    
                    const map<int,bool> * const prec = cons->stepsBefore(dummyGap);
                    if (prec && remapTo != dummyGap && remapTo == startGap) {
                        extraPrecedenceSets.push_back(prec);
                        ignoreEdgesBackTo.insert(dummyGap);
                    }
                }
                                
                toReturn->makeEdgeListFor(dummyGap);
            }
        }


        const int mustComeBeforeOpenEnds = MinimalState::getTransformer()->stepThatMustPrecedeUnfinishedActions(cons);

        if (mustComeBeforeOpenEnds != -1) {
            assert(mustComeBeforeOpenEnds == startGap);

            list<StartEvent>::iterator seqFillItr = seq.begin();
            const list<StartEvent>::iterator seqFillEnd = seq.end();

            for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                if (spawnDebug) cout << "Adding edge from time zero to a future step " << cbf << " to set its min ts to " << tilTime + 0.001 << "\n";
                toReturn->addNewEdge(BFEdge(-1, cbf, tilTime + 0.001, distFromZero[cbf]));
                
                if (spawnDebug) cout << "Adding epsilon separation edge from " << startGap << " to some future end event " << cbf << "\n";
                toReturn->addNewEdge(BFEdge(startGap, cbf, 0.001, DBL_MAX));

            }
        } else {
            list<StartEvent>::iterator seqFillItr = seq.begin();
            const list<StartEvent>::iterator seqFillEnd = seq.end();

            for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                if (!beforeFutureStep) continue;

                if (beforeFutureStep->find(startGap) != beforeFutureStep->end()) {
                    if (spawnDebug) cout << "Adding edge from time zero to a future step " << cbf << " to set its min ts to " << tilTime + 0.001 << "\n";
                    toReturn->addNewEdge(BFEdge(-1, cbf, tilTime + 0.001, distFromZero[cbf]));
                    
                    if (spawnDebug) cout << "Adding epsilon separation edge from " << startGap << " to some future end event " << cbf << "\n";
                    toReturn->addNewEdge(BFEdge(startGap, cbf, 0.001, DBL_MAX));
                    
                }
            }
        }

        {
            
            
            const map<int, bool> * beforeNewStep = cons->stepsBefore(startGap);

            map<int,bool> mergedEdges;
            
            if (!extraPrecedenceSets.empty()) {
                if (beforeNewStep) {
                    mergedEdges = *beforeNewStep;
                }
                beforeNewStep = &mergedEdges;
                                
                mergeEdges(mergedEdges, extraPrecedenceSets, startGap, ignoreEdgesBackTo);
            }

            if (beforeNewStep) {
                map<int, bool>::const_iterator ecaItr = beforeNewStep->begin();
                const map<int, bool>::const_iterator ecaEnd = beforeNewStep->end();

                int earlier;
                for (; ecaItr != ecaEnd; ++ecaItr) {
                    const int afR = ecaItr->first;

                    if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                        if (spawnDebug) cout << "TIL comes after step " << earlier << endl;

                        double w = distToZero[earlier];
                        if (w != 0.0) w = -w;
                        if (w > tilTime - 0.001) {
                            if (spawnDebug) cout << "- Found a simple cycle: the earliest step " << earlier << " could go at was " << w << ", i.e. too late for a TIL at " << tilTime << endl;
                            delete toReturn;
                            return 0;
                        }

                        if (distFromZero[earlier] > tilTime - 0.001) {
                            if (spawnDebug) cout << "Adding edge from time zero to a preceding step " << earlier << " to set its max ts to " << tilTime - 0.001 << "\n";
                            toReturn->addNewEdge(BFEdge(-1, earlier, w, tilTime - 0.001));
                            if (spawnDebug) cout << "Adding epsilon separation edge from step " << earlier << " to TIL\n";
                            toReturn->addNewEdge(BFEdge(earlier, startGap, 0.001, DBL_MAX));                                        
                        } else {
                            if (spawnDebug) cout << "Latest step " << earlier << " could come at was " << distFromZero[earlier] << ", so it is unaffected\n";
                            toReturn->makeEdgeListFor(earlier).addFollower(startGap, true, EPSILON);
                            toReturn->makeEdgeListFor(startGap).addPredecessor(earlier, true, EPSILON);
                        }
                        
                        /* else {
                            childEvents[af]->lpMaxTimestamp = tilTime - 0.001;
                        }*/

                    } else {
                        toReturn->makeSoftEdgeListFor(-1).addPredecessor(afR, false, -(tilTime - EPSILON));
                        toReturn->makeSoftEdgeListFor(afR).addPredecessor(-1, false, -(tilTime - EPSILON));
                    }
                }
            }

        }
        
        if (naSize > 1) {
                        
            list<FFEvent>::iterator newStep = newActs.begin();
            const list<FFEvent>::iterator newEnd = newActs.end();            
            
            ++newStep;
            
            list<int>::const_iterator gapItr = gapsUsed.begin();
            
            for (; newStep != newEnd; ++newStep, ++gapItr) {
                const int dummyGap = *gapItr;
                const int applyEdgesTo = toReturn->edgesAreNonSoft(dummyGap);
                
                double localMin = 0.0;
                double localMax = DBL_MAX;
                
                if (applyEdgesTo == *gapItr) {
                    const map<int, bool> * const preceding = cons->stepsBefore(dummyGap);
                    
                    if (preceding) {
                        map<int, bool>::const_iterator pItr = preceding->begin();
                        const map<int, bool>::const_iterator pEnd = preceding->end();
                        
                        for (; pItr != pEnd; ++pItr) {
                            if (pItr->first == startGap) {
                                if (localMin < tilTime + (pItr->second ? 0.001 : 0.0)) {
                                    localMin = tilTime + (pItr->second ? 0.001 : 0.0);
                                }
                            } else {
                                if (toReturn->edgesAreNonSoft(pItr->first)) {
                                    const double w = -(toReturn->getDistToZero()[pItr->first] - (pItr->second ? 0.001 : 0.0));
                                    if (localMin < w) localMin = w;
                                }
                            }
                        }
                    }
                }

                if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE) {
                    if (newStep->pairWithStep >= 0) {
                        const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                        if (pref.cons == VAL::E_ALWAYSWITHIN) {                    
                            if (applyEdgesTo == -1) {
                                toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(newStep->pairWithStep, false, -pref.deadline);
                                toReturn->makeSoftEdgeListFor(newStep->pairWithStep).addFollower(dummyGap, false, -pref.deadline);
                            } else {
                                assert(applyEdgesTo != dummyGap);
                                assert(newStep->getEffects);
                                toReturn->addNewEdge(BFEdge(applyEdgesTo, newStep->pairWithStep, 0.001, pref.deadline));
                            }                                     
                        }
                    }
                } else if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE) {
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                    if (pref.cons == VAL::E_WITHIN) {
                        if (newStep->getEffects) {
                            assert(applyEdgesTo == dummyGap);                        
                            localMax = pref.deadline;
                        } else {
                            assert(applyEdgesTo == -1);
                            toReturn->makeSoftEdgeListFor(-1).addPredecessor(dummyGap, false, -pref.deadline);
                            toReturn->makeSoftEdgeListFor(dummyGap).addFollower(-1, false, -pref.deadline);
                        }
                    }
                }
                
                                
                if (newStep->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE && newStep->getEffects) {
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[newStep->divisionID];
                    if (pref.cons == VAL::E_WITHIN) {
                        localMax = pref.deadline;
                    }
                }
                
                if (localMin > localMax) {
                    delete toReturn;
                    return 0;
                }
                                        
                                                        
                toReturn->autoMinima[dummyGap] = localMin;
                
                if (localMin > 0.0) {
                    toReturn->setDTZ(dummyGap, -localMin);
                }
                    
                if (Globals::paranoidScheduling || Globals::profileScheduling) {
                    childEvents[dummyGap]->lpMinTimestamp = 0.0;
                    childEvents[dummyGap]->lpMaxTimestamp = DBL_MAX;
                } else {
                    childEvents[dummyGap]->lpMinTimestamp = localMin;
                    childEvents[dummyGap]->lpMaxTimestamp = localMax;
                }
                    
                if (applyEdgesTo == dummyGap) {
                    const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);

                    if (beforeDummyStep) {
                        map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                        const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();

                        int earlier;
                        
                        for (; ecaItr != ecaEnd; ++ecaItr) {
                            const int afR = ecaItr->first;

                            if ((earlier = toReturn->edgesAreNonSoft(afR)) != -1) {
                                if (spawnDebug) {
                                    if (ecaItr->second) {
                                        cout << "Due to recorded constraints: adding edge to denote that preference checking step " << dummyGap << " comes at least epsilon after step " << earlier << endl;                                
                                    } else {
                                        cout << "Due to recorded constraints: adding edge to denote that preference checking step " << dummyGap << " comes after (or alongside) step " << earlier << endl;
                                    }
                                }

                                toReturn->addNewEdge(BFEdge(earlier, dummyGap, (ecaItr->second ? 0.001 : 0.0), DBL_MAX));
                            } else {
                                toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            }
                        }
                    } else {
                        if (spawnDebug) {
                            cout << "No steps must come before the end just added\n";
                        }
                    }
                } else if (applyEdgesTo == -1) {
                    const map<int, bool> * beforeDummyStep = cons->stepsBefore(dummyGap);
                    
                    if (beforeDummyStep) {
                        map<int, bool>::const_iterator ecaItr = beforeDummyStep->begin();
                        const map<int, bool>::const_iterator ecaEnd = beforeDummyStep->end();
                        for (; ecaItr != ecaEnd; ++ecaItr) {
                            const int afR = ecaItr->first;
                            toReturn->makeSoftEdgeListFor(dummyGap).addPredecessor(afR, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                            toReturn->makeSoftEdgeListFor(afR).addFollower(dummyGap, ecaItr->second, (ecaItr->second ? 0.001 : 0.0));
                        }
                    }
                }
                
                {
                    
                    list<StartEvent>::iterator seqFillItr = seq.begin();
                    const list<StartEvent>::iterator seqFillEnd = seq.end();
                    
                    for (; seqFillItr != seqFillEnd; ++seqFillItr) {
                        const int cbf = toReturn->getPairWith()[seqFillItr->stepID];
                        const map<int, bool> * beforeFutureStep = cons->stepsBefore(cbf);
                        if (!beforeFutureStep) continue;
                        
                        map<int, bool>::const_iterator toThisItr = beforeFutureStep->find(dummyGap);
                        if (toThisItr != beforeFutureStep->end()) {
                            if (applyEdgesTo != -1) {
                                if (spawnDebug) {
                                    if (toThisItr->second) {
                                        cout << "Constraint to future step: adding epsilon separation edge from " << applyEdgesTo << " to some future end event " << cbf << "\n";
                                    } else {
                                        cout << "Constraint to future step: adding zero separation edge from " << applyEdgesTo << " to some future end event " << cbf << "\n";
                                    }
                                }
                                toReturn->addNewEdge(BFEdge(applyEdgesTo, cbf, (toThisItr->second ? 0.001 : 0.0), DBL_MAX));
                            } else {
                                toReturn->makeSoftEdgeListFor(cbf).addPredecessor(dummyGap, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                                toReturn->makeSoftEdgeListFor(dummyGap).addFollower(cbf, toThisItr->second, (toThisItr->second ? 0.001 : 0.0));
                            }
                        }
                        
                    }
                }
            }                
        }
    }

    return toReturn;
};

bool ChildData::propagateNewEdges(const vector<AutomatonPosition::Position> & previousPreferenceStatus, const TemporalConstraints * cons, bool & preferencesWereAsExpected)
{

    static const bool floydDoubleCheck = Globals::paranoidScheduling;
    static const bool noisy = Globals::globalVerbosity & 4096;

    if (Globals::globalVerbosity & 4096) {
        cout << "Propagating " << newEdges.size() << " edges\n";
        cout << "Before new edges, timestamps of events are: [";
        const int fs = eventsWithFakes.size();
        for (int i = 0; i < fs; ++i) {
            if (!(eventsWithFakes[i])) continue;
            if (i) cout << ",";
            cout << -distToZero[i];
        }
        cout << "]\n";
    }
    if (checkSanity) sanityCheck();

    if (floydDoubleCheck) {
        // should, here, be consistent
        const int mSize = eventsWithFakes.size() + 1;

        vector<vector<double> > matrix(mSize, vector<double>(mSize, DBL_MAX));

        for (int m = 0; m < mSize; ++m) {
            matrix[m][m] = 0.0;
        }

        for (int m = 1; m < mSize; ++m) {
            matrix[m][0] = 0.0;
            if (!eventsWithFakes[m-1]) continue;
            
            if (eventsWithFakes[m-1]->isDummyStep()) {
                matrix[m][0] = 0.0;
                matrix[0][m] = DBL_MAX;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero is 0.0, as it's a dummy preference-checking step\n";
            } else if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_START) {
                const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[eventsWithFakes[m-1]->action->getID()];
                const double startMin = tsBounds[0].first;
                const double startMax = tsBounds[0].second;

                matrix[m][0] = -1 * startMin;
                matrix[0][m] = startMax;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -startMin << " due to earliest RPG start point of action\n";
            } else if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_END) {
                const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[eventsWithFakes[m-1]->action->getID()];
                const double endMin = tsBounds[1].first;
                const double endMax = tsBounds[1].second;

                matrix[m][0] = -1 * endMin;
                matrix[0][m] = endMax;
                if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -endMin << " due to earliest RPG end point of action\n";

            }
        }

        for (int m = 1; m < mSize; ++m) {
            if (!eventsWithFakes[m-1]) continue;

            if (pairWith[m-1] >= 0) {
                if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_START) {
                    matrix[m][pairWith[m-1] + 1] = eventsWithFakes[m-1]->maxDuration;
                    if (noisy) cout << "Edge from " << m - 1 << " to " << pairWith[m-1] << " - " << eventsWithFakes[m-1]->maxDuration << " due to max duration" << endl;
                } else {
                    matrix[m][pairWith[m-1] + 1] = -1 * eventsWithFakes[m-1]->minDuration;
                    if (noisy) cout << "Edge from " << m - 1 << " to " << pairWith[m-1] << " - " << -eventsWithFakes[m-1]->minDuration << " due to min duration" << endl;
                }
            } else if (pairWith[m-1] == -2) {
                const double tilTime = LPScheduler::getTILTimestamp(eventsWithFakes[m-1]->divisionID);
                matrix[0][m] = tilTime;
                matrix[m][0] = -1 * tilTime;
            }

            if (eventsWithFakes[m-1]->lpMinTimestamp != -1.0) {
                const double backEdge = (eventsWithFakes[m-1]->lpMinTimestamp == 0.0 ? 0.0 : -(eventsWithFakes[m-1]->lpMinTimestamp));
                if (backEdge < matrix[m][0]) {
                    matrix[m][0] = backEdge;
                    if (noisy) cout << "Changing edge from " << m - 1 << " to time zero - " << backEdge << " due to known minimum timestamp for action\n";
                } else {
                    if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
                }
            } else {
                if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
            }
            
            if (eventsWithFakes[m-1]->lpMaxTimestamp != -1.0) {
                if (eventsWithFakes[m-1]->lpMaxTimestamp < matrix[0][m]) {
                    matrix[0][m] = eventsWithFakes[m-1]->lpMaxTimestamp;
                    if (noisy) cout << "Changing edge from time zero to " << m - 1 << " to " << matrix[0][m] << " due to known maximum timestamp for action\n";
                } else {
                    if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
                }
            } else {
                if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
            }

            map<int, IncomingAndOutgoing>::const_iterator eItr = temporaryEdges.find(m - 1);
            if (eItr != temporaryEdges.end()) {
                map<int, pair<bool,double> >::const_iterator pItr = eItr->second.mustPrecedeThis().begin();
                const map<int, pair<bool,double> >::const_iterator pEnd = eItr->second.mustPrecedeThis().end();

                double negatedValue;
                for (; pItr != pEnd; ++pItr) {
                    negatedValue = (pItr->second.second == 0.0 ? 0.0 : -pItr->second.second);
                    if (negatedValue < matrix[m][pItr->first + 1]) {
                        matrix[m][pItr->first + 1] = negatedValue;
                        if (noisy) cout << "Edge from " << m - 1 << " to " << pItr->first << " - " << negatedValue << " due to recorded outgoing edges" << endl;
                    }
                }
            }
        }

        {
            map<int, double>::const_iterator aItr = autoMinima.begin();
            const map<int, double>::const_iterator aEnd = autoMinima.end();

            for (; aItr != aEnd; ++aItr) {
                if (-aItr->second < matrix[aItr->first + 1][0]) {
                    matrix[aItr->first + 1][0] = -aItr->second;
                    if (noisy) cout << "Edge from " << aItr->first << " to time zero, weight " << -aItr->second << " due to it having to follow after actions with known timestamps\n";
                }
            }
        }

        int k, i, j;
        double distIK, distKJ;

        for (k = 0; k < mSize; ++k) {
            for (i = 0; i < mSize; ++i) {
                distIK = matrix[i][k];
                if (distIK == DBL_MAX) continue;
                for (j = 0; j < mSize; ++j) {
                    distKJ = matrix[k][j];

                    if (distKJ != DBL_MAX) {
                        double & distIJ = matrix[i][j];
                        if ((distIK + distKJ) - distIJ < -0.00001) {
                            distIJ = distIK + distKJ;
                        }
                    }
                }
            }
        }

        for (int m = 0; m < mSize; ++m) {
            assert(fabs(matrix[m][m]) < 0.000000001);
        }

        if (noisy) {
            cout << "Floyd gives pre-expansion timestamps of: [";
            for (int m = 1; m < mSize; ++m) {
                if (!eventsWithFakes[m-1]) continue;
                if (m >= 2) cout << ",";
                cout << -(matrix[m][0]);
            }
            cout << "]\n";
        }
    }

    list<BFEdge>::iterator neItr = newEdges.begin();
    const list<BFEdge>::iterator neEnd = newEdges.end();

    for (; neItr != neEnd; ++neItr) {
        const bool pResult = Propagation(*Q, *neItr, distFromZero, distToZero, pairWith, eventsWithFakes, temporaryEdges);

        if (noisy) {
            cout << "After that edge, timestamps of events are: [";
            const int fs = eventsWithFakes.size();
            for (int i = 0; i < fs; ++i) {
                if (!(eventsWithFakes[i])) continue;
                if (i) cout << ",";
                cout << -distToZero[i];
            }
            cout << "]\n";
                    
        }
        
        if (floydDoubleCheck) {

            const int mSize = eventsWithFakes.size() + 1;

            vector<vector<double> > matrix(mSize, vector<double>(mSize, DBL_MAX));
            vector<vector<int> > paths(mSize, vector<int>(mSize, -1));

            for (int m = 0; m < mSize; ++m) {
                matrix[m][m] = 0.0;
                paths[m][m] = m;
            }

            for (int m = 1; m < mSize; ++m) {
                matrix[m][0] = 0.0;
                paths[m][0] = 0;
                paths[0][m] = m;
                if (!eventsWithFakes[m-1]) continue;
                if (eventsWithFakes[m-1]->isDummyStep()) {
                    matrix[m][0] = 0.0;
                    matrix[0][m] = DBL_MAX;
                    
                    if (noisy) cout << "Edge from " << m - 1 << " to time zero is 0.0, as it's a dummy preference-checking step\n";
                    
                } else if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_START) {
                    const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[eventsWithFakes[m-1]->action->getID()];
                    const double startMin = tsBounds[0].first;
                    const double startMax = tsBounds[0].second;

                    matrix[m][0] = -1 * startMin;
                    matrix[0][m] = startMax;
                    
                    if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -startMin << " due to earliest RPG start point of action\n";
                } else if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_END) {
                    const vector<pair<double, double> > & tsBounds = TemporalAnalysis::getActionTSBounds()[eventsWithFakes[m-1]->action->getID()];
                    const double endMin = tsBounds[1].first;
                    const double endMax = tsBounds[1].second;

                    matrix[m][0] = -1 * endMin;
                    matrix[0][m] = endMax;
                    if (noisy) cout << "Edge from " << m - 1 << " to time zero - " << -endMin << " due to earliest RPG end point of action\n";

                }
            }

            for (int m = 1; m < mSize; ++m) {
                if (!eventsWithFakes[m-1]) continue;

                if (pairWith[m-1] >= 0) {
                    if (eventsWithFakes[m-1]->time_spec == Planner::E_AT_START) {
                        matrix[m][pairWith[m-1] + 1] = eventsWithFakes[m-1]->maxDuration;
                        paths[m][pairWith[m-1] + 1] = pairWith[m-1] + 1;
                        if (noisy) cout << "Edge from " << m - 1 << " to " << pairWith[m-1] << " - " << eventsWithFakes[m-1]->maxDuration << " due to max duration" << endl;
                    } else {
                        matrix[m][pairWith[m-1] + 1] = -1 * eventsWithFakes[m-1]->minDuration;
                        paths[m][pairWith[m-1] + 1] = pairWith[m-1] + 1;
                        if (noisy) cout << "Edge from " << m - 1 << " to " << pairWith[m-1] << " - " << -eventsWithFakes[m-1]->minDuration << " due to min duration" << endl;
                    }
                } else if (pairWith[m-1] == -2) {
                    const double tilTime = LPScheduler::getTILTimestamp(eventsWithFakes[m-1]->divisionID);
                    matrix[0][m] = tilTime;
                    paths[0][m] = m;
                    matrix[m][0] = -1 * tilTime;
                    paths[m][0] = 0;
                }

                if (eventsWithFakes[m-1]->lpMinTimestamp != -1.0) {
                    const double backEdge = (eventsWithFakes[m-1]->lpMinTimestamp == 0.0 ? 0.0 : -(eventsWithFakes[m-1]->lpMinTimestamp));
                    if (backEdge < matrix[m][0]) {
                        matrix[m][0] = backEdge;
                        paths[m][0] = 0;
                        if (noisy) cout << "Changing edge from " << m - 1 << " to time zero - " << backEdge << " due to known minimum timestamp for action\n";
                    } else {
                        if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
                    }
                } else {
                    if (noisy) cout << "Not changing edge from " << m - 1 << " to time zero due to known minimum timestamp for action\n";
                }
            
                if (eventsWithFakes[m-1]->lpMaxTimestamp != -1.0) {
                    if (eventsWithFakes[m-1]->lpMaxTimestamp < matrix[0][m]) {
                        matrix[0][m] = eventsWithFakes[m-1]->lpMaxTimestamp;
                        paths[0][m] = m;
                        if (noisy) cout << "Changing edge from time zero to " << m - 1 << " to " << matrix[0][m] << " due to known maximum timestamp for action\n";
                    } else {
                        if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
                    }
                } else {
                    if (noisy) cout << "Not changing edge from time zero to " << m - 1 << " due to known maximum timestamp for action\n";
                }

                map<int, IncomingAndOutgoing>::const_iterator eItr = temporaryEdges.find(m - 1);
                if (eItr != temporaryEdges.end()) {
                    map<int, pair<bool,double> >::const_iterator pItr = eItr->second.mustPrecedeThis().begin();
                    const map<int, pair<bool,double> >::const_iterator pEnd = eItr->second.mustPrecedeThis().end();
                    double negatedValue;
                    for (; pItr != pEnd; ++pItr) {
                        negatedValue = (pItr->second.second == 0.0 ? 0.0 : -pItr->second.second);
                        if (negatedValue < matrix[m][pItr->first + 1]) {
                            matrix[m][pItr->first + 1] = negatedValue;
                            paths[m][pItr->first + 1] = pItr->first + 1;
                            if (noisy) cout << "Edge from " << m - 1 << " to " << pItr->first << " - " << negatedValue << " due to recorded outgoing edges" << endl;
                        }
                    }
                }
            }

            {
                map<int, double>::const_iterator aItr = autoMinima.begin();
                const map<int, double>::const_iterator aEnd = autoMinima.end();

                for (; aItr != aEnd; ++aItr) {
                    if (-aItr->second < matrix[aItr->first + 1][0]) {
                        matrix[aItr->first + 1][0] = -aItr->second;
                        paths[aItr->first + 1][0] = 0;
                        if (noisy) cout << "Edge from " << aItr->first << " to time zero, weight " << -aItr->second << " due to it having to follow after actions with known timestamps\n";
                    }
                }
            }

            int k, i, j;
            double distIK, distKJ;

            for (k = 0; k < mSize; ++k) {
                for (i = 0; i < mSize; ++i) {
                    distIK = matrix[i][k];
                    if (distIK == DBL_MAX) continue;
                    for (j = 0; j < mSize; ++j) {
                        distKJ = matrix[k][j];

                        if (distKJ != DBL_MAX) {
                            double & distIJ = matrix[i][j];
                            if ((distIK + distKJ) - distIJ < -0.00001) {
                                /*if (noisy) {
                                    cout << "Path from " << i-1 << " to " << j-1 << " is shorter via " << k-1 << endl;
                                    if (distIJ == DBL_MAX) {
                                        cout << "Was infinite, now " << distIK + distKJ << endl;
                                    } else {
                                        cout << "Was " << distIJ << ", now " << distIK + distKJ << endl;
                                    }
                                }*/
                                
                                distIJ = distIK + distKJ;
                                paths[i][j] = k;
                            }
                        }
                    }
                }
            }

            bool isOkay = true;

            for (int m = 0; m < mSize; ++m) {
                if (matrix[m][m] < 0.0) {
                    isOkay = false;
                }
            }

            if (isOkay) {
                bool matchup = true;
                for (int m = 1; m < mSize; ++m) {
                    if (!eventsWithFakes[m-1]) continue;
                    if (noisy) {
                        cout << std::setprecision(6) << (-1 * matrix[m][0]) << " vs " << -distToZero[m-1] << " - step " << m - 1 << " (" << eventsWithFakes[m-1]->lpMinTimestamp << ")" <<  endl;
                        if (fabs(fabs(distToZero[m-1]) - fabs(matrix[m][0])) >= 0.0005) {
                            cout << " - Path from " << (m-1) << " to time zero: ";
                            int previous = m;
                            int goTo = paths[m][0];        
                            cout << " to " << goTo - 1 << ", ";
                            while (goTo != previous) {
                                cout << matrix[previous][goTo];
                                previous = goTo;
                                goTo = paths[goTo][0];         
                                cout << "; to " << goTo - 1 << ", ";
                            }
                            cout << endl;
                        }
                    }
                    matchup = matchup && (fabs(fabs(distToZero[m-1]) - fabs(matrix[m][0])) < 0.0005);
                }
                assert(matchup);
                assert(pResult);
            } else {
                assert(!pResult);
            }

        }

        if (!pResult) {
            return false;
        }
    }

    newEdges.clear();

    if (checkSanity) sanityCheck();

    if (!cons) {
        return true;
    }

        
#ifdef SINGLEFACTWITHINSONLY
#define CANBEVIOLATEDHERE(x) {cerr << "Incorrectly think that preference " << RPGBuilder::getPreferences()[x].name << ":" << x << " cannot be satisfied in the STP.  Is in position " << positionName[previousPreferenceStatus[x]] << "\n"; assert(false); }
#else
#define CANBEVIOLATEDHERE(x) {}
#endif


    if (!RPGBuilder::getPreferences().empty()) {
        
        const int planSize = eventsWithFakes.size();
        
        preferencesWereAsExpected = true;
        
        double accruedPreferencePreconditionViolations = 0.0;
        
        const list<int> & withinPrefs = PreferenceHandler::getListOfWithinPreferences();
        const list<int> & sometimePrefs = PreferenceHandler::getListOfSometimePreferences();
        
        map<int,bool> satisfiedWithins;
        map<int,bool> satisfiedSometimes;
        
        {
            list<int>::const_iterator wiItr = withinPrefs.begin();           
            const list<int>::const_iterator wiEnd = withinPrefs.end();
            
            for (map<int,bool>::iterator insItr = satisfiedWithins.end(); wiItr != wiEnd; ++wiItr) {
                insItr = satisfiedWithins.insert(insItr, make_pair(*wiItr,false));
            }
        }
        
        {
            list<int>::const_iterator wiItr = sometimePrefs.begin();           
            const list<int>::const_iterator wiEnd = sometimePrefs.end();
            
            for (map<int,bool>::iterator insItr = satisfiedSometimes.end(); wiItr != wiEnd; ++wiItr) {
                insItr = satisfiedSometimes.insert(insItr, make_pair(*wiItr,false));
            }
        }
        
        map<int, map<int, double> > alwaysWithinOrSometimeAfterPrefOpenedAtStep; // if sometime-after a b, then dummies for b only re-satisfy the preference if ater an a
        
        map<int, map<int, double> > sometimeBeforePrefSatisfiedAtStep; // if sometime-before a b, then dummies for a need to come after dummies for b
        
        for (int p = 0; p < planSize; ++p) {
            if (!eventsWithFakes[p]) {
                continue;
            }
            switch (eventsWithFakes[p]->time_spec) {
                case Planner::E_CONTINUOUS: {
                    std::cerr << "Fatal internal error: uninitialised dummy step found when checking whether soft-edges are satisfied\n";
                    exit(1);
                    break;
                }
                case Planner::E_DUMMY_PREFERENCE_PRECONDITION: {
                    
                    bool edgesHold = true;
                                        
                    
                    if (softEdges[p] == -1) {
                        
                        // if the edges actually are soft
                        
                        const map<int, IncomingAndOutgoing>::const_iterator tseItr = temporarySoftEdges.find(p);
                        
                        if (tseItr != temporarySoftEdges.end()) {
                            // get the time step of the actual action event to which the preference is attached
                            // i.e. look at pair with step
                            const double negativeTimeOfStepWithPreference = distToZero[eventsWithFakes[p]->pairWithStep];
                            
                            edgesHold = allHold(tseItr->second, negativeTimeOfStepWithPreference, cons);                            
                        }
                        
                        
                    }
                    
                    if (!edgesHold) {
                        accruedPreferencePreconditionViolations += RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID].cost;
                    }
                    
                    
                    break;
                    
                }
                
                case Planner::E_DUMMY_TEMPORAL_GOAL_FALSE:
                case Planner::E_DUMMY_TEMPORAL_GOAL_TRUE: {

                    static const bool tgDebug = false;
                    
                    const AutomatonPosition::Position & currPosition = previousPreferenceStatus[eventsWithFakes[p]->divisionID];
                    if (currPosition == AutomatonPosition::unreachable || currPosition == AutomatonPosition::eternallysatisfied) {
                        if (tgDebug) {
                            cout << "Skipping update of goal of " << RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID].name << ":" << eventsWithFakes[p]->divisionID << " - is in position " << positionName[currPosition] << endl;
                        }
                        break;
                    }
                    
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID];                
                                        
                    bool edgesHold = true;
                    double dummyDistToZero = 0.0;
                    double dummyDistFromZero = DBL_MAX;
                    
                    if (softEdges[p] == -1) {
                        // if the edges actually are soft
                        
                        const map<int, IncomingAndOutgoing>::const_iterator tseItr = temporarySoftEdges.find(p);
                        
                        if (tseItr != temporarySoftEdges.end()) {
                            if (tgDebug) {
                                cout << "Updating goal of " << RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID].name << ":" << eventsWithFakes[p]->divisionID << " - checking edges into dummy step " << p << ")\n";
                            }
                            #ifndef NDEBUG
                            if (pref.cons == VAL::E_WITHIN) {
                                assert(tseItr->second.mustFollowThis().find(-1) != tseItr->second.mustFollowThis().end());
                            }
                            #endif
                            edgesHold = allHold(tseItr->second, cons, dummyDistToZero, dummyDistFromZero);
                        } else {
                            
                            assert(pref.cons != VAL::E_WITHIN); // withins should have at least edges from zero                            
                        } 
                        
                        
                    } else {
                        dummyDistToZero = distToZero[softEdges[p]];
                        dummyDistFromZero = distFromZero[softEdges[p]];
                        
                        if (tgDebug) {
                            cout << "Updating goal of " << RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID].name << ":" << eventsWithFakes[p]->divisionID << ", dummy dist to zero = " << dummyDistToZero << ", dummy dist from zero = " << dummyDistFromZero << endl;
                        }
                        
                    }
                     
                    assert(eventsWithFakes[p]->time_spec == Planner::E_DUMMY_TEMPORAL_GOAL_TRUE || pref.cons == VAL::E_ATMOSTONCE);
                    
                    if (!edgesHold) {
                        if (   pref.cons != VAL::E_SOMETIMEBEFORE && pref.cons != VAL::E_ALWAYSWITHIN && pref.cons != VAL::E_SOMETIMEAFTER
                            && pref.cons != VAL::E_SOMETIME && pref.cons != VAL::E_WITHIN) {
                            preferencesWereAsExpected = false;
                            CANBEVIOLATEDHERE(eventsWithFakes[p]->divisionID);
                            return true;
                        } else {
                            CANBEVIOLATEDHERE(eventsWithFakes[p]->divisionID);
                        }
                    } else {                        
                        if (pref.cons == VAL::E_SOMETIME) {
                            const map<int,bool>::iterator wiItr = satisfiedSometimes.find(eventsWithFakes[p]->divisionID);                            
                            assert(wiItr != satisfiedSometimes.end());
                            wiItr->second = true;
                        } else if (pref.cons == VAL::E_WITHIN) {
                            if (-pref.deadline <= dummyDistToZero) {                            
                                const map<int,bool>::iterator wiItr = satisfiedWithins.find(eventsWithFakes[p]->divisionID);                            
                                assert(wiItr != satisfiedWithins.end());
                                wiItr->second = true;
                            }
                        } else if (pref.cons == VAL::E_SOMETIMEBEFORE) {
                            
                            sometimeBeforePrefSatisfiedAtStep[eventsWithFakes[p]->divisionID].insert(make_pair(p,dummyDistToZero));
                            
                        } else if (pref.cons == VAL::E_ALWAYSWITHIN || pref.cons == VAL::E_SOMETIMEAFTER) {
                            // means we have the means of closing an always-within/sometime-after preference that was opened earlier
                            // see if it actually does so or not
                           
                            const map<int, map<int, double> >::iterator awItr = alwaysWithinOrSometimeAfterPrefOpenedAtStep.find(eventsWithFakes[p]->divisionID);
                            
                            if (awItr != alwaysWithinOrSometimeAfterPrefOpenedAtStep.end()) {
                                // then there is a trigger we could perhaps close
                                
                                map<int,double>::iterator stepItr = awItr->second.begin();
                                const map<int,double>::iterator stepEnd = awItr->second.end();
                                
                                while (stepItr != stepEnd) {
                                    if (dummyDistToZero <= stepItr->second // in both cases, it's only any good if the goal is at or after the trigger
                                        && (pref.cons == VAL::E_SOMETIMEAFTER || stepItr->second - pref.deadline <= dummyDistToZero) ) { // for always-within: finished on time
                                        const map<int,double>::iterator stepDel = stepItr++;
                                        awItr->second.erase(stepDel);
                                    } else {
                                        ++stepItr;
                                    }
                                }
                                
                                if (awItr->second.empty()) {                                
                                    alwaysWithinOrSometimeAfterPrefOpenedAtStep.erase(awItr);                                
                                }
                            }
                        }
                    }
                    
                    break;
                    
                }
                
                case Planner::E_DUMMY_TEMPORAL_TRIGGER_TRUE: {
                    
                    
                    const AutomatonPosition::Position & currPosition = previousPreferenceStatus[eventsWithFakes[p]->divisionID];
                    if (currPosition == AutomatonPosition::unreachable || currPosition == AutomatonPosition::eternallysatisfied) {
                        break;
                    }
                    
                    const RPGBuilder::Constraint & pref = RPGBuilder::getPreferences()[eventsWithFakes[p]->divisionID];                
                                        
                    bool edgesHold = true;
                    double dummyDistToZero = 0.0;
                    double dummyDistFromZero = DBL_MAX;
                    
                    if (pref.cons == VAL::E_ALWAYSWITHIN) {

                        dummyDistToZero = distToZero[eventsWithFakes[p]->pairWithStep];
                        dummyDistFromZero = distFromZero[eventsWithFakes[p]->pairWithStep];
                        
                    } else {
                    
                        if (softEdges[p] == -1) {
                            // if the edges actually are soft
                            
                            const map<int, IncomingAndOutgoing>::const_iterator tseItr = temporarySoftEdges.find(p);
                            
                            if (tseItr != temporarySoftEdges.end()) {
                                edgesHold = allHold(tseItr->second, cons, dummyDistToZero, dummyDistFromZero);
                            }
                        } else {
                            
                            dummyDistToZero = distToZero[softEdges[p]];
                            dummyDistFromZero = distFromZero[softEdges[p]];
                            
                        }
                        
                    }                    
                    
                    
                    if (!edgesHold) {
                        // its position in the timelines wasn't respected by accident
                        // give up and let the MIP thrash it out

                        preferencesWereAsExpected = false;
                        CANBEVIOLATEDHERE(eventsWithFakes[p]->divisionID);
                        return true;
                    }
                    
                    if (pref.cons == VAL::E_SOMETIMEBEFORE) {
                        
                        const map<int, map<int, double> >::iterator awItr = sometimeBeforePrefSatisfiedAtStep.find(eventsWithFakes[p]->divisionID);
                        
                        if (awItr != sometimeBeforePrefSatisfiedAtStep.end()) {
                            // then there is a requirement we are okay if we come after
                                                            
                            map<int,double>::iterator stepItr = awItr->second.begin();
                            const map<int,double>::iterator stepEnd = awItr->second.end();
                            
                            for (; stepItr != stepEnd; ++stepItr) {
                                if (dummyDistFromZero < stepItr->second) { // if this step comes after that - great
                                    break;
                                }
                            }
                            
                            if (stepItr == stepEnd) { // haven't come after an earlier goal match
                                preferencesWereAsExpected = false;
                                CANBEVIOLATEDHERE(eventsWithFakes[p]->divisionID);
                                return true;
                            }
                                
                        }
                        
                    } else if (pref.cons == VAL::E_ALWAYSWITHIN || pref.cons == VAL::E_SOMETIMEAFTER) {
                        
                        alwaysWithinOrSometimeAfterPrefOpenedAtStep[eventsWithFakes[p]->divisionID].insert(make_pair(p,dummyDistToZero));
                        
                    }
                    
                    break;
                    
                    
                    
                }
                
                default: {
                    assert(eventsWithFakes[p]->time_spec != Planner::E_DUMMY_TEMPORAL_TRIGGER_FALSE);
                    // is a real step, not a dummy preference-checking step
                }
                
            }
            
            
            
        }
        
        
        for (int pass = 0; pass < 2; ++pass) {
            const map<int,bool> & happened = (pass ? satisfiedWithins : satisfiedSometimes);
            map<int,bool>::const_iterator wiItr = happened.begin();
            const map<int,bool>::const_iterator wiEnd = happened.end();
            
            for (; wiItr != wiEnd; ++wiItr) {
                
                if (!wiItr->second) {
                    // an unsatisfied within preference - check if it was considered satisfied at all
                    
                    const AutomatonPosition::Position & currPosn = previousPreferenceStatus[wiItr->first];
                    
                    if (currPosn != AutomatonPosition::unsatisfied && currPosn != AutomatonPosition::unreachable) {
                        // nothing ever satisfied this preference in time, and the automaton position for it suggests it's satisfied
                        preferencesWereAsExpected = false;
                        CANBEVIOLATEDHERE(wiItr->first);
                        return true;
                    }
                    
                }
                
            }
        }
        
        {
            map<int, map<int, double> >::const_iterator awiItr =  alwaysWithinOrSometimeAfterPrefOpenedAtStep.begin();
            const map<int, map<int, double> >::const_iterator awiEnd =  alwaysWithinOrSometimeAfterPrefOpenedAtStep.end();
            
            for (; awiItr != awiEnd; ++awiItr) {
                const AutomatonPosition::Position & currPosn = previousPreferenceStatus[awiItr->first];
                
                if (currPosn == AutomatonPosition::eternallysatisfied || currPosn == AutomatonPosition::probablyeternallysatisfied || currPosn == AutomatonPosition::satisfied) {
                    preferencesWereAsExpected = false;
                    CANBEVIOLATEDHERE(awiItr->first);
                    return true;
                }
            }
            
            
        }
        
    }
    
    return true;
}

bool ChildData::updateLPMinTimestamp(const double & d, const int & stepID)
{
    double w = distToZero[stepID];
    if (w != 0) w = -w;
    if (d <= w) {
        if (Globals::globalVerbosity & 4096) {
            cout << COLOUR_light_red << "Post LP, not changing minimum timestamp of node " << stepID << ": is still " << w << COLOUR_default << endl;
        }
        return true;
    }

    if (Globals::globalVerbosity & 4096) {
        cout << COLOUR_light_red << "Post LP, setting minimum timestamp of node " << stepID << " to " << d << " rather than " << w << COLOUR_default << endl;
    }
    addNewEdge(BFEdge(-1, stepID, d, distFromZero[stepID]));
    static bool ignore;
    return propagateNewEdges(*((vector<AutomatonPosition::Position>*) 0), 0, ignore);
}



};
