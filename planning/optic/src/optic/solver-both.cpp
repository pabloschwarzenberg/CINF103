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

#include "solver-both.h"

#include "solver-clp.h"
#include "solver-cpx.h"

#include <sstream>

using std::ostringstream;

const bool debugBoth = false;

void readParams(char * argv[], const int & a)
{
    
}

MILPSolver * getNewSolver()
{
    MILPSolver * const toReturn = new MILPSolverBoth();
    return toReturn;
}

const double LPinfinity = COIN_DBL_MAX;



MILPSolverBoth::MILPSolverBoth()
    : solvers(debugBoth ? 4 : 2)
{
    solvers[0] = new MILPSolverCPX();
    solvers[1] = new MILPSolverCLP();
    if (debugBoth) {
        solvers[2] = new MILPSolverCPX();
        solvers[3] = new MILPSolverCLP();
    }
}

MILPSolverBoth::MILPSolverBoth(const MILPSolverBoth & c)
    : solvers(debugBoth ? 4 : 2)
{
    solvers[0] = c.solvers[0]->clone();
    solvers[1] = c.solvers[1]->clone();
    if (debugBoth) {
        solvers[2] = c.solvers[2]->clone();
        solvers[3] = c.solvers[3]->clone();
    }
}


MILPSolverBoth::~MILPSolverBoth()
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        delete solvers[s];
    }
}

MILPSolver * MILPSolverBoth::clone()
{
    return new MILPSolverBoth(*this);
}

double MILPSolverBoth::getInfinity()
{
    return COIN_DBL_MAX;
}

int MILPSolverBoth::getNumCols()
{
    const int toReturn = solvers[0]->getNumCols();
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            assert(solvers[s]->getNumCols() == toReturn);
        }
    }
    return toReturn;
}

int MILPSolverBoth::getNumRows()
{
    const int toReturn = solvers[0]->getNumRows();
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            assert(solvers[s]->getNumRows() == toReturn);
        }
    }
    return toReturn;
}

void MILPSolverBoth::setColName(const int & var, const string & asString)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->setColName(var,asString);
    }
}

string MILPSolverBoth::getColName(const int & var)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getColName(var);
    }
    return solvers[0]->getColName(var);
}

void MILPSolverBoth::setRowName(const int & cons, const string & asString)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->setRowName(cons, asString);
    }
}

string MILPSolverBoth::getRowName(const int & cons)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getRowName(cons);
    }
    return solvers[0]->getRowName(cons);
}

/*
void MILPSolverBoth::setInteger(const int & var)
{
    lp->setInteger(var);
}
*/

double MILPSolverBoth::getColUpper(const int & var)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getColUpper(var);
    }
    const double toReturn = solvers[0]->getColUpper(var);
    
    if (toReturn == solvers[0]->getInfinity()) {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(solvers[s]->getColUpper(var) == solvers[s]->getInfinity());
            }
        }
        return LPinfinity;
    } else {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(fabs(solvers[s]->getColUpper(var) - toReturn) < 0.0000001);
            }
        }
        return toReturn;
    }
}

void MILPSolverBoth::setColUpper(const int & var, const double & b)
{
    if (b == LPinfinity) {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setColUpper(var, solvers[s]->getInfinity());
        }                
    } else {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setColUpper(var, b);
        }
    }
}

double MILPSolverBoth::getRowUpper(const int & c)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getRowUpper(c);
    }
    const double toReturn = solvers[0]->getRowUpper(c);
    
    if (toReturn == solvers[0]->getInfinity()) {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(solvers[s]->getRowUpper(c) == solvers[s]->getInfinity());
            }
        }
        return LPinfinity;
    } else {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(fabs(solvers[s]->getRowUpper(c) - toReturn) < 0.0000001);
            }
        }
        return toReturn;
    }
}

void MILPSolverBoth::setRowUpper(const int & c, const double & b)
{
    if (b == LPinfinity) {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setRowUpper(c, solvers[s]->getInfinity());
        }                
    } else {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setRowUpper(c, b);
        }
    }
}

double MILPSolverBoth::getRowLower(const int & c)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getRowLower(c);
    }
    const double toReturn = solvers[0]->getRowLower(c);
    
    if (toReturn == -solvers[0]->getInfinity()) {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(solvers[s]->getRowLower(c) == -solvers[s]->getInfinity());
            }
        }
        return LPinfinity;
    } else {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(fabs(solvers[s]->getRowLower(c) - toReturn) < 0.0000001);
            }
        }
        return toReturn;
    }
}

void MILPSolverBoth::setRowLower(const int & c, const double & b)
{
    if (b == -LPinfinity) {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setRowLower(c, -solvers[s]->getInfinity());
        }
    } else {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setRowLower(c, b);
        }
    }
}

double MILPSolverBoth::getColLower(const int & var)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getColLower(var);
    }
    const double toReturn = solvers[0]->getColLower(var);
    
    if (toReturn == -solvers[0]->getInfinity()) {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(solvers[s]->getColLower(var) == -solvers[s]->getInfinity());
            }
        }
        return LPinfinity;
    } else {
        if (debugBoth) {
            for (unsigned int s = 1; s < solvers.size(); ++s) {
                assert(fabs(solvers[s]->getColLower(var) - toReturn) < 0.0000001);
            }
        }
        return toReturn;
    }
}

void MILPSolverBoth::setColLower(const int & var, const double & b)
{
    if (b == -LPinfinity) {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setColLower(var, -solvers[s]->getInfinity());
        }
    } else {
        for (unsigned int s = 0; s < solvers.size(); ++s) {
            solvers[s]->setColLower(var, b);
        }
    }
}

void MILPSolverBoth::setColBounds(const int & var, const double & lb, const double & ub)
{
    setColLower(var,lb);
    setColUpper(var,ub);
}

bool MILPSolverBoth::isColumnInteger(const int & c)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->isColumnInteger(c);
    }
    const bool toReturn = solvers[0]->isColumnInteger(c);
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            assert(solvers[s]->isColumnInteger(c) == toReturn);
        }
    }
    return toReturn;
}

bool MILPSolverBoth::isColumnBinary(const int & c)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->isColumnBinary(c);
    }
    const bool toReturn = solvers[0]->isColumnBinary(c);
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            assert(solvers[s]->isColumnBinary(c) == toReturn);
        }
    }
    return toReturn;
}

void MILPSolverBoth::addCol(const vector<pair<int,double> > & entries, const double & lb, const double & ub, const ColumnType & type)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        const double localLB = (lb == -LPinfinity ? -solvers[s]->getInfinity() : lb);
        const double localUB = (ub ==  LPinfinity ?  solvers[s]->getInfinity() : ub);
        solvers[s]->addCol(entries,localLB,localUB,type);        
    }
}

void MILPSolverBoth::addRow(const vector<pair<int,double> > & entries, const double & lb, const double & ub)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        const double localLB = (lb == -LPinfinity ? -solvers[s]->getInfinity() : lb);
        const double localUB = (ub ==  LPinfinity ?  solvers[s]->getInfinity() : ub);        
        solvers[s]->addRow(entries,localLB,localUB);        
    }    
}

void MILPSolverBoth::setMaximiseObjective(const bool & maxim)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->setMaximiseObjective(maxim);
    }
}

void MILPSolverBoth::setObjective(double * const entries)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->setObjective(entries);
    }
}

void MILPSolverBoth::clearObjective()
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->clearObjective();
    }
    
}
    

void MILPSolverBoth::setObjCoeff(const int & var, const double & w)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->setObjCoeff(var,w);
    }
}

void MILPSolverBoth::writeLp(const string & filename)
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        ostringstream fn;
        fn << "solver" << s << filename;
        string newfn = fn.str();
        solvers[s]->writeLp(newfn.c_str());
    }
}

bool MILPSolverBoth::solve(const bool & skipPresolve)
{
    if (!debugBoth) {
        const bool toReturn = solvers[0]->solve(skipPresolve);
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            solvers[s]->solve(skipPresolve);
        }
        return toReturn;
    }
    
    vector<MILPSolver*> backups(2);
    backups[0] = solvers[2]->clone();
    backups[1] = solvers[3]->clone();
    
    const bool toReturn = solvers[0]->solve(skipPresolve);
    bool fail = false;
    
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        if (solvers[s]->solve(skipPresolve) != toReturn) {
            std::cerr << "Solver " << s << " disagrees\n";
            fail = true;
        }
    }
    
    if (fail) {
        writeLp("failed.lp");
    }
    
    assert(!fail);
    
    delete solvers[2];
    delete solvers[3];
    
    solvers[2] = backups[0];
    solvers[3] = backups[1];
    
    return toReturn;
}

const double * MILPSolverBoth::getSolution()
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getSolution();
    }
    return solvers[0]->getSolution();
}

const double * MILPSolverBoth::getSolutionRows()
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getSolutionRows();
    }
    return solvers[0]->getSolutionRows();
}

const double * MILPSolverBoth::getPartialSolution(const int & from, const int & to)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getPartialSolution(from,to);
    }
    return solvers[0]->getPartialSolution(from, to);
}

double MILPSolverBoth::getSingleSolutionVariableValue(const int & col) {
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getSingleSolutionVariableValue(col);
    }
    return solvers[0]->getSingleSolutionVariableValue(col);
}

double MILPSolverBoth::getObjValue()
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        solvers[s]->getObjValue();
    }
    const double toReturn = solvers[0]->getObjValue();
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size() - 2; ++s) {
            assert(fabs(solvers[s]->getObjValue() - toReturn) < 0.0000001);
        }
    }
    return toReturn;
}

bool MILPSolverBoth::supportsQuadratic() const
{
    return true;
}


void MILPSolverBoth::hush()
{
    for (unsigned int s = 0; s < solvers.size(); ++s) {
        solvers[s]->hush();
    }
}

void MILPSolverBoth::getRow(const int & row, vector<pair<int,double> > & entries)
{
    for (unsigned int s = 1; s < solvers.size(); ++s) {
        vector<pair<int,double> > ignore;
        solvers[s]->getRow(row,ignore);
    }
    solvers[0]->getRow(row, entries);
    if (debugBoth) {
        for (unsigned int s = 1; s < solvers.size(); ++s) {
            vector<pair<int,double> > tmpEntries;
            solvers[s]->getRow(row, tmpEntries);
            
            assert(tmpEntries.size() == entries.size());
            
            map<int,double> tmpMap;
            tmpMap.insert(tmpEntries.begin(), tmpEntries.end());
            
            const int entSize = entries.size();
            
            for (int e = 0; e < entSize; ++e) {
                map<int,double>::const_iterator tItr = tmpMap.find(entries[e].first);
                assert(tItr != tmpMap.end());
                assert(fabs(tItr->second - entries[e].second) < 0.00000001);
            }
        }
    }
}
