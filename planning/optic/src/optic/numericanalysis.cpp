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

#include "numericanalysis.h"
#include "RPGBuilder.h"
#include "temporalanalysis.h"

#include "colours.h"
#include <fstream>
#include <sstream>
using std::cerr;
using std::endl;
using std::ifstream;
using std::ostringstream;

using namespace VAL;

namespace Planner {

bool NumericAnalysis::readBounds = false;
    
vector<NumericAnalysis::dominance_constraint> NumericAnalysis::dominanceConstraints;
vector<NumericAnalysis::order_independence> NumericAnalysis::allEffectsAreOrderIndependent;

#ifdef POPF3ANALYSIS

void NumericAnalysis::checkConditionalNumericEffectsAreOnlyOnMetricTrackingVariables()
{
    vector<list<RPGBuilder::ConditionalEffect> > & actionsToConditionalEffects = RPGBuilder::getEditableActionsToConditionalEffects();
    const int opCount = actionsToConditionalEffects.size();

    for (int op = 0; op < opCount; ++op) {
        if (RPGBuilder::rogueActions[op]) continue;

        list<RPGBuilder::ConditionalEffect>::iterator eff = actionsToConditionalEffects[op].begin();
        const list<RPGBuilder::ConditionalEffect>::iterator effEnd = actionsToConditionalEffects[op].end();

        while (eff != effEnd) {
            list<pair<int, Planner::time_spec> >::iterator numEff = eff->getEditableNumericEffects().begin();
            const list<pair<int, Planner::time_spec> >::iterator numEffEnd = eff->getEditableNumericEffects().end();

            while (numEff != numEffEnd) {                
                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[numEff->first];
                if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_METRICTRACKING) {
                    ++numEff;
                } else if (NumericAnalysis::getDominanceConstraints()[currEff.fluentIndex] == NumericAnalysis::E_IRRELEVANT) {
                    const list<pair<int, Planner::time_spec> >::iterator numDel = numEff++;
                    eff->getEditableNumericEffects().erase(numDel);
                } else {
                    postmortem_noADL();
                }
            }
            
            if (eff->getEditableNumericEffects().empty()) {
                const list<RPGBuilder::ConditionalEffect>::iterator effDel = eff++;
                actionsToConditionalEffects[op].erase(effDel);
            } else {
                ++eff;
            }
        }        
    }
}


bool NumericAnalysis::doGoalLimitAnalysis = true;

NumericAnalysis::dominance_constraint NumericAnalysis::preconditionDominanceInOneDirection(const int & varID, const map<int,list<int> > & numericPreconditionsThatAreInCondEffs)
{
    static const bool localDebug = (Globals::globalVerbosity & 16384);
    
    const vector<RPGBuilder::RPGNumericPrecondition> & rpgNumericPreconditions = RPGBuilder::getNumericPreTable();
    const vector<RPGBuilder::ArtificialVariable> & rpgArtificialVariables = RPGBuilder::getArtificialVariableTable();
    
    /* Index 0: true if bigger is better; Index 1: true if smaller is better */
    vector<bool> possibleAnswers(2,true);
    
    const int pneCount =  RPGBuilder::getPNECount();
    const int rnpCount = rpgNumericPreconditions.size();
    const int negativeI = varID + pneCount;
    
    for (int rnp = 0; rnp < rnpCount; ++rnp) {
        const RPGBuilder::RPGNumericPrecondition & currRNP = rpgNumericPreconditions[rnp];
        if (currRNP.LHSVariable == varID) {
            if (localDebug) {
                if (currRNP.desirable && currRNP.undesirable) {
                    cout << "Found a preference desirable and undesirable precondition on ";
                } else if (currRNP.desirable) {
                    cout << "Found a preference-desirable precondition on ";
                } else if (currRNP.undesirable) {
                    cout << "Found a preference-undesirable precondition on ";
                } else {
                    cout << "Found a precondition on ";
                }
                cout << *(RPGBuilder::getPNE(varID)) << ": " << currRNP << endl;
            }
            if (possibleAnswers[1]) {
                if (   requiringNotFullOnlySupportsReplenishment(rnp)
                    && preconditionOnlySupportsWorseMetricThanOtherOptions(rnp, numericPreconditionsThatAreInCondEffs)) {
                    
                    // do nothing in this case: v >= c just means we can either make v smaller again (with no gap)
                    // or that we can't have a metrically superior v < c option
                    if (localDebug) {
                        cout << "Precondition doesn't let us do better - ignoring it\n";
                    }
                } else {
                    // we have a precondition v > or >= c, which doesn't just support resource replenishment, so smaller isn't preferable
                    if (localDebug) {
                        cout << "That means that smaller values aren't preferable\n";
                    }
                    possibleAnswers[1] = false;
                    if (!possibleAnswers[0]) {
                        if (localDebug) {
                            cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                        }
                        return E_NODOMINANCE;
                    }
                }
            }
        } else if (currRNP.LHSVariable == negativeI) {
            if (localDebug) {
                if (currRNP.desirable && currRNP.undesirable) {
                    cout << "Found a preference desirable and undesirable precondition on ";
                } else if (currRNP.desirable) {
                    cout << "Found a preference-desirable precondition on ";
                } else if (currRNP.undesirable) {
                    cout << "Found a preference-undesirable precondition on ";
                } else {
                    cout << "Found a precondition on ";
                }
                cout << *(RPGBuilder::getPNE(varID)) << ": " << currRNP << endl;
            }

            if (possibleAnswers[0]) {
                if (   requiringNotFullOnlySupportsReplenishment(rnp)
                    && preconditionOnlySupportsWorseMetricThanOtherOptions(rnp, numericPreconditionsThatAreInCondEffs)) {
                    
                    // do nothing in this case: v <= c just means we can either make v bigger again (with no gap)
                    // or that we can't have a metrically superior v > c option
                    if (localDebug) {
                        cout << "Precondition doesn't let us do better - ignoring it\n";
                    }
                                        
                } else {
                // we have a precondition v < or <= c,  which doesn't just support resource replenishment, so bigger isn't preferable
                    possibleAnswers[0] = false;
                    if (localDebug) {
                        cout << "That means that bigger values aren't preferable\n";
                    }                    
                    if (!possibleAnswers[1]) {
                        if (localDebug) {
                            cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                        }
                        return E_NODOMINANCE;
                    }
                }
            }
        } else if (currRNP.LHSVariable >= 2 * pneCount) {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currRNP.LHSVariable);
            if (currAV.size == 1) {
                if (currAV.fluents[0] == varID) {
                    if (localDebug) {
                        if (currRNP.desirable && currRNP.undesirable) {
                            cout << "Found a preference desirable and undesirable precondition on ";
                        } else if (currRNP.desirable) {
                            cout << "Found a preference-desirable precondition on ";
                        } else if (currRNP.undesirable) {
                            cout << "Found a preference-undesirable precondition on ";
                        } else {
                            cout << "Found a precondition on ";
                        }
                        cout << *(RPGBuilder::getPNE(varID)) << ": " << currRNP << endl;
                    }
                    
                    if (possibleAnswers[1]) {
                        if (   requiringNotFullOnlySupportsReplenishment(rnp)
                            && preconditionOnlySupportsWorseMetricThanOtherOptions(rnp, numericPreconditionsThatAreInCondEffs)) {
                            if (localDebug) {
                                cout << "Precondition doesn't let us do better - ignoring it\n";
                            }

                        } else {
                            
                            // we have a precondition v > or >= c, which doesn't just support resource replenishment, so smaller isn't preferable
                            if (localDebug) {
                                cout << "That means that smaller values aren't preferable (case 2)\n";
                            }

                            possibleAnswers[1] = false;
                            if (!possibleAnswers[0]) {
                                if (localDebug) {
                                    cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                                }
                                return E_NODOMINANCE;
                            }
                        }
                    }                    
                } else if (currAV.fluents[0] == negativeI) {
                    if (localDebug) {
                        cout << "Found a precondition on " << *(RPGBuilder::getPNE(varID)) << ": " << currRNP << endl;
                    }
                    
                    if (possibleAnswers[0]) {
                        if (   requiringNotFullOnlySupportsReplenishment(rnp)
                            && preconditionOnlySupportsWorseMetricThanOtherOptions(rnp, numericPreconditionsThatAreInCondEffs)) {
                            if (localDebug) {
                                cout << "Precondition doesn't let us do better - ignoring it\n";
                            }

                        } else {
                            // we have a precondition v < or <= c,  which doesn't just support resource replenishment, so bigger isn't preferable
                            if (localDebug) {
                                cout << "That means that bigger values aren't preferable (case 2)\n";
                            }

                            possibleAnswers[0] = false;
                            if (!possibleAnswers[1]) {
                                if (localDebug) {
                                    cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                                }
                                return E_NODOMINANCE;
                            }
                        }
                    }                                        
                }
            }
        }
    }
    
    
    // next, check artificial variables - these are only ever used in preconditions of the form
    // av {>, >=} constant
    
    const int avCount = rpgArtificialVariables.size();
    for (int av = 0; av < avCount; ++av) {
        const RPGBuilder::ArtificialVariable & currAV = rpgArtificialVariables[av];
        const int avfSize = currAV.size;
        
        if (avfSize == 1) {
            if (currAV.fluents[0] == varID || currAV.fluents[0] == negativeI) {
                // is an AV on just the variable we're looking at
                // caught these cases in the for loop higher up
                continue;
            }            
        }
        
        for (int f = 0; f < avfSize; ++f) {
            const int currF = currAV.fluents[f];
            if (currF == varID) {
                if (localDebug) {
                    if (currAV.desirable && currAV.undesirable) {
                        cout << "Found a preference desirable and undesirable AV on ";
                    } else if (currAV.desirable) {
                        cout << "Found a preference-desirable AV on ";
                    } else if (currAV.undesirable) {
                        cout << "Found a preference-undesirable AV on ";
                    } else {
                        cout << "Found an AV on ";
                    }
                    cout << *(RPGBuilder::getPNE(varID)) << ": " << currAV << endl;
                }
                
                // we have a precondition v > or >= c, so smaller isn't preferable
                possibleAnswers[1] = false;
                if (!possibleAnswers[0]) {
                    if (localDebug) {
                        cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                    }
                    return E_NODOMINANCE;
                }
            } else if (currF == negativeI) {
                if (localDebug) {
                    if (currAV.desirable) {
                        cout << "Found a preference-desirable AV on ";
                    } else {
                        cout << "Found a preference-undesirable AV on ";
                    }
                    cout << *(RPGBuilder::getPNE(varID)) << ": " << currAV << endl;
                }
                                
                // we have a precondition v < or <= c, so bigger isn't preferable
                possibleAnswers[0] = false;
                if (!possibleAnswers[1]) {
                    if (localDebug) {
                        cout << COLOUR_light_cyan << "Cannot show any dominance on " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
                    }
                    return E_NODOMINANCE;
                }
            }
        }
    }                    
    
    // if we get this far, then there is dominance in the preconditions
    
    if (possibleAnswers[0] && possibleAnswers[1]) {
        //cout << "Fatal internal error: is good to have bigger and smaller values of " << *(RPGBuilder::getPNE(varID)) << endl;
        //assert(!(possibleAnswers[0] && possibleAnswers[1]));
        if (localDebug) {
            cout << COLOUR_light_cyan << "Shown irrelevance: " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
        }
        return E_IRRELEVANT;
    }
    
    if (possibleAnswers[0]) {
        if (localDebug) {
            cout << COLOUR_light_cyan << "Shown bigger is better for " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
        }
        return E_BIGGERISBETTER;
    }
    
    if (possibleAnswers[1]) {
        if (localDebug) {
            cout << COLOUR_light_cyan << "Shown smaller is better for " << *(RPGBuilder::getPNE(varID)) << COLOUR_default << endl;
        }

        return E_SMALLERISBETTER;
    }
    
    return E_NODOMINANCE;
}


VarOpConst::VarOpConst(const int & varIn, const double & bound, const VAL::comparison_op & isUpper) 
    : var(varIn), op(isUpper), constant(bound)
{
}

VarOpConst::VarOpConst(const RPGBuilder::RPGNumericPrecondition & rnp, bool & success)
    : var(rnp.LHSVariable), op(rnp.op), constant(rnp.RHSConstant) {           

    static const int pneCount = RPGBuilder::getPNECount();
        
    if (var >= 2 * pneCount) {
        const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(var);
        if (currAV.size != 1) {
            success = false;
            return;
        }
        var = currAV.fluents[0];
        constant -= currAV.constant;
                    
    }
    
    bool invertOp = false;
    
    if (var == -19) {
        invertOp = true;
        var = -3;
    } else if (var == -20) {
        invertOp = true;
        var = -4;
    } else if (var >= pneCount) {
        invertOp = true;
        var -= pneCount;
    }
    
    if (invertOp) {
        if (op == VAL::E_GREATER) {
            op = VAL::E_LESS;
        } else {
            assert(op == VAL::E_GREATEQ);
            op = VAL::E_LESSEQ;
        }
        
        if (constant != 0.0) {
            constant = -constant;
        }
    }

    success = true;
}
    
bool VarOpConst::implies(const VarOpConst & other) const {
    if (var != other.var) {
        return false;
    }
    
    if (   (op == VAL::E_GREATER || op == VAL::E_GREATEQ)
        && (other.op == VAL::E_LESS || other.op == VAL::E_LESSEQ)) {
        return false;
    }
    
    if (   (op == VAL::E_LESS || op == VAL::E_LESSEQ)
        && (other.op == VAL::E_GREATER || other.op == VAL::E_GREATEQ)) {
        
        return false;
    }

    switch (op) {
        case VAL::E_GREATEQ: {
            if (other.op == VAL::E_GREATEQ) {
                // v >= d implies v >= c
                // so long as d >= c
                return (constant >= other.constant);
            } else {
                // v >= d implies v > c
                // so long as d >= c + a small amount
                return (constant  >= other.constant + 0.00001);
            }
            break;
        }         
        case VAL::E_GREATER: {
            if (other.op == VAL::E_GREATER) {
                // v > d implies v > c
                // so long as d >= c
                return (constant >= other.constant);
            } else {
                // v > d implies v >= c
                // so long as d >= c
                return (constant >= other.constant);
            }
            break;
        }
        case VAL::E_LESSEQ: {
            if (other.op == VAL::E_LESSEQ) {
                // v <= d implies v <= c
                // so long as d <= c
                return (constant <= other.constant);
            } else {
                // v <= d implies v < c
                // so long as d <= c - a small amount
                return (constant >= other.constant - 0.00001);
            }
            break;
        }
        case VAL::E_LESS: {
            if (other.op == VAL::E_LESS) {
                // v < d implies v < c
                // so long as d <= c
                return (constant <= other.constant);
            } else {
                // v < d implies v <= c
                // so long as d <= c
                return (constant <= other.constant);
            }
            break;
        }
        default: {
            cerr << "Fatal internal error: the = precondition should have been pre-processed into a >=,<= pair\n";
            exit(1);
        }
    }

}
        
bool VarOpConst::isMutexWith(const VarOpConst & other) const {
    if (var != other.var) {
        return false;
    }
    
    if (   (op == VAL::E_GREATER || op == VAL::E_GREATEQ)
        && (other.op == VAL::E_GREATER || other.op == VAL::E_GREATEQ)) {
        return false;
    }
    
    if (   (op == VAL::E_LESS || op == VAL::E_LESSEQ)
        && (other.op == VAL::E_LESS || other.op == VAL::E_LESSEQ)) {
        return false;
    }
    
    switch (op) {
        case VAL::E_GREATEQ: {
            if (other.op == VAL::E_LESS) {
                // v >= d is mutex with v < c
                // so long as d >= c
                return (constant >= other.constant);
            } else {
                // v >= d is mutex with v <= c
                // so long as (d - a small amount) >= c
                return ((constant - 0.00001) >= other.constant);
            }
            break;
        }         
        case VAL::E_GREATER: {
            if (other.op == VAL::E_LESSEQ) {
                // v > d is mutex with v <= c
                // so long as d >= (c - a margin of error)
                return (constant >= other.constant);
            } else {
                // v > d is mutex with v < c
                // so long as (d - a small amount) >= c
                return ((constant - 0.00001) >= other.constant);
            }
            break;
        }
        case VAL::E_LESSEQ: {
            if (other.op == VAL::E_GREATER) {
                // v >= d is mutex with v < c
                // so long as d >= c
                return (other.constant >= constant);
            } else {
                // v >= d is mutex with v <= c
                // so long as (d - a small amount) >= c
                return ((other.constant - 0.00001) >= constant);
            }
            break;                
        }
        case VAL::E_LESS: {
            if (other.op == VAL::E_GREATEQ) {
                // v >= d is mutex with v < c
                // so long as d >= c
                return (other.constant >= constant);
            } else {
                // v >= d is mutex with v <= c
                // so long as (d - a small amount) >= c
                return ((other.constant - 0.00001) >= constant);
            }
            break;                
        }
        default: {
            cerr << "Fatal internal error: the = precondition should have been pre-processed into a >=,<= pair\n";
            exit(1);
        }
    }
}
    
bool VarOpConst::overlaps(const VarOpConst & other) const {
    assert(op == VAL::E_GREATER || op == VAL::E_GREATEQ); // only defined for this case
    
    if (op == VAL::E_GREATER) {
        if (other.op == VAL::E_LESSEQ) {
            
            // this has   v > c
            // other has  v <= d                
            // they can both be satisfied if c < d
            
            return (constant < other.constant);
        } else {
            
            // this has   v > c
            // other has  v < d                
            // they can both be satisfied if c < d
            return (constant < other.constant);
        }
    } else {            
        if (other.op == VAL::E_LESS) {
            // this has   v >= c
            // other has  v < d                
            // they can both be satisfied if c < d
            
            return (constant < other.constant);                
        } else {
            
            // this has   v >= c
            // other has  v <= d                
            // they can both be satisfied if c <= d 
            
            return (constant <= other.constant);
        }
    }
}
    
bool VarOpConst::operator >(const VarOpConst & other) const {
    assert(op == VAL::E_GREATER || op == VAL::E_GREATEQ); // only defined for this case
    
    if (op == VAL::E_GREATER) {
        if (other.op == VAL::E_LESSEQ) {
            
            // this has   v > c
            // other has  v <= d                
            // this is greater than if c >= d
            
            return (constant >= other.constant);
        } else {
            
            // this has   v > c
            // other has  v < d                
            // this is greater than if c >= d
            return (constant >= other.constant);
        }
    } else {            
        if (other.op == VAL::E_LESS) {
            // this has   v >= c
            // other has  v < d                
            // this is greater than if c >= d
            
            return (constant >= other.constant);                
        } else {
            
            // this has   v >= c
            // other has  v <= d                
            // this is greater if c > d
            
            return (constant > other.constant);
        }
    }
}
    
void VarOpConst::tighten(const VarOpConst & other) {
    switch (op) {
        case VAL::E_GREATEQ: {
            if (other.op == VAL::E_GREATEQ) {
                if (other.constant > constant) {
                    constant = other.constant;
                }
            } else {
                assert(other.op == VAL::E_GREATER);
                if (other.constant >= constant) {
                    op = VAL::E_GREATER;
                    constant = other.constant;
                }
            }
            break;
        }
        case VAL::E_GREATER: {
            if (other.op == VAL::E_GREATER) {
                if (other.constant > constant) {
                    constant = other.constant;
                }
            } else {
                assert(other.op == VAL::E_GREATEQ);
                if (other.constant > constant) {
                    op = VAL::E_GREATEQ;
                    constant = other.constant;
                }
            }
            break;
        }
        case VAL::E_LESSEQ: {
            if (other.op == VAL::E_LESSEQ) {
                if (other.constant < constant) {
                    constant = other.constant;
                }
            } else {
                assert(other.op == VAL::E_LESS);
                if (other.constant < constant) {
                    op = VAL::E_LESS;
                    constant = other.constant;
                }
            }
            break;
        }
        case VAL::E_LESS: {
            if (other.op == VAL::E_LESS) {
                if (other.constant < constant) {
                    constant = other.constant;
                }
            } else {
                assert(other.op == VAL::E_LESSEQ);
                if (other.constant < constant) {
                    op = VAL::E_LESSEQ;
                    constant = other.constant;
                }
            }
            break;
        }
    }
}

ostream & operator<<(ostream & o, const VarOpConst & masterPre) {
    if (masterPre.var == -3) {
        o << "?duration ";
    } else {
        o << *(RPGBuilder::getPNE(masterPre.var)) << " ";
    }
    switch (masterPre.op) {
        case VAL::E_GREATEQ: {
            o << ">= ";
            break;
        }
        case VAL::E_GREATER: {
            o << "> ";
            break;
        }
        case VAL::E_LESSEQ: {
            o << "<= ";
            break;
        }
        case VAL::E_LESS: {
            o << "< ";
            break;
        }                            
    }
    if (masterPre.constant == -DBL_MAX) {
        o << "-inf";
    } else if (masterPre.constant == DBL_MAX) {
        o << "inf";        
    } else {
        o << masterPre.constant;
    }
    return o;

}

void NumericAnalysis::MaskedVariableBounds::applyPreToBounds(const RPGBuilder::RPGNumericPrecondition & currPre)
{
    bool success = false;
    VarOpConst limit(currPre, success);
    if (success) {
        switch (limit.op) {
            case VAL::E_GREATEQ: {
                tightenLower(limit.var, limit.constant);
                break;
            }
            case VAL::E_GREATER: {
                tightenLower(limit.var, limit.constant);
                break;
            }
            case VAL::E_LESSEQ: {
                tightenUpper(limit.var, limit.constant);
                break;
            }
            case VAL::E_LESS: {
                tightenUpper(limit.var, limit.constant);
                break;
            }
        }
    }
}



struct ConditionBoundsAndOutcome {
    
        
    VarOpConst lb;
    VarOpConst ub;
    
    const RPGBuilder::ConditionalEffect* outcome;
    
    int fanIn;
    list<ConditionBoundsAndOutcome*> successors;
    
    ConditionBoundsAndOutcome(const RPGBuilder::ConditionalEffect* o, const VarOpConst & lbIn, const VarOpConst & ubIn )
        : lb(lbIn), ub(ubIn), outcome(o), fanIn(0) {
    }
    
    bool operator <(const ConditionBoundsAndOutcome & other) const {
        return (other.lb > ub);
    }
    
};

bool NumericAnalysis::couldIncreaseVariable(const RPGBuilder::RPGNumericEffect & eff, const MaskedVariableBounds & variableBounds)
{
    static const int pneCount = RPGBuilder::getPNECount();
    double maxEffect = eff.constant;
    
    for (int s = 0; s < eff.size; ++s) {
        int lVar = eff.variables[s];
        if (lVar < pneCount && lVar != -19) {

            if (variableBounds[lVar].second == DBL_MAX) {
                maxEffect = DBL_MAX;
                break;  
            }
            
            maxEffect += variableBounds[lVar].second * eff.weights[s];
            
        } else {

            if (lVar == -19) {
                lVar = -3;
            } else {
                lVar -= pneCount;
            }
            if (variableBounds[lVar].first == -DBL_MAX) {
                maxEffect = DBL_MAX;
                break;  
            }
            
            maxEffect -= variableBounds[lVar].first * eff.weights[s];
        }
        
    }
    
    if (eff.isAssignment) {
        return (maxEffect > variableBounds[eff.fluentIndex].first);
    }
    
    return (maxEffect > 0.00001);
    
}

bool NumericAnalysis::couldDecreaseVariable(const RPGBuilder::RPGNumericEffect & eff, const MaskedVariableBounds & variableBounds)
{
    static const bool localDebug = false;
    
    if (localDebug) {
        cout << "Effect starts as an increase by " << eff.constant << endl;
    }
    
    static const int pneCount = RPGBuilder::getPNECount();
    double maxEffect = eff.constant;
    
    for (int s = 0; s < eff.size; ++s) {
        int lVar = eff.variables[s];
        if (lVar < pneCount && lVar != -19) {

            if (variableBounds[lVar].first == -DBL_MAX) {
                maxEffect = -DBL_MAX;
                break;  
            }
            
            maxEffect += variableBounds[lVar].first * eff.weights[s];
                
        } else {
            
            if (lVar == -19) {
                lVar = -3;
            } else {
                lVar -= pneCount;
            }
            
            if (variableBounds[lVar].second == DBL_MAX) {
                if (localDebug) {
                    if (lVar == -3) {
                        cout << "Decrease by ?duration, with upper-unbounded ?duration\n";
                    } else {
                        cout << "Decrease by " << *(RPGBuilder::getPNE(lVar)) << ", which is upper-unbounded\n";
                    }
                }
                maxEffect = -DBL_MAX;
                break;  
            }
            
            maxEffect -= variableBounds[lVar].second * eff.weights[s];
            
            if (localDebug) {
                if (lVar == -3) {
                    cout << "Decrease by ?duration";
                } else {
                    cout << "Decrease by " << *(RPGBuilder::getPNE(lVar));
                }
                
                cout << "*" << eff.weights[s] << " = " << variableBounds[lVar].second << "*" << eff.weights[s] << " = " << variableBounds[lVar].second * eff.weights[s] << endl;
            }
                        
        }
    }
    
    if (eff.isAssignment) {
        return (maxEffect < variableBounds[eff.fluentIndex].second);
    }
    
    if (localDebug) {
        if (maxEffect < -0.00001) {
            cout << "Most decreasing-effect is negative\n";
        } else if (maxEffect > 0.00001) {
            cout << "Most decreasing-effect is positive\n";
        } else {
            cout << "Most decreasing-effect is zero\n";            
        }
    }
    
    return (maxEffect < -0.00001);
    
}

bool NumericAnalysis::couldBeWorseThan(const RPGBuilder::ConditionalEffect * a, const RPGBuilder::ConditionalEffect * b, const MaskedVariableBounds & variableBounds)
{
    typedef map<int, pair<const RPGBuilder::RPGNumericEffect*, const RPGBuilder::RPGNumericEffect*> > EffectMap;
 
    static const int pneCount = RPGBuilder::getPNECount();
    static const bool localDebug = false;
    
    EffectMap startEffectsByVar;
    EffectMap endEffectsByVar;
    
    MaskedVariableBounds aBounds(variableBounds);
    MaskedVariableBounds bBounds(variableBounds);
    
    
    for (int pass = 0; pass < 2; ++pass) {
        const RPGBuilder::ConditionalEffect * curr = (pass ? b : a);        
        if (!curr) {
            continue;
        }
        
        MaskedVariableBounds & currBounds = (pass ? bBounds : aBounds);
        {
            const list<pair<int, Planner::time_spec> > & numEffs = curr->getNumericEffects();
        
            list<pair<int, Planner::time_spec> >::const_iterator neItr = numEffs.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator neEnd = numEffs.end();
            
            for (; neItr != neEnd; ++neItr) {
                
                EffectMap & writeTo = (neItr->second == Planner::E_AT_START ? startEffectsByVar : endEffectsByVar);
                
                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[neItr->first];

                if (dominanceConstraints[currEff.fluentIndex] != E_METRICTRACKING) {
                    continue;
                }
                
                if (pass) {
                    writeTo.insert(make_pair(currEff.fluentIndex, pair<RPGBuilder::RPGNumericEffect*, RPGBuilder::RPGNumericEffect*>(0,0))).first->second.second = &currEff;
                } else {
                    writeTo.insert(make_pair(currEff.fluentIndex, pair<RPGBuilder::RPGNumericEffect*, RPGBuilder::RPGNumericEffect*>(0,0))).first->second.first = &currEff;
                }
                
            }
        }
        
        {
            const list<pair<int, Planner::time_spec> > & numPres = curr->getNumericPreconditions();
            
            list<pair<int, Planner::time_spec> >::const_iterator npItr = numPres.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numPres.end();
            
            for (; npItr != npEnd; ++npItr) {
                bool success = false;
                VarOpConst limit(RPGBuilder::getNumericPreTable()[npItr->first], success);
                if (success) {
                    switch (limit.op) {
                        case VAL::E_GREATEQ: {
                            currBounds.tightenLower(limit.var, limit.constant);
                            break;
                        }
                        case VAL::E_GREATER: {
                            currBounds.tightenLower(limit.var, limit.constant);
                            break;
                        }
                        case VAL::E_LESSEQ: {
                            currBounds.tightenUpper(limit.var, limit.constant);
                            break;
                        }
                        case VAL::E_LESS: {
                            currBounds.tightenUpper(limit.var, limit.constant);
                            break;
                        }
                    }
                }
            }
        }           
    }
    

    if (localDebug) {
        cout << "Comparing effects by variable:\n";
        for (int pass = 0; pass < 2; ++pass) {
            const EffectMap & lookIn = (pass ? startEffectsByVar : endEffectsByVar);
            
            EffectMap::const_iterator mItr = lookIn.begin();
            const EffectMap::const_iterator mEnd = lookIn.end();
            
            for (; mItr != mEnd; ++mItr) {
                
                cout << *(RPGBuilder::getPNE(mItr->first)) << ":\n";
                if (mItr->second.first) {
                    cout << "\ta: " <<  *(mItr->second.first) << endl;
                } else {
                    cout << "a: has no effect\n";
                } 
                if (mItr->second.second) {
                    cout << "\tb: " <<  *(mItr->second.second) << endl;
                } else {
                    cout << "b: has no effect\n";
                } 
            }
        }
    }
    
    for (int pass = 0; pass < 2; ++pass) {
        const EffectMap & lookIn = (pass ? startEffectsByVar : endEffectsByVar);
        
        EffectMap::const_iterator mItr = lookIn.begin();
        const EffectMap::const_iterator mEnd = lookIn.end();
        
        for (; mItr != mEnd; ++mItr) {
            const map<int,bool>::const_iterator mtStatus = metricVarIsBetterBigger.find(mItr->first);
            assert(mtStatus != metricVarIsBetterBigger.end());
            
            if (localDebug) {
                if (mtStatus->second) {
                    cout << "For the metric " << *(RPGBuilder::getPNE(mItr->first)) << " should be bigger\n";               
                } else {
                    cout << "For the metric " << *(RPGBuilder::getPNE(mItr->first)) << " should be smaller\n";
                }
            }
            
            
            if (mItr->second.first && !mItr->second.second) {
                
                // a affects this variable, b doesn't
                
                if (mtStatus->second) {
                    if (couldDecreaseVariable(*mItr->second.first, aBounds)) {
                        // the variable is better to be bigger, but a could decrease it
                        // therefore, a could be worse than b
                        if (localDebug) {
                            cout << "+ a could be worse than b, as a could decrease " << *(RPGBuilder::getPNE(mItr->first)) << " and b has no effect on it\n";
                        }
                        return true;
                    }
                } else {
                    if (couldIncreaseVariable(*mItr->second.first, aBounds)) {
                        // the variable is better to be smaller, but a could increase it
                        // therefore, a could be worse than b
                        if (localDebug) {
                            cout << "+ a could be worse than b, as a could increase " << *(RPGBuilder::getPNE(mItr->first)) << " and b has no effect on it\n";
                        }
                                                                        
                        return true;
                    }
                }
                
            } else if (!mItr->second.first && mItr->second.second) {
                
                // b affects this variable, a doesn't
                
                if (mtStatus->second) {
                    if (couldIncreaseVariable(*mItr->second.second, bBounds)) {
                        // the variable is better to be bigger, and b could increase it
                        // whereas a cannot; therefore, a could be worse than b
                        if (localDebug) {
                            cout << "+ a could be worse than b, as b could increase " << *(RPGBuilder::getPNE(mItr->first)) << " and a has no effect on it\n";
                        }
                        return true;
                                                                        
                    }
                } else {
                    if (couldDecreaseVariable(*mItr->second.second, bBounds)) {
                        // the variable is better to be smaller, and b could decrease it
                        // whereas a cannot; therefore, a could be worse than b
                        if (localDebug) {
                            cout << "+ a could be worse than b, as b could decrease " << *(RPGBuilder::getPNE(mItr->first)) << " and a has no effect on it\n";
                        }                        
                        return true;
                    }
                }
                
                
            } else {
                
                // check either both assignments, or neither assignments
                
                if (mItr->second.first->isAssignment && !mItr->second.second->isAssignment) {                    
                    // could maybe be worse - hard to tell
                    if (localDebug) {
                        cout << "+ maybe worse: mixed assignment-and-not\n";
                    }
                    return true;
                }
                
                if (!mItr->second.first->isAssignment && mItr->second.second->isAssignment) {
                    // could maybe be worse - hard to tell
                    if (localDebug) {
                        cout << "+ maybe worse: mixed assignment-and-not\n";
                    }                                                        
                    return true;
                }
                
                // both affect - need to work out the difference in effects as a weighted sum
                
                map<int,pair<double,double> > varToWeightAB;
                
                {
                    const RPGBuilder::RPGNumericEffect & eff =  *(mItr->second.first);
                    
                    for (int s = 0; s < eff.size; ++s) {
                        int lVar = eff.variables[s];
                        
                        if (lVar == -3) {
                            varToWeightAB.insert(make_pair(-3, make_pair(eff.weights[s],0.0)));
                        } else if (lVar == -19) {
                            varToWeightAB.insert(make_pair(-3, make_pair(-eff.weights[s],0.0)));
                        } else {
                            assert(lVar >= 0);
                            
                            if (lVar < pneCount) {
                                varToWeightAB.insert(make_pair(lVar, make_pair(eff.weights[s],0.0)));
                            } else {
                                varToWeightAB.insert(make_pair(lVar - pneCount, make_pair(-eff.weights[s],0.0)));
                            }
                        }
                    }
                }
                
                {
                    const RPGBuilder::RPGNumericEffect & eff =  *(mItr->second.second);
                    
                    for (int s = 0; s < eff.size; ++s) {
                        int lVar = eff.variables[s];
                        
                        if (lVar == -3) {
                            varToWeightAB.insert(make_pair(-3, make_pair(0.0,0.0))).first->second.second = eff.weights[s];
                        } else if (lVar == -19) {
                            varToWeightAB.insert(make_pair(-3,  make_pair(0.0,0.0))).first->second.second = -eff.weights[s];
                        } else {
                            assert(lVar >= 0);
                            
                            if (lVar < pneCount) {
                                varToWeightAB.insert(make_pair(lVar, make_pair(0.0,0.0))).first->second.second = eff.weights[s];
                            } else {
                                varToWeightAB.insert(make_pair(lVar - pneCount, make_pair(0.0,0.0))).first->second.second = -eff.weights[s];
                            }
                        }
                    }
                }

                if (varToWeightAB.size() > 1) {
                    if (localDebug) {
                        cout << "+ maybe worse: effect on " << *(RPGBuilder::getPNE(mItr->first)) << " involves " << varToWeightAB.size() << " variables\n";
                    }
                    
                    return true;
                }
                    
                if (mtStatus->second) {
                    
                    // the var is better to be bigger
                    // to find if a could be worse than b, we try to see if the bounds on the outcome from a
                    // are definitely better than those from b

                    // for now, we only cope with single variables here
                    
                    double aImprovementOverB = mItr->second.first->constant - mItr->second.second->constant;

                    if (!varToWeightAB.empty()) {
                        map<int,pair<double,double> >::const_iterator vwItr = varToWeightAB.begin();

                        // give A the least possible effect and B the greatest possible
                        
                        double aInput = 0.0;
                        double aWeight = fabs(vwItr->second.first);
                        if (vwItr->second.first > 0.0) {
                            aInput = aBounds[vwItr->first].first;
                        } else if (vwItr->second.first < 0.0) {
                            if (aBounds[vwItr->first].second != 0.0) {
                                aInput = -aBounds[vwItr->first].second;
                            }
                        }
                        
                        double bInput = 0.0;
                        double bWeight = fabs(vwItr->second.second);
                        if (vwItr->second.second > 0.0) {
                            bInput = bBounds[vwItr->first].second;
                        } else if (vwItr->second.second < 0.0) {
                            if (bBounds[vwItr->first].first != 0.0) {
                                bInput = -bBounds[vwItr->first].first;
                            }
                        }
                        
                        // if anything hits infinity, bail out
                        if (aInput == -DBL_MAX || aInput == DBL_MAX) {
                            return true;
                        }
                        
                        // if anything hits infinity, bail out
                        if (bInput == -DBL_MAX || bInput == DBL_MAX) {
                            return true;
                        }
                        
                        // now have definitely finite bounds                                                
                        aImprovementOverB += (aWeight * aInput) - (bWeight * bInput);
                        
                        
                    }
                    
                    if (aImprovementOverB < 0.001) {
                        if (localDebug) {
                            cout << "+ returning true - var should be bigger and improvement of a over b is = " << aImprovementOverB << endl;
                        }
                        return true;
                    }
                    
                } else {
                    // the var is better to be smaller
                    // to find if a could be worse than b, we try to see if the bounds on the outcome from a
                    // are definitely better than those from b

                    // for now, we only cope with single variables here
                    
                    double aCostIncreaseOverB = mItr->second.first->constant - mItr->second.second->constant;

                    if (!varToWeightAB.empty()) {
                        map<int,pair<double,double> >::const_iterator vwItr = varToWeightAB.begin();

                        // give A the greatest possible effect and B the least possible
                        
                        double aInput = 0.0;
                        double aWeight = fabs(vwItr->second.first);
                        if (vwItr->second.first > 0.0) {
                            aInput = aBounds[vwItr->first].second;
                        } else if (vwItr->second.first < 0.0) {
                            if (aBounds[vwItr->first].first != 0.0) {
                                aInput = -aBounds[vwItr->first].first;
                            }
                        }
                        
                        double bInput = 0.0;
                        double bWeight = fabs(vwItr->second.second);
                        if (vwItr->second.second > 0.0) {
                            bInput = bBounds[vwItr->first].first;
                        } else if (vwItr->second.second < 0.0) {
                            if (bBounds[vwItr->first].second != 0.0) {
                                bInput = -bBounds[vwItr->first].second;
                            }
                        }
                        
                        // if anything hits infinity, bail out
                        if (aInput == -DBL_MAX || aInput == DBL_MAX) {
                            return true;
                        }
                        
                        // if anything hits infinity, bail out
                        if (bInput == -DBL_MAX || bInput == DBL_MAX) {
                            return true;
                        }
                        
                        // now have definitely finite bounds
                        
                        aCostIncreaseOverB += (aWeight * aInput) - (bWeight * bInput);
                        
                        
                    }
                    
                    if (aCostIncreaseOverB > 0.001) {
                        if (localDebug) {
                            cout << "+ returning true - var should be smaller and saving of a over b is = " << aCostIncreaseOverB << endl;
                        }
                        return true;
                    }
                    
                }
                
            }

        }
    }
    
    return false;
    
}

bool NumericAnalysis::preconditionOnlySupportsWorseMetricThanOtherOptions(const int & preID,
                                                                          const map<int, list<int> > & numericPreconditionsThatAreInCondEffs)
{
    // This assumes that 'requiringNotFullOnlySupportsReplenishment' has already been called, to check that
    // the precondition isn't a goal, and its behaviour within preconditions (rather than conditional
    // effect conditions) means that having the precondition satisfied is not in itself a good idea.
    // Here, we just look at conditional effects.
    
    static const bool localDebug = (Globals::globalVerbosity & 16384);
    
    const map<int, list<int> >::const_iterator mapItr = numericPreconditionsThatAreInCondEffs.find(preID);
    if (mapItr == numericPreconditionsThatAreInCondEffs.end()) {
        // this pre isn't in any conditional effects
        return true;
    }

    if (localDebug) {
        cout << "Looking at conditional effects that depend on " << RPGBuilder::getNumericPreTable()[preID] << endl;
    }
    
    
    bool masterIsSingleVar = false;
    
    VarOpConst masterPre(RPGBuilder::getNumericPreTable()[preID], masterIsSingleVar);
    
    if (!masterIsSingleVar) {
        // multi-variable numeric precondition - give up for now on trying to analyse if it's a range of options        
        if (localDebug) {
            cout << "- Depends on multiple variables, pessimistically giving up\n";
        }
        
        return false;        
    }
    
    if (localDebug) {
        cout << "Writing precondition as " << masterPre << endl;
    }
    
    const int masterVar = masterPre.var;
    
    // Short-circuit check for tautologous pres.  Rationale: if a pre is tautologous, it's always true,
    // so the dominance of making it 'more true' doesn't make any sense - it really doesn't matter.
    
    switch (masterPre.op) {
        case VAL::E_GREATEQ: {
            if (masterVariableBounds[masterPre.var].first >= masterPre.constant) {
                if (localDebug) {
                    cout << "- Precondition is tautologous\n";
                }                
                return true;
            }
            break;
        }
        case VAL::E_GREATER: {
            if (masterVariableBounds[masterPre.var].first > masterPre.constant) {
                if (localDebug) {
                    cout << "- Precondition is tautologous\n";
                }                                
                return true;
            }
            break;
        }
        case VAL::E_LESSEQ: {
            if (masterVariableBounds[masterPre.var].second <= masterPre.constant) {
                if (localDebug) {
                    cout << "- Precondition is tautologous\n";
                }                                
                return true;
            }
            break;
        }
        case VAL::E_LESS: {
            if (masterVariableBounds[masterPre.var].second < masterPre.constant) {
                if (localDebug) {
                    cout << "- Precondition is tautologous\n";
                }                                
                return true;
            }
            break;
        }
    };
        
    
    list<int>::const_iterator actItr = mapItr->second.begin();
    const list<int>::const_iterator actEnd = mapItr->second.end();
    
    for (; actItr != actEnd; ++actItr) {
        if (localDebug) {
            cout << "* Looking at cond effs of " << *(RPGBuilder::getInstantiatedOp(*actItr)) << endl;
        }                
        
        const list<RPGBuilder::ConditionalEffect> & condEffs = RPGBuilder::getActionsToConditionalEffects()[*actItr];
        

        MaskedVariableBounds actBounds;
        
        for (int pass = 0; pass < 2; ++pass) {
            const list<int> & actPres = (pass ? RPGBuilder::getEndPreNumerics()[*actItr]
                                              : RPGBuilder::getStartPreNumerics()[*actItr]);
            
            list<int>::const_iterator apItr = actPres.begin();
            const list<int>::const_iterator apEnd = actPres.end();
            
            for (; apItr != apEnd; ++apItr) {
                bool thisPreCouldBeBuilt = false;
                VarOpConst currPre(RPGBuilder::getNumericPreTable()[*apItr], thisPreCouldBeBuilt);
                
                if (thisPreCouldBeBuilt) {
                    if (currPre.op == VAL::E_GREATER || currPre.op == VAL::E_GREATEQ) {
                        actBounds.tightenLower(currPre.var, currPre.constant);
                    } else {
                        actBounds.tightenUpper(currPre.var, currPre.constant);
                    }
                }
            }
        }
                
        const VarOpConst lbPre(masterPre.var, actBounds[masterPre.var].first, VAL::E_GREATEQ);
        const VarOpConst ubPre(masterPre.var, actBounds[masterPre.var].second, VAL::E_LESSEQ);

        // see if we can put the effects on a continuum based on the variable in this pre
        
        // first, find the cond effs with this pre ID in it
                        
        
        list<ConditionBoundsAndOutcome> condEffsWithThisPre;
        list<ConditionBoundsAndOutcome> condEffsWithoutThisPre;
        
        const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs.end();
        
        list<RPGBuilder::ConditionalEffect>::const_iterator thisCondEff = condEffs.begin();

        bool seenAtStart = false;
        bool seenAtEnd = false;
        
        
        for (; thisCondEff != ceEnd; ++thisCondEff) {
            bool hasThisPre = false;
            
            ConditionBoundsAndOutcome segment(&(*thisCondEff), lbPre, ubPre);
            
            {
                list<pair<int, Planner::time_spec> >::const_iterator npItr = thisCondEff->getNumericPreconditions().begin();
                const list<pair<int, Planner::time_spec> >::const_iterator npEnd = thisCondEff->getNumericPreconditions().end();
                
                for (; npItr != npEnd; ++npItr) {
                    if (npItr->first == preID) {
                        hasThisPre = true;
                    }

                    seenAtStart = seenAtStart || (npItr->second == Planner::E_AT_START);
                    seenAtEnd = seenAtEnd || (npItr->second == Planner::E_AT_END);
                    
                    bool thisPreCouldBeBuilt = false;
                    VarOpConst currPre(RPGBuilder::getNumericPreTable()[npItr->first], thisPreCouldBeBuilt);
                    
                    if (thisPreCouldBeBuilt) {
                        if (currPre.var == masterPre.var) {
                            
                            if (currPre.op == VAL::E_GREATER || currPre.op == VAL::E_GREATEQ) {
                                segment.lb.tighten(currPre);
                            } else {
                                segment.ub.tighten(currPre);
                            }
                        }
                    }
                }
            }

            {
                list<pair<int, Planner::time_spec> >::const_iterator neItr = thisCondEff->getNumericEffects().begin();
                const list<pair<int, Planner::time_spec> >::const_iterator neEnd = thisCondEff->getNumericEffects().end();
                
                for (; neItr != neEnd; ++neItr) {
                    seenAtStart = seenAtStart || (neItr->second == Planner::E_AT_START);
                    seenAtEnd = seenAtEnd || (neItr->second == Planner::E_AT_END);
                }
            }
            
            if (hasThisPre) {
                condEffsWithThisPre.push_back(segment);
            } else {
                condEffsWithoutThisPre.push_back(segment);
            }
        }
        
        assert(!condEffsWithThisPre.empty()); // should definitely have been found somewhere
        
        if (condEffsWithThisPre.size() != 1) {
            // give up for now - we just assume there's a single continuum of outcomes
            // rather than several based on other pres too
            if (localDebug) {
                cout << " > Multiple conditions refer to this pre, giving up for now\n";
            }                            
            return false;
        }
        
        if (seenAtStart && seenAtEnd) {
            // give up for now if all the comparisons to this var aren't just at either the start or end of an action
            // maybe at some point do something more clever?
            if (localDebug) {
                cout << " > Condition has conditions at the start and the end, giving up for now\n";
            }                
            return false;
        }

        
        
        
        const RPGBuilder::ConditionalEffect* const withPre = condEffsWithThisPre.front().outcome;

        list<ConditionBoundsAndOutcome*> continuum;
        
        set<pair<Literal*, Planner::time_spec> > presWeKnowFromTheMasterCond;
        set<pair<int, Planner::time_spec> > numericPresWeKnowFromTheMasterCond;
        
        presWeKnowFromTheMasterCond.insert(withPre->getPropositionalConditions().begin(), withPre->getPropositionalConditions().end());
        
        {
            // for numerics, exclude anything depending on the current var
            list<pair<int, Planner::time_spec> >::const_iterator npItr = withPre->getNumericPreconditions().begin();
            const list<pair<int, Planner::time_spec> >::const_iterator npEnd = withPre->getNumericPreconditions().end();
            
            for (; npItr != npEnd; ++npItr) {
                bool thisPreCouldBeBuilt = false;
                VarOpConst currPre(RPGBuilder::getNumericPreTable()[npItr->first], thisPreCouldBeBuilt);
                
                if (thisPreCouldBeBuilt && currPre.var == masterPre.var) {
                    continue;
                }
                
                numericPresWeKnowFromTheMasterCond.insert(*npItr);
            }
            
        }

        if (localDebug) {
            cout << "    : Looping over outcomes:";
            cout.flush();
        }
        list<ConditionBoundsAndOutcome>::iterator ocItr = condEffsWithoutThisPre.begin();
        const list<ConditionBoundsAndOutcome>::iterator ocEnd = condEffsWithoutThisPre.end();
        
        for (; ocItr != ocEnd; ++ocItr) {
            if (localDebug) {
                cout << ".";
                cout.flush();
            }
            {
                set<pair<Literal*, Planner::time_spec> > presFromThisOutcome(ocItr->outcome->getPropositionalConditions().begin(), ocItr->outcome->getPropositionalConditions().end());
                
                set<pair<Literal*, Planner::time_spec> > notCovered;
                
                std::set_difference(presFromThisOutcome.begin(), presFromThisOutcome.end(), presWeKnowFromTheMasterCond.begin(), presWeKnowFromTheMasterCond.end(),
                                    std::insert_iterator<set<pair<Literal*, Planner::time_spec> > >(notCovered, notCovered.begin()));
                                    
                if (!notCovered.empty()) {
                    // an alternative outcome couldn't definitely fire if the conditions on the outcome
                    // containing 'preID' were satisfied
                    if (localDebug) {
                        cout << "   > One of the other outcomes has propositional preconditions not covered by those attached to the outcome under scrutiny\n";
                    }
                    return false;
                }
                                    
            }
            
            {
                set<pair<int, Planner::time_spec> > numericPresFromThisOutcome;
                
                list<pair<int, Planner::time_spec> >::const_iterator npItr = ocItr->outcome->getNumericPreconditions().begin();
                const list<pair<int, Planner::time_spec> >::const_iterator npEnd = ocItr->outcome->getNumericPreconditions().end();
                
                for (; npItr != npEnd; ++npItr) {
                    bool thisPreCouldBeBuilt = false;
                    VarOpConst currPre(RPGBuilder::getNumericPreTable()[npItr->first], thisPreCouldBeBuilt);
                    
                    if (thisPreCouldBeBuilt && currPre.var == masterPre.var) {
                        continue;
                    }
                                    
                    numericPresFromThisOutcome.insert(*npItr);
                }
                
                set<pair<int, Planner::time_spec> > notCovered;
                
                std::set_difference(numericPresFromThisOutcome.begin(), numericPresFromThisOutcome.end(), numericPresWeKnowFromTheMasterCond.begin(), numericPresWeKnowFromTheMasterCond.end(),
                                    std::insert_iterator<set<pair<int, Planner::time_spec> > >(notCovered, notCovered.begin()));
                                    
                if (!notCovered.empty()) {
                    // an alternative outcome couldn't definitely fire if the conditions on the outcome
                    // containing 'preID' were satisfied
                    if (localDebug) {
                        cout << "   > One of the other outcomes has numeric preconditions not covered by those attached to the outcome under scrutiny\n";
                    }

                    return false;
                }
            }

            if (condEffsWithThisPre.front() < *ocItr) {
                condEffsWithThisPre.front().successors.push_back(&(*ocItr));
                ++(ocItr->fanIn);
            }

            if (*ocItr < condEffsWithThisPre.front()) {
                ocItr->successors.push_back(&(condEffsWithThisPre.front()));
                ++(condEffsWithThisPre.front().fanIn);
            }
                        
                                    
        
            list<ConditionBoundsAndOutcome>::iterator oc2Itr = condEffsWithoutThisPre.begin();
                
            for (; oc2Itr != ocItr; ++oc2Itr) {
                if (*oc2Itr < *ocItr) {
                    oc2Itr->successors.push_back(&(*ocItr));
                    ++(ocItr->fanIn);
                }                                
                if (*ocItr < *oc2Itr) {
                    ocItr->successors.push_back(&(*oc2Itr));
                    ++(oc2Itr->fanIn);
                }
            }
        }
        
        {
            ConditionBoundsAndOutcome * visitFirst = 0;
            
            if (condEffsWithThisPre.front().fanIn == 0) {
                visitFirst = &(condEffsWithThisPre.front());
            }
            
            list<ConditionBoundsAndOutcome>::iterator ocItr = condEffsWithoutThisPre.begin();
            const list<ConditionBoundsAndOutcome>::iterator ocEnd = condEffsWithoutThisPre.end();
            
            for (; ocItr != ocEnd; ++ocItr) {
                if (ocItr->fanIn == 0) {
                    if (visitFirst) {
                        // multiple possibly concurrent points on the continuum
                        return false;
                    }
                    visitFirst = &(*ocItr);
                }
            }
            
            while (visitFirst) {
                continuum.push_back(visitFirst);
                
                ConditionBoundsAndOutcome * visitNext = 0;
                
                list<ConditionBoundsAndOutcome*>::const_iterator succItr = visitFirst->successors.begin();
                const list<ConditionBoundsAndOutcome*>::const_iterator succEnd = visitFirst->successors.end();
                
                for (; succItr != succEnd; ++succItr) {
                    if ((--((*succItr)->fanIn)) == 0) {
                        if (visitNext) {
                            // multiple possibly concurrent points on the continuum
                            return false;
                        }
                        visitNext = *succItr;
                    }
                }
                
                visitFirst = visitNext;
            }
            
            if (continuum.size() != condEffsWithoutThisPre.size() + condEffsWithThisPre.size()) {
                // cylical ordering
                return false;
            }
        }
                
        // continuum now contains the outcomes, sorted according to the var in preID
        
        // add a dummy entry at each end if the range on the var doesn't totally contain its bounds

        auto_ptr<ConditionBoundsAndOutcome> lbTmp(0);
        auto_ptr<ConditionBoundsAndOutcome> ubTmp(0);
                
                
        
        {
            const ConditionBoundsAndOutcome & lowest = *(continuum.front());
            
            if (lowest.lb.op == VAL::E_GREATEQ) {
                if (lowest.lb.constant > actBounds[masterVar].first) {
                    lbTmp = auto_ptr<ConditionBoundsAndOutcome>(
                         new ConditionBoundsAndOutcome(0, lbPre, VarOpConst(masterVar, lowest.lb.constant, VAL::E_LESS)));
                    continuum.push_front(lbTmp.get());
                }
            } else {
                assert(lowest.lb.op == VAL::E_GREATER);
                if (lowest.lb.constant >= actBounds[masterVar].first) {
                    lbTmp = auto_ptr<ConditionBoundsAndOutcome>(
                        new ConditionBoundsAndOutcome(0, lbPre, VarOpConst(masterVar, lowest.lb.constant, VAL::E_LESSEQ)));
                    continuum.push_front(lbTmp.get());
                }
            }            
        }
        
        {
            const ConditionBoundsAndOutcome & highest = *(continuum.back());
            
            if (highest.ub.op == VAL::E_LESSEQ) {
                if (highest.ub.constant < actBounds[masterVar].second) {
                    ubTmp = auto_ptr<ConditionBoundsAndOutcome>(
                        new ConditionBoundsAndOutcome(0, VarOpConst(masterVar, highest.ub.constant, VAL::E_GREATER), ubPre));
                    continuum.push_back(ubTmp.get());
                }
            } else {
                assert(highest.ub.op == VAL::E_LESS);
                if (highest.ub.constant <= actBounds[masterVar].second) {
                    ubTmp = auto_ptr<ConditionBoundsAndOutcome>(
                        new ConditionBoundsAndOutcome(0, VarOpConst(masterVar, highest.ub.constant, VAL::E_GREATEQ), ubPre));
                    continuum.push_back(ubTmp.get());
                }
            }
        }
        
        if (localDebug) {
            cout << "\nContinuum containing that pre:\n";
            list<ConditionBoundsAndOutcome*>::iterator condItr = continuum.begin();
            const list<ConditionBoundsAndOutcome*>::iterator condEnd = continuum.end();
            
            for (; condItr != condEnd; ++condItr) {
                cout << (*condItr)->lb << " to " << (*condItr)->ub << endl;                
            }
            
        }
        
        list<ConditionBoundsAndOutcome*>::const_iterator conditionedOnThisPre = continuum.begin();
        for (; (*conditionedOnThisPre)->outcome != withPre; ++conditionedOnThisPre) ;                
        
        list<ConditionBoundsAndOutcome*>::const_iterator mustBeAtLeastAsGood;
        list<ConditionBoundsAndOutcome*>::const_iterator mustBeAtLeastAsGoodEnd;
        
        list<ConditionBoundsAndOutcome*>::const_iterator cannotBeBetter;
        list<ConditionBoundsAndOutcome*>::const_iterator cannotBeBetterEnd;
        
        if (masterPre.op == VAL::E_GREATER || masterPre.op == VAL::E_GREATEQ) {
            // the master pre defines v >= c, v < some upper bound
            // if v < c, the outcome must be at least as good
            // if v > that upper bound, the outcome must be no better
            
            if (localDebug) {
                cout << "Earlier points must be at least as good as this point\n";
            }
            mustBeAtLeastAsGood = continuum.begin();
            mustBeAtLeastAsGoodEnd = conditionedOnThisPre;

            if (localDebug) {
                cout << "Later points must be no better than this point\n";
            }
            
            cannotBeBetter = conditionedOnThisPre;
            ++cannotBeBetter;
            cannotBeBetterEnd = continuum.end();                                    
            
        } else {
            // the master pre defines v <= c, v > some lower bound
            // if v > c, the outcome must be at least as good
            // if v < that upper bound, the outcome must be no better

            if (localDebug) {
                cout << "Later points must be at least as good as this point\n";
            }
            
            
            mustBeAtLeastAsGood = conditionedOnThisPre;
            ++mustBeAtLeastAsGood;
            mustBeAtLeastAsGoodEnd = continuum.end();                                    
            
            if (localDebug) {
                cout << "Earlier points must be no better than this point\n";
            }
            
            cannotBeBetter = continuum.begin();
            cannotBeBetterEnd = conditionedOnThisPre;
            
        }
        
        for (; mustBeAtLeastAsGood != mustBeAtLeastAsGoodEnd; ++mustBeAtLeastAsGood) {
            
            if (couldBeWorseThan((*mustBeAtLeastAsGood)->outcome, (*conditionedOnThisPre)->outcome, actBounds)) {
                // found a worse outcome
                if (localDebug) {
                    cout << "Outcome from range {" << (*mustBeAtLeastAsGood)->lb << "," << (*mustBeAtLeastAsGood)->ub << "} cannot be worse than the output from the range defined by this pre in order to make this pre not necessarily a good idea\n";
                }
                return false;
            }
            
            if (localDebug) {
                cout << "Outcome from range {" << (*mustBeAtLeastAsGood)->lb << "," << (*mustBeAtLeastAsGood)->ub << "} is fine\n";
            }
        }
        
        for (; cannotBeBetter != cannotBeBetterEnd; ++cannotBeBetter) {
            
            if (couldBeWorseThan((*conditionedOnThisPre)->outcome, (*cannotBeBetter)->outcome, actBounds)) {
                // found a better outcome
                if (localDebug) {
                    cout << "Outcome from range {" << (*cannotBeBetter)->lb << "," << (*cannotBeBetter)->ub << "} cannot be better than the output from the range defined by this pre in order to make this pre not necessarily a good idea\n";
                }
                    
                return false;
            }
            if (localDebug) {
                cout << "Outcome from range {" << (*cannotBeBetter)->lb << "," << (*cannotBeBetter)->ub << "} is fine\n";
            }
                
            
        }
    }
    
    if (localDebug) {
        cout << RPGBuilder::getNumericPreTable()[preID] << " only supports metrically worse options than the alternatives\n";
    }
    
    return true;
    
}

struct WeightedSumAndConstant {
  
    map<int,double> weightedSum;
    double constant;
    
};

bool NumericAnalysis::requiringNotFullOnlySupportsReplenishment(const int & preID)
{
    static const bool localDebug = (Globals::globalVerbosity & 16384);
    
    static LiteralSet literalGoals;    
    static bool lgDefined = false;
    
    if (!lgDefined) {
        lgDefined = true;
        literalGoals.insert(RPGBuilder::getLiteralGoals().begin(), RPGBuilder::getLiteralGoals().end());
    }

    if (localDebug) {
        cout << "Seeing if " << RPGBuilder::getNumericPreTable()[preID] << " only supports effects in the opposite direction\n";
    }
    
    
    static const int pneCount = RPGBuilder::getPNECount();
    
    const RPGBuilder::RPGNumericPrecondition & currRNP = RPGBuilder::getNumericPreTable()[preID];
    
    if (currRNP.desirable && !currRNP.undesirable) {
        if (localDebug) {
            cout << "It is desirable and not undesirable for preferences - returning false\n";
        }                
        return false;
    }
        
    
    const list<pair<int, Planner::time_spec> > & actionsWithThatPre = RPGBuilder::getRawRpgNumericPreconditionsToActions()[preID];
    
    {
        // first, if this precondion is a goal, then it's definitely worth getting in its own right
        const list<pair<int, int> > & numericGoals = RPGBuilder::getNumericRPGGoals();
        
        list<pair<int, int> >::const_iterator ngItr = numericGoals.begin();
        const list<pair<int, int> >::const_iterator ngEnd = numericGoals.end();
        
        for (; ngItr != ngEnd; ++ngItr) {
            
            if (ngItr->first == preID) {
                if (localDebug) {
                    cout << "The precondition is a goal, so is definitely worth aiming for - returning false\n";
                }
                return false;
            }
            
            if (ngItr->second == preID) {
                if (localDebug) {
                    cout << "The precondition is a goal, so is definitely worth aiming for - returning false\n";
                }                
                return false;
            }
        }
    }
    
    
    
    if (actionsWithThatPre.empty()) {
        // if no actions require the precondition, bail out here
        {
            if (localDebug) {
                cout << "No actions have this as a precondition, and is not a goal, but it is not desirable/undesirable for preferences - returning true\n";
            }                
            
            return true;
        }
    }
    
    // otherwise, see if we can reduce the precondition to a simple v >=c or v <= c
    
    int varID = currRNP.LHSVariable;
    bool geq = true; // if false: means it's a <=
    double constant = currRNP.RHSConstant;
    
    if (varID >= 2 * RPGBuilder::getPNECount()) {
        const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(varID);
        if (currAV.size != 1) {
            // is a compound numeric precondition, so no obvious resource analogy
            if (localDebug) {
                cout << "Variable is in multi-variable AV, so no obvious increase/decrease resource analogy - returning false\n";
            }
            return false;
        }
        varID = currAV.fluents[0];
        constant -= currAV.constant;
    }
    
    if (varID >= RPGBuilder::getPNECount()) {
        varID -= RPGBuilder::getPNECount();
        if (constant != 0.0) {
            constant = -constant;
        }
        geq = false;
    }
    
    if (varID < 0) {
        // is a condition on something other than a simple task variable
        if (localDebug) {
            cout << "Condition is on something other than a simple task variable - returning false\n";
        }
                            
        return false;
    }
    
    if (localDebug) {
        
        cout << COLOUR_light_red << "Reduced pre to " << *(RPGBuilder::getPNE(varID));
        if (geq) {
            cout << " >= " << constant;
        } else {
            cout << " <= " << constant;
        }
        cout << COLOUR_default << endl;
    }
    // if we get this far, we know it's v <= c or v >= c
    // if the effects are all (assign v c), then we can return true
    
    list<pair<int, Planner::time_spec> >::const_iterator actItr = actionsWithThatPre.begin();
    const list<pair<int, Planner::time_spec> >::const_iterator actEnd = actionsWithThatPre.end();
    
    for (; actItr != actEnd; ++actItr) {
        // first, see if anything needs the propositional effects of the action with this precondition,
        // in which case meeting the precondition could be a good idea
        
        for (int pass = 0; pass < 2; ++pass) {
            const list<Literal*> & effList = (pass ? RPGBuilder::getEndPropositionAdds()[actItr->first]
                                                   : RPGBuilder::getStartPropositionAdds()[actItr->first] );
            
            list<Literal*>::const_iterator eItr = effList.begin();
            const list<Literal*>::const_iterator eEnd = effList.end();
            
            for (int fID; eItr != eEnd; ++eItr) {
                fID = (*eItr)->getStateID();
                if (RPGBuilder::getSemaphoreFacts().find(fID) != RPGBuilder::getSemaphoreFacts().end()) {
                    continue;
                }
                if (!RPGBuilder::getPresToActions()[fID].empty()) {
                    // an action needs this fact
                    if (localDebug) {
                        cout << "An action with this pre adds " << *(*eItr) << ", required by an action - returning false\n";
                    }
                    
                    return false;
                }
                if (literalGoals.find(*eItr) != literalGoals.end()) {
                    // fact is a goal
                    if (localDebug) {
                        cout << "An action with this pre adds a goal - returning false\n";
                    }
                                                            
                    return false;
                }
            }
        }
        
        // so far have shown that this action has no useful propositional effects
        // now check that all numeric effects are equally dull, either on
        // irrelevant variables, or replenishing this resource to the value 'constant'
        
        for (int pass = 0; pass < 2; ++pass) {
            const list<int> & effs = (pass ? RPGBuilder::getEndEffNumerics()[actItr->first] : RPGBuilder::getStartEffNumerics()[actItr->first]);
            
            list<int>::const_iterator effItr = effs.begin();
            const list<int>::const_iterator effEnd = effs.end();
            
            for (; effItr != effEnd; ++effItr) {
                const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*effItr];
                if (dominanceConstraints[currEff.fluentIndex] == E_IRRELEVANT) {                    
                    continue;
                }
                
                if (currEff.fluentIndex != varID) {
                    // found effect on another numeric variable, give up
                    if (localDebug) {
                        cout << *(RPGBuilder:: getInstantiatedOp(actItr->first)) << ", with this pre, affects some other variable, " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << ", so returning false\n";
                    }                    
                    return false;
                }
                                    
                map<int, pair<double,double> > upperBoundsOnVariable;
                map<int, pair<double,double> > lowerBoundsOnVariable;

                if (currEff.size) {
                    
                    // find bounds on the variable in terms of the variable we're looking at
                    // each pair: first is a weight, second is a constant

                    const list<int> & simultaneousNumericPres = (pass ? RPGBuilder::getEndPreNumerics()[actItr->first] : RPGBuilder::getStartPreNumerics()[actItr->first]);

                    for (int s = 0; s < currEff.size; ++s) {
                    
                        int lVar = currEff.variables[s];
                        if (lVar == -3 || lVar == -19) {
                            const vector<RPGBuilder::RPGDuration*> & des = RPGBuilder::getRPGDEs(actItr->first);
                        
                            assert(!des.empty());
                            for (int pass = 0; pass < 3; ++pass) {
                                const list<RPGBuilder::DurationExpr *> & currList = (*des[0])[pass];
                                list<RPGBuilder::DurationExpr *>::const_iterator deItr = currList.begin();
                                const list<RPGBuilder::DurationExpr *>::const_iterator deEnd = currList.end();
                                
                                for (; deItr != deEnd; ++deItr) {
                                    const int vCount = (*deItr)->variables.size();
                                    if (vCount != 1) {
                                        continue;
                                    }
                                    int lVar = (*deItr)->variables[0];
                                    double lW = (*deItr)->weights[0];
                                    
                                    if (lVar >= pneCount) {
                                        lW = -lW;
                                        lVar -= pneCount;
                                    }
                                    
                                    if (lVar == currEff.fluentIndex) {
                                        if (pass == 0 || pass == 2) {
                                            // is ?duration = the var we're looking for times some constant
                                            
                                            if (upperBoundsOnVariable.find(-3) != upperBoundsOnVariable.end()) {
                                                // duplicate bound defined
                                                if (localDebug) {
                                                    cout << COLOUR_light_red << "An action with this pre has a complex effect " << currEff << " with two upper bounds on ?duration - returning false\n" << COLOUR_default;
                                                    // complex effect, not simple constant
                                                    return false;
                                                }  
                                            }
                                            upperBoundsOnVariable[-3] = make_pair(lW, (*deItr)->constant);
                                            
                                        }
                                        if (pass == 0 || pass == 1) {
                                            if (lowerBoundsOnVariable.find(-3) != lowerBoundsOnVariable.end()) {
                                                // duplicate bound defined
                                                if (localDebug) {
                                                    cout << COLOUR_light_red << "An action with this pre has a complex effect " << currEff << " with two lower bounds on ?duration - returning false\n" << COLOUR_default;
                                                    // complex effect, not simple constant
                                                    return false;
                                                }  
                                            }
                                            lowerBoundsOnVariable[-3] = make_pair(lW, (*deItr)->constant);
                                        }
                                    }
                                    
                                }
                            }
                            
                        } else {
                            if (localDebug) {
                                cout << COLOUR_light_red << "An action with this pre has a complex effect " << currEff << " depending on something other than ?duration - returning false\n" << COLOUR_default;
                                // complex effect, not simple constant
                            }                    
                            
                            return false;
                    
                        }
                    }
                }
                
                map<int,double> rhsAsWeightedSum;
                double rhsConstant = currEff.constant;
                
                if (!currEff.isAssignment) {
                    // reducing to assignment: x += c  -> x = x + c
                    rhsAsWeightedSum.insert(make_pair(currEff.fluentIndex, 1.0));
                }
                
                for (int s = 0; s < currEff.size; ++s) {
                    
                    int lVar = currEff.variables[s];
                    double lW = currEff.weights[s];
                    
                    assert(lVar == -3 || lVar == -19);
                    
                    if (lVar == -19) {
                        lVar = -3;
                        lW = -lW;
                    }
                        
                    if (geq) {
                        // precondition is of the form x >= c
                        // we want to see if we can get an effect such that x is assigned something less than c
                        if (lW < 0) {
                            // negative weighted duration term: max out the duration
                            const map<int, pair<double,double> >::const_iterator boundItr = upperBoundsOnVariable.find(lVar);
                            if (boundItr == upperBoundsOnVariable.end()) {
                                // no upper bound: set duration to infinity
                                rhsConstant = -DBL_MAX;
                            } else {
                                rhsConstant += boundItr->second.second * lW;
                                rhsAsWeightedSum.insert(make_pair(currEff.fluentIndex,0.0)).first->second += boundItr->second.first * lW;
                            }                            
                        } else {
                            // positive weighted duration term: make the duration as small as posible
                            const map<int, pair<double,double> >::const_iterator boundItr = lowerBoundsOnVariable.find(lVar);
                            if (boundItr == lowerBoundsOnVariable.end()) {
                                // no lower bound: set duration to epsilon
                                rhsConstant += (0.001 * lW);
                            } else {
                                rhsConstant += boundItr->second.second * lW;
                                rhsAsWeightedSum.insert(make_pair(currEff.fluentIndex,0.0)).first->second += boundItr->second.first * lW;
                            }  
                        }
                    } else {
                        // precondition is of the form x <= c
                        // we want to see if we can get an effect such that x is assigned something greater than c
                        
                        if (lW > 0) {
                            //positive weighted duration term: max out the duration
                            const map<int, pair<double,double> >::const_iterator boundItr = upperBoundsOnVariable.find(lVar);
                            if (boundItr == upperBoundsOnVariable.end()) {
                                // no upper bound: set duration to infinity
                                rhsConstant = DBL_MAX;
                            } else {
                                rhsConstant += boundItr->second.second * lW;
                                rhsAsWeightedSum.insert(make_pair(currEff.fluentIndex,0.0)).first->second += boundItr->second.first * lW;
                            }                            
                        } else {
                            // negative weighted duration term: make the duration as small as posible
                            const map<int, pair<double,double> >::const_iterator boundItr = lowerBoundsOnVariable.find(lVar);
                            if (boundItr == lowerBoundsOnVariable.end()) {
                                // no lower bound: set duration to epsilon
                                rhsConstant += (0.001 * lW);
                            } else {
                                rhsConstant += boundItr->second.second * lW;
                                rhsAsWeightedSum.insert(make_pair(currEff.fluentIndex,0.0)).first->second += boundItr->second.first * lW;
                            }  
                        }
                    }
                }
                        
                        
                map<int,double>::const_iterator fiWeight = rhsAsWeightedSum.find(currEff.fluentIndex);
                if (fiWeight != rhsAsWeightedSum.end()) {
                
                    if (fabs(fiWeight->second) > 0.00001) {
                        if (localDebug) {
                            cout << COLOUR_light_red << "Reduction to assigning a constant failed: " << fiWeight->second << " is non-zero - returning false\n" << COLOUR_default;
                            // complex effect, not simple constant
                        }                                        
                        return false;
                    }
                }                
                
                if (localDebug) {
                    cout << COLOUR_yellow << "Have reduced " << currEff << " to, at most, (assign " << *(RPGBuilder::getPNE(currEff.fluentIndex)) << " " << rhsConstant << ")\n" << COLOUR_default;
                }
                
                if (geq) {
                    if (rhsConstant - constant < -0.000001 ) {
                        if (localDebug) {
                            cout << "Have a band-gap assignment: decreasing sufficiently allows us to exceed prior bound, getting to " << rhsConstant << " instead of " << constant << " - returning false\n";
                        }
                        // have a 'gap' situation: v >= c allows (assign v d), where d < c
                        return false;
                    }
                    // will happily also ignore the case where v >= c
                                                                    
                } else {                    
                    if (rhsConstant - constant > 0.000001 ) {
                        if (localDebug) {
                            cout << "Have a band-gap assignment: increasing sufficiently allows us to exceed prior bound, getting to " << rhsConstant << " instead of " << constant << " - returning false\n";
                        }
                        
                        // have a 'gap' situation: v <= c allows (assign v d), where d > c
                        return false;
                    }
                    // will happily also ignore the case where v >= c
                }
                          
                /*
                                                                
                if (!currEff.isAssignment) {
                    if (geq) {
                        if (currEff.constant < 0) {
                            if (localDebug) {
                                cout << "An action with this pre can decrease the var - returning false\n";
                            }                            
                            return false;
                        }
                        // willing to tolerate 'v >= c  means we can increase c'
                    } else {
                        if (currEff.constant > 0) {
                            if (localDebug) {
                                cout << "An action with this pre can increase the var - returning false\n";
                            }
                            return false;
                        }
                        // willing to tolerate 'v <= c  means we can decrease c'
                    }
                    
                } else {                    
                    if (geq) {
                        if (currEff.constant - constant < -0.000001 ) {
                            if (localDebug) {
                                cout << "Have a band-gap assignment: decreasing sufficiently allows us to exceed prior bound - returning false\n";
                            }
                            // have a 'gap' situation: v >= c allows (assign v d), where d < c
                            return false;
                        }
                        // will happily also ignore the case where v >= c
                                                                        
                    } else {                    
                        if (currEff.constant - constant > 0.000001 ) {
                            if (localDebug) {
                                cout << "Have a band-gap assignment: increasing sufficiently allows us to go lower than prior bound - returning false\n";
                            }
                            
                            // have a 'gap' situation: v <= c allows (assign v d), where d > c
                            return false;
                        }
                        // will happily also ignore the case where v >= c
                    }
                }*/
            }
        }                    
    }

    if (localDebug) {
        cout << "All actions with this pre either push it in a 'less satisfied' direction, or assign it to the same value it must be leq/geq than - returning true\n";
    }
        
    return true;
        
}


void NumericAnalysis::updateForDurationDependence(const int & v, const double & w,
                                                  const int & durVar, const bool & pass,
                                                  vector<dominance_constraint> & workingDominanceConstraints)
{
    static const bool localDebug = (Globals::globalVerbosity & 16384);
    switch (workingDominanceConstraints[v]) {
        case E_NODOMINANCE:
        {
            if (localDebug) {
                if (workingDominanceConstraints[durVar] != E_NODOMINANCE) {
                    cout << "This erodes any dominance on " << *(RPGBuilder::getPNE(durVar)) << endl;
                }
            }
            workingDominanceConstraints[durVar] = E_NODOMINANCE;
            break;
        }
        case E_SMALLERISBETTER:
        {
            if (w < 0.0) {
                // if we are decreasing a variable that is better smaller, then we
                // want as long a duration as possible
                
                if (pass ? workingDominanceConstraints[durVar] == E_BIGGERISBETTER
                         : workingDominanceConstraints[durVar] == E_SMALLERISBETTER) {
                    
                    if (localDebug) {
                        cout << "This erodes any dominance on " << *(RPGBuilder::getPNE(durVar)) << ", as for this effect it's better for the duration to be long\n";
                    }

                    workingDominanceConstraints[durVar] = E_NODOMINANCE;
                }
            } else if (w > 0.0) {
                // if we are increasing a variable that is better smaller, then we
                // want as short a duration as possible
                                                
                if (pass ? workingDominanceConstraints[durVar] == E_SMALLERISBETTER
                         : workingDominanceConstraints[durVar] == E_BIGGERISBETTER) {
                    if (localDebug) {
                        cout << "This erodes any dominance on " << *(RPGBuilder::getPNE(durVar)) << ", as for this effect it's better for the duration to be short\n";
                    }

                    workingDominanceConstraints[durVar] = E_NODOMINANCE;
                }
            }
            break;
        }
        case E_BIGGERISBETTER:
        {
            if (w < 0.0) {
                // if we are decreasing a variable that is better bigger, then we
                // want as short a duration as possible
                
                if (pass ? workingDominanceConstraints[durVar] == E_SMALLERISBETTER
                         : workingDominanceConstraints[durVar] == E_BIGGERISBETTER) {
                    if (localDebug) {
                        cout << "This erodes any dominance on " << *(RPGBuilder::getPNE(durVar)) << ", as for this effect it's better for the duration to be short\n";
                    }

                    workingDominanceConstraints[durVar] = E_NODOMINANCE;
                }
            } else if (w > 0.0) {
                // if we are inccreasing a variable that is better bigger, then we
                // want as long a duration as possible
                                                
                if (pass ? workingDominanceConstraints[durVar] == E_BIGGERISBETTER
                         : workingDominanceConstraints[durVar] == E_SMALLERISBETTER) {
                    workingDominanceConstraints[durVar] = E_NODOMINANCE;
                    if (localDebug) {
                        cout << "This erodes any dominance on " << *(RPGBuilder::getPNE(durVar)) << ", as for this effect it's better for the duration to be long\n";
                    }

                }
            }
            break;
        }
        case E_IRRELEVANT:
        case E_METRICTRACKING:
        {
            break;            
        }
    }
}

vector<map<int, list<int> > > NumericAnalysis::goalHasIndependentCostOnLimit;
bool NumericAnalysis::thereAreIndependentGoalCosts = false;

void NumericAnalysis::considerCostsOfLiteralGoalsReachedByGoalOnlyOperators()
{        
    
    static const unsigned int localDebug = 7;
    
    const list<Literal*> & litGoals = RPGBuilder::getLiteralGoals();
    
    goalHasIndependentCostOnLimit.resize(litGoals.size());
 
    const int nldSize = goalNumericUsageLimits.size();
    
    if (!nldSize) {
        if (localDebug) {
            cout << COLOUR_light_blue << "No analytic limits found, not considering limit effects of goal-only operators" << COLOUR_default << endl;
        }
        return;
    }
    
    map<int, list<int> > variableIsInLimit;
    bool variableIsInLimitDefined = false;
    
    list<Literal*>::const_iterator gItr = litGoals.begin();
    const list<Literal*>::const_iterator gEnd = litGoals.end();
    
    for (int gID = 0; gItr != gEnd; ++gItr, ++gID) {
        
        // first, exclude static goals, or goals which are preconditions
        
        if (RPGBuilder::isStatic(*gItr).first
            || !RPGBuilder::getRawPresToActions()[(*gItr)->getStateID()].empty()) {
            if (localDebug & 1) {
                cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", is static or a precondition" << COLOUR_default << endl;
            }
            
            continue;
        }
        
        const list<pair<int, Planner::time_spec> > & eta = RPGBuilder::getEffectsToActions((*gItr)->getStateID());
        
        set<int> achievedBy;
        
        if (localDebug & 4) {
            cout << COLOUR_light_red << "Looking for achievers for goal index " << gID << ", fact " << *(*gItr) << " with fID " << (*gItr)->getStateID() <<  COLOUR_default << endl;
        }
        
        list<pair<int, Planner::time_spec> >::const_iterator eItr = eta.begin();
        const list<pair<int, Planner::time_spec> >::const_iterator eEnd = eta.end();
        
        for (; eItr != eEnd; ++eItr) {
            if (eItr->second == Planner::E_AT) {
                break;
            }
            if (localDebug & 4) {
                cout << " " << *(RPGBuilder::getInstantiatedOp(eItr->first));
            }
            achievedBy.insert(eItr->first);
            
        }
        
        if (localDebug & 4) {
            cout << endl;
        }
        
        if (eItr != eEnd) {
            
            // was reached by a TIL, skip it
            if (localDebug & 1) {
                cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be reached by a TIL" << COLOUR_default << endl;
            }
            continue;
        }
        
        // now we see whether the achieving actions' effects are all boring
        
        bool safe = true;
        bool anyNum = false;
        
        {            
                
            set<int>::const_iterator aItr = achievedBy.begin();
            const set<int>::const_iterator aEnd = achievedBy.end();
            
            for (; safe && aItr != aEnd; ++aItr) {
                
                
                // check that it only achieves this goal
                            
                for (int pass = 0; safe && pass < 2; ++pass) {
                    const list<Literal*> & adds = (pass ? RPGBuilder::getEndPropositionAdds()[*aItr] : RPGBuilder::getStartPropositionAdds()[*aItr]);
                    
                    list<Literal*>::const_iterator aeItr = adds.begin();
                    const list<Literal*>::const_iterator aeEnd = adds.end();
                    
                    for (; aeItr != aeEnd; ++aeItr) {
                        if (*aeItr != *gItr) {
                            if (localDebug & 1) {
                                cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has other interesting effects (including one on " << *(*aeItr) << " )" << COLOUR_default << endl;
                            }
                            safe = false;
                            break;
                        }
                    }
                }
                
                if (!safe) {
                    break;
                }
                
                if (localDebug & 1) {
                    cout << "  Looking at numeric effects of " << *(RPGBuilder::getInstantiatedOp(*aItr)) << ": ";
                    cout << RPGBuilder::getStartEffNumerics()[*aItr].size() << " and " << RPGBuilder::getEndEffNumerics()[*aItr].size() << endl;
                }
                
                for (int pass = 0; safe && pass < 2; ++pass) {
                    const list<int> & numEffs = (pass ? RPGBuilder::getEndEffNumerics()[*aItr] : RPGBuilder::getStartEffNumerics()[*aItr]);
                    
                    list<int>::const_iterator neItr = numEffs.begin();
                    const list<int>::const_iterator neEnd = numEffs.end();
                    
                    for (; safe && neItr != neEnd; ++neItr) {
                        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*neItr];
                        
                        if (dominanceConstraints[currEff.fluentIndex] == E_IRRELEVANT) {
                            if (localDebug & 1) {
                                cout << "  Ignoring an irrelevant effect\n";
                            }
                            continue;
                        }

                        if (dominanceConstraints[currEff.fluentIndex] == E_METRICTRACKING) {
                            if (currEff.size > 1 || currEff.isAssignment) {
                                if (localDebug & 1) {
                                    cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                    cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a non-trivial numeric effect " << currEff << COLOUR_default << endl;
                                }
                                
                                safe = false;
                                break;
                            }

                        } else {
                            if (currEff.size || currEff.isAssignment) {
                                if (localDebug & 1) {
                                    cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                    cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a non-trivial numeric effect " << currEff << COLOUR_default << endl;
                                }
                                
                                safe = false;
                                break;
                            }
                            
                            if (currEff.constant == 0.0) {
                                continue;
                            }
                                                    
                                                    
                        }
                        
                        switch (dominanceConstraints[currEff.fluentIndex]) {
                            case E_IRRELEVANT:
                            {
                                cerr << "Internal error: this should never, ever happen, as it means the dominance constraints have changed mid-function\n";
                                exit(1);
                            }
                            case E_METRICTRACKING:
                            {
                                if (Globals::optimiseSolutionQuality) {
                                    anyNum = true;
                                }
                                break;
                            }
                            case E_SMALLERISBETTER: {
                                if (currEff.constant < 0.0) {
                                    // beneficial effect: makes something smaller
                                    safe = false;
                                    if (localDebug & 1) {
                                        cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                        cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a beneficial decrease effect " << currEff << COLOUR_default << endl;
                                    }
                                    
                                }
                                anyNum = true;
                                break;
                            }
                            case E_BIGGERISBETTER: {
                                if (currEff.constant > 0.0) {
                                    // beneficial effect: makes something smaller
                                    safe = false;
                                    if (localDebug & 1) {
                                        cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                        cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a beneficial increase effect " << currEff << COLOUR_default << endl;
                                    }
                                    
                                    
                                }
                                anyNum = true;
                                break;
                            }
                            default: {
                                if (localDebug & 1) {
                                    cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                    cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a no-known-dominance effect " << currEff << COLOUR_default << endl;
                                }
                                safe = false;
                            }
                        }
                                            
                    }
                }
                
                if (!safe) {
                    break;
                }
                
                {
                
                    const list<RPGBuilder::ConditionalEffect> & condEffs = RPGBuilder::getActionsToConditionalEffects()[*aItr];
                    
                    if (localDebug & 1) {
                        cout << "  No troublesome numerics - looking at conditional effects on " << *(RPGBuilder::getInstantiatedOp(*aItr)) << ", of which there are " << condEffs.size() << endl;
                    }
                    
                    list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs.begin();
                    const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs.end();
                    
                    for (; ceItr != ceEnd; ++ceItr) {
                        const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
                        
                        list<pair<int, Planner::time_spec> >::const_iterator neItr = numEffs.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator neEnd = numEffs.end();
                        
                        for (; neItr != neEnd; ++neItr) {
                            const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[neItr->first];
                            assert(currEff.size <= 1 && !currEff.isAssignment);

                            if (dominanceConstraints[currEff.fluentIndex] == E_IRRELEVANT) {
                                if (localDebug & 1) {
                                    cout << "   Found a conditional irrelevant effect\n";
                                }
                                continue;
                            }                            
                            
                            assert(dominanceConstraints[currEff.fluentIndex] == E_METRICTRACKING);
                            
                            if (currEff.size > 1 || currEff.isAssignment) {
                                if (localDebug & 1) {
                                    cout << COLOUR_light_blue << "For limits: literal goal index " << gID << ", fact " << *(*gItr) << ", could be achieved by operator ";
                                    cout << *(RPGBuilder::getInstantiatedOp(*aItr))  << ", which has a non-trivial conditional numeric effect " << currEff << COLOUR_default << endl;
                                }
                                
                                safe = false;
                                break;
                            }
                            
                            if (localDebug & 1) {
                                cout << "   Found a conditional metric effect\n";
                            }
                                                                    
                            anyNum = true;
                        }
                    }
                }

                
            }
            
        }
                
        if (safe && anyNum) {
            
            if (localDebug & 1) {
                cout << "  Conditional effects are okay and at least one metric effect was found\n";
            }
            
            // if we get this far, the goal is achieved only by actions that 
            //  i) only achieve one fact - the goal
            // ii) have numeric effects that are only ever a bad idea, so we'd never want to apply them in their
            //     own right for that
            // iii) some sort of numeric effectage that might have an effect on a cost limit

            if (!variableIsInLimitDefined) {

                variableIsInLimitDefined = true;
                
                for (int nl = 0; nl < nldSize; ++nl) {
                    
                    const NumericAnalysis::NumericLimitDescriptor & nld = goalNumericUsageLimits[nl];
                    
                    map<int,double>::const_iterator vItr = nld.var.begin();
                    const map<int,double>::const_iterator vEnd = nld.var.end();
                    
                    for (; vItr != vEnd; ++vItr) {
                        variableIsInLimit[vItr->first].push_back(nl);
                    }
                    
                }
            }
    
            bool pushed = false;
            
            
            set<int>::const_iterator aItr = achievedBy.begin();
            const set<int>::const_iterator aEnd = achievedBy.end();
            
            for (; aItr != aEnd; ++aItr) {
                
                set<pair<int, int> > knownToAffect;
                
                for (int pass = 0; safe && pass < 2; ++pass) {
                    const list<int> & numEffs = (pass ? RPGBuilder::getEndEffNumerics()[*aItr] : RPGBuilder::getStartEffNumerics()[*aItr]);
                    
                    list<int>::const_iterator neItr = numEffs.begin();
                    const list<int>::const_iterator neEnd = numEffs.end();
                    
                    for (; safe && neItr != neEnd; ++neItr) {
                        const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[*neItr];
                        
                        assert(currEff.size <= 1 && !currEff.isAssignment);

                        if (dominanceConstraints[currEff.fluentIndex] == E_IRRELEVANT) {
                            continue;
                        }                            
                        
                        if (currEff.constant == 0.0 && currEff.size == 0) {
                            continue;
                        }
                        
                        const map<int,list<int> >::const_iterator lsItr = variableIsInLimit.find(currEff.fluentIndex);
                        
                        if (lsItr != variableIsInLimit.end()) {
                            
                            list<int>::const_iterator lItr = lsItr->second.begin();
                            const list<int>::const_iterator lEnd = lsItr->second.end();
                            
                            for (; lItr != lEnd; ++lItr) {                                
                                if (knownToAffect.insert(make_pair(gID,*lItr)).second) {
                                    goalHasIndependentCostOnLimit[gID][*lItr].push_back(*aItr);
                                }
                            }
                            
                        }
                    }
                }
                
                if (!pushed) {
                    const list<RPGBuilder::ConditionalEffect> & condEffs = RPGBuilder::getActionsToConditionalEffects()[*aItr];
                    list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs.begin();
                    const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs.end();
                    
                    for (; ceItr != ceEnd; ++ceItr) {
                        const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
                        
                        list<pair<int, Planner::time_spec> >::const_iterator neItr = numEffs.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator neEnd = numEffs.end();
                        
                        for (; neItr != neEnd; ++neItr) {
                            const RPGBuilder::RPGNumericEffect & currEff = RPGBuilder::getNumericEff()[neItr->first];
                            assert(currEff.size <= 1 && !currEff.isAssignment);

                            if (dominanceConstraints[currEff.fluentIndex] == E_IRRELEVANT) {
                                continue;
                            }                            
                            
                            if (currEff.constant == 0.0 && currEff.size == 0) {
                                continue;
                            }
                            
                            const map<int,list<int> >::const_iterator lsItr = variableIsInLimit.find(currEff.fluentIndex);
                            
                            if (lsItr != variableIsInLimit.end()) {
                                
                                list<int>::const_iterator lItr = lsItr->second.begin();
                                const list<int>::const_iterator lEnd = lsItr->second.end();
                                
                                for (; lItr != lEnd; ++lItr) {                          
                                    if (knownToAffect.insert(make_pair(gID,*lItr)).second) {
                                        goalHasIndependentCostOnLimit[gID][*lItr].push_back(*aItr);
                                    }
                                }
                                
                            }
                        }
                    }
                }
            }
            
            if ((localDebug & 2) && !goalHasIndependentCostOnLimit[gID].empty()) {
                
                cout << COLOUR_yellow << "To achieve goal index " << gID << ", fact " << *(*gItr) << ", there is a definite effect on one or more limits:\n" << COLOUR_default;
                
                map<int, list<int> >::const_iterator leItr = goalHasIndependentCostOnLimit[gID].begin();
                const map<int, list<int> >::const_iterator leEnd = goalHasIndependentCostOnLimit[gID].end();
                
                for (; leItr != leEnd; ++leItr) {
                    cout << "Limit " << leItr->first;
                    
                    if (goalNumericUsageLimits[leItr->first].optimisationLimit) {
                        cout << " (the metric)";
                    }
                    cout << ", if using one of:";
                    list<int>::const_iterator oItr = leItr->second.begin();
                    const list<int>::const_iterator oEnd = leItr->second.end();
                    
                    for (; oItr != oEnd; ++oItr) {
                        cout << " " << *(RPGBuilder::getInstantiatedOp(*oItr));
                    }
                    cout << endl;
                }
                
            }
        }
    }
    
    {
        const int gc = goalHasIndependentCostOnLimit.size();
        
        for (int gID = 0; gID < gc; ++gID) {
            if (!goalHasIndependentCostOnLimit[gID].empty()) {
                thereAreIndependentGoalCosts = true;
                return;
            }
        }
    }
    
}

struct ValueWeightedSum {
    
    map<int,double> startWeights;
    double startConst;    
    bool startAssignment;
    
    double ctsGradient;

    map<int,double> endWeights;
    double endConst;
    bool endAssignment;
    
    ValueWeightedSum()
        : startConst(0.0), startAssignment(false), ctsGradient(0.0), endConst(0.0), endAssignment(false) {
    }
};

void NumericAnalysis::considerConflictingDominanceThroughEffects(vector<dominance_constraint> & workingDominanceConstraints)
{
    
    static const bool localDebug = (Globals::globalVerbosity & 16384);
    const int pneCount =  RPGBuilder::getPNECount();
    
    const vector<RPGBuilder::RPGNumericEffect> & rpgNumericEffects = RPGBuilder::getNumericEff();
    
    const int effCount = rpgNumericEffects.size();
    
    int v;
    double w;
    
    map<int, map<int,bool> > actionToDurationDependentEffects;
    
    for (int effID = 0; effID < effCount; ++effID) {
        
        const RPGBuilder::RPGNumericEffect & currEff = rpgNumericEffects[effID];
        
        bool everIsolated = true;
        
        /*{
            list<pair<int, Planner::time_spec> >::const_iterator actItr = RPGBuilder::getRpgNumericEffectsToActions()[effID].begin();
            const list<pair<int, Planner::time_spec> >::const_iterator actEnd = RPGBuilder::getRpgNumericEffectsToActions()[effID].end();
            
            for (; actItr != actEnd; ++actItr) {
                
                if (actItr->second == Planner::E_AT_START) {
                    everIsolated = true;
                    break;
                }
                
                assert(actItr->second == Planner::E_AT_END);
                
                const int actID = actItr->first;
                
                
                // now have an action, actID, with this numeric effect at the end
                // in principle this could have been coupled with earlier effects on this variable
                // so we look at the net effect of the action's execution to see if it was
                // detrimental to the affected variable or not
                
                // first, check that variables in the effect are guarded by this action
                // otherwise, during the action's execution, something else could change the value of the variable
                // and hence mess up the analysis by making it actually do net-worse when we thought it would be net-better

                set<int> mustBeGuarded;
                
                for (int s = 0; s < currEff.size; ++s) {
                    if (currEff.variables[s] < 0) {
                        // ?duration is definitely the same at the start and at the end
                        continue;
                    }
                    int lVar = currEff.variables[s];
                    if (lVar >= pneCount) {
                        lVar -= pneCount;
                    }
                    
                    mustBeGuarded.insert(lVar);
                   
                   
                }

                if (!mustBeGuarded.empty()) {
                    
                    
                    set<int> addedAtTheStart;
                    
                    {
                        list<Literal*>::const_iterator addItr = RPGBuilder::getStartPropositionAdds()[actID].begin();
                        const list<Literal*>::const_iterator addEnd = RPGBuilder::getStartPropositionAdds()[actID].end();
                        
                        for (; addItr != addEnd; ++addItr) {
                            addedAtTheStart.insert((*addItr)->getStateID);
                        }
                    }

                    set<int> guarded;

                    {
                        list<Literal*>::const_iterator delItr = RPGBuilder::getStartPropositionDeletes()[actID].begin();
                        const list<Literal*>::const_iterator delEnd = RPGBuilder::getStartPropositionDeletes()[actID].end();
                        
                        for (; delItr != delEnd; ++delItr) {
                            const map<int, RPGBuilder::Guarded>::const_iterator sfItr = RPGBuilder::getSemaphoreFacts().find((*delItr)->stateID());
                            
                            if (sfItr == RPGBuilder::getSemaphoreFacts().end()) {
                                continue;
                            }
                            
                            guarded.insert(sfItr->second.guardedEffectVars.begin(), sfItr->second.guardedEffectVars.end());
                        }
                    }

                    set<int> unguarded;
                    
                    std::set_difference(mustBeGuarded.begin(), mustBeGuarded.end(), guarded.begin(), guarded.end(),
                                        std::insert_iterator<set<int> >(unguarded, unguarded.end()));
                                        
                    if (!unguarded.empty()) {
                        everIsolated = true;
                        break;
                    }
                    
                }

                map<int, int> varToPresentStartEffect;
                
                {
                    list<int>::const_iterator seItr = getStartEffNumerics()[actID].begin();
                    const list<int>::const_iterator seEnd = getStartEffNumerics()[actID].end();
                    
                    for (; seItr != seEnd; ++seItr) {
                        
                        varToPresentStartEffect.insert(make_pair(rpgNumericEffects[*seItr].fluentIndex, *seItr));
                        
                    }
                }
                
                const LinearEffects* const currLE = RPGBuilder::getLinearDiscretisation()[actID];
                
                map<int, ValueWeightedSum> valueOfVarDuringAction;
                
                {
                    set<int> dummySet;
                    dummySet.insert(currEff.fluentIndex);
                    
                    for (int vPass = 0; vPass < 2; ++vPass) {
                        const set<int> & currSet = (vPass == 0 ? mustBeGuarded : dummySet);
                        set<int>::const_iterator gvItr = currSet.begin();
                        const set<int>::const_iterator gvEnd = currSet.end();
                        
                        for (; gvItr != gvEnd; ++gvItr) {
                            
                            ValueWeightedSum & dest = valueOfVarDuringAction[*gvItr];
                            
                            map<int, int>::const_iterator startEffItr = varToPresentStartEffect.find(*gvItr);
                            
                            if (startEffItr != varToPresentStartEffect.end()) {
                                
                                const RPGBuilder::RPGNumericEffect & earlierEff = rpgNumericEffects[startEffItr->second];
                                
                                dest.startConst = earlierEff.constant;
                                
                                for (int s = 0; s < earlierEff.size; ++s) {
                                    if (earlierEff.variables[s] < 0) {
                                        if (earlierEff.variables[s] == -3) {
                                            dest.startWeights.insert(make_pair(-3,0.0)).second += earlierEff.weights[s];
                                        } else if (earlierEff.variables[s] == -19) {
                                            dest.startWeights.insert(make_pair(-3,0.0)).second -= earlierEff.weights[s];
                                        } else {
                                            cerr << "Fatal internal error: non duration or var term " << earlierEff.variables[s] << " in instantaneous effect " << earlierEff << endl;
                                            exit(1);
                                        } 
                                    } else {
                                        if (earlierEff.variables[s] >= pneCount) {
                                            dest.startWeights.insert(make_pair(earlierEff.variables[s] - pneCount,0.0)).second -= earlierEff.weights[s];
                                        } else {
                                            dest.startWeights.insert(make_pair(earlierEff.variables[s],0.0)).second += earlierEff.weights[s];
                                        }
                                    }
                                }
                                
                                if (earlierEff.isAssignment) {
                                    dest.startAssignment = true;
                                }
                            }
                            
                            if (currLE) {
                                for (int s = 0; s < currLE->vars.size(); ++s) {
                                    if (currLE->vars[s] == *gvItr) {
                                        dest.ctsGradient = currLE->effects[0][s].constant;
                                        break;
                                    }
                                }
                            }                                                                        
                        }
                    }
                }
                
                                
                MaskedVariableBounds startBounds;                
                
                {
                    list<int>::const_iterator spItr = getStartPreNumerics()[actID].begin();
                    const list<int>::const_iterator spEnd = getStartPreNumerics()[actID].end();
                    
                    for (; spItr != spEnd; ++spItr) {
                        
                        startBounds.applyPreToBounds(RPGBuilder::getNumericPreTable()[*spItr]);
                        
                    }
                }
                
                const ValueWeightedSum & effectsOnFI = valueOfVarDuringAction.find(currEff.fluentIndex);
                
                bool couldEverIncrease = false;
                bool couldEverDecrease = false;
                
                vector<double> startEffMinMaxValue(2,effectsOnFI.startConst);
                
                {
                    for (int pass = 0; pass < 2; ++pass) {
                        double & toUpdate = startEffMinMaxValue[pass];
                        
                        
                        
                    }
                    
                }
                
            }
        }*/
        
        if (everIsolated) {
            int effectIsDurative = 0;
            switch (workingDominanceConstraints[currEff.fluentIndex]) {
                case E_NODOMINANCE:
                {
                    for (int vi = 0; vi < currEff.size; ++vi) {
                        v = currEff.variables[vi];
                        if (v < 0) {
                            if (v == -3) {
                                effectIsDurative = 1;
                            } else if (v == -19) {
                                effectIsDurative = -1;
                            } else {
                                cerr << "Internal error: effects can only depend on task variables, constant, or ?duration\n";
                                exit(1);
                            }
                            continue;
                        }
                        if (v >= pneCount) {
                            if (localDebug) {
                                if (workingDominanceConstraints[v-pneCount] != E_NODOMINANCE) {
                                    cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v-pneCount)) << endl;
                                }
                            }
                            workingDominanceConstraints[v-pneCount] = E_NODOMINANCE;
                        } else {
                            if (localDebug) {
                                if (workingDominanceConstraints[v-pneCount] != E_NODOMINANCE) {
                                    cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v)) << endl;
                                }
                            }
                            workingDominanceConstraints[v] = E_NODOMINANCE;
                        }
                    }
                    break;
                }
                case E_BIGGERISBETTER:
                {
                    for (int vi = 0; vi < currEff.size; ++vi) {
                        v = currEff.variables[vi];
                        if (v < 0) {
                            if (v == -3) {
                                effectIsDurative = 1;
                            } else if (v == -19) {
                                effectIsDurative = -1;
                            } else {
                                cerr << "Internal error: effects can only depend on task variables, constant, or ?duration\n";
                                exit(1);
                            }
                            continue;
                        }
                        if (v >= pneCount) {
                            if (currEff.weights[vi] > 0.0) {
                                if (workingDominanceConstraints[v-pneCount] == E_BIGGERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v-pneCount)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v-pneCount] = E_NODOMINANCE;
                                }
                            } else if (currEff.weights[vi] < 0.0) {
                                if (workingDominanceConstraints[v-pneCount] == E_SMALLERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v-pneCount)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v-pneCount] = E_NODOMINANCE;
                                }
                            }
                        } else {
                            if (currEff.weights[vi] > 0.0) {
                                if (workingDominanceConstraints[v] == E_SMALLERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v] = E_NODOMINANCE;
                                }
                            } else if (currEff.weights[vi] < 0.0) {
                                if (workingDominanceConstraints[v] == E_BIGGERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v)) << endl;                                    
                                    }

                                    workingDominanceConstraints[v] = E_NODOMINANCE;
                                }
                            }
                        }
                    }
                    break;
                }
                case E_SMALLERISBETTER:
                {
                    for (int vi = 0; vi < currEff.size; ++vi) {
                        v = currEff.variables[vi];
                        if (v < 0) {
                            if (v == -3) {
                                effectIsDurative = 1;
                            } else if (v == -19) {
                                effectIsDurative = -1;
                            } else {
                                cerr << "Internal error: effects can only depend on task variables, constant, or ?duration\n";
                                exit(1);
                            }                        
                            continue;
                        }
                        if (v >= pneCount) {
                            if (currEff.weights[vi] > 0.0) {
                                if (workingDominanceConstraints[v-pneCount] == E_SMALLERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v-pneCount)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v-pneCount] = E_NODOMINANCE;
                                }
                            } else if (currEff.weights[vi] < 0.0) {
                                if (workingDominanceConstraints[v-pneCount] == E_BIGGERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v-pneCount)) << endl;                                    
                                    }
                                  workingDominanceConstraints[v-pneCount] = E_NODOMINANCE;
                                }
                            }   
                        } else {
                            if (currEff.weights[vi] > 0.0) {
                                if (workingDominanceConstraints[v] == E_BIGGERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v] = E_NODOMINANCE;
                                }
                            } else if (currEff.weights[vi] < 0.0) {
                                if (workingDominanceConstraints[v] == E_SMALLERISBETTER) {
                                    if (localDebug) {
                                        cout << "Effect " << currEff << " erodes any dominance on " << *(RPGBuilder::getPNE(v)) << endl;                                    
                                    }
                                    workingDominanceConstraints[v] = E_NODOMINANCE;
                                }
                            }
                        }
                    }
                    break;
                }
                case E_IRRELEVANT:
                case E_METRICTRACKING:
                {
                    break;
                }
            }
            
            if (effectIsDurative != 0) {
                
                if (localDebug) {
                    cout << "Noting that effect " << currEff << " is durative, attached to actions {";
                }
                const list<pair<int, Planner::time_spec> > & eta = RPGBuilder::getRpgNumericEffectsToActions()[effID];
                list<pair<int, Planner::time_spec> >::const_iterator etaItr = eta.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator etaEnd = eta.end();
                
                for (; etaItr != etaEnd; ++etaItr) {
                    actionToDurationDependentEffects[etaItr->first].insert(make_pair(effID, effectIsDurative == 1 ? true : false));
                    if (localDebug) {
                        cout << " " << etaItr->first;
                    }
                }
                if (localDebug) {
                    cout << " }\n";
                }
            }
        }
    }
    
    const vector<RPGBuilder::LinearEffects*> & ctsEffs = RPGBuilder::getLinearDiscretisation();    
    const int actCount = ctsEffs.size();
    
    map<int,map<int,bool> >::const_iterator ddEffs = actionToDurationDependentEffects.begin();
    
    const RPGBuilder::LinearEffects* leffs;
    
    for (int actID = 0; actID < actCount; ++actID) {
        if (RPGBuilder::rogueActions[actID]) continue;
        
        leffs = ctsEffs[actID];
        
        while (ddEffs != actionToDurationDependentEffects.end() && ddEffs->first < actID) {
            ++ddEffs;
        }
        
        if ((ddEffs == actionToDurationDependentEffects.end() || actID < ddEffs->first) && !leffs) {
            // action has no duration-dependent effects or continuous effects
            continue;
        }
        
        const vector<RPGBuilder::RPGDuration*> DEs = RPGBuilder::getRPGDEs(actID);
        #ifndef NDEBUG
        if (DEs.empty()) {
            cerr << "Fatal internal error: action " << actID << ", " << *(RPGBuilder::getInstantiatedOp(actID)) << " has no duration constraints, but has ";
            if (ddEffs != actionToDurationDependentEffects.end()) {
                cerr << "duration-dependent effects as action " << ddEffs->first;
            }
            if (leffs) {
                cerr << ", continuous numeric effects";
            }
            cerr << endl;
        }
        assert(!DEs.empty());
        #endif 
        
        set<int> makesDurBigger;
        set<int> makesDurSmaller;
        
        for (int pass = 0; pass < 3; ++pass) {
            const list<RPGBuilder::DurationExpr*> & exprs = (*(DEs[0]))[pass];
            
            list<RPGBuilder::DurationExpr*>::const_iterator dItr = exprs.begin();
            const list<RPGBuilder::DurationExpr*>::const_iterator dEnd = exprs.end();
            
            for (; dItr != dEnd; ++dItr) {
                
                const int vCount = (*dItr)->variables.size();
                
                for (int vID = 0; vID < vCount; ++vID) {
                    #ifdef STOCHASTICDURATIONS
                    v = (*dItr)->variables[vID].first;
                    if (v < 0) {
                        continue;
                    }
                    #else
                    v = (*dItr)->variables[vID];
                    #endif
                    w = (*dItr)->weights[vID];
                    
                    if (v >= pneCount) {
                        if (w > 0.0) {
                            if (pass == 0 || pass == 2) {
                                // fixed durations are reduced by negative-vars with positive weights
                                // min durations are *allowed* to be smaller but don't have to be
                                // max durations are tightened
                                makesDurSmaller.insert(v - pneCount);
                            }
                        } else if (w < 0.0) {
                            if (pass == 0 || pass == 1) {
                                // fixed durations are reduced by negative-vars with positive weights
                                // min durations are tightened
                                // max durations are *allowed* to be smaller but don't have to be
                                makesDurBigger.insert(v - pneCount);
                            }
                        }
                    } else {
                        if (w > 0.0) {
                            if (pass == 0 || pass == 1) {
                                // fixed durations are reduced by negative-vars with positive weights
                                // min durations are tightened
                                // max durations are *allowed* to be smaller but don't have to be
                                makesDurBigger.insert(v);
                            }
                        } else if (w < 0.0) {
                            if (pass == 0 || pass == 2) {
                                // fixed durations are reduced by negative-vars with positive weights
                                // min durations are *allowed* to be smaller but don't have to be
                                // max durations are tightened
                                makesDurSmaller.insert(v);
                            }
                        }
                    }
                }
            }
        }
        
        const int ctsVCount = (leffs ? (*leffs).vars.size() : 0);
        
        for (int pass = 0; pass < 2; ++pass) {
            const set<int> & loopover = (pass ? makesDurSmaller : makesDurBigger);
            set<int>::const_iterator vItr = loopover.begin();
            const set<int>::const_iterator vEnd = loopover.end();
            
            for (; vItr != vEnd; ++vItr) {
                for (int cvID = 0; cvID < ctsVCount; ++cvID) {
                    v = (*leffs).vars[cvID];
                    w = (*leffs).effects[0][cvID].constant;
                    if (localDebug) {
                        cout << "A continuous effect on " << *(RPGBuilder::getPNE(v)) << " by " << *(RPGBuilder::getInstantiatedOp(actID)) << " is made ";
                        if (pass) {
                            cout << "smaller by ";
                        } else {
                            cout << "bigger by ";
                        }
                        cout << *(RPGBuilder::getPNE(*vItr)) << endl;
                    }
                    updateForDurationDependence(v,w,*vItr,(pass == 1),workingDominanceConstraints);
                }
                
                if (ddEffs != actionToDurationDependentEffects.end() && ddEffs->first == actID) {
                    map<int,bool>::const_iterator effID = ddEffs->second.begin();
                    const map<int,bool>::const_iterator effIDEnd = ddEffs->second.end();
                    
                    for (; effID != effIDEnd; ++effID) {
                        v = rpgNumericEffects[effID->first].fluentIndex;
                        w = (effID->second ? 1.0 : -1.0);
                        if (localDebug) {
                            cout << "A duration-dependent effect on " << *(RPGBuilder::getPNE(v)) << " by " << *(RPGBuilder::getInstantiatedOp(actID)) << " is made ";
                            if (pass) {
                                cout << "smaller by ";
                            } else {
                                cout << "bigger by ";
                            }
                            cout << *(RPGBuilder::getPNE(*vItr)) << endl;
                        }
                        updateForDurationDependence(v,w,*vItr,(pass == 1),workingDominanceConstraints);
                    }
                }
            }
        }
    }
}

vector<NumericAnalysis::NumericLimitDescriptor> NumericAnalysis::goalNumericUsageLimits;

NumericAnalysis::NumericLimitDescriptor::NumericLimitDescriptor(const int & v, const double & w, const VAL::comparison_op & cOp, const double & lim)
    : op(cOp), limit(lim), optimisationLimit(false)
{
        
    const int pneCount = RPGBuilder::getPNECount();
        
    assert(v >= 0);
    assert(v < 2 * pneCount);
    
    if (v < pneCount) {
        var.insert(make_pair(v,w));
    } else {
        var.insert(make_pair(v - pneCount,-w));
    }
    
}
            
NumericAnalysis::NumericLimitDescriptor::NumericLimitDescriptor(const vector<int> & v, const vector<double> & w, const int & size, const VAL::comparison_op & cOp, const double & lim)
    : op(cOp), limit(lim), optimisationLimit(false)
{
        
        
    const int pneCount = RPGBuilder::getPNECount();
    
    for (int s = 0; s < size; ++s) {
        assert(v[s] >= 0);
        assert(v[s] < 2 * pneCount);
        
        if (v[s] < pneCount) {
            var.insert(make_pair(v[s],w[s]));
        } else {
            var.insert(make_pair(v[s] - pneCount,-w[s]));
        }
    }
    
}
            
NumericAnalysis::NumericLimitDescriptor::NumericLimitDescriptor(const vector<int> & v, const vector<double> & w, const int & size)
    : op(VAL::E_GREATEQ), limit(-DBL_MAX), optimisationLimit(true)
{
                    
    const int pneCount = RPGBuilder::getPNECount();
        
    for (int s = 0; s < size; ++s) {
        assert(v[s] >= 0 || v[s] == -4);
        assert(v[s] < 2 * pneCount);
        if (v[s] < pneCount) {
            var.insert(make_pair(v[s],w[s]));
        } else {
            var.insert(make_pair(v[s] - pneCount,-w[s]));
        }
    }
        
}

bool NumericAnalysis::safeForMetricLimit(const RPGBuilder::RPGNumericEffect & currEff,
                                         const NumericAnalysis::MaskedVariableBounds & variableBounds,
                                         const double & weightsecond)
{
    static const int pneCount = RPGBuilder::getPNECount();
    
    static const bool localDebug = false;
    
    int v = currEff.variables[0];
    if ((v >= 0 && v < pneCount) || v == -3) {
        const pair<double,double> & varBounds = variableBounds[v];
        
        if (varBounds.first == -DBL_MAX) {
            // this effect is definitely going to be a decrease effect if this variable bound holds                        
            // so, a negative weight in the metric would lead to improvement
            //
            // ((currEff.weights[0] * varBounds.first) + currEff.constant) * weight->second
            // ((currEff.weights[0] * -DBL_MAX       ) + currEff.constant) * weight->second
            //
            // currEff.weights[0] is strictly positive, so:
            // ( -DBL_MAX         + currEff.constant) * weight->second
            // -DBL_MAX * weight->second
            
            if (-weightsecond > 0.001) {
                if (localDebug) {
                    cout << "No lower bound on ";
                    if (v == -3) {
                        cout << "?duration";
                    } else {
                        cout << *(RPGBuilder::getPNE(v));
                    }
                    cout << ", and weight is " << weightsecond << ", so could lead to metric improvement\n";
                }
                return false;
            }
        } else {
            // simple case - finite bound, just evaluate the effect
            if (((currEff.weights[0] * varBounds.first) + currEff.constant) * weightsecond > 0.001) {
                if (localDebug) {
                    cout << "Lower bound of " << varBounds.first << " on ";
                    if (v == -3) {
                        cout << "?duration";
                    } else {
                        cout << *(RPGBuilder::getPNE(v));
                    }
                    cout << ", and weight is " << weightsecond << ", so could lead to metric improvement\n";
                }
                return false;
            }                                                            
        }
        
        if (varBounds.second == DBL_MAX) {
            // this effect is definitely going to be a decrease effect if this variable bound holds                        
            // so, a negative weight in the metric would lead to improvement
            //
            // ((currEff.weights[0] * varBounds.second) + currEff.constant) * weight->second
            // ((currEff.weights[0] * DBL_MAX       ) + currEff.constant) * weight->second
            //
            // currEff.weights[0] is strictly positive, so:
            // ( DBL_MAX         + currEff.constant) * weight->second
            // DBL_MAX * weight->second
            
            if (weightsecond > 0.001) {
                if (localDebug) {
                    cout << "No upper bound on ";
                    if (v == -3) {
                        cout << "?duration";
                    } else {
                        cout << *(RPGBuilder::getPNE(v));
                    }
                    cout << ", and weight is " << weightsecond << ", so could lead to metric improvement\n";
                }
                
                return false;
            }
        } else {
            // simple case - finite bound, just evaluate the effect
            if (((currEff.weights[0] * varBounds.second) + currEff.constant) * weightsecond > 0.001) {
                if (localDebug) {
                    cout << "Upper bound of " << varBounds.second << " on ";
                    if (v == -3) {
                        cout << "?duration";
                    } else {
                        cout << *(RPGBuilder::getPNE(v));
                    }
                    cout << ", and weight is " << weightsecond << ", so could lead to metric improvement\n";
                }
                return false;
            }                                                            
        }
    } else {
        
        const pair<double,double> & varBounds = variableBounds[v == -19 ? -3 : v - pneCount];
        
        if (varBounds.first == -DBL_MAX) {
            // this effect is definitely going to be a decrease effect if this variable bound holds                        
            // so, a negative weight in the metric would lead to improvement
            //
            // ((-currEff.weights[0] * varBounds.first) + currEff.constant) * weight->second
            // ((-currEff.weights[0] * -DBL_MAX       ) + currEff.constant) * weight->second
            //
            // -currEff.weights[0] is strictly negative, so:
            // ( DBL_MAX         + currEff.constant) * weight->second
            // DBL_MAX * weight->second
            
            if (weightsecond > 0.0) {
                return false;
            }
        } else {
            // simple case - finite bound, just evaluate the effect
            if (((-currEff.weights[0] * varBounds.first) + currEff.constant) * weightsecond > 0.001) {
                return false;
            }                                                            
        }
        
        if (varBounds.second == DBL_MAX) {
            // this effect is definitely going to be a decrease effect if this variable bound holds                        
            // so, a negative weight in the metric would lead to improvement
            //
            // ((-currEff.weights[0] * varBounds.second) + currEff.constant) * weight->second
            // ((-currEff.weights[0] * DBL_MAX       ) + currEff.constant) * weight->second
            //
            // -currEff.weights[0] is strictly positive, so:
            // ( -DBL_MAX         + currEff.constant) * weight->second
            // -DBL_MAX * weight->second
            
            if (-weightsecond > 0.001) {
                return false;
            }
        } else {
            // simple case - finite bound, just evaluate the effect
            if (((-currEff.weights[0] * varBounds.second) + currEff.constant) * weightsecond > 0.001) {
                return false;
            }                                            
        }
    }
    
    return true;
}

void NumericAnalysis::seeIfInducesALimit(const NumericAnalysis::NumericLimitDescriptor & hypothesisedLimit,
                                         const map<int, list<int> > & numericEffectsThatAreInConditionalEffects,
                                         map<NumericAnalysis::NumericLimitDescriptor,bool> & upperBounds)
{

    static const bool localDebug = false;
    static const int pneCount = RPGBuilder::getPNECount();
    
    const map<NumericAnalysis::NumericLimitDescriptor,bool>::iterator bItr = upperBounds.find(hypothesisedLimit);

    if (bItr != upperBounds.end()) {
        if (bItr->second) {
            // if effects on this variable are one way, check if we should update the limit
            
            NumericAnalysis::NumericLimitDescriptor * const editableFirst = const_cast<NumericAnalysis::NumericLimitDescriptor*>(&(bItr->first));
            
            if (hypothesisedLimit.op == VAL::E_GREATEQ && editableFirst->op == VAL::E_GREATEQ) {
                if (hypothesisedLimit.limit > editableFirst->limit) {
                    editableFirst->limit = hypothesisedLimit.limit;
                }
            } else if (hypothesisedLimit.op == VAL::E_GREATER && editableFirst->op == VAL::E_GREATEQ) {
                if (hypothesisedLimit.limit >= editableFirst->limit) {
                    editableFirst->limit = hypothesisedLimit.limit;
                    editableFirst->op = VAL::E_LESS;
                }
            } else if (hypothesisedLimit.op == VAL::E_GREATEQ && editableFirst->op == VAL::E_GREATER) {
                if (hypothesisedLimit.limit > editableFirst->limit) {
                    editableFirst->limit = hypothesisedLimit.limit;
                    editableFirst->op = VAL::E_GREATEQ;
                }
            } else {
                if (hypothesisedLimit.limit > editableFirst->limit) {
                    editableFirst->limit = hypothesisedLimit.limit;
                }
            }
        }
                // if we've just updated a previous constraint, we don't need to go on to one-way checking and then deduce whether to keep the limit based on that
        return;
    }
                
    if (localDebug) {
        cout << "Seeing if there's a goal limit\n";
    }
                
    bool allDecreasers = true;
    
    const vector<RPGBuilder::RPGNumericEffect> & rpgNumericEffects = RPGBuilder::getNumericEff();
    const vector<list<pair<int, Planner::time_spec> > > & neta = RPGBuilder::getRpgNumericEffectsToActions();
    
    const int effCount = rpgNumericEffects.size();
                
    for (int effID = 0; effID < effCount; ++effID) {
        const RPGBuilder::RPGNumericEffect & currEff = rpgNumericEffects[effID];
        
        const map<int,double>::const_iterator weight = hypothesisedLimit.var.find(currEff.fluentIndex);
        if (weight == hypothesisedLimit.var.end()) {
            // ignore effects on other variables
            continue;
        }
        if (localDebug) {
            cout << currEff << " affects one of the variables\n";
        }
        
        if (currEff.isAssignment) {
            // all bets are off if it's an assignment effect
            allDecreasers = false;
            break;
        }
        
        if (currEff.size > 1) {
            // for now, give up - would need to trade off many variable bounds
            allDecreasers = false;
            break;
        } else if (currEff.size == 1) {
            

            {
                list<pair<int, Planner::time_spec> >::const_iterator actItr = neta[effID].begin();
                const list<pair<int, Planner::time_spec> >::const_iterator actEnd = neta[effID].end();
                
                for (; actItr != actEnd; ++actItr) {
                    
                    if (localDebug) {
                        cout << "- Attached to " << *(RPGBuilder::getInstantiatedOp(actItr->first)) << endl;
                    }
                    
                    MaskedVariableBounds bounds;
                    
                    if (currEff.variables[0] == -3 || currEff.variables[0] == -19) {
                        bounds.tightenLower(-3, RPGBuilder::getOpMinDuration(actItr->first,0));
                        /*if (localDebug) {
                            cout << "  - Tightened lower bound on duration to " << RPGBuilder::getOpMinDuration(actItr->first,0) << " => " << bounds[-3].first << endl;
                        }*/
                        bounds.tightenUpper(-3, RPGBuilder::getOpMaxDuration(actItr->first,0));
                        /*if (localDebug) {
                            cout << "  - Tightened upper bound on duration to " << RPGBuilder::getOpMaxDuration(actItr->first,0) << " => " << bounds[-3].second << endl;
                        }*/
                        
                    } else {
                        const list<int> & preList = (actItr->second == Planner::E_AT_START ? RPGBuilder::getStartPreNumerics()[actItr->first]
                                                                                       : RPGBuilder::getEndPreNumerics()[actItr->first]);
                        
                        list<int>::const_iterator npItr = preList.begin();
                        const list<int>::const_iterator npEnd = preList.end();
                        
                        for (; npItr != npEnd; ++npItr) {
                            bounds.applyPreToBounds(RPGBuilder::getNumericPreTable()[*npItr]);
                        }
                                                                                        
                    }
                    
                    if (!safeForMetricLimit(currEff, bounds, weight->second)) {
                        if (localDebug) {
                            cout << "* Not safe\n";
                        }
                        allDecreasers = false;                   
                        break;
                    }
                    
                    
                }
            }

            if (allDecreasers) {
                const map<int, list<int> >::const_iterator ceItr = numericEffectsThatAreInConditionalEffects.find(effID);
                if (ceItr != numericEffectsThatAreInConditionalEffects.end()) {
                    list<int>::const_iterator actItr = ceItr->second.begin();
                    const list<int>::const_iterator actEnd = ceItr->second.end();
                    
                    for (; actItr != actEnd; ++actItr) {
                        
                        if (localDebug) {
                            cout << "- Attached to a conditional effect of " << *(RPGBuilder::getInstantiatedOp(*actItr)) << endl;
                        }
                        
                        const list<RPGBuilder::ConditionalEffect> & condEffs = RPGBuilder::getActionsToConditionalEffects()[*actItr];
                        list<RPGBuilder::ConditionalEffect>::const_iterator currCEItr = condEffs.begin();
                        const list<RPGBuilder::ConditionalEffect>::const_iterator currCEEnd = condEffs.end();
                        
                        for (; currCEItr != currCEEnd; ++currCEItr) {
                            
                            const list<pair<int, Planner::time_spec> > & neMatchIn = currCEItr->getNumericEffects();
                            
                            list<pair<int, Planner::time_spec> >::const_iterator neMatchItr = neMatchIn.begin();
                            const list<pair<int, Planner::time_spec> >::const_iterator neMatchEnd = neMatchIn.end();
                            
                            for (; neMatchItr != neMatchEnd; ++neMatchItr) {
                                if (neMatchItr->first != effID) {
                                    continue;
                                }
                                MaskedVariableBounds actBounds;
                                if (currEff.variables[0] == -3 || currEff.variables[0] == -19) {
                                    actBounds.tightenLower(-3, RPGBuilder::getOpMinDuration(*actItr,0));
                                    actBounds.tightenUpper(-3, RPGBuilder::getOpMaxDuration(*actItr,0));
                                } else {
                                    
                                    {
                                        const list<int> & preList = (neMatchItr->second == Planner::E_AT_START ? RPGBuilder::getStartPreNumerics()[*actItr]
                                                                                                           : RPGBuilder::getEndPreNumerics()[*actItr]);
                                    
                                        list<int>::const_iterator npItr = preList.begin();
                                        const list<int>::const_iterator npEnd = preList.end();
                                        
                                        for (; npItr != npEnd; ++npItr) {
                                            actBounds.applyPreToBounds(RPGBuilder::getNumericPreTable()[*npItr]);
                                        }
                                    }
                                    
                                    {
                                        const list<pair<int, Planner::time_spec> > & preListB = currCEItr->getNumericPreconditions();
                                        
                                        list<pair<int, Planner::time_spec> >::const_iterator npItr = preListB.begin();
                                        const list<pair<int, Planner::time_spec> >::const_iterator npEnd = preListB.end();
                                        
                                        for (; npItr != npEnd; ++npItr) {
                                            if (npItr->second != neMatchItr->second) {
                                                continue;
                                            }
                                            actBounds.applyPreToBounds(RPGBuilder::getNumericPreTable()[npItr->first]);
                                        }
                                                                                
                                    }
                                    
                                }
                        
                                if (!safeForMetricLimit(currEff, actBounds, weight->second)) {
                                    if (localDebug) {
                                        cout << "* Not safe\n";
                                    }
                                    allDecreasers = false;                   
                                    break;
                                }
                                
                            }
                        }
                        
                    }
                }
            }
            
            if (!allDecreasers) {
                break;
            }
            
        } else {
            // simple case - variable depends on nothing
            // see if it can ever lead to metric improvement
            if (currEff.constant * weight->second > 0.0) {
                allDecreasers = false;                   
                break;
            }            
        }
    }
    
    upperBounds.insert(make_pair(hypothesisedLimit, allDecreasers));

}

void NumericAnalysis::findGoalNumericUsageLimits()
{
    static const bool localDebug = true;
    
    if (!doGoalLimitAnalysis) {        
        return;
    }
    
    map<int, list<int> > numericEffectsThatAreInConditionalEffects;
    
    {
        const vector<list<RPGBuilder::ConditionalEffect> > & condEffs = RPGBuilder::getActionsToConditionalEffects();
        const int actCount = condEffs.size();
        for (int act = 0; act < actCount; ++act) {
            if (RPGBuilder::rogueActions[act]) {
                continue;                    
            }
            
            if (condEffs[act].empty()) {
                continue;
            }
            
            set<int> usedInThisAct;
            
            list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[act].begin();
            const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[act].end();
            
            for (; ceItr != ceEnd; ++ceItr) {
                
                if (ceItr->getNumericEffects().empty()) {
                    continue;
                }
                
                const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
                list<pair<int, Planner::time_spec> >::const_iterator neItr = numEffs.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator neEnd = numEffs.end();
                
                for (; neItr != neEnd; ++neItr) {
                    usedInThisAct.insert(neItr->first);
                }
            }
            
            set<int>::const_iterator uItr = usedInThisAct.begin();
            const set<int>::const_iterator uEnd = usedInThisAct.end();
            
            for (; uItr != uEnd; ++uItr) {
                numericEffectsThatAreInConditionalEffects[*uItr].push_back(act);
            }
        }

        
    }
    
    const int pneCount =  RPGBuilder::getPNECount();
    
    const list<pair<int, int> > & numericGoals = RPGBuilder::getNumericRPGGoals();
    
    map<NumericLimitDescriptor,bool> upperBounds;
    
    if (Globals::optimiseSolutionQuality) {
        RPGBuilder::Metric * theMetric = RPGBuilder::getMetric();
        
        if (theMetric) {
            
            if (localDebug) {
                cout << "Seeing if metric is defined in terms of task vars or a minimal value of makespan\n";
            }
            
            const int size = theMetric->variables.size();
            
            vector<double> weights(size);
            vector<int> vars(size);
                      
            bool metricOnlyUsesTaskVariables = true;
            
            list<int>::const_iterator mvItr = theMetric->variables.begin();
            list<double>::const_iterator mwItr = theMetric->weights.begin();
            const list<int>::const_iterator mvEnd = theMetric->variables.end();
            
            for (int s = 0; mvItr != mvEnd; ++mvItr, ++mwItr, ++s) {
                if (*mvItr < 0) {
                    if (*mvItr != -4) { // :makespan
                        metricOnlyUsesTaskVariables = false;
                        break;
                    }
                }
                if (theMetric->minimise) {
                    weights[s] = -(*mwItr);
                } else {
                    weights[s] = (*mwItr);
                }
                if (*mvItr == -4 && weights[s] > 0.0) {
                    if (localDebug) {
                        cout << "- Found :makespan, but is better to be maximised.\n";
                    }
                    metricOnlyUsesTaskVariables = false;
                    break;
                }
                vars[s] = *mvItr;
            }
            
            if (metricOnlyUsesTaskVariables) {
                if (localDebug) {
                    cout << "- Yes it is\n";
                }
                NumericLimitDescriptor hypothesisedLimit(vars, weights, size);            
                seeIfInducesALimit(hypothesisedLimit, numericEffectsThatAreInConditionalEffects, upperBounds);
            }
            
        }
    }
    
    
    list<pair<int, int> >::const_iterator ngItr = numericGoals.begin();
    const list<pair<int, int> >::const_iterator ngEnd = numericGoals.end();
    
    for (; ngItr != ngEnd; ++ngItr) {
        for (int pass = 0; pass < 2; ++pass) {
            const int preID = (pass ? ngItr->second : ngItr->first);            
            if (preID == -1) continue;
            
            const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[preID];
            
            NumericLimitDescriptor hypothesisedLimit;
            
            if (currPre.LHSVariable < 2 * pneCount) {
                hypothesisedLimit = NumericLimitDescriptor(currPre.LHSVariable, 1.0, currPre.op, currPre.RHSConstant);
            } else {
                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
                hypothesisedLimit = NumericLimitDescriptor(currAV.fluents, currAV.weights, currAV.size, currPre.op, currPre.RHSConstant - currAV.constant);
            }
                                    
            seeIfInducesALimit(hypothesisedLimit, numericEffectsThatAreInConditionalEffects, upperBounds);
        }
    }
    
    {        
        map<NumericLimitDescriptor,bool>::const_iterator limItr = upperBounds.begin();
        const map<NumericLimitDescriptor,bool>::const_iterator limEnd = upperBounds.end();
        
        for (; limItr != limEnd; ++limItr) {
            if (!limItr->second) {
                // limit not defined - not all effects were decreasers/increasers
                continue;
            }

            // if we get this far, we now have a limit
            cout << "Recognised a monotonic-change-induced limit on ";
            
            {
                map<int,double>::const_iterator vItr = limItr->first.var.begin();
                const map<int,double>::const_iterator vEnd = limItr->first.var.end();
                
                for (bool second=false; vItr != vEnd; ++vItr, second=true) {
                    if (second) {
                        cout << " + ";
                    }
                    if (vItr->second != 1.0) {
                        cout << vItr->second << "*";
                    }
                    if (vItr->first < 0) {
                        cout << "<special>";
                    } else {
                        cout << "var" << vItr->first;
                        cout.flush();
                        cout << *(RPGBuilder::getPNE(vItr->first));
                    }
                }
            }
            cout << std::endl;
            switch (limItr->first.op) {
                case VAL::E_GREATEQ:
                {
                    cout << "- Must be >= ";
                    break;
                }
                case VAL::E_GREATER:                
                {
                    cout << "- Must be > ";
                    break;
                }                                
                default:                    
                {
                    cout << "Internal error - must only have > or >= limits here\n";
                    exit(1);
                }
            }
            if (limItr->first.limit == -DBL_MAX) {
                assert(limItr->first.optimisationLimit);
                cout << " the metric";
            } else {
                cout << limItr->first.limit;
                if (limItr->first.optimisationLimit) {
                    cout << " and/or the metric";
                }
            }
            cout << std::endl;
            goalNumericUsageLimits.push_back(limItr->first);
        }
    }
    
    considerCostsOfLiteralGoalsReachedByGoalOnlyOperators();
}


#endif

vector<double> NumericAnalysis::maximumPositiveGradientOnVariable;
vector<double> NumericAnalysis::maximumNegativeGradientOnVariable;

vector<bool> NumericAnalysis::variableOnlyIncreasesByGradients;
vector<bool> NumericAnalysis::variableOnlyDecreasesByGradients;


void NumericAnalysis::findMaximumGradients()
{

    const int varCount = RPGBuilder::getPNECount();
    maximumNegativeGradientOnVariable.resize(varCount,0.0);
    maximumPositiveGradientOnVariable.resize(varCount,0.0);
    variableOnlyDecreasesByGradients.resize(varCount,true);
    variableOnlyIncreasesByGradients.resize(varCount,true);
    
    
    const vector<RPGBuilder::LinearEffects*> & ctsEffs = RPGBuilder::getLinearDiscretisation();
    
    const int actCount = ctsEffs.size();
    int vCount;
    bool selfOverlaps;
    double w;
    int v;
    
    for (int act = 0; act < actCount; ++act) {
        if (RPGBuilder::rogueActions[act]) {
            continue;
        }
        if (!ctsEffs[act]) {
            continue;
        }
        selfOverlaps = !RPGBuilder::isSelfMutex(act);
        
        vCount = ctsEffs[act]->vars.size();
        
        for (int i = 0; i < vCount; ++i) {
            w = ctsEffs[act]->effects[0][i].constant;
            v = ctsEffs[act]->vars[i];
            if (w > 0.0) {
                if (selfOverlaps) {
                    maximumPositiveGradientOnVariable[v] = DBL_MAX;
                } else {
                    if (maximumPositiveGradientOnVariable[v] != DBL_MAX) {
                        maximumPositiveGradientOnVariable[v] += w;
                    }
                }
            } else if (w < 0.0) {
                if (selfOverlaps) {
                    maximumNegativeGradientOnVariable[v] = -DBL_MAX;
                } else {
                    if (maximumNegativeGradientOnVariable[v] != -DBL_MAX) {
                        maximumNegativeGradientOnVariable[v] += w;
                    }
                }
            }
        }
    }
    
    const vector<RPGBuilder::RPGNumericEffect> & numericEffs = RPGBuilder::getNumericEff();
    const vector<list<pair<int, Planner::time_spec> > > & eta = RPGBuilder::getRpgNumericEffectsToActions();

    const int effCount = numericEffs.size();
    
    for (int eff = 0; eff < effCount; ++eff) {
        if (eta[eff].empty()) {
            continue;
        }
        if (numericEffs[eff].isAssignment || numericEffs[eff].size) {
            // simplication: assume that assignment could be increase or decrease
            // and effects that are non-constant could have positive or negative outcome
            variableOnlyDecreasesByGradients[numericEffs[eff].fluentIndex] = false;
            variableOnlyIncreasesByGradients[numericEffs[eff].fluentIndex] = false;
        } else {
            if (numericEffs[eff].constant > 0) {
                variableOnlyIncreasesByGradients[numericEffs[eff].fluentIndex] = false;
            } else if (numericEffs[eff].constant < 0) {
                variableOnlyDecreasesByGradients[numericEffs[eff].fluentIndex] = false;
            }
        }
    }
}


void NumericAnalysis::findDominanceConstraintsAndMetricTrackingVariables()
{
    const int pneCount =  RPGBuilder::getPNECount();
    
    const vector<RPGBuilder::RPGNumericPrecondition> & rpgNumericPreconditions = RPGBuilder::getNumericPreTable();
    const vector<RPGBuilder::ArtificialVariable> & rpgArtificialVariables = RPGBuilder::getArtificialVariableTable();
    
    dominanceConstraints.resize(pneCount, E_NODOMINANCE);
    
    list<int> knownToBeUseful;
    
    for (int i = 0; i < pneCount; ++i) {
        
        const int negativeI = i + pneCount;
        //PNE* const currPNE = RPGBuilder::getPNE(i);
        
        { // case one - never appears as a precondition, presume it's a tracking quantity
            bool neverInPrecondition = true;
            const int rnpCount = rpgNumericPreconditions.size();
            for (int rnp = 0; rnp < rnpCount; ++rnp) {
                const RPGBuilder::RPGNumericPrecondition & currRNP = rpgNumericPreconditions[rnp];                
                if (currRNP.LHSVariable == i || currRNP.LHSVariable == negativeI
                    ||  currRNP.RHSVariable == i || currRNP.RHSVariable == negativeI) {
                    neverInPrecondition = false;
                    break;
                }
            }
            if (neverInPrecondition) {
                const int avCount = rpgArtificialVariables.size();
                for (int av = 0; av < avCount; ++av) {
                    const RPGBuilder::ArtificialVariable & currAV = rpgArtificialVariables[av];
                    const int avfSize = currAV.size;
                    for (int f = 0; f < avfSize; ++f) {
                        const int currF = currAV.fluents[f];
                        if (currF == i || currF == negativeI) {
                            neverInPrecondition = false;
                            break;
                        }
                    }
                }
            }
            if (neverInPrecondition) {
                // cout << "Have a metric tracking fluent: " << *currPNE << "\n";
                dominanceConstraints[i] = E_IRRELEVANT;
            }
        }
    }
    
    
    // case two - also must not be needed for a duration
    {
        
        const int actCount = instantiatedOp::howMany();
        for (int actID = 0; actID < actCount; ++actID) {
            
            if (RPGBuilder::rogueActions[actID]) {
                continue;
            }
            
            const vector<RPGBuilder::RPGDuration*> & duration = RPGBuilder::getRPGDEs(actID);
            
            if (duration.empty()) {
                continue;
            }
            
            for (int pass = 0; pass < 3; ++pass) {
                const list<RPGBuilder::DurationExpr *> & loopover = (*(duration[0]))[pass];
                
                list<RPGBuilder::DurationExpr *>::const_iterator deItr = loopover.begin();
                const list<RPGBuilder::DurationExpr *>::const_iterator deEnd = loopover.end();
                
                for (; deItr != deEnd; ++deItr) {
                    
                    const int vCount = (*deItr)->variables.size();
                    
                    for (int vi = 0; vi < vCount; ++vi) {
                        dominanceConstraints[(*deItr)->variables[vi]] = E_NODOMINANCE;
                    }
                    
                }
            }
            
        }
        
    }
    
    // case three - also must not appear as an input to an effect on a non-tracking variable
    
    for (int i = 0; i < pneCount; ++i) {
        if (dominanceConstraints[i] != E_IRRELEVANT) {
            knownToBeUseful.push_back(i);
        }
    }
    
    vector<bool> inputToAnEffect(pneCount, false);
    
    while (!knownToBeUseful.empty()) {
        list<int> newKnownToBeUseful;
        
        vector<RPGBuilder::RPGNumericEffect> & effs = RPGBuilder::getNumericEff();
        
        const int effCount = effs.size();
        int currVar;
        for (int effID = 0; effID < effCount; ++effID) {
            if (dominanceConstraints[effs[effID].fluentIndex] == E_IRRELEVANT) {
                // ignore effects on irrelevant variables
                continue;
            }
            
            for (int i = 0; i < effs[effID].size; ++i) {
                currVar = effs[effID].variables[i];
                if (currVar < 0) {
                    // ignore terms such as ?duration
                    continue;
                }
                if (currVar >= pneCount) {
                    currVar -= pneCount;
                }
                
                if (dominanceConstraints[currVar] == E_IRRELEVANT) {
                    // this variable is an input to an effect on a known-useful variable
                    // it isn't irrelvant any more...
                    dominanceConstraints[currVar] = E_NODOMINANCE;
                    inputToAnEffect[currVar] = true;
                    // ...and next time round, make sure the inputs to any effects on this variable
                    // are also not marked as irrelevant
                    newKnownToBeUseful.push_back(currVar);
                }
            }
        }
        
        knownToBeUseful.swap(newKnownToBeUseful);
    }
    
    #ifdef POPF3ANALYSIS
    
    if (Globals::optimiseSolutionQuality) {
        RPGBuilder::Metric * theMetric = RPGBuilder::getMetric();
        
        if (theMetric) {
            list<double>::const_iterator mwItr = theMetric->weights.begin();
            list<int>::const_iterator mvItr = theMetric->variables.begin();
            const list<int>::const_iterator mvEnd = theMetric->variables.end();
            
            for (; mvItr != mvEnd; ++mvItr, ++mwItr) {
                if (*mvItr >= 0) {
                    if (dominanceConstraints[*mvItr] == E_IRRELEVANT) {
                        if (Globals::globalVerbosity & 32) {
                            cout << "Keeping " << *(RPGBuilder::getPNE(*mvItr)) << " as a metric-tracking variable\n";
                        }
                        dominanceConstraints[*mvItr] = E_METRICTRACKING;
                        knownToBeUseful.push_back(*mvItr);
                    }
                    if (theMetric->minimise) {
                        // metric is to minimise: bigger vars will give a better metric iff they have negative weights
                        metricVarIsBetterBigger[*mvItr] = (*mwItr < 0);
                    } else {
                        // metric is to maximise: bigger vars will give a better metric iff they have positive weights
                        metricVarIsBetterBigger[*mvItr] = (*mwItr > 0);
                    }
                }
            }
            
            while (!knownToBeUseful.empty()) {
                list<int> newKnownToBeUseful;
                
                vector<RPGBuilder::RPGNumericEffect> & effs = RPGBuilder::getNumericEff();
                
                const int effCount = effs.size();
                int currVar;
                for (int effID = 0; effID < effCount; ++effID) {
                    if (dominanceConstraints[effs[effID].fluentIndex]!= E_METRICTRACKING) {
                        //if (Globals::globalVerbosity & 32) {
                        //    cout << "Ignoring effects on " << *(RPGBuilder::getPNE(effs[effID].fluentIndex)) << " as it's not just been labelled as being metric-tracking\n";
                        //}
                        // ignore effects on irrelevant variables
                        continue;
                    }
                    
                    if (Globals::globalVerbosity & 32) {
                        cout << effs[effID] << ":\n";
                    }
                        
                    for (int i = 0; i < effs[effID].size; ++i) {
                        currVar = effs[effID].variables[i];
                        if (currVar < 0) {
                            // ignore terms such as ?duration
                            continue;
                        }
                        if (currVar >= pneCount) {
                            currVar -= pneCount;
                        }
                        
                        
                        if (dominanceConstraints[currVar] == E_IRRELEVANT || dominanceConstraints[currVar] == E_METRICTRACKING) {
                            // this variable is an input to an effect on a known-useful variable
                            // it isn't irrelvant any more...
                            dominanceConstraints[currVar] = E_NODOMINANCE;
                            if (Globals::globalVerbosity & 32) {
                                cout << "Promoting " << *(RPGBuilder::getPNE(currVar)) << " to not being irrelevant\n";
                            }
                            inputToAnEffect[currVar] = true;
                            // ...and next time round, make sure the inputs to any effects on this variable
                            // are also not marked as irrelevant
                            newKnownToBeUseful.push_back(currVar);
                        } else {
                            if (Globals::globalVerbosity & 32) {
                                cout << "Not changing " << *(RPGBuilder::getPNE(currVar)) << " as it's not previously considered to be irrelevant\n";
                            }
                        }
                    }
                }
                
                knownToBeUseful.swap(newKnownToBeUseful);
            }
        }
    }

    #endif

#ifndef NDEBUG

    {
        vector<RPGBuilder::RPGNumericEffect> & effs = RPGBuilder::getNumericEff();
                
        const int effCount = effs.size();
        int currVar;
        for (int effID = 0; effID < effCount; ++effID) {
            if (dominanceConstraints[effs[effID].fluentIndex] == E_IRRELEVANT) {
                // ignore effects on irrelevant variables
                continue;
            }
            
            for (int i = 0; i < effs[effID].size; ++i) {
                currVar = effs[effID].variables[i];
                if (currVar < 0) {
                    // ignore terms such as ?duration
                    continue;
                }
                if (currVar >= pneCount) {
                    currVar -= pneCount;
                }
                assert(dominanceConstraints[currVar] != E_IRRELEVANT);
            }
        }
    }

#endif
    
    checkConditionalNumericEffectsAreOnlyOnMetricTrackingVariables();

    
    #ifdef POPF3ANALYSIS
    bool anyCandidates = false;
    vector<dominance_constraint> workingDCs(dominanceConstraints);
    map<int, list<int> > numericPreconditionsThatAreInCondEffs;
    bool definedNumericPreconditionsThatAreInCondEffs = false;
    
    for (int i = 0; i < pneCount; ++i) {
        
        if (workingDCs[i] == E_NODOMINANCE && !inputToAnEffect[i]) {
            if (!definedNumericPreconditionsThatAreInCondEffs) {
                const vector<list<RPGBuilder::ConditionalEffect> > & condEffs = RPGBuilder::getActionsToConditionalEffects();
                
                const int actCount = condEffs.size();
                for (int act = 0; act < actCount; ++act) {
                    if (RPGBuilder::rogueActions[act]) {
                        continue;                    
                    }
                    
                    if (condEffs[act].empty()) {
                        continue;
                    }
                    
                    set<int> usedInThisAct;
                    
                    list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[act].begin();
                    const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[act].end();
                    
                    for (; ceItr != ceEnd; ++ceItr) {
                        
                        if (ceItr->getNumericEffects().empty()) {
                            continue;
                        }
                        
                        const list<pair<int, Planner::time_spec> > & numPres = ceItr->getNumericPreconditions();
                        list<pair<int, Planner::time_spec> >::const_iterator npItr = numPres.begin();
                        const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numPres.end();
                        
                        for (; npItr != npEnd; ++npItr) {
                            usedInThisAct.insert(npItr->first);
                        }
                    }
                    
                    set<int>::const_iterator uItr = usedInThisAct.begin();
                    const set<int>::const_iterator uEnd = usedInThisAct.end();
                    
                    for (; uItr != uEnd; ++uItr) {
                        numericPreconditionsThatAreInCondEffs[*uItr].push_back(act);
                    }
                }
                
                definedNumericPreconditionsThatAreInCondEffs = true;
            }
            if ((workingDCs[i] = preconditionDominanceInOneDirection(i,numericPreconditionsThatAreInCondEffs)) != E_NODOMINANCE) {
                anyCandidates = true;
            }
        }
    }
    
    if (!anyCandidates) {        
        return;
    }
    
    /*for (int i = 0; i < pneCount; ++i) {
        
        if (workingDCs[i] == E_BIGGERISBETTER) {
            cout << "Have identified that bigger values of " << *(RPGBuilder::getPNE(i)) << " might be preferable\n";
        } else if (workingDCs[i] == E_SMALLERISBETTER) {
            cout << "Have identified that smaller values of " << *(RPGBuilder::getPNE(i)) << " might be preferable\n";
        }
    }*/
    
    considerConflictingDominanceThroughEffects(workingDCs);
    for (int i = 0; i < pneCount; ++i) {
        
        if (workingDCs[i] == E_BIGGERISBETTER) {
            dominanceConstraints[i] = E_BIGGERISBETTER;
            cout << "Have identified that bigger values of " << *(RPGBuilder::getPNE(i)) << " are preferable\n";
        } else if (workingDCs[i] == E_SMALLERISBETTER) {
            dominanceConstraints[i] = E_SMALLERISBETTER;
            cout << "Have identified that smaller values of " << *(RPGBuilder::getPNE(i)) << " are preferable\n";
        }
    }

    #endif
    
    if (readBounds) {
        ifstream boundsFile("bounds");
        if (!boundsFile.good()) {
            cout << "Exiting: could not open file 'bounds'\n";
            exit(1);
        }
        while (!boundsFile.eof()) {
            string varName;
            getline(boundsFile,varName);
            if (varName.empty()) {
                break;
            }
            string setTo;
            getline(boundsFile,setTo);
            int v = 0;
            for (; v < pneCount; ++v) {
                ostringstream vn;
                vn << *(RPGBuilder::getPNE(v));
                string asString = vn.str();
                if (varName == asString) {
                    break;
                }
            }
            if (v == pneCount) {
                cerr << "Exiting: variable '" << varName << "' not found, or is considered static\n";
                exit(1);
            }
            
            if (setTo == "E_BIGGERISBETTER") {
                dominanceConstraints[v] = E_BIGGERISBETTER;
            } else if (setTo == "E_SMALLERISBETTER") {
                dominanceConstraints[v] = E_SMALLERISBETTER;
            } else {
                cerr << "Error: " << setTo << " has to be one of either E_BIGGERISBETTER or E_SMALLERISBETTER\n";
                exit(1);
            }
            cout << "Forced dominance constraint on " << *(RPGBuilder::getPNE(v)) << endl;
        }        
        boundsFile.close();
    }
}

bool durationsAreConstantBounded(const list<pair<int, Planner::time_spec> > & actions)
{
    static const bool localDebug = true;
   
    list<pair<int, Planner::time_spec> >::const_iterator actItr = actions.begin();
    const list<pair<int, Planner::time_spec> >::const_iterator actEnd = actions.end();
    
    int de;
    for (; actItr != actEnd; ++actItr) {
        if (RPGBuilder::rogueActions[actItr->first] != RPGBuilder::OT_NORMAL_ACTION) {
            continue;
        }
        const vector<RPGBuilder::RPGDuration*> & duration = RPGBuilder::getRPGDEs(actItr->first);
                
        if (duration.empty()) {
            cerr << "Fatal internal error: have a duration-dependent effect on " << *(RPGBuilder::getInstantiatedOp(actItr->first)) << ", but no durations\n";
            assert(!duration.empty()); // would mean a non-temporal action has a duration-dependent effect
        }
        
        for (de = 0; de < 3; ++de) {
            const list<RPGBuilder::DurationExpr *> & currList = (*(duration[0]))[de];
            {
                list<RPGBuilder::DurationExpr*>::const_iterator exprItr = currList.begin();
                const list<RPGBuilder::DurationExpr*>::const_iterator exprEnd = currList.end();
                for (; exprItr != exprEnd; ++exprItr) {
                    if (!(*exprItr)->variables.empty()) { // if the duration constraint depends on other variables
                        if (localDebug) {
                            cout << "- Duration of " << *(RPGBuilder::getInstantiatedOp(actItr->first)) << " is not constant-bounded\n";
                        }
                        return false;
                    }
                }
            }
        }        
    }
    
    return true;
} 

void NumericAnalysis::findWhichVariablesHaveOrderIndependentEffects()
{
    static const bool localDebug = true;
    const int pneCount =  RPGBuilder::getPNECount();
    
    allEffectsAreOrderIndependent.resize(pneCount, E_ORDER_INDEPENDENT);
    
    const vector<RPGBuilder::RPGNumericEffect> & numericEffects = RPGBuilder::getNumericEff();
    
    const int effCount = numericEffects.size();
    
    for (int i = 0; i < effCount; ++i) {
        
        if (numericEffects[i].isAssignment) {  // assignment effects cannot be ordered arbitrarily
            allEffectsAreOrderIndependent[numericEffects[i].fluentIndex] = E_ORDER_DEPENDENT;
            if (localDebug) {
                cout << "Assignment numeric effect " << numericEffects[i] << " makes effects on " << numericEffects[i].fluentIndex << " be order-dependent\n";
            }
        } else if (numericEffects[i].size > 1) {
            allEffectsAreOrderIndependent[numericEffects[i].fluentIndex] = E_ORDER_DEPENDENT;
            if (localDebug) {
                cout << "Multi-variate effect " << numericEffects[i] << " makes effects on " << numericEffects[i].fluentIndex << " be order-dependent\n";
            }
        } else if (numericEffects[i].size == 1) {
            // the only order-independent non-constant effects are those that depend on the duration
            // of an action, where that duration does not depend on variables
            
            #ifdef POPF3ANALYSIS
            const map<int,double>::const_iterator tItr = tickerVariables.find(numericEffects[i].variables[0] >= pneCount
                                                                              ? numericEffects[i].variables[0] - pneCount
                                                                              : numericEffects[i].variables[0]);
            
            if (tItr != tickerVariables.end()) {
                continue;
            }
            #endif
            
            
            if (   numericEffects[i].variables[0] != -3 // -3 denotes the variable ?duration
                && numericEffects[i].variables[0] != -19) { // -19 denotes -?duration
                if (localDebug) {
                    cout << "Numeric effect " << numericEffects[i] << " makes effects on " << numericEffects[i].fluentIndex << " be order-dependent\n";
                }
                allEffectsAreOrderIndependent[numericEffects[i].fluentIndex] = E_ORDER_DEPENDENT;
                continue;   
            }
            
            if (!durationsAreConstantBounded(RPGBuilder::getRpgNumericEffectsToActions()[i])) {
                if (localDebug) {
                    cout << "Non-constant-bounded duration-dependent effect " << numericEffects[i] << " makes effects on " << numericEffects[i].fluentIndex << " be order-dependent\n";
                }
                allEffectsAreOrderIndependent[numericEffects[i].fluentIndex] = E_ORDER_DEPENDENT;
            }
        }        
    }
    
    const vector<RPGBuilder::LinearEffects*> ctsEffects = RPGBuilder::getLinearDiscretisation();
    const int opCount = ctsEffects.size();
    
    for (int op = 0; op < opCount; ++op) {
        if (!(ctsEffects[op])) continue;
        
        list<pair<int, Planner::time_spec> > dummyList;
        dummyList.push_back(make_pair(op, Planner::E_AT_START));
        
        const bool constantDur = durationsAreConstantBounded(dummyList);
        
        const int vCount = ctsEffects[op]->vars.size();
        for (int v = 0; v < vCount; ++v) {
            order_independence & currStatus = allEffectsAreOrderIndependent[ctsEffects[op]->vars[v]];
            if (!constantDur) { // if the duration is non constant
                currStatus = E_ORDER_DEPENDENT; // then the effect could be order-dependent
            } else if (currStatus == E_ORDER_INDEPENDENT) { // otherwise, if it's currently order-independent
                currStatus = E_ORDER_INDEPENDENT_AT_END; // then the CTS effect is order-independent, but only if no actions are executing
            }
        }
        
    }
    
}


#ifdef POPF3ANALYSIS

vector<bool> NumericAnalysis::onlyAtStartConditionsOnVariable;

void NumericAnalysis::findWhichVariablesAreOnlyInAtStarts()
{
    const int pneCount =  RPGBuilder::getPNECount();
    
    onlyAtStartConditionsOnVariable.resize(pneCount, true);
    
    const vector<RPGBuilder::RPGNumericPrecondition> & numPres = RPGBuilder::getNumericPreTable();
    
    vector<list<pair<int, Planner::time_spec> > > & presToActions = RPGBuilder::getRawNumericPresToActions();
    
    assert(numPres.size() == presToActions.size());
    
    const int npCount = numPres.size();
    
    for (int np = 0; np < npCount; ++np) {
        list<pair<int, Planner::time_spec> >::const_iterator depItr = presToActions[np].begin();
        const list<pair<int, Planner::time_spec> >::const_iterator depEnd = presToActions[np].end();
        
        for (; depItr != depEnd; ++depItr) {
            if (depItr->second != Planner::E_AT_START) {
                break;
            }
        }
        
        if (depItr != depEnd) { // then it was found in an invariant
            
            if (numPres[np].LHSVariable < pneCount) {
                onlyAtStartConditionsOnVariable[numPres[np].LHSVariable] = false;
            } else if (numPres[np].LHSVariable < 2 * pneCount) {
                onlyAtStartConditionsOnVariable[numPres[np].LHSVariable - pneCount] = false;
            } else {
                const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(numPres[np].LHSVariable);
                for (int s = 0; s < currAV.size; ++s) {
                    if (currAV.fluents[s] < 0) {
                        continue;
                    } else if (currAV.fluents[s] < pneCount) {
                        onlyAtStartConditionsOnVariable[currAV.fluents[s]] = false;
                    } else {
                        onlyAtStartConditionsOnVariable[currAV.fluents[s] - pneCount] = false;
                    }
                }
            }
            
        }
    }
}  

bool NumericAnalysis::metricIsMonotonicallyWorsening = false;

void NumericAnalysis::findWhetherTheMetricIsMonotonicallyWorsening()
{
    static bool knowWhetherTheMetricIsMonotonicallyWorsening = false;
    
    if (knowWhetherTheMetricIsMonotonicallyWorsening) {
        return;
    }
    
    knowWhetherTheMetricIsMonotonicallyWorsening = true;
    
    const int lCount = goalNumericUsageLimits.size();
    
    for (int l = 0; l < lCount; ++l) {
        const NumericLimitDescriptor & currLim = goalNumericUsageLimits[l];
        
        if (currLim.optimisationLimit) {
            metricIsMonotonicallyWorsening = true;
            break;
        }
    }
    
    if (!metricIsMonotonicallyWorsening && RPGBuilder::getMetric() && RPGBuilder::getMetric()->variables.empty()) {        
        metricIsMonotonicallyWorsening = true;//TemporalAnalysis::goalSoftDeadlinesHaveMonotonicallyWorseningCosts();        
    }
    
}

map<int, bool> NumericAnalysis::metricVarIsBetterBigger;        
map<int,double> NumericAnalysis::tickerVariables;

void NumericAnalysis::findVariablesThatAreTickers()
{

    {
        const vector<RPGBuilder::LinearEffects*> & ctsEffs = RPGBuilder::getLinearDiscretisation();    
        const int actCount = ctsEffs.size();
        for (int actID = 0; actID < actCount; ++actID) {
            if (RPGBuilder::rogueActions[actID] != RPGBuilder::OT_PROCESS) continue;
            if (!ctsEffs[actID]) continue;
            
            const int varCount = ctsEffs[actID]->vars.size();
            
            for (int i = 0; i < varCount; ++i) {
                tickerVariables.insert(make_pair(ctsEffs[actID]->vars[i],0.0)).first->second += ctsEffs[actID]->effects[0][i].constant;
            }                        
        }
            
    }
    
    if (tickerVariables.empty()) {
        return;
    }
    
    const vector<RPGBuilder::RPGNumericEffect> & numericEffects = RPGBuilder::getNumericEff();
    const vector<list<pair<int, Planner::time_spec> > > & eta = RPGBuilder::getRpgNumericEffectsToActions();
    
    const int effCount = numericEffects.size();
    
    for (int effID = 0; !tickerVariables.empty() && effID < effCount; ++effID) {
        if (eta[effID].empty()) {
            continue;
        }
        tickerVariables.erase(numericEffects[effID].fluentIndex);
    }

    if (tickerVariables.empty()) {
        return;
    }
    
    const vector<list<RPGBuilder::ConditionalEffect> > & condEffs = RPGBuilder::getActionsToConditionalEffects();
    
    const int actCount = condEffs.size();
    for (int act = 0; act < actCount; ++act) {
        if (RPGBuilder::rogueActions[act]) {
            continue;                    
        }
        
        if (condEffs[act].empty()) {
            continue;
        }
        
        list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[act].begin();
        const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[act].end();
        
        for (; ceItr != ceEnd; ++ceItr) {
            const list<pair<int, Planner::time_spec> > & numPres = ceItr->getNumericEffects();
            list<pair<int, Planner::time_spec> >::const_iterator npItr = numPres.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numPres.end();
            
            for (; npItr != npEnd; ++npItr) {
                tickerVariables.erase(numericEffects[npItr->first].fluentIndex);
            }
        }
        
        if (tickerVariables.empty()) {
            return;
        }
        
    }
    
    
}

struct CostAtTimeInternal {
  
    EpsilonResolutionTimestamp start;
    EpsilonResolutionTimestamp end;
    
    list<int> costs;
    
    CostAtTimeInternal()
        : start(EpsilonResolutionTimestamp::zero()), end(EpsilonResolutionTimestamp::infinite())
    {
    }
    
    void tighten(const double & b, const VarOpConst & limit) {
        EpsilonResolutionTimestamp bound(limit.constant / b, true);
        switch (limit.op) {
            case VAL::E_GREATEQ: {
                if (bound > start) {
                    start = bound;
                }
                break;
            }
            case VAL::E_GREATER: {
                ++bound;
                if (bound > start) {
                    start = bound;
                }
                break;
            }
            case VAL::E_LESSEQ: {
                if (bound < end) {
                    end = bound;
                }
                break;
            }
            case VAL::E_LESS: {
                --bound;
                if (bound < end) {
                    end = bound;
                }
                break;
            }
        }
    }
    
};

vector<list<NumericAnalysis::CostAtTime*>* > NumericAnalysis::timeDependentStartCosts;
vector<list<NumericAnalysis::CostAtTime*>* > NumericAnalysis::timeDependentEndCosts;
vector<int> NumericAnalysis::timeDependentRewardFacts;
map<int,int> NumericAnalysis::factToTDRArrayIndex;
vector<set<int> > NumericAnalysis::timeDependentRewardFactsDueToGoal;

void NumericAnalysis::findEarlierIsBetterTimeDependentRewards()
{
    static const bool localDebug = false;
    
    const vector<list<RPGBuilder::ConditionalEffect> > & condEffs = RPGBuilder::getActionsToConditionalEffects();
    
    const int actCount = condEffs.size();       
    
    timeDependentStartCosts.resize(actCount,0);
    timeDependentEndCosts.resize(actCount,0);
    
    if (goalNumericUsageLimits.empty()) {
        if (localDebug) {
            cout << "Not looking for earlier-is-better time-dependent rewards: no goal limits\n";
        }
        return;
    }

    map<int, map<int,double> > varIsInWhichLimitAndWithWhatWeight;
    const int limSize = goalNumericUsageLimits.size();
    
    for (int lim = 0; lim < limSize; ++lim) {
        const NumericLimitDescriptor & currLim = goalNumericUsageLimits[lim];
        
        map<int,double>::const_iterator vItr = currLim.var.begin();
        const map<int,double>::const_iterator vEnd = currLim.var.end();
        
        for (; vItr != vEnd; ++vItr) {
            varIsInWhichLimitAndWithWhatWeight[vItr->first].insert(make_pair(lim, vItr->second));
        }
    }
        
        
    const vector<RPGBuilder::RPGNumericEffect> & numericEffects = RPGBuilder::getNumericEff();
    const vector<list<pair<int, Planner::time_spec> > > & eta = RPGBuilder::getRpgNumericEffectsToActions();    
    const int effCount = numericEffects.size();
    const int pneCount = RPGBuilder::getPNECount();
    
    vector<list<EffectDeterminedByTime*> > limitEffsAsTimeEffs(effCount);
    vector<list<EffectDeterminedByTime*> > varEffsAsTimeEffs(effCount);
        
    set<pair<int, Planner::time_spec> > visitAction;
        
    for (int effID = 0;effID < effCount; ++effID) {
        if (eta[effID].empty()) {
            continue;
        }       
        if (varIsInWhichLimitAndWithWhatWeight.find(numericEffects[effID].fluentIndex) != varIsInWhichLimitAndWithWhatWeight.end()) {
            visitAction.insert(eta[effID].begin(), eta[effID].end());
        }
    }
    
    for (int act = 0; act < actCount; ++act) {
        if (RPGBuilder::rogueActions[act]) {
            continue;                    
        }
        
        if (condEffs[act].empty()) {
            continue;
        }
        
        list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[act].begin();
        const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[act].end();
        
        for (; ceItr != ceEnd; ++ceItr) {
            const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
            list<pair<int, Planner::time_spec> >::const_iterator npItr = numEffs.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numEffs.end();
            
            for (; npItr != npEnd; ++npItr) {
                if (varIsInWhichLimitAndWithWhatWeight.find(numericEffects[npItr->first].fluentIndex) != varIsInWhichLimitAndWithWhatWeight.end()) {
                    visitAction.insert(make_pair(act, npItr->second));
                }
            }
        }
        
        
    }
    
    bool anyTDRs = false;
    
    set<pair<int, Planner::time_spec> >::const_iterator actItr = visitAction.begin();
    const set<pair<int, Planner::time_spec> >::const_iterator actEnd = visitAction.end();
    
    for (; actItr != actEnd; ++actItr) {
        
        if (localDebug) {
            cout << "Considering " << *(RPGBuilder::getInstantiatedOp(actItr->first));
            if (actItr->second == Planner::E_AT_START) {
                cout << " start\n";
            } else {
                cout << " end\n";
            }
        }
        
        bool dependsOnAnythingElse = false;
        
        list<CostAtTimeInternal> outcomes;
        
        CostAtTimeInternal wholeAction;
        
        {
            const list<int> & pres = (actItr->second == Planner::E_AT_START
                                        ? RPGBuilder::getStartPreNumerics()[actItr->first]
                                        : RPGBuilder::getEndPreNumerics()[actItr->first]);
            
            list<int>::const_iterator pItr = pres.begin();
            const list<int>::const_iterator pEnd = pres.end();
            
            for (; pItr != pEnd; ++pItr) {
                bool success;
                VarOpConst limit(RPGBuilder::getNumericPreTable()[*pItr], success);
                if (success) {
                    const map<int,double>::const_iterator tItr = tickerVariables.find(limit.var);
                    if (tItr != tickerVariables.end() && dominanceConstraints[limit.var] == E_SMALLERISBETTER) {
                        wholeAction.tighten(tItr->second, limit);                                                
                    }
                }
            }            
        }
        
        
        {
            const list<int> & effs = (actItr->second == Planner::E_AT_START
                                        ? RPGBuilder::getStartEffNumerics()[actItr->first]
                                        : RPGBuilder::getEndEffNumerics()[actItr->first]);
            
            list<int>::const_iterator eItr = effs.begin();
            const list<int>::const_iterator eEnd = effs.end();
            
            for (; eItr != eEnd; ++eItr) {
                const RPGBuilder::RPGNumericEffect & currEff = numericEffects[*eItr];
                if (varIsInWhichLimitAndWithWhatWeight.find(currEff.fluentIndex) != varIsInWhichLimitAndWithWhatWeight.end()) {
                    wholeAction.costs.push_back(*eItr);
                    if (currEff.size) {
                        assert(currEff.size == 1);
                        int lVar = currEff.variables[0];
                        if (lVar < 0) {
                            if (localDebug) {
                                cout << "Found a duration-dependent effect, doesn't fit desired pattern of time-dependency\n";
                            }
                            dependsOnAnythingElse = true;
                        } else {
                            if (lVar >= pneCount) {
                                lVar -= pneCount;
                            }                            
                            const map<int,double>::const_iterator tItr = tickerVariables.find(lVar);
                            if (tItr == tickerVariables.end() || dominanceConstraints[lVar] != E_SMALLERISBETTER) {
                                if (localDebug) {
                                    if (tItr == tickerVariables.end()) {
                                        cout << "Found an effect depending on a non-ticker variable, doesn't fit desired pattern of time-dependency\n";
                                    } else {
                                        cout << "Found an effect depending on a ticker variable which isn't better to be smaller\n";
                                    }
                                        
                                }

                                dependsOnAnythingElse = true;
                            }
                        }
                    }
                }                    
            }                        
        }
        
        if (dependsOnAnythingElse) {
            continue;
        }
        
        if (!wholeAction.costs.empty()) {
            outcomes.push_back(wholeAction);
            wholeAction.costs.clear();
        }
        
        list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[actItr->first].begin();
        const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[actItr->first].end();
        
        for (; ceItr != ceEnd; ++ceItr) {
            bool anything = false;
            CostAtTimeInternal condAction(wholeAction);
            {
                const list<pair<int, Planner::time_spec> > & numPres = ceItr->getNumericPreconditions();
                list<pair<int, Planner::time_spec> >::const_iterator npItr = numPres.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numPres.end();
                
                for (; npItr != npEnd; ++npItr) {
                    if (npItr->second == actItr->second) {
                        bool success;
                        VarOpConst limit(RPGBuilder::getNumericPreTable()[npItr->first], success);
                        if (success) {
                            const map<int,double>::const_iterator tItr = tickerVariables.find(limit.var);
                            if (tItr != tickerVariables.end() && dominanceConstraints[limit.var] == E_SMALLERISBETTER) {
                                condAction.tighten(tItr->second, limit);                                                
                            } else {
                                if (localDebug) {
                                    cout << "Found a conditional outcome conditioned on something other than a ticker, doesn't fit desired pattern of time-dependency\n";
                                }
                                dependsOnAnythingElse = true;
                            }
                        } else {
                            if (localDebug) {
                                cout << "Found a conditional outcome with a non-simple v >= c or v <= c condition, doesn't fit desired pattern of time-dependency\n";
                            }

                            dependsOnAnythingElse = true;
                        }
                    }
                }
            }
            {                            
                const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
                list<pair<int, Planner::time_spec> >::const_iterator npItr = numEffs.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator npEnd = numEffs.end();
                
                for (; npItr != npEnd; ++npItr) {
                    const RPGBuilder::RPGNumericEffect & currEff = numericEffects[npItr->first];
                    if (varIsInWhichLimitAndWithWhatWeight.find(currEff.fluentIndex) != varIsInWhichLimitAndWithWhatWeight.end()) {
                        condAction.costs.push_back(npItr->first);
                        anything = true;
                        if (currEff.size) {
                            assert(currEff.size == 1);
                            int lVar = currEff.variables[0];
                            if (lVar < 0) {
                                dependsOnAnythingElse = true;
                                if (localDebug) {
                                    cout << "Found a conditional duration-dependent effect, doesn't fit desired pattern of time-dependency\n";
                                }
                            } else {
                                if (lVar >= pneCount) {
                                    lVar -= pneCount;
                                }
                                const map<int,double>::const_iterator tItr = tickerVariables.find(lVar);
                                if (tItr == tickerVariables.end() || dominanceConstraints[lVar] != E_SMALLERISBETTER) {
                                    dependsOnAnythingElse = true;
                                    if (localDebug) {
                                        if (tItr == tickerVariables.end()) {
                                            cout << "Found an effect depending on a non-ticker variable, doesn't fit desired pattern of time-dependency\n";
                                        } else {
                                            cout << "Found an effect depending on a ticker variable which isn't better to be smaller\n";
                                        }
                                            
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (anything) {
                outcomes.push_back(condAction);
            }
        }

        if (dependsOnAnythingElse) {
            continue;
        }
                
        // now have a list of outcomes, one or more of which may fire at a given time
        // and where the outcome is better earlier (or else the tickers wouldn't be E_SMALLERISBETTER)
        
        if (outcomes.empty()) {
            continue;
        }
        
        if (localDebug) {
            cout << "Have " << outcomes.size() << " outcome(s)\n";
        }
        
        list<CostAtTime*>*& dest = (actItr->second == Planner::E_AT_START ? timeDependentStartCosts[actItr->first]
                                                                      : timeDependentEndCosts[actItr->first]);
        
        dest = new list<CostAtTime*>();
        
        list<CostAtTimeInternal>::const_iterator oItr = outcomes.begin();
        const list<CostAtTimeInternal>::const_iterator oEnd = outcomes.end();
        
        for (; oItr != oEnd; ++oItr) {
            CostAtTime * const forList = new CostAtTime(oItr->start, oItr->end);
            
            if (localDebug) {
                cout << "- From " << forList->start << " to " << forList->end << ":\n";
            }
            list<int>::const_iterator effItr = oItr->costs.begin();
            const list<int>::const_iterator effEnd = oItr->costs.end();
            for (; effItr != effEnd; ++effItr) {
                if (localDebug) {
                    cout << "  * " << numericEffects[*effItr] << endl;
                }
                if (limitEffsAsTimeEffs[*effItr].empty()) {
                    const RPGBuilder::RPGNumericEffect & currEff = numericEffects[*effItr];
                    EffectDeterminedByTime eTmp(-1, currEff.constant, 0.0);
                    EffectDeterminedByTime * const evTmp = new EffectDeterminedByTime(currEff.fluentIndex, currEff.constant, 0.0);
                    if (currEff.size) {
                        assert(currEff.size == 1);
                        int lVar = currEff.variables[0];
                        if (lVar >= pneCount) {
                            lVar -= pneCount;
                            const map<int,double>::const_iterator tItr = tickerVariables.find(lVar);
                            assert(tItr != tickerVariables.end());
                            eTmp.m = -(tItr->second * currEff.weights[0]);
                            evTmp->m = -(tItr->second * currEff.weights[0]);
                        } else {
                            const map<int,double>::const_iterator tItr = tickerVariables.find(lVar);
                            assert(tItr != tickerVariables.end());
                            eTmp.m = tItr->second * currEff.weights[0];
                            evTmp->m = tItr->second * currEff.weights[0];
                        }                                                
                    }
                    
                    if (dominanceConstraints[currEff.fluentIndex] == E_METRICTRACKING) {                    
                        varEffsAsTimeEffs[*effItr].push_back(evTmp);
                        cout << "Effect " << *effItr << " gives a metric time-dependent update\n";
                    } else {
                        delete evTmp;
                    }
                    
                    const map<int, map<int,double> >::const_iterator depItr = varIsInWhichLimitAndWithWhatWeight.find(currEff.fluentIndex);
                    assert(depItr != varIsInWhichLimitAndWithWhatWeight.end());
                    
                    map<int,double>::const_iterator glItr = depItr->second.begin();
                    const map<int,double>::const_iterator glEnd = depItr->second.end();
                    
                    for (; glItr != glEnd; ++glItr) {
                        EffectDeterminedByTime * const eHere = new EffectDeterminedByTime(eTmp);
                        eHere->y = glItr->first;
                        eHere->m *= glItr->second;
                        eHere->c *= glItr->second;
                        if (localDebug) {
                            cout << "    + Affects limit " << eHere->y << " by " << eHere->c << " + " << eHere->m << ".t\n";
                        }
                        limitEffsAsTimeEffs[*effItr].push_back(eHere);                        
                    }
                } else {
                    if (localDebug) {
                        cout << "    + The same effect as last time it appeared here\n";
                    }
                }
                forList->limitCosts.insert(forList->limitCosts.end(), limitEffsAsTimeEffs[*effItr].begin(), limitEffsAsTimeEffs[*effItr].end());
                forList->varCosts.insert(forList->varCosts.end(), varEffsAsTimeEffs[*effItr].begin(), varEffsAsTimeEffs[*effItr].end());
            }
            
            if (forList->limitCosts.empty() && forList->varCosts.empty()) {
                delete forList;
            } else {
                dest->push_back(forList);
            }
        }
        
        if (dest->empty()) {
            delete dest;
            dest = 0;
        } else {
            anyTDRs = true;
        }
    }
    
    if (anyTDRs) {
        map<int,int> candidateFacts;
        
        {
            const list<Literal*> & goals = RPGBuilder::getLiteralGoals();
            
            timeDependentRewardFactsDueToGoal.resize(goals.size());
            
            list<Literal*>::const_iterator gItr = goals.begin();
            const list<Literal*>::const_iterator gEnd = goals.end();
            
            for (int gID = 0; gItr != gEnd; ++gItr, ++gID) {
                candidateFacts.insert(make_pair((*gItr)->getStateID(), gID));                
            }            
        }

        set<int> factsSupportingIdentifiedTDRs;                
                        
        {                
            map<int,int>::const_iterator fItr = candidateFacts.begin();
            const map<int,int>::const_iterator fEnd = candidateFacts.end();

            for (; fItr != fEnd; ++fItr) {
                const list<pair<int, Planner::time_spec> > & achievers = RPGBuilder::getEffectsToActions(fItr->first);

                if (achievers.size() > 1) { 
                    cerr << "Implementation limitation: only supports single achievers for time-dependent-reward marker facts, so ignoring " << *(RPGBuilder::getLiteral(fItr->first)) << endl;
                    continue;
                }
                
                // check one: some of them are time-dependent
                
                list<pair<int, Planner::time_spec> >::const_iterator accItr = achievers.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator accEnd = achievers.end();
                
                for (; accItr != accEnd; ++accItr) {
                    
                    if (accItr->second == Planner::E_AT) {
                        continue;                
                    }

                    const bool includeThisAction = ( (timeDependentStartCosts[accItr->first] && !timeDependentStartCosts[accItr->first]->empty()) ||
                                                     (timeDependentEndCosts[accItr->first] && !timeDependentEndCosts[accItr->first]->empty())        );
                    
                    if (!includeThisAction) {
                        continue;
                    }
                                        
                    
                    for (int pass = 0; pass < 2; ++pass) {
                        
                        const list<Literal*> & preList = (!pass ? RPGBuilder::getProcessedStartPropositionalPreconditions()[accItr->first]
                                                                : RPGBuilder::getEndPropositionalPreconditions()[accItr->second]);
                        
                        list<Literal*>::const_iterator pItr = preList.begin();
                        const list<Literal*>::const_iterator pEnd = preList.end();
                        
                        int fID;
                        for (; pItr != pEnd; ++pItr) {
                            fID = (*pItr)->getStateID();
                            if (!RPGBuilder::getEffectsToActions(fID).empty()) { // skip non-addable facts, as we don't need to look for support
                                factsSupportingIdentifiedTDRs.insert(fID);
                                timeDependentRewardFactsDueToGoal[fItr->second].insert(fID);
                            }
                        }
                        
                        if (accItr->second == Planner::E_AT_START) {
                            break;
                        }
                        
                    }
                    
                    
                }
                
            }
        }
        
        timeDependentRewardFacts.insert(timeDependentRewardFacts.end(), factsSupportingIdentifiedTDRs.begin(), factsSupportingIdentifiedTDRs.end());
        
        const int tdrFactCount = timeDependentRewardFacts.size();
        
        for (int tdrF = 0; tdrF < tdrFactCount; ++tdrF) {
            factToTDRArrayIndex.insert(make_pair(timeDependentRewardFacts[tdrF], tdrF));
        }
    }
    

        
}

double NumericAnalysis::bestAdditionalRewardFromHere(const MinimalState & theState)
{

    static const bool localDebug = false;
    
    if (timeDependentRewardFacts.empty()) {
        return 0.0;
    }
    
    double toReturn = 0.0;
    
    
    const list<Literal*> & goals = RPGBuilder::getLiteralGoals();
        
    list<Literal*>::const_iterator gItr = goals.begin();
    const list<Literal*>::const_iterator gEnd = goals.end();
    
    int gfID;
    
    for (int gID = 0; gItr != gEnd; ++gItr, ++gID) {
                        
        if (timeDependentRewardFactsDueToGoal[gID].empty()) {
            continue;
        }

        gfID = (*gItr)->getStateID();
                                
        if (theState.first.find(gfID) != theState.first.end()) {
            continue;
        }

        if (localDebug) {
            cout << "Looking at getting " << *(*gItr) << endl;
        }
                
        const list<pair<int, Planner::time_spec> > & achievers = RPGBuilder::getEffectsToActions(gfID);
        
        const pair<int, Planner::time_spec> * const accItr = &(achievers.front());
        
        double canStartAt = 0.0;
        double canEndAt = 0.0;

        bool beenRewarded = false;
        
        for (int pass = 0; pass < 2; ++pass) {
                        
            const list<Literal*> & preList = (!pass ? RPGBuilder::getProcessedStartPropositionalPreconditions()[accItr->first]
                                                    : RPGBuilder::getEndPropositionalPreconditions()[accItr->second]);
            
            double & preUpdate = (pass ? canEndAt : canStartAt);
            
            list<Literal*>::const_iterator pItr = preList.begin();
            const list<Literal*>::const_iterator pEnd = preList.end();
            
            int fID;
            for (; pItr != pEnd; ++pItr) {
                fID = (*pItr)->getStateID();
                if (RPGBuilder::getEffectsToActions(fID).empty() && theState.first.find(fID) == theState.first.end()) {
                    beenRewarded = true;
                    break;
                }
                
                const map<int,int>::const_iterator indexed = factToTDRArrayIndex.find(fID);
                if (indexed != factToTDRArrayIndex.end()) {
                    if (localDebug) {
                        cout << "- Must come after " << *(RPGBuilder::getLiteral(indexed->first)) << " at " << theState.lowerBoundOnTimeDependentRewardFacts[indexed->second] << endl;
                    }
                    if (preUpdate < theState.lowerBoundOnTimeDependentRewardFacts[indexed->second]) {
                        preUpdate = theState.lowerBoundOnTimeDependentRewardFacts[indexed->second];                        
                    }
                }
            }
            
            if (beenRewarded) {
                break;
            }
        }
        
        if (beenRewarded) {
            continue;
        }
        
        const double maxDur = RPGBuilder::getOpMaxDuration(accItr->first, -1);
        if (canStartAt < canEndAt - maxDur) {
            canStartAt = canEndAt - maxDur;
        }
        const double minDur = RPGBuilder::getOpMinDuration(accItr->first, -1);
        if (canEndAt < canStartAt + minDur) {
            canEndAt = canStartAt + minDur;
        }
        
        for (int pass = 0; pass < 2; ++pass) {
            const list<CostAtTime*> * const use = (!pass ? timeDependentStartCosts[accItr->first] : timeDependentEndCosts[accItr->first]);
            
            EpsilonResolutionTimestamp currTS(pass ? canEndAt : canStartAt, true);
            
            if (use) {
                
                list<CostAtTime*>::const_iterator costItr = use->begin();
                const list<CostAtTime*>::const_iterator costEnd = use->end();
                
                for (; costItr != costEnd; ++costItr) {
                    
                    if (currTS >= (*costItr)->start && currTS <= (*costItr)->end) {
                        list<EffectDeterminedByTime*>::const_iterator limItr = (*costItr)->limitCosts.begin();
                        const list<EffectDeterminedByTime*>::const_iterator limEnd = (*costItr)->limitCosts.end();
                        
                        for (; limItr != limEnd; ++limItr) {                            
                            if (goalNumericUsageLimits[(*limItr)->y].optimisationLimit) {                                
                                if (localDebug) {
                                    cout << "Reward in window [" << (*costItr)->start << "," << (*costItr)->end << "] = " << ((*limItr)->m * currTS.toDouble()) + (*limItr)->c << endl;
                                }
                                toReturn += ((*limItr)->m * currTS.toDouble()) + (*limItr)->c; // y = mx + c
                            }                            
                        }                                                
                    }                    
                }
            }
        }
        
    }            

    if (localDebug) {
        cout << "Returning " << toReturn << endl;
    }
        
    return toReturn;

}


vector<pair<double,double> > NumericAnalysis::masterVariableBounds;

map<int, list<pair<int, Planner::time_spec> > > NumericAnalysis::numericEffectsThatAreInConditionalEffects;

void NumericAnalysis::findVariableBounds()
{
    
    // TODO: This could be a lot better.  Right now it assumes v -=c can send v to - infinity,
    // whereas if it's coupled with a precondition v >= d, then at most it can send it to (d - c)
    
    static const bool localDebug = false;
    
    const int pneCount =  RPGBuilder::getPNECount();
    
    masterVariableBounds.resize(pneCount);
    
    vector<pair<double,double> > & variableBounds = masterVariableBounds;
    
    vector<double> initialValues;
    
    {
        LiteralSet propositional; // don't care...
        RPGBuilder::getInitialState(propositional, initialValues);
    }
    
    set<int> needToVisit;
    map<int, set<int> > revisitIfFiniteBounded;
    
    for (int v = 0; v < pneCount; ++v) {
        variableBounds[v].first = -DBL_MAX;
        variableBounds[v].second = DBL_MAX;
        needToVisit.insert(v);
    }
    
    vector<pair<bool,bool> > everDecreasedIncreasedContinuously(pneCount, pair<bool,bool>(false,false));
    
    {
        const vector<RPGBuilder::LinearEffects*> & ctsEffs = RPGBuilder::getLinearDiscretisation();    
        const int actCount = ctsEffs.size();
        for (int actID = 0; actID < actCount; ++actID) {
            if (RPGBuilder::rogueActions[actID] == RPGBuilder::OT_INVALID_ACTION) continue;
            if (!ctsEffs[actID]) continue;
                        
            const int varCount = ctsEffs[actID]->vars.size();
            
            for (int i = 0; i < varCount; ++i) {
                if (ctsEffs[actID]->effects[0][i].constant > 0) {
                    everDecreasedIncreasedContinuously[ctsEffs[actID]->vars[i]].second = true;
                } else if (ctsEffs[actID]->effects[0][i].constant < 0) {
                    everDecreasedIncreasedContinuously[ctsEffs[actID]->vars[i]].first = true;
                }
            }                        
        }
                    
    }

    {
        const vector<list<RPGBuilder::ConditionalEffect> > & condEffs = RPGBuilder::getActionsToConditionalEffects();
        const int actCount = condEffs.size();
        for (int act = 0; act < actCount; ++act) {
            if (RPGBuilder::rogueActions[act]) {
                continue;                    
            }
            
            if (condEffs[act].empty()) {
                continue;
            }
            
            set<pair<int, Planner::time_spec> > usedInThisAct;
            
            list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = condEffs[act].begin();
            const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = condEffs[act].end();
            
            for (; ceItr != ceEnd; ++ceItr) {
                
                if (ceItr->getNumericEffects().empty()) {
                    continue;
                }
                
                const list<pair<int, Planner::time_spec> > & numEffs = ceItr->getNumericEffects();
                list<pair<int, Planner::time_spec> >::const_iterator neItr = numEffs.begin();
                const list<pair<int, Planner::time_spec> >::const_iterator neEnd = numEffs.end();
                
                for (; neItr != neEnd; ++neItr) {
                    usedInThisAct.insert(*neItr);
                }
            }
            
            set<pair<int, Planner::time_spec> >::const_iterator uItr = usedInThisAct.begin();
            const set<pair<int, Planner::time_spec> >::const_iterator uEnd = usedInThisAct.end();
            
            for (; uItr != uEnd; ++uItr) {
                numericEffectsThatAreInConditionalEffects[uItr->first].push_back(make_pair(act,uItr->second));
            }
        }

        
    }
        
    vector<bool> definedYet(RPGBuilder::getWhetherDefinedValueInInitialState());
    
    const vector<RPGBuilder::RPGNumericEffect> & numericEffs = RPGBuilder::getNumericEff();

    const int effCount = numericEffs.size();
    
    static const bool defDebug = false;
    
    while (!needToVisit.empty()) {
        
        set<int> oldNeedToVisit;
        needToVisit.swap(oldNeedToVisit);
        
        set<int>::const_iterator vItr = oldNeedToVisit.begin();
        const set<int>::const_iterator vEnd = oldNeedToVisit.end();
        
        for (; vItr != vEnd; ++vItr) {
            
            bool lbPreviouslyUnbounded = (variableBounds[*vItr].first == -DBL_MAX);
            bool ubPreviouslyUnbounded = (variableBounds[*vItr].second == DBL_MAX);
                                
            variableBounds[*vItr].first = initialValues[*vItr];
            variableBounds[*vItr].second = initialValues[*vItr];

            if (localDebug) {
                cout << "Visiting " << *(RPGBuilder::getPNE(*vItr)) << endl;
                if (lbPreviouslyUnbounded) {
                    cout << "- Previously lower unbounded\n";
                }
                if (ubPreviouslyUnbounded) {
                    cout << "- Previously upper unbounded\n";
                }
                cout << "For now assuming it takes its initial value " << initialValues[*vItr] << endl;
            }                                                
            
            bool previousEffectsLeftLBUnbounded = false;
            bool previousEffectsLeftUBUnbounded = false;
            
            if (everDecreasedIncreasedContinuously[*vItr].first) {
                variableBounds[*vItr].first = -DBL_MAX;
            }
            
            if (everDecreasedIncreasedContinuously[*vItr].second) {
                variableBounds[*vItr].second = DBL_MAX;
            }
                                    
                                 
            if (!definedYet[*vItr] || (variableBounds[*vItr].first != -DBL_MAX) || (variableBounds[*vItr].second != DBL_MAX)) {
             
                // look for non-continuous effects on this var
                
                for (int eff = 0; eff < effCount; ++eff) {

                    if (numericEffs[eff].fluentIndex != *vItr) {
                        // doesn't affect this variable
                        continue;
                    }
                
                                
                    if (!numericEffs[eff].canEverHappen) {
                        // no applicable action has this effect
                        if (defDebug) {
                            cout << "Ignoring " << numericEffs[eff] << " when calculating bounds\n";
                        }
                        continue;
                    }
                    
                
                    double rhsLB = numericEffs[eff].constant;
                    double rhsUB = numericEffs[eff].constant;

                    if (definedYet[*vItr] || numericEffs[eff].isAssignment) {
                        
                        if (numericEffs[eff].size) {

                            if (localDebug) {
                                cout << "Looking at actions with multi-variable effect " << numericEffs[eff] << endl;
                            }
                            
                            for (int condPass = 0; condPass < 2; ++condPass) {
                                
                                if (condPass == 1 && numericEffectsThatAreInConditionalEffects.find(eff) == numericEffectsThatAreInConditionalEffects.end()) {
                                    continue;
                                }
                                
                                const list<pair<int, Planner::time_spec> > & acts = (condPass ? numericEffectsThatAreInConditionalEffects.find(eff)->second
                                                                                              : RPGBuilder::getRpgNumericEffectsToActions()[eff]);
                            
                                list<pair<int, Planner::time_spec> >::const_iterator actItr = acts.begin();
                                const list<pair<int, Planner::time_spec> >::const_iterator actEnd = acts.end();
                                
                                for (; actItr != actEnd; ++actItr) {
                                    MaskedVariableBounds localBounds;
                                    
                                    if (localDebug) {
                                        cout << "  Found on " << *(RPGBuilder::getInstantiatedOp(actItr->first)) << ", ";
                                        if (actItr->second == Planner::E_AT_START) {
                                            cout << "start\n";
                                        } else {
                                            cout << "end\n";
                                        }
                                    }
                                    
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
                                    
                                    for (int pass = 0; pass < 2; ++pass) {
                                        double localBoundToUpdate = numericEffs[eff].constant;
                                        
                                        for (int term = 0; (localBoundToUpdate != DBL_MAX && localBoundToUpdate != -DBL_MAX) && term < numericEffs[eff].size; ++term) {

                                            double relevantBound;
                                            switch (numericEffs[eff].variables[term]) {
                                                case -3: {
                                                    // ?duration - assume in range [epsilon, infinity]
                                                    relevantBound = numericEffs[eff].weights[term] * (pass ? localBounds[-3].second : localBounds[-3].first);
                                                    break;
                                                }
                                                case -19: {
                                                    // -?duration - assume in range [-infinity, -epsilon]
                                                    relevantBound = numericEffs[eff].weights[term] * (pass ? -localBounds[-3].first : -localBounds[-3].second);
                                                    break;
                                                }
                                                default: {
                                                    assert(numericEffs[eff].variables[term] >= 0);
                                                    if (numericEffs[eff].variables[term] >= pneCount) {
                                                        relevantBound = -numericEffs[eff].weights[term] * (pass ? localBounds[numericEffs[eff].variables[term] - pneCount].first : localBounds[numericEffs[eff].variables[term] - pneCount].second);
                                                    } else {
                                                        relevantBound = numericEffs[eff].weights[term] * (pass ? localBounds[numericEffs[eff].variables[term]].second : localBounds[numericEffs[eff].variables[term]].first);
                                                    }
                                                }
                                            }
                                            if (localDebug) {
                                                cout << "   Contribution from term " << term << " = " << relevantBound << endl;
                                            }
                                            localBoundToUpdate += relevantBound;
                                        }
                                        
                                        if (pass) {
                                            if (localBoundToUpdate > rhsUB) {
                                                rhsUB = localBoundToUpdate;
                                                if (localDebug) {
                                                    cout << "  UB of effect outcome pushed up to " << rhsUB << endl;
                                                }                                            
                                            } else {
                                                if (localDebug) {
                                                    cout << "  Leaving UB at " << rhsUB << endl;
                                                }                                            
                                            }
                                        } else {
                                            if (localBoundToUpdate < rhsLB) {
                                                rhsLB = localBoundToUpdate;
                                                if (localDebug) {
                                                    cout << "  LB of effect outcome pushed down to " << rhsLB << endl;
                                                }                                            
                                            } else {
                                                if (localDebug) {
                                                    cout << "  Leaving LB at " << rhsLB << endl;
                                                }                 
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    
                    if (numericEffs[eff].isAssignment) {
                        
                        if (definedYet[*vItr]) {
                            if (rhsUB > variableBounds[*vItr].second) {
                                variableBounds[*vItr].second = rhsUB;
                                if (defDebug) {
                                    cout << numericEffs[eff] << " increases UB on " << *(RPGBuilder::getPNE(*vItr)) << " to " << rhsUB << "]\n";
                                }
                            } else {
                                if (defDebug) {
                                    cout << numericEffs[eff] << " does not change UB to " << rhsUB << "\n";
                                }
                            }
                            if (rhsLB < variableBounds[*vItr].first) {
                                variableBounds[*vItr].first = rhsLB;
                                if (defDebug) {
                                    cout << numericEffs[eff] << " decreases LB on " << *(RPGBuilder::getPNE(*vItr)) << " to " << rhsLB << "]\n";
                                }                                
                            } else {
                                if (defDebug) {
                                    cout << numericEffs[eff] << " does not change LB to " << rhsLB << "\n";
                                }
                            }
                        } else {
                            if (defDebug) {
                                cout << numericEffs[eff] << " is the first assigner to " << *(RPGBuilder::getPNE(*vItr)) << ": [" << rhsLB << "," << rhsUB << "]\n";
                            }
                            variableBounds[*vItr].second = rhsUB;
                            variableBounds[*vItr].first = rhsLB;
                            definedYet[*vItr] = true;
                        }
                        
                    } else if (definedYet[*vItr]) {
                        
                        if (rhsUB > 0) {
                            variableBounds[*vItr].second = DBL_MAX;
                            if (localDebug) {
                                cout << " Assuming increase effect shoots off to infinity\n";
                            }                 
                        }
                        if (rhsLB < 0) {
                            variableBounds[*vItr].first = -DBL_MAX;
                            if (localDebug) {
                                cout << " Assuming decrease effect shoots off to -infinity\n";
                            }
                        }
                    }
                    
                    if (   ((variableBounds[*vItr].first == -DBL_MAX) && !previousEffectsLeftLBUnbounded)
                        || ((variableBounds[*vItr].second == DBL_MAX) && !previousEffectsLeftUBUnbounded)) {
                        for (int term = 0; term < numericEffs[eff].size; ++term) {
                            if (numericEffs[eff].variables[term] < 0) {
                                continue;                        
                            }
                            
                            if (numericEffs[eff].variables[term] >= pneCount) {
                                revisitIfFiniteBounded[numericEffs[eff].variables[term] - pneCount].insert(*vItr);
                                if (localDebug) {
                                    cout << "- If " << *(RPGBuilder::getPNE(numericEffs[eff].variables[term] - pneCount)) << " ever becomes finite bounded, revisit this\n";
                                }
                            } else {
                                revisitIfFiniteBounded[numericEffs[eff].variables[term]].insert(*vItr);
                                if (localDebug) {
                                    cout << "- If " << *(RPGBuilder::getPNE(numericEffs[eff].variables[term])) << " ever becomes finite bounded, revisit this\n";
                                }
                            }
                            
                        }
                    }
                    
                    previousEffectsLeftLBUnbounded = (previousEffectsLeftLBUnbounded || (variableBounds[*vItr].first == -DBL_MAX));
                    previousEffectsLeftUBUnbounded = (previousEffectsLeftUBUnbounded || (variableBounds[*vItr].second == DBL_MAX));
                    
                    if ((variableBounds[*vItr].first == -DBL_MAX) && (variableBounds[*vItr].second == DBL_MAX)) {
                        // variable in range [-inf, inf] - no point exploring further bounds
                        break;
                    }
                }
                
            }

            if (localDebug) {
                cout << *(RPGBuilder::getPNE(*vItr)) << " is in the range [";
                if (variableBounds[*vItr].first == -DBL_MAX) {
                    cout << "-inf,";
                } else {
                    cout << variableBounds[*vItr].first << ",";
                }
                if (variableBounds[*vItr].second == DBL_MAX) {
                    cout << "inf]\n";
                } else {
                    cout << variableBounds[*vItr].second << "]\n";
                }
                
            }
            
            if ((lbPreviouslyUnbounded && (variableBounds[*vItr].first != -DBL_MAX)) || (ubPreviouslyUnbounded && (variableBounds[*vItr].second != DBL_MAX))) {
                // variable's bounds are finite at at least one end
                
                const map<int, set<int> >::iterator rvItr = revisitIfFiniteBounded.find(*vItr);
                
                if (rvItr != revisitIfFiniteBounded.end()) {
                    if (localDebug) {
                        cout << "Because it is finite, we have to revisit";
                        set<int>::const_iterator poItr = rvItr->second.begin();
                        const set<int>::const_iterator poEnd = rvItr->second.end();
                        
                        for (; poItr != poEnd; ++poItr) {
                            cout << " " << *(RPGBuilder::getPNE(*poItr));
                        }
                        cout << endl;
                    }
                    needToVisit.insert(rvItr->second.begin(), rvItr->second.end());
                    revisitIfFiniteBounded.erase(rvItr);
                }
            }
            
        }
    }
    
    for (int v = 0; v < pneCount; ++v) {
        if (variableBounds[v].first != -DBL_MAX && variableBounds[v].second != DBL_MAX) {
            cout << *(RPGBuilder::getPNE(v)) << " has finite bounds: [" << variableBounds[v].first << "," << variableBounds[v].second << "]\n";
        } else if (variableBounds[v].first != -DBL_MAX) {
            cout << *(RPGBuilder::getPNE(v)) << " has a finite lower bound: [" << variableBounds[v].first << ",inf]\n";
        } else if (variableBounds[v].second != DBL_MAX) {
            cout << *(RPGBuilder::getPNE(v)) << " has a finite upper bound: [-inf," << variableBounds[v].second << "]\n";
        }
    }
    
}

#endif

map<int, set<int> > NumericAnalysis::factsThatDefineAndFixVariables;
map<int, set<int> > NumericAnalysis::variablesFixedAndDefinedByFact;

void NumericAnalysis::findFactsThatDefineAndFixVariables()
{
    set<int> variablesThatDoNotFit;
    
    map<int, pair<set<int>,set<int> > > requiredThenDeletedToGetValue;
    
    const vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();
    
    const int effCount = effTable.size();
    
    vector<list<pair<int, Planner::time_spec> > > iceLookup(effCount);
    
    {
        const map<int, list<RPGBuilder::IntegralContinuousEffect> > & ice = RPGBuilder::getActionsToIntegralConditionalEffects();
        
        map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceMapItr = ice.begin();
        const map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceMapEnd = ice.end();
        
        for (; iceMapItr != iceMapEnd; ++iceMapItr) {
            
            list<RPGBuilder::IntegralContinuousEffect>::const_iterator icItr = iceMapItr->second.begin();
            const list<RPGBuilder::IntegralContinuousEffect>::const_iterator icEnd = iceMapItr->second.end();
            
            for (; icItr != icEnd; ++icItr) {
                {
                    list<pair<int,double> >::const_iterator effItr = icItr->getLeftStartEffects().begin();
                    const list<pair<int,double> >::const_iterator effEnd = icItr->getLeftStartEffects().end();
                    
                    for (; effItr != effEnd; ++effItr) {
                        iceLookup[effItr->first].push_back(make_pair(iceMapItr->first, Planner::E_AT_START));
                    }
                }
                
                {
                    list<pair<int,double> >::const_iterator effItr = icItr->getLeftEndEffects().begin();
                    const list<pair<int,double> >::const_iterator effEnd = icItr->getLeftEndEffects().end();
                    
                    for (; effItr != effEnd; ++effItr) {
                        iceLookup[effItr->first].push_back(make_pair(iceMapItr->first, Planner::E_AT_END));
                    }
                }
            }
        }
    }
    
    for (int effID = 0; effID < effCount; ++effID) {
        const RPGBuilder::RPGNumericEffect & currEff = effTable[effID];
        
        if (variablesThatDoNotFit.find(currEff.fluentIndex) != variablesThatDoNotFit.end()) {
            continue;
        }
        
        set<int> requiredThenDeletedWithThisEffect;
        set<int> definitelyAddedWithThisEffect;
        
        bool first = true;
        
        for (int iceOrNot = 0; iceOrNot < 2; ++iceOrNot) {
            const list<pair<int, Planner::time_spec> > & effList = (iceOrNot ? iceLookup[effID] : RPGBuilder::getRpgNumericEffectsToActions()[effID]);
            list<pair<int, Planner::time_spec> >::const_iterator actItr = effList.begin();
            const list<pair<int, Planner::time_spec> >::const_iterator actEnd = effList.end();
            
            
            
            for (; (first || !requiredThenDeletedWithThisEffect.empty()) && actItr != actEnd; ++actItr, first = false) {
                set<int> required;
                {
                    const list<Literal*> & pres = (actItr->second == Planner::E_AT_START ? RPGBuilder::getStartPropositionalPreconditions()[actItr->first] : RPGBuilder::getEndPropositionalPreconditions()[actItr->first]);
                    list<Literal*>::const_iterator pItr = pres.begin();
                    const list<Literal*>::const_iterator pEnd = pres.end();
                    
                    for (; pItr != pEnd; ++pItr) {
                        if (RPGBuilder::getEffectsToActions((*pItr)->getStateID()).empty()) {
                            required.insert((*pItr)->getStateID());
                        }
                    }
                }
                if (required.empty()) {
                    requiredThenDeletedWithThisEffect.clear();
                    break;
                }
                {
                    const list<Literal*> & dels = (actItr->second == Planner::E_AT_START ? RPGBuilder::getStartPropositionDeletes()[actItr->first] : RPGBuilder::getEndPropositionDeletes()[actItr->first]);
                    set<int> delSet;
                    list<Literal*>::const_iterator pItr = dels.begin();
                    const list<Literal*>::const_iterator pEnd = dels.end();
                    
                    for (; pItr != pEnd; ++pItr) {
                        delSet.insert((*pItr)->getStateID());
                    }
                    
                    set<int> iSect;
                    std::set_intersection(required.begin(), required.end(), delSet.begin(), delSet.end(), std::insert_iterator<set<int> >(iSect, iSect.end()));
                    iSect.swap(required);
                }
                if (required.empty()) {
                    requiredThenDeletedWithThisEffect.clear();
                    break;
                }
                if (first) {
                    requiredThenDeletedWithThisEffect.swap(required);
                } else {
                    set<int> iSect;
                    std::set_intersection(required.begin(), required.end(), requiredThenDeletedWithThisEffect.begin(), requiredThenDeletedWithThisEffect.end(), std::insert_iterator<set<int> >(iSect, iSect.end()));
                    iSect.swap(requiredThenDeletedWithThisEffect);
                }
                
                set<int> addSet;

                {
                    const list<Literal*> & adds = (actItr->second == Planner::E_AT_START ? RPGBuilder::getStartPropositionAdds()[actItr->first] : RPGBuilder::getEndPropositionAdds()[actItr->first]);
                    list<Literal*>::const_iterator pItr = adds.begin();
                    const list<Literal*>::const_iterator pEnd = adds.end();
                    
                    for (; pItr != pEnd; ++pItr) {
                        if (RPGBuilder::getNegativeEffectsToActions()[(*pItr)->getStateID()].empty()) {
                            addSet.insert((*pItr)->getStateID());
                        }
                    }
                }
                if (first) {
                    definitelyAddedWithThisEffect.swap(addSet);
                } else {
                    set<int> iSect;
                    std::set_intersection(addSet.begin(), addSet.end(), definitelyAddedWithThisEffect.begin(), definitelyAddedWithThisEffect.end(), std::insert_iterator<set<int> >(iSect, iSect.end()));
                    iSect.swap(definitelyAddedWithThisEffect);
                }
            }
        }
        
        if (first) {
            // nothing has this effect
            continue;
        }

        if (requiredThenDeletedWithThisEffect.empty()) {
            variablesThatDoNotFit.insert(currEff.fluentIndex);
            continue;
        }
        
        // have some facts that are required then deleted irrecovably to get this effect
        
        pair<map<int, pair<set<int>, set<int> > >::iterator,bool> beforeItr = requiredThenDeletedToGetValue.insert(make_pair(currEff.fluentIndex, make_pair(requiredThenDeletedWithThisEffect, definitelyAddedWithThisEffect)));
        
        if (!beforeItr.second) {
            // look at the other effects on this variable
            set<int> iSect;
            std::set_intersection(beforeItr.first->second.first.begin(), beforeItr.first->second.first.end(), requiredThenDeletedWithThisEffect.begin(), requiredThenDeletedWithThisEffect.end(), std::insert_iterator<set<int> >(iSect, iSect.end()));
            
            if (iSect.empty()) {
                requiredThenDeletedToGetValue.erase(beforeItr.first);
                variablesThatDoNotFit.insert(currEff.fluentIndex);
            } else {
                iSect.swap(beforeItr.first->second.first);
                
                set<int> iSect2;
                std::set_intersection(beforeItr.first->second.second.begin(), beforeItr.first->second.second.end(), definitelyAddedWithThisEffect.begin(), definitelyAddedWithThisEffect.end(), std::insert_iterator<set<int> >(iSect2, iSect2.end()));
            
                iSect2.swap(beforeItr.first->second.second);
            }
            
        }
    }

    if (requiredThenDeletedToGetValue.empty()) {
        return;
    }
    
    map<int, pair<set<int>,set<int> > >::const_iterator reqItr = requiredThenDeletedToGetValue.begin();
    const map<int, pair<set<int>,set<int> > >::const_iterator reqEnd = requiredThenDeletedToGetValue.end();
    
    for (; reqItr != reqEnd; ++reqItr) {
        if (!reqItr->second.second.empty()) {
            cout << *(RPGBuilder::getPNE(reqItr->first)) << " fixed and defined by at least " << *(RPGBuilder::getLiteral(*(reqItr->second.second.begin()))) << endl;
            factsThatDefineAndFixVariables.insert(make_pair(reqItr->first, reqItr->second.second));
            set<int>::const_iterator fItr = reqItr->second.second.begin();
            const set<int>::const_iterator fEnd = reqItr->second.second.end();
            
            for (; fItr != fEnd; ++fItr) {
                variablesFixedAndDefinedByFact[*fItr].insert(reqItr->first);
            }
        }
        
    }
    
    
}

void NumericAnalysis::findOrphanedNumericEffects() {
    
    vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();
    
    const int effCount = effTable.size();
    
    for (int eff = 0; eff < effCount; ++eff) {
        
        RPGBuilder::RPGNumericEffect & currEff = effTable[eff];
        currEff.canEverHappen = !(RPGBuilder::getRpgNumericEffectsToActions()[eff].empty());
                
    }
    
    const map<int, list<RPGBuilder::IntegralContinuousEffect> > & actionsToIntegralConditionalEffects = RPGBuilder::getActionsToIntegralConditionalEffects();
    
    {
        map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceItr = actionsToIntegralConditionalEffects.begin();
        const map<int, list<RPGBuilder::IntegralContinuousEffect> >::const_iterator iceEnd = actionsToIntegralConditionalEffects.end();
        
        for (; iceItr != iceEnd; ++iceItr) {
            
            list<RPGBuilder::IntegralContinuousEffect>::const_iterator icItr = iceItr->second.begin();
            const list<RPGBuilder::IntegralContinuousEffect>::const_iterator icEnd = iceItr->second.end();
            
            for (; icItr != icEnd; ++icItr) {
                list<int> keep;
                icItr->getRelaxedStartEffects(keep,0.0);
                icItr->getRelaxedEndEffects(keep,0.0);
                
                list<int>::const_iterator effItr = keep.begin();
                const list<int>::const_iterator effEnd = keep.end();
                
                for (; effItr != effEnd; ++effItr) {
                    if (!effTable[*effItr].canEverHappen) {
                        cout << "Conditional effect on " << *(RPGBuilder::getInstantiatedOp(iceItr->first)) << " means we keep " << effTable[*effItr] << endl;
                    }
                    effTable[*effItr].canEverHappen = true;
                }
            }
        }
    }

    const vector<list<RPGBuilder::ConditionalEffect> > & actionsToConditionalEffects = RPGBuilder::getActionsToConditionalEffects();
    
    {
        const int actCount = actionsToConditionalEffects.size();
        
        for (int actID = 0; actID < actCount; ++actID) {
            if (RPGBuilder::rogueActions[actID]) {
                continue;
            }
            
            list<RPGBuilder::ConditionalEffect>::const_iterator ceItr = actionsToConditionalEffects[actID].begin();
            const list<RPGBuilder::ConditionalEffect>::const_iterator ceEnd = actionsToConditionalEffects[actID].end();
            
            for (; ceItr != ceEnd; ++ceItr) {
                list<pair<int, Planner::time_spec> >::const_iterator effItr = ceItr->getNumericEffects().begin();
                const list<pair<int, Planner::time_spec> >::const_iterator effEnd = ceItr->getNumericEffects().end();

                for (; effItr != effEnd; ++effItr) {
                    if (!effTable[effItr->first].canEverHappen) {
                        cout << "Conditional effect on " << *(RPGBuilder::getInstantiatedOp(actID)) << " means we keep " << effTable[effItr->first] << endl;
                    }
                    effTable[effItr->first].canEverHappen = true;
                }
            }
        }
    }
    
    for (int eff = 0; eff < effCount; ++eff) {
        if (!effTable[eff].canEverHappen) {
            cout << "Effect " << effTable[eff] << " is orphaned\n";
        }
    }
}

vector<bool> NumericAnalysis::whetherEffectCanBeMovedToStart;

void NumericAnalysis::findEndEffectsSafeToMoveToTheStart() {
    vector<RPGBuilder::RPGNumericEffect> & effTable = RPGBuilder::getNumericEff();
    
    const int effCount = effTable.size();
    
    whetherEffectCanBeMovedToStart.resize(effCount, false);
    
    for (int eff = 0; eff < effCount; ++eff) {
        
        if (factsThatDefineAndFixVariables.find(effTable[eff].fluentIndex) == factsThatDefineAndFixVariables.end()) {
            continue;
        }
        
        whetherEffectCanBeMovedToStart[eff] = true;
        
        for (int s = 0; s < effTable[eff].size; ++s) {
            const int v = effTable[eff].variables[s];
            if (v < 0) { // duration-dependent
                continue;
            }
            
            if (v < RPGBuilder::getPNECount()) {
                if (tickerVariables.find(v) == tickerVariables.end()) {
                    whetherEffectCanBeMovedToStart[eff] = false;
                    break;
                }
            } else {
                if (tickerVariables.find(v - RPGBuilder::getPNECount()) == tickerVariables.end()) {
                    whetherEffectCanBeMovedToStart[eff] = false;
                    break;
                }
            }
        }
        
    }
    
}
  
  
void NumericAnalysis::identifyIntegralVariablesAndUpdatePreconditions()
{
    
}

};

