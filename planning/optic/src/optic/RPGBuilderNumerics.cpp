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

#include "RPGBuilder.h"
#include "globals.h"
#include "temporalanalysis.h"
#include "numericanalysis.h"

#include "PreferenceHandler.h"

#include <sstream>

using std::ostringstream;

#include "typecheck.h"
#include "TIM.h"
#include "FuncAnalysis.h"


using namespace TIM;
using namespace Inst;
using namespace VAL;

using std::endl;
using std::cerr;

namespace Planner
{

static bool toleranceWarningGiven = false;

class ExpressionBuilder: public VisitController
{

private:

    list<RPGBuilder::Operand> & formula;
    VAL::TypeChecker * tc;
    VAL::FastEnvironment * fe;
    bool valid;
    bool debug;
public:

    ExpressionBuilder(list<RPGBuilder::Operand> & formulaIn, VAL::FastEnvironment * f, VAL::TypeChecker * t = 0) :
            formula(formulaIn), tc(t), fe(f), debug(Globals::globalVerbosity & 16) {};

    bool buildFormula(VAL::expression * e) {
        if (debug) cout << "Building numeric expression\n";
        valid = true;
        e->visit(this);
        return valid;
    }

    void visit_plus_expression(const plus_expression * s) {
        if (debug) cout << "+ term\n";
        s->getLHS()->visit(this);
        s->getRHS()->visit(this);
        formula.push_back(RPGBuilder::Operand(RPGBuilder::NE_ADD));
    }

    void visit_minus_expression(const minus_expression * s) {
        if (debug) cout << "- term\n";
        s->getLHS()->visit(this);
        s->getRHS()->visit(this);
        formula.push_back(RPGBuilder::Operand(RPGBuilder::NE_SUBTRACT));
    }
    void visit_mul_expression(const mul_expression * s) {
        if (debug) cout << "* term\n";
        s->getLHS()->visit(this);
        s->getRHS()->visit(this);
        formula.push_back(RPGBuilder::Operand(RPGBuilder::NE_MULTIPLY));
    }
    void visit_div_expression(const div_expression * s) {
        if (debug) cout << "/ term\n";
        s->getLHS()->visit(this);
        s->getRHS()->visit(this);
        formula.push_back(RPGBuilder::Operand(RPGBuilder::NE_DIVIDE));
    }

    void visit_uminus_expression(const uminus_expression * s) {
        if (debug) cout << "0- term\n";
        formula.push_back(RPGBuilder::Operand((double) 0.0));
        s->getExpr()->visit(this);
        formula.push_back(RPGBuilder::Operand(RPGBuilder::NE_SUBTRACT));
    }
    void visit_int_expression(const int_expression * s) {
        if (debug) cout << "int term " << s->double_value() << endl;
        formula.push_back(RPGBuilder::Operand((double) s->double_value()));
    }
    void visit_float_expression(const float_expression * s) {
        if (debug) cout << "float term " << s->double_value() << endl;
        const double rounded = round(s->double_value() / Globals::numericTolerance) * Globals::numericTolerance;
        if (fabs(rounded - s->double_value()) > (Globals::numericTolerance * 0.1)
            && !toleranceWarningGiven) {
            cerr << "Warning: rounding numeric constants such as " << s->double_value() << " to an accuracy of " << Globals::numericTolerance << endl;
            
            toleranceWarningGiven = true;
        }
        formula.push_back(RPGBuilder::Operand((double) rounded));
    };

    void visit_special_val_expr(const special_val_expr * v) {
        if (v->getKind() == E_HASHT) {
            if (debug) {
                cout << "#t term\n";
            }
            formula.push_back(RPGBuilder::Operand((int) - 2));
        } else if (v->getKind() == E_DURATION_VAR) {
            if (debug) {
                cout << "?duration term\n";
            }            
            formula.push_back(RPGBuilder::Operand((int) - 3));
        } else if (v->getKind() == E_TOTAL_TIME) {
            if (debug) {
                cout << "total-time term\n";
            }            
            formula.push_back(RPGBuilder::Operand((int) - 4));
        } else {
            cout << "Error parsing expression: unsupported task constant " << *v << " found\n";
        }
    };


    void visit_func_term(const func_term * s) {
        PNE lookupPNE(s, fe);
        //cout << "Looking up " << lookupPNE << "\n";
        PNE * realPNE = instantiatedOp::findPNE(&lookupPNE);

        if (!realPNE) {
            if (debug) {
                cout << "PNE " << lookupPNE << " did not exist\n";
            }
            formula.push_back(RPGBuilder::Operand((double) 0.0));
            valid = false;
        } else {
            if (realPNE->getHead()->getName() == "fake-duration") {
                static bool printed = false;
                if (!printed) {
                    printed = true;
                    cout << "Detected fake-duration in condition, replaced with ?duration\n";
                }
                formula.push_back(RPGBuilder::Operand((int) - 3));
            } else {
                #ifdef STOCHASTICDURATIONS
                if (   realPNE->getHead()->getName().find("exponential") == 0
                    || realPNE->getHead()->getName().find("stochastic-") == 0) {
                    if (debug) {
                        cout << "Stochastic duration PNE " << *realPNE << ", ID " << realPNE->getGlobalID() << std::endl;
                    }                                                            
                    formula.push_back(realPNE);
                }
                else
                #endif
                if (realPNE->getStateID() == -1) {
                    if (debug) {
                        cout << "PNE " << *realPNE << ", with static value " << EFT(realPNE->getHead())->getInitial(realPNE->begin(), realPNE->end()).second << std::endl; 
                    }                    
                    const double originalValue = EFT(realPNE->getHead())->getInitial(realPNE->begin(), realPNE->end()).second;
                    const double rounded = round(originalValue / Globals::numericTolerance) * Globals::numericTolerance;
                    if (fabs(rounded - originalValue) > (Globals::numericTolerance * 0.1)
                        && !toleranceWarningGiven) {
                        cerr << "Warning: rounding numeric constants such as " << originalValue << " to an accuracy of " << Globals::numericTolerance << endl;
                        
                        toleranceWarningGiven = true;
                    }

                    formula.push_back(RPGBuilder::Operand(rounded));
                } else {
                    if (debug) {
                        cout << "PNE " << *realPNE << ", ID " << realPNE->getStateID() << std::endl;
                    }                                        
                    formula.push_back(RPGBuilder::Operand((int) realPNE->getStateID()));
                }
            }
        }
    };

    void visit_violation_term(const violation_term * s) {
        formula.push_back(RPGBuilder::Operand(s->getName()));
    };

};

double RPGBuilder::calculateRHS(const list<Operand> & formula, vector<double> & fluents)
{

    list<double> RHS;

    list<Operand>::const_iterator fItr = formula.begin();
    const list<Operand>::const_iterator fEnd = formula.end();

    for (; fItr != fEnd; ++fItr) {
        const Operand & currOperand = *fItr;
        const math_op currMathOp = currOperand.numericOp;
        switch (currMathOp) {
        case RPGBuilder::NE_ADD: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() += oldFront;
        }
        break;
        case RPGBuilder::NE_SUBTRACT: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() -= oldFront;
        }
        break;
        case RPGBuilder::NE_MULTIPLY: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() *= oldFront;
        }
        break;
        case RPGBuilder::NE_DIVIDE: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() /= oldFront;
        }
        break;
        case RPGBuilder::NE_CONSTANT:
            RHS.push_front(currOperand.constantValue);
            break;
        case RPGBuilder::NE_FLUENT:
            RHS.push_front(fluents[currOperand.fluentValue]);
            break;
        #ifdef STOCHASTICDURATIONS            
        case RPGBuilder::NE_STOCHASTIC_DURATION_TERM: {                    
            assert(currOperand.durationVar);
            assert(EFT(currOperand.durationVar->getHead())->isStatic());
            RHS.push_front(EFT(currOperand.durationVar->getHead())->getInitial(currOperand.durationVar->begin(), currOperand.durationVar->end()).second);
            break;
        }
        #endif
        default:
            // this should never happen
            assert(false);
        }
    }

    return RHS.front();

};

pair<double, bool> RPGBuilder::constRHS(const list<Operand> & formula)
{

    list<double> RHS;

    assert(!formula.empty());
    
    list<Operand>::const_iterator fItr = formula.begin();
    const list<Operand>::const_iterator fEnd = formula.end();

    for (; fItr != fEnd; ++fItr) {
        const Operand & currOperand = *fItr;
        const math_op currMathOp = currOperand.numericOp;
        switch (currMathOp) {
        case RPGBuilder::NE_ADD: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() += oldFront;
        }
        break;
        case RPGBuilder::NE_SUBTRACT: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() -= oldFront;
        }
        break;
        case RPGBuilder::NE_MULTIPLY: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() *= oldFront;
        }
        break;
        case RPGBuilder::NE_DIVIDE: {
            const double oldFront = RHS.front();
            RHS.pop_front();
            RHS.front() /= oldFront;
        }
        break;
        case RPGBuilder::NE_CONSTANT: {
            RHS.push_front(currOperand.constantValue);
            break;
        }
        #ifdef STOCHASTICDURATIONS            
        case RPGBuilder::NE_STOCHASTIC_DURATION_TERM: {                    
            assert(currOperand.durationVar);
            if (EFT(currOperand.durationVar->getHead())->isStatic()) {
                RHS.push_front(EFT(currOperand.durationVar->getHead())->getInitial(currOperand.durationVar->begin(), currOperand.durationVar->end()).second);
                break;
            } else {
                return pair<double, bool>(0.0, false);
                break;
            }
        }
        #endif
        case RPGBuilder::NE_FLUENT: {
            //cout << "Duration expression is non-constant\n";
            return pair<double, bool>(0.0, false);            
            break;
        }
        default:
            // this should never happen
            assert(false);
        }
    }

    assert(!RHS.empty());
    
    //cout << "Duration expression is constant" << std::endl;    
    //cout << "Value " << RHS.front() << std::endl;
    
    return pair<double, bool>(RHS.front(), true);

};

double RPGBuilder::ArtificialVariable::evaluateWCalculate(const vector<double> & fluentTable, const int & pneCount)
{
    //cout << "Evaluating AV " << ID << " of size " << size << "\n";
    double toReturn = constant;
    //cout << "Evaluating AV of size " << size << "\n";
    for (int i = 0; i < size; ++i) {
        int var = fluents[i];
        if (var < 0) return std::numeric_limits<double>::signaling_NaN();
        double w = weights[i];
        if (var >= pneCount) {
            var -= pneCount;
            if (w != 0.0) w = 0.0 - w;
        }
        toReturn += w * fluentTable[var];
    }
    return toReturn;
};


double RPGBuilder::ArtificialVariable::evaluateWCalculate(const vector<double> & minFluentTable, const vector<double> & maxFluentTable, const int & pneCount) const
{
    //cout << "Evaluating AV " << ID << " of size " << size << "\n";
    double toReturn = constant;
    //cout << "Evaluating AV of size " << size << "\n";
    for (int i = 0; i < size; ++i) {
        int var = fluents[i];
        if (var < 0) return std::numeric_limits<double>::signaling_NaN();
        double w = weights[i];
        if (var >= pneCount) {
            var -= pneCount;
            if (w != 0.0) w = 0.0 - w;
            toReturn += w * minFluentTable[var];
        } else {
            toReturn += w * maxFluentTable[var];
        }
    }
    return toReturn;
};


bool RPGBuilder::RPGNumericPrecondition::isSatisfiedWCalculate(const vector<double> & maxFluents) const
{

    const int pneCount = RPGBuilder::getPNECount();
    int var = LHSVariable;
    if (var < 0) {
        return false;
    }
    //cout << "Precondition based on variable " << var << "\n";
    if (var < pneCount) {
        //cout << "Precondition based on positive variable " << var << "\n";
        if (op == VAL::E_GREATER) {
            return (maxFluents[var] > RHSConstant);
        } else {
            return (maxFluents[var] >= RHSConstant);
        }
    }
    var -= pneCount;
    if (var < pneCount) {
        //cout << "Precondition based on negative variable " << var << "\n";
        const double localVal = (maxFluents[var] != 0.0 ? 0.0 - maxFluents[var] : 0.0);
        if (op == VAL::E_GREATER) {
            return (localVal > RHSConstant);
        } else {
            return (localVal >= RHSConstant);
        }
    }
    var += pneCount;
    //cout << "Precondition based on artificial variable " << var << "\n";
    ArtificialVariable & av = RPGBuilder::getArtificialVariable(var);
    const double localVal = av.evaluateWCalculate(maxFluents, pneCount);
    if (localVal == std::numeric_limits<double>::signaling_NaN()) return false;
    if (op == VAL::E_GREATER) {
        return (localVal > RHSConstant);
    } else {
        return (localVal >= RHSConstant);
    }

};

bool RPGBuilder::RPGNumericPrecondition::isSatisfiedWCalculate(const vector<double> & minFluents, const vector<double> & maxFluents) const
{

    const int pneCount = RPGBuilder::getPNECount();
    int var = LHSVariable;
    if (var < 0) {
        return false;
    }
    //cout << "Precondition based on variable " << var << "\n";
    if (var < pneCount) {
        //cout << "Precondition based on positive variable " << var << "\n";
        if (op == VAL::E_GREATER) {
            return (maxFluents[var] > RHSConstant);
        } else {
            return (maxFluents[var] >= RHSConstant);
        }
    }
    var -= pneCount;
    if (var < pneCount) {
        //cout << "Precondition based on negative variable " << var << "\n";
        const double localVal = (minFluents[var] != 0.0 ? 0.0 - minFluents[var] : 0.0);
        if (op == VAL::E_GREATER) {
            return (localVal > RHSConstant);
        } else {
            return (localVal >= RHSConstant);
        }
    }
    var += pneCount;
    //cout << "Precondition based on artificial variable " << var << "\n";
    ArtificialVariable & av = RPGBuilder::getArtificialVariable(var);
    const double localVal = av.evaluateWCalculate(minFluents, maxFluents, pneCount);
    if (localVal == std::numeric_limits<double>::signaling_NaN()) return false;
    if (op == VAL::E_GREATER) {
        return (localVal > RHSConstant);
    } else {
        return (localVal >= RHSConstant);
    }

};

bool RPGBuilder::RPGNumericPrecondition::canBeUnsatisfiedWCalculate(const vector<double> & minFluents, const vector<double> & maxFluents) const
{
    
    const int pneCount = RPGBuilder::getPNECount();
    int var = LHSVariable;
    //cout << "Precondition based on variable " << var << "\n";
    if (var < pneCount) {
        //cout << "Precondition based on positive variable " << var << "\n";
        if (op == VAL::E_GREATER) {
            return (minFluents[var] <= RHSConstant);
        } else {
            return (minFluents[var] < RHSConstant);
        }
    }
    var -= pneCount;
    if (var < pneCount) {
        //cout << "Precondition based on negative variable " << var << "\n";
        const double localVal = (maxFluents[var] != 0.0 ? 0.0 - maxFluents[var] : 0.0);
        if (op == VAL::E_GREATER) {
            return (localVal <= RHSConstant);
        } else {
            return (localVal < RHSConstant);
        }
    }
    var += pneCount;
    //cout << "Precondition based on artificial variable " << var << "\n";
    ArtificialVariable & av = RPGBuilder::getArtificialVariable(var);
    const double localVal = av.evaluateWCalculate(minFluents, maxFluents, pneCount);
    if (op == VAL::E_GREATER) {
        return (localVal <= RHSConstant);
    } else {
        return (localVal < RHSConstant);
    }
                
}


RPGBuilder::NumericEffect::NumericEffect(const VAL::assign_op & opIn, const int & fIn, VAL::expression * formulaIn, VAL::FastEnvironment * f, VAL::TypeChecker * t) :
        fluentIndex(fIn), op(opIn)
{
    ExpressionBuilder builder(formula, f, t);
    builder.buildFormula(formulaIn);
};

RPGBuilder::NumericPrecondition::NumericPrecondition(const VAL::comparison_op & opIn, VAL::expression * LHSformulaIn, VAL::expression * RHSformulaIn, VAL::FastEnvironment * f, VAL::TypeChecker * t, const bool p) :
        op(opIn), valid(true), polarity(p)
{
    {
        ExpressionBuilder builder(LHSformula, f, t);
        valid = builder.buildFormula(LHSformulaIn);
    }
    {
        ExpressionBuilder builder(RHSformula, f, t);
        valid = (valid && builder.buildFormula(RHSformulaIn));
    }

};

double RPGBuilder::NumericEffect::applyEffect(vector<double> & fluents) const
{

    const double RHS = calculateRHS(formula, fluents);

    switch (op) {
    case VAL::E_ASSIGN:
        return RHS;
        break;
    case VAL::E_INCREASE:
        return (fluents[fluentIndex] + RHS);
        break;
    case VAL::E_DECREASE:
        return (fluents[fluentIndex] - RHS);
        break;
    case VAL::E_SCALE_UP:
        return (fluents[fluentIndex] * RHS);
        break;
    case VAL::E_SCALE_DOWN:
        return (fluents[fluentIndex] / RHS);
        break;
    default:
        // this should never happen
        assert(false);
    }


};

bool RPGBuilder::NumericPrecondition::isSatisfied(vector<double> & fluents) const
{

    const double LHS = calculateRHS(LHSformula, fluents);
    const double RHS = calculateRHS(RHSformula, fluents);

    switch (op) {
    case VAL::E_GREATER:
        return (LHS > RHS);
        break;
    case VAL::E_GREATEQ:
        return (LHS >= RHS);
        break;
    case VAL::E_LESS:
        return (LHS < RHS);
        break;
    case VAL::E_LESSEQ:
        return (LHS <= RHS);
        break;
    case VAL::E_EQUALS:
        return (LHS == RHS);
        break;
    }

    assert(false); // this should never happen
    return false;

};

double RPGBuilder::NumericPrecondition::evaluateRHS(vector<double> & fluentTable) const
{
    return calculateRHS(RHSformula, fluentTable);
}

pair<double, bool> RPGBuilder::NumericPrecondition::constRHS() const
{
    return RPGBuilder::constRHS(RHSformula);
}

void RPGBuilder::NumericEffect::display(ostream & o) const
{

    o << *(RPGBuilder::getPNE(fluentIndex)) << " ";
    switch (op) {

    case VAL::E_ASSIGN:
        o << "= ";
        break;
    case VAL::E_INCREASE:
        o << "+= ";
        break;
    case VAL::E_DECREASE:
        o << "-= ";
        break;
    case VAL::E_SCALE_UP:
        o << "*= ";
        break;
    case VAL::E_SCALE_DOWN:
        o << "/= ";
        break;
    default:
        break;
    };
    {
        list<Operand>::const_iterator opItr = formula.begin();
        const list<Operand>::const_iterator opEnd = formula.end();
        o << "(";
        for (; opItr != opEnd; ++opItr) {
            const Operand & currOperand = *opItr;
            const math_op currMathOp = currOperand.numericOp;
            switch (currMathOp) {
            case RPGBuilder::NE_ADD: {
                o << " +";
            }
            break;
            case RPGBuilder::NE_SUBTRACT: {
                o << " -";
            }
            break;
            case RPGBuilder::NE_MULTIPLY: {
                o << " *";
            }
            break;
            case RPGBuilder::NE_DIVIDE: {
                o << " /";
            }
            break;
            case RPGBuilder::NE_CONSTANT: {
                o << " " << currOperand.constantValue;
            }
            break;
            case RPGBuilder::NE_FLUENT: {
                if (currOperand.fluentValue < 0) {
                    o << " <special>";
                } else {
                    o << " " << *(RPGBuilder::getPNE(currOperand.fluentValue));
                }
            }
            break;
            default:
                // this should never happen
                assert(false);
            }
        }
        o << ")";
    }

};

void RPGBuilder::NumericPrecondition::display(ostream & o) const
{

    {
        list<Operand>::const_iterator opItr = LHSformula.begin();
        const list<Operand>::const_iterator opEnd = LHSformula.end();
        o << "(";
        for (; opItr != opEnd; ++opItr) {
            const Operand & currOperand = *opItr;
            const math_op currMathOp = currOperand.numericOp;
            switch (currMathOp) {
            case RPGBuilder::NE_ADD: {
                o << " +";
            }
            break;
            case RPGBuilder::NE_SUBTRACT: {
                o << " -";
            }
            break;
            case RPGBuilder::NE_MULTIPLY: {
                o << " *";
            }
            break;
            case RPGBuilder::NE_DIVIDE: {
                o << " /";
            }
            break;
            case RPGBuilder::NE_CONSTANT: {
                o << " " << currOperand.constantValue;
            }
            break;
            case RPGBuilder::NE_FLUENT: {
                if (currOperand.fluentValue < 0) {
                    o << " <special>";
                } else {
                    o << " " << *(RPGBuilder::getPNE(currOperand.fluentValue));
                }
            }
            break;
            #ifdef STOCHASTICDURATIONS            
            case RPGBuilder::NE_STOCHASTIC_DURATION_TERM: {                    
                assert(currOperand.durationVar);
                o << " " << *(currOperand.durationVar);
                break;
            }
            #endif
            default:
                // this should never happen
                assert(false);
            }
        }
        o << ")";
    }

    switch (op) {

    case VAL::E_GREATER:
        o << " > ";
        break;
    case VAL::E_GREATEQ:
        o << " >= ";
        break;
    case VAL::E_LESS:
        o << " < ";
        break;
    case VAL::E_LESSEQ:
        o << " <= ";
        break;
    case VAL::E_EQUALS:
        o << " = ";
        break;
    };
    {
        list<Operand>::const_iterator opItr = RHSformula.begin();
        const list<Operand>::const_iterator opEnd = RHSformula.end();
        o << "(";
        for (; opItr != opEnd; ++opItr) {
            const Operand & currOperand = *opItr;
            const math_op currMathOp = currOperand.numericOp;
            switch (currMathOp) {
            case RPGBuilder::NE_ADD: {
                o << " +";
            }
            break;
            case RPGBuilder::NE_SUBTRACT: {
                o << " -";
            }
            break;
            case RPGBuilder::NE_MULTIPLY: {
                o << " *";
            }
            break;
            case RPGBuilder::NE_DIVIDE: {
                o << " /";
            }
            break;
            case RPGBuilder::NE_CONSTANT: {
                o << " " << currOperand.constantValue;
            }
            break;
            case RPGBuilder::NE_FLUENT: {
                if (currOperand.fluentValue == -1) {
                    o << " <special>";
                } else {
                    o << " " << *(RPGBuilder::getPNE(currOperand.fluentValue));
                }
            }
            break;
            #ifdef STOCHASTICDURATIONS            
            case RPGBuilder::NE_STOCHASTIC_DURATION_TERM: {                    
                assert(currOperand.durationVar);
                o << " " << *(currOperand.durationVar);
                break;
            }
            #endif
            default:
                // this should never happen
                assert(false);
            }
        }
        o << ")";
    }

};

ostream & operator <<(ostream & o, const RPGBuilder::NumericPrecondition & p)
{
    p.display(o);
    return o;
};

ostream & operator <<(ostream & o, const RPGBuilder::NumericEffect & p)
{
    p.display(o);
    return o;
};

ostream & operator <<(ostream & o, const RPGBuilder::RPGNumericPrecondition & p)
{
    p.display(o);
    return o;
};

ostream & operator <<(ostream & o, const RPGBuilder::ArtificialVariable & p)
{
    p.display(o);
    return o;
};

ostream & operator <<(ostream & o, const RPGBuilder::RPGNumericEffect & p)
{
    p.display(o);
    return o;
};

bool RPGBuilder::ArtificialVariable::operator <(const RPGBuilder::ArtificialVariable & v) const
{

    if (size < v.size) return true;
    if (size > v.size) return false;

    for (int i = 0; i < size; ++i) {
        const double w1 = weights[i];
        const double w2 = v.weights[i];
        if (w1 < w2) return true;
        if (w1 > w2) return false;
    }

    for (int i = 0; i < size; ++i) {
        const int w1 = fluents[i];
        const int w2 = v.fluents[i];
        if (w1 < w2) return true;
        if (w1 > w2) return false;
    }

    if (constant < v.constant) return true;

    return false;
};

bool RPGBuilder::RPGNumericPrecondition::operator <(const RPGBuilder::RPGNumericPrecondition & r) const
{

    if (LHSVariable < r.LHSVariable) return true;
    if (LHSVariable > r.LHSVariable) return false;

    if (LHSConstant < r.LHSConstant) return true;
    if (LHSConstant > r.LHSConstant) return false;

    if (op < r.op) return true;
    if (op > r.op) return false;

    if (RHSVariable < r.RHSVariable) return true;
    if (RHSVariable > r.RHSVariable) return false;

    if (RHSConstant < r.RHSConstant) return true;

    return false;

};

bool RPGBuilder::RPGNumericEffect::operator <(const RPGNumericEffect & e) const
{
    if (fluentIndex < e.fluentIndex) return true;
    if (fluentIndex > e.fluentIndex) return false;

    if (!isAssignment && e.isAssignment) return true;
    if (isAssignment && !e.isAssignment) return false;

    if (size < e.size) return false;
    if (size > e.size) return true;

    if (constant < e.constant) return true;
    if (constant > e.constant) return false;

    for (int i = 0; i < size; ++i) {

        if (variables[i] < e.variables[i]) return true;
        if (variables[i] > e.variables[i]) return false;

        if (weights[i] < e.weights[i]) return true;
        if (weights[i] > e.weights[i]) return false;

    }

    return false;


};

void RPGBuilder::ArtificialVariable::display(ostream & o) const
{


    o << "av of size " << size << ", id " << ID << " (";
    const int lim = RPGBuilder::getPNECount();

    for (int i = 0; i < size; ++i) {
        if (i) o << " + ";
        if (weights[i] != 1.0) {
            o << weights[i] << "*";
        }
        const int v = fluents[i];

        if (v < 0) {
            if (v == -3) {
                o << "?duration";
            } else if (v == -19) {
                o << "-?duration";
            } else {
                o << "<special?>";
            }
        } else if (v < lim) {
            o << *(RPGBuilder::getPNE(v));
        } else {
            o << "-1*" << *(RPGBuilder::getPNE(v - lim));
        }
    }
    if (constant != 0.0) {
        if (size) o << " + ";
        o << constant;
    }

    o << ")";
}

void RPGBuilder::RPGNumericPrecondition::display(ostream & o) const
{

    const int lim = RPGBuilder::getPNECount();

    if (LHSVariable < 0) {
        if (LHSVariable == -1) {
            o << LHSConstant;
        } else if (LHSVariable == -3) {
            o << "?duration";
        } else if (LHSVariable == -19) {
            o << "?duration";
        } else {
            o << "<special?>";
        }
    } else {
        if (LHSVariable < lim) {
            if (LHSConstant != 1.0) o << LHSConstant << "*";
            o << *(RPGBuilder::getPNE(LHSVariable));
        } else if (LHSVariable < (2 * lim)) {
            if (LHSConstant != 1.0) o << LHSConstant << "*";
            o << "-1*" << *(RPGBuilder::getPNE(LHSVariable - lim));
        } else {
            o << RPGBuilder::getArtificialVariable(LHSVariable);
        }
    }
    
    if (op == VAL::E_GREATER) {
        o << " > ";
    } else if (op == VAL::E_GREATEQ) {
        o << " >= ";
    } else {
        assert(false);
    }

    if (RHSVariable < 0) {
        if (RHSVariable == -1) {
            o << RHSConstant;
        } else if (RHSVariable == -3) {
            o << "?duration";
        } else if (RHSVariable == -19) {
            o << "?duration";
        } else {
            o << "<special?>";
        }
    } else {
        if (RHSVariable < lim) {
            if (RHSConstant != 1.0) o << RHSConstant << "*";
            o << *(RPGBuilder::getPNE(RHSVariable));
        } else if (RHSVariable < (2 * lim)) {
            if (RHSConstant != 1.0) o << RHSConstant << "*";
            o << "-1*" << *(RPGBuilder::getPNE(RHSVariable - lim));
        } else {
            o << RPGBuilder::getArtificialVariable(RHSVariable);
        }
    }

    o << " [lv=" << LHSVariable << ",lc=" << LHSConstant << ",rv=" << RHSVariable << ",rc=" << RHSConstant << "]";

};

void RPGBuilder::RPGNumericEffect::display(ostream & o) const
{
    static const int lim = RPGBuilder::getPNECount();
    o << "(";

    o << *(RPGBuilder::getPNE(fluentIndex));
    if (isAssignment) {
        o << " =";
    } else {
        o << " +=";
    }
    int t = 0;
    if (constant != 0.0 || size == 0) {
        o << " " << constant;
        ++t;
    }
    for (int i = 0; i < size; ++i, ++t) {
        if (t) o << " + ";
        if (weights[i] != 1.0) {
            o << weights[i] << "*";
        }
        const int v = variables[i];

        if (v == -3) {
            o << "?duration";
        } else if (v == -19) {
            o << "-?duration";
        } else if (v == -2) {
            o << "#t";
        } else if (v == -18) {
            o << "-#t";
        } else if (v < lim) {
            o << *(RPGBuilder::getPNE(v));
        } else {
            o << "-1*" << *(RPGBuilder::getPNE(v - lim));
        }
    }

    o << ")";
}


void RPGBuilder::simplify(pair<list<double>, list<int> > & p)
{


    map<int,double> simplified;

    list<double>::iterator fItr = p.first.begin();
    const list<double>::iterator fEnd = p.first.end();

    list<int>::iterator sItr = p.second.begin();

    for (; fItr != fEnd; ++fItr, ++sItr) {
        simplified.insert(make_pair(*sItr, 0.0)).first->second += *fItr;
    }
     
    p.first.clear();
    p.second.clear();

    map<int,double>::const_iterator rItr = simplified.begin();
    const map<int,double>::const_iterator rEnd = simplified.end();

    for (; rItr != rEnd; ++rItr) {
        p.first.push_back(rItr->second);
        p.second.push_back(rItr->first);
    }

    /*
    list<double>::iterator fItr = p.first.begin();
    const list<double>::iterator fEnd = p.first.end();
    list<double>::iterator constTerm = fEnd;

    list<int>::iterator sItr = p.second.begin();
    //const list<double>::iterator sEnd = p.second.end();

    while (fItr != fEnd) {

        if (*sItr >= 0 || *sItr <= -2) {
            ++sItr;
            ++fItr;
        } else {
            if (constTerm == fEnd) {
                constTerm = fItr;
                ++fItr;
                ++sItr;
            } else {
                *constTerm += *fItr;
                list<double>::iterator fErase = fItr;
                list<int>::iterator sErase = sItr;

                ++fItr;
                ++sItr;
                p.first.erase(fErase);
                p.second.erase(sErase);
            }
        }

    }*/

}

#ifdef STOCHASTICDURATIONS
void RPGBuilder::simplify(pair<list<double>, list<pair<int,PNE*> > > & p)
{
    
    
    
    list<double>::iterator fItr = p.first.begin();
    const list<double>::iterator fEnd = p.first.end();
    list<double>::iterator constTerm = fEnd;
    
    list<pair<int,PNE*> >::iterator sItr = p.second.begin();
    //const list<double>::iterator sEnd = p.second.end();
    
    while (fItr != fEnd) {
        
        if (sItr->second || sItr->first >= 0 || sItr->first <= -2) {
            ++sItr;
            ++fItr;
        } else {
            if (constTerm == fEnd) {
                constTerm = fItr;
                ++fItr;
                ++sItr;
            } else {
                *constTerm += *fItr;
                list<double>::iterator fErase = fItr;
                list<pair<int,PNE*> >::iterator sErase = sItr;
                
                ++fItr;
                ++sItr;
                p.first.erase(fErase);
                p.second.erase(sErase);
            }
        }
        
    }
    
}
#endif


struct InvData {

    typedef RPGBuilder::RPGNumericPrecondition RPGNumericPrecondition;
    typedef RPGBuilder::ArtificialVariable ArtificialVariable;

    struct LTAVPointer {

        bool operator()(const RPGBuilder::ArtificialVariable * const a, const RPGBuilder::ArtificialVariable * const b) {
            return ((*a) < (*b));
        };

    };

    struct LTRNPPointer {

        bool operator()(const RPGBuilder::RPGNumericPrecondition * const a, const RPGBuilder::RPGNumericPrecondition * const b) {
            return ((*a) < (*b));
        };

    };


    set<ArtificialVariable*, LTAVPointer> avReuse;
    set<const RPGNumericPrecondition*, LTRNPPointer> preReuse;

    list<ArtificialVariable*> newAVs;
    list<RPGNumericPrecondition*> newPres;

    bool avReuseInit;
    bool preReuseInit;
    int baseNextAVIndex;
    int nextAVIndex;
    int baseNextPreIndex;
    int nextPreIndex;

    vector<ArtificialVariable> & rpgArtificialVariables;
    vector<RPGNumericPrecondition> & rpgNumericPreconditions;

    InvData(vector<ArtificialVariable> & avs, vector<RPGNumericPrecondition> & pres) : avReuseInit(false), preReuseInit(false), baseNextAVIndex(-1), nextAVIndex(-1), baseNextPreIndex(-1), nextPreIndex(-1), rpgArtificialVariables(avs), rpgNumericPreconditions(pres) {};

    pair<ArtificialVariable*, bool> insertAV(ArtificialVariable* candidate) {
        if (!avReuseInit) {
            const int loopLim = rpgArtificialVariables.size();
            for (int s = 0; s < loopLim; ++s) {
                avReuse.insert(&(rpgArtificialVariables[s]));
                if (rpgArtificialVariables[s].ID > nextAVIndex) nextAVIndex = rpgArtificialVariables[s].ID;
            }
            ++nextAVIndex;
            baseNextAVIndex = nextAVIndex;
            avReuseInit = true;
        }

        pair<set<ArtificialVariable*, LTAVPointer>::iterator, bool> avrItr = avReuse.insert(candidate);

        if (avrItr.second) {
            candidate->ID = nextAVIndex;
            ++nextAVIndex;
            newAVs.push_back(candidate);
            return pair<ArtificialVariable*, bool>(candidate, true);
        }

        delete candidate;

        return pair<ArtificialVariable*, bool>(*(avrItr.first), false);
    };

    pair<const RPGNumericPrecondition*, bool> insertPre(RPGNumericPrecondition* const candidate) {
        if (!preReuseInit) {
            const int loopLim = rpgNumericPreconditions.size();
            for (int s = 0; s < loopLim; ++s) {
                preReuse.insert(&(rpgNumericPreconditions[s]));
                if (rpgNumericPreconditions[s].ID > nextPreIndex) nextPreIndex = rpgNumericPreconditions[s].ID;
            }
            ++nextPreIndex;
            baseNextPreIndex = nextPreIndex;
            preReuseInit = true;
        }

        pair<set<const RPGNumericPrecondition*, LTRNPPointer>::iterator, bool> avrItr = preReuse.insert(candidate);

        if (avrItr.second) {
            candidate->ID = nextPreIndex;
            ++nextPreIndex;
            newPres.push_back(candidate);
            return pair<const RPGNumericPrecondition*, bool>(candidate, true);
        }

        delete candidate;

        return pair<const RPGNumericPrecondition*, bool>(*(avrItr.first), false);
    };

    void erase(const RPGNumericPrecondition * const pre) {
        assert(pre->ID == (nextPreIndex - 1));
        preReuse.erase(pre);
        delete pre;
        newPres.pop_back();
        --nextPreIndex;
    };

    void erase(ArtificialVariable * av) {
        assert(av->ID == (nextAVIndex - 1));
        avReuse.erase(av);
        delete av;
        newAVs.pop_back();
        --nextAVIndex;
    };

    int anyNewPres() {
        return (nextPreIndex - baseNextPreIndex);
    }

    int anyNewAVs() {
        return (nextAVIndex - baseNextAVIndex);
    }


};

bool RPGBuilder::pushInvariantBackThroughStartEffects(const RPGBuilder::RPGNumericPrecondition & pre,
                                                      list<int> & startEffs, RPGBuilder::LinearEffects* ctsEffs,
                                                      InvData & commonData,
                                                      pair<const RPGBuilder::RPGNumericPrecondition *, bool> & preResult, pair<RPGBuilder::ArtificialVariable *, bool> & avResult)
{

    static const bool debug = false;
    
    static const int pneCount = pnes.size();
    map<int, double> lhs;
    double rhs = pre.RHSConstant;
    bool unchanged = true;

    if (debug) {
        cout << "Considering invariant " << pre << endl;
    }
    
    
    if (pre.LHSVariable < pneCount) {
        lhs.insert(make_pair(pre.LHSVariable, pre.LHSConstant));
    } else if (pre.LHSVariable < (2 * pneCount)) {
        lhs.insert(make_pair(pre.LHSVariable - pneCount, -pre.LHSConstant));
    } else {
        ArtificialVariable & currAV = getArtificialVariable(pre.LHSVariable);
        rhs -= currAV.constant;
        for (int s = 0; s < currAV.size; ++s) {
            if (currAV.fluents[s] < pneCount) {
                lhs.insert(make_pair(currAV.fluents[s], currAV.weights[s]));
            } else {
                lhs.insert(make_pair(currAV.fluents[s] - pneCount, -currAV.weights[s]));
            }
        }
    }

//  const map<int, double> lhsBefore = lhs;
//  const double rhsBefore = rhs;


    map<int, pair<map<int, double>, double> > mapOn;

    list<int>::iterator effItr = startEffs.begin();
    const list<int>::iterator effEnd = startEffs.end();

    for (; effItr != effEnd; ++effItr) {
        RPGNumericEffect & currEff = rpgNumericEffects[*effItr];

        map<int, double>::iterator lookup = lhs.find(currEff.fluentIndex);
        if (lookup != lhs.end()) {
            if (debug) {
                cout << "- Relevant start effect: " << currEff << endl;
            }
            map<int, double> localMap;
            double localConst = currEff.constant * lookup->second;
            {
                if (!currEff.isAssignment) localMap.insert(make_pair(currEff.fluentIndex, lookup->second));
                const int loopLim = currEff.weights.size();

                for (int s = 0; s < loopLim; ++s) {
                    if (currEff.variables[s] < pneCount) {
                        localMap.insert(make_pair(currEff.variables[s], currEff.weights[s] * lookup->second));
                    } else {
                        localMap.insert(make_pair(currEff.variables[s] - pneCount, -currEff.weights[s] * lookup->second));
                    }
                }

            }

            mapOn[currEff.fluentIndex] = make_pair(localMap, localConst);

        }
    }

    if (ctsEffs) {
        const int ctsVarCount = ctsEffs->vars.size();
        
        for (int v = 0; v < ctsVarCount; ++v) {
            map<int, double>::iterator lookup = lhs.find(ctsEffs->vars[v]);
            if (lookup != lhs.end()) {
                if (debug) {
                    cout << "- Relevant CTS effect: increase " << *(getPNE(ctsEffs->vars[v])) << " * #t " << ctsEffs->effects[0][v].constant << endl;
                }
                
                map<int, pair<map<int, double>, double> >::iterator moItr = mapOn.find(ctsEffs->vars[v]);
                if (moItr == mapOn.end()) {
                    map<int, double> localMap;
                    localMap.insert(make_pair(ctsEffs->vars[v], lookup->second));
                    moItr = mapOn.insert(make_pair(ctsEffs->vars[v], make_pair(localMap, 0.0))).first;
                }
                moItr->second.second += EPSILON * ctsEffs->effects[0][v].constant * lookup->second;
                
                
                unchanged = false;
                lhs.erase(lookup);
            }
        }
    }

    map<int, pair<map<int, double>, double> >::iterator moItr = mapOn.begin();
    const map<int, pair<map<int, double>, double> >::iterator moEnd = mapOn.end();

    for (; moItr != moEnd; ++moItr) {
        
        if (debug) {
            cout << "Rewriting due to term on " << *(getPNE(moItr->first)) << endl;
        }
        
        rhs -= moItr->second.second;

        if (debug && moItr->second.second != 0.0) {
            cout << "* RHS is now " << rhs;
            if (moItr->second.second > 0.0) {
                cout << " - smaller than it was\n";
            } else {
                cout << " - bigger than it was\n";
            }
        }
        
        map<int, double>::iterator mergeItr = moItr->second.first.begin();
        const map<int, double>::iterator mergeEnd = moItr->second.first.end();

        for (; mergeItr != mergeEnd; ++mergeItr) {
            const map<int, double>::iterator dest = lhs.insert(pair<int, double>(mergeItr->first, 0.0)).first;
            dest->second += mergeItr->second;
            if (debug) {
                cout << "* Changes coeffienct on " << *(getPNE(mergeItr->first)) << " to " << mergeItr->second << endl;
            }
            if (fabs(dest->second < 0.00000000001)) lhs.erase(dest);
        }
    }

    if (fabs(rhs) < 0.00000000001) rhs = 0.0;

    if (lhs.empty()) { //variable-less precondition
        preResult = pair<RPGNumericPrecondition*, bool>(0, false);
        avResult = pair<ArtificialVariable*, bool>(0, false);
        if (pre.op == E_GREATER) {
            return (0.0 > rhs);
        } else {
            return (0.0 >= rhs);
        }
    }

    if (unchanged) {
        if (debug) {
            cout << "Invariant is unchanged: copy as-is" << endl;
        }
        preResult = pair<const RPGNumericPrecondition*, bool>(&pre, false);
        avResult = pair<ArtificialVariable*, bool>(0, false);
        return true;
    }

    const int lhsSize = lhs.size();

    if (lhsSize == 1 && lhs.begin()->second > 0.0) {
        avResult = pair<ArtificialVariable*, bool>(0, false);
        RPGNumericPrecondition * const candidate = new RPGNumericPrecondition();
        candidate->LHSConstant = lhs.begin()->second;
        candidate->LHSVariable = lhs.begin()->first;
        candidate->op = pre.op;
        candidate->RHSConstant = rhs;
        preResult = commonData.insertPre(candidate);
        return true;
    }

    RPGNumericPrecondition * const candidate = new RPGNumericPrecondition();
    candidate->LHSConstant = 1.0;
    candidate->op = pre.op;
    candidate->RHSConstant = 0;


    ArtificialVariable * const candidateAV = new ArtificialVariable();

    candidateAV->size = lhsSize;
    candidateAV->weights.reserve(lhsSize);
    candidateAV->fluents.reserve(lhsSize);
    candidateAV->constant = -rhs;

    map<int, double>::iterator lhsItr = lhs.begin();
    const map<int, double>::iterator lhsEnd = lhs.end();

    for (; lhsItr != lhsEnd; ++lhsItr) {
        if (lhsItr->second >= 0.0) {
            candidateAV->weights.push_back(lhsItr->second);
            candidateAV->fluents.push_back(lhsItr->first);
        } else {
            candidateAV->weights.push_back(-lhsItr->second);
            candidateAV->fluents.push_back(lhsItr->first + pneCount);
        }
    }

    avResult = commonData.insertAV(candidateAV);

    candidate->LHSVariable = avResult.first->ID;

    preResult = commonData.insertPre(candidate);

    return true;

};

void RPGBuilder::handleNumericInvariants()
{

    InvData commonData(rpgArtificialVariables, rpgNumericPreconditions);


    static const int pneCount = pnes.size();
    const int opCount = instantiatedOps.size();
    const int rpgNumPrecCount = rpgNumericPreconditionsToActions.size();

    processedRPGNumericPreconditionsToActions = vector<list<pair<int, Planner::time_spec> > >(rpgNumPrecCount);

    {

        for (int i = 0; i < rpgNumPrecCount; ++i) {
            list<pair<int, Planner::time_spec> > & copyTo = processedRPGNumericPreconditionsToActions[i] = rpgNumericPreconditionsToActions[i];

            list<pair<int, Planner::time_spec> >::iterator ctItr = copyTo.begin();
            const list<pair<int, Planner::time_spec> >::iterator ctEnd = copyTo.end();

            while (ctItr != ctEnd) {
                if (ctItr->second == Planner::E_OVER_ALL) {
                    list<pair<int, Planner::time_spec> >::iterator ctPrev = ctItr;
                    ++ctItr;
                    copyTo.erase(ctPrev);
                } else {
                    ++ctItr;
                }
            }
        }
    }

//  actionsToProcessedStartNumericPreconditions = vector<list<NumericPrecondition> >(opCount);
    actionsToProcessedStartRPGNumericPreconditions = vector<list<int> >(opCount);
    initialUnsatisfiedProcessedStartNumericPreconditions = vector<int>(opCount);

    map<int, list<int> > precToActionMap;

    for (int i = 0; i < opCount; ++i) {

        if (!rogueActions[i]) {

            list<pair<ArtificialVariable*, bool> > localAVs;
            list<pair<const RPGNumericPrecondition*, bool> > localPres;

            list<int> & addToTwo = actionsToProcessedStartRPGNumericPreconditions[i] = actionsToRPGNumericStartPreconditions[i];

            //cout << "Before handing action " << i << " had " << addToTwo.size() << " numeric start pres\n";

            set<int> alreadyAtStart;
            alreadyAtStart.insert(actionsToRPGNumericStartPreconditions[i].begin(), actionsToRPGNumericStartPreconditions[i].end());


            bool eliminate = false;
            {


                list<int>::iterator liItr = actionsToRPGNumericInvariants[i].begin();
                const list<int>::iterator liEnd = actionsToRPGNumericInvariants[i].end();

                for (bool first=true; liItr != liEnd; ++liItr,first=false) {

                    if (Globals::globalVerbosity & 16 && first) {
                        cout << "Invariants of " << *(RPGBuilder::getInstantiatedOp(i)) << endl;
                    }
                    const RPGNumericPrecondition & invPre = rpgNumericPreconditions[*liItr];

                    pair<const RPGNumericPrecondition*, bool> preResult(0, false);
                    pair<ArtificialVariable*, bool> avResult(0, false);

                    const bool feasible = pushInvariantBackThroughStartEffects(invPre, actionsToRPGNumericStartEffects[i], linearDiscretisation[i], commonData, preResult, avResult);

                    if (!feasible) {
                        eliminate = true;
                        break;
                    }

                    if (avResult.first) localAVs.push_back(avResult);
                    if (preResult.first && alreadyAtStart.find(preResult.first->ID) == alreadyAtStart.end()) {
                        if (Globals::globalVerbosity & 16) {
                            cout << "Extra start precondition: " << *(preResult.first) << endl;
                        }
                        localPres.push_back(preResult);
                    }

                }

            }

            if (eliminate) {

                list<pair<ArtificialVariable*, bool> >::reverse_iterator avItr = localAVs.rbegin();
                const list<pair<ArtificialVariable*, bool> >::reverse_iterator avEnd = localAVs.rend();

                for (; avItr != avEnd; ++avItr) {
                    if (avItr->second) {
                        commonData.erase(avItr->first);
                    }
                }

                list<pair<const RPGNumericPrecondition*, bool> >::reverse_iterator preItr = localPres.rbegin();
                const list<pair<const RPGNumericPrecondition*, bool> >::reverse_iterator preEnd = localPres.rend();

                for (; preItr != preEnd; ++preItr) {
                    if (preItr->second) {
                        commonData.erase(preItr->first);
                    }
                }

                pruneIrrelevant(i);

            } else {

                list<pair<const RPGNumericPrecondition*, bool> >::iterator preItr = localPres.begin();
                const list<pair<const RPGNumericPrecondition*, bool> >::iterator preEnd = localPres.end();

                for (; preItr != preEnd; ++preItr) {
                    addToTwo.push_back(preItr->first->ID);
                    static const list<int> emptyList;
                    precToActionMap.insert(make_pair(preItr->first->ID, emptyList)).first->second.push_back(i);
                }

                initialUnsatisfiedProcessedStartNumericPreconditions[i] = addToTwo.size();

            }

        }

    }

    if (commonData.anyNewAVs()) {
        const int newAVLimit = rpgArtificialVariables.size() + commonData.anyNewAVs();
        rpgArtificialVariables.resize(newAVLimit);
        rpgArtificialVariablesToPreconditions.resize(newAVLimit);

        list<ArtificialVariable*>::iterator avItr = commonData.newAVs.begin();
        const list<ArtificialVariable*>::iterator avEnd = commonData.newAVs.end();

        for (; avItr != avEnd; ++avItr) {
            ArtificialVariable & currAV = rpgArtificialVariables[(*avItr)->ID - (2 * pneCount)] = *(*avItr);

            const int afflim = currAV.size;
            for (int aff = 0; aff < afflim; ++aff) {
                const int affVar = currAV.fluents[aff];
                if (affVar >= 0) rpgVariableDependencies[affVar].push_back(currAV.ID);
            }
        }
    }

    if (commonData.anyNewPres()) {
        const int newPreLimit = rpgNumericPreconditions.size() + commonData.anyNewPres();
        rpgNumericPreconditions.resize(newPreLimit);
        processedRPGNumericPreconditionsToActions.resize(newPreLimit);
        rpgNumericPreconditionsToActions.resize(newPreLimit);
        
        numericAchievedInLayer.resize(newPreLimit, EpsilonResolutionTimestamp::undefined());
        numericAchievedInLayerReset.resize(newPreLimit, EpsilonResolutionTimestamp::undefined());
//      negativeNumericAchievedInLayer.resize(newPreLimit);
//      negativeNumericAchievedInLayerReset.resize(newPreLimit);

        numericAchievedBy.resize(newPreLimit);
        numericAchievedByReset.resize(newPreLimit);
//      negativeNumericAchievedBy.resize(newPreLimit);
//      negativeNumericAchievedByReset.resize(newPreLimit);


        //cout << "Now have " << newPreLimit << " numeric pres\n";

        list<RPGNumericPrecondition*>::iterator preItr = commonData.newPres.begin();
        const list<RPGNumericPrecondition*>::iterator preEnd = commonData.newPres.end();

        for (; preItr != preEnd; ++preItr) {
            RPGNumericPrecondition & currPre = rpgNumericPreconditions[(*preItr)->ID] = *(*preItr);
            
            if (currPre.LHSVariable < pneCount) {
                rpgPositiveVariablesToPreconditions[currPre.LHSVariable].push_back(currPre.ID);
                assert(currPre.ID < newPreLimit);
            } else if (currPre.LHSVariable < 2 * pneCount) {
                rpgNegativeVariablesToPreconditions[currPre.LHSVariable - pneCount].push_back(currPre.ID);
                assert(currPre.ID < newPreLimit);
            } else {
                rpgArtificialVariablesToPreconditions[currPre.LHSVariable - 2 * pneCount].push_back(currPre.ID);
                assert(currPre.ID < newPreLimit);
            }

            numericAchievedInLayerReset[currPre.ID] = EpsilonResolutionTimestamp::undefined();
        }

        assert(rpgNumericPreconditions.size() == numericAchievedByReset.size()); /// EH?
    }

    map<int, list<int> >::iterator ptaItr = precToActionMap.begin();
    const map<int, list<int> >::iterator ptaEnd = precToActionMap.end();

    for (; ptaItr != ptaEnd; ++ptaItr) {
        list<pair<int, Planner::time_spec> > & destList = processedRPGNumericPreconditionsToActions[ptaItr->first];

        list<int>::iterator actItr = ptaItr->second.begin();
        const list<int>::iterator actEnd = ptaItr->second.end();

        for (; actItr != actEnd; ++actItr) {
            destList.push_back(make_pair(*actItr, Planner::E_AT_START));
        }
    }

    assert(rpgNumericPreconditions.size() == numericAchievedInLayerReset.size());

#ifndef NDEBUG

    for (int i = 0; i < opCount; ++i) {
        if (!rogueActions[i]) {
            assert(actionsToProcessedStartRPGNumericPreconditions[i].size() == ((unsigned int) initialUnsatisfiedProcessedStartNumericPreconditions[i]));
        }
    }

#endif

//  initialisedNumericPreTable = true;

}
void RPGBuilder::makeOneSided(pair<list<double>, list<int> > & LHSvariable, pair<list<double>, list<int> > & RHSvariable, const int & negOffset)
{
    //pushes variables to the LHS and constants to the RHS
    //result is an expression of the form (w.x [>,>=,<,<=,==] c )

    {
        list<double>::iterator dlItr = LHSvariable.first.begin();
        list<int>::iterator ilItr = LHSvariable.second.begin();
        const list<double>::iterator dlEnd = LHSvariable.first.end();

        while (dlItr != dlEnd) {
            if (*dlItr < 0.0) { // for negative weights
                if (*ilItr == -1) { // push constants to RHS
                    RHSvariable.first.push_back(0.0 - *dlItr);
                    RHSvariable.second.push_back(-1);
                    simplify(RHSvariable);
                    list<double>::iterator dlErr = dlItr;
                    list<int>::iterator ilErr = ilItr;
                    ++dlItr;
                    ++ilItr;
                    LHSvariable.first.erase(dlErr);
                    LHSvariable.second.erase(ilErr);
                } else { // keep vars here, but refer to negative instances and flip sign on weight
                    if (*ilItr >= 0) {
                        *ilItr += negOffset;
                    } else {
                        *ilItr -= 16;                        
                    }
                    
                    *dlItr = 0.0 - *dlItr;
                    ++dlItr;
                    ++ilItr;
                }
            } else { // positive weights are fine
                ++dlItr;
                ++ilItr;
            }
        }
    }


    { // finally, push constants to right, variables to left (sec 5.1, col 2)

        list<double>::iterator dlItr = RHSvariable.first.begin();
        list<int>::iterator ilItr = RHSvariable.second.begin();
        const list<double>::iterator dlEnd = RHSvariable.first.end();

        while (dlItr != dlEnd) {
            if (*ilItr == -1) {
                // leave it alone - it's a constant term :)
                ++dlItr;
                ++ilItr;
            } else {
                if (*dlItr > 0.0) {
                    LHSvariable.first.push_back(*dlItr);
                    if (*ilItr >= 0) {
                        LHSvariable.second.push_back(*ilItr + negOffset);
                    } else {
                        LHSvariable.second.push_back(*ilItr - 16);
                    }

                } else if (*dlItr == 0.0) {
                    // a null weight is a very silly thing

                } else {
                    LHSvariable.first.push_back(0.0 - *dlItr);
                    LHSvariable.second.push_back(*ilItr);
                }

                list<double>::iterator dlErr = dlItr;
                list<int>::iterator ilErr = ilItr;
                ++dlItr;
                ++ilItr;
                RHSvariable.first.erase(dlErr);
                RHSvariable.second.erase(ilErr);

            }
        }

        simplify(RHSvariable); // why not!
        simplify(LHSvariable); // why not!

    }

}

#ifdef STOCHASTICDURATIONS
void printStackTerm(list<double> & first, list<pair<int,PNE*> > & second)
{
    static const int pneCount = RPGBuilder::getPNECount();
    
    list<double>::iterator ldItr = first.begin();
    list<double>::iterator ldEnd = first.end();

    if (ldItr == ldEnd) {
        cout << "0.0";
        return;
    }
    
    list<pair<int,PNE*> >::iterator liItr = second.begin();

    for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
        if (term) cout << " + ";
        if (!liItr->second && liItr->first == -1) {
            cout << *ldItr;
        } else {
            if (*ldItr != 1.0) cout << *ldItr << "*";
            if (liItr->second) {
                cout << *(liItr->second);
            } else {
                if (liItr->first >= 0) {
                    if (liItr->first >= pneCount) {                    
                        cout << "-" << *(RPGBuilder::getPNE(liItr->first - pneCount));
                    } else {
                        cout << *(RPGBuilder::getPNE(liItr->first));
                    }
                } else {
                    if (liItr->first == -3) {
                        cout << "?duration";
                    } else if (liItr->first == -2) {
                        cout << "#t";
                    } else if (liItr->first == -19) {
                        cout << "-?duration";
                    } else if (liItr->first == -18) {
                        cout << "-#t";
                    } else if (*liItr == -512) {
                        cout << "trueprefs";
                    } else if (*liItr == -513) {
                        cout << "falseprefs";
                    } else if (*liItr == -528) {
                        cout << "-trueprefs";
                    } else if (*liItr == -529) {
                        cout << "-falseprefs";
                    } else if (*liItr <= -1048576) {
                        cout << "-(is-violated " << RPGBuilder::getPreferences()[-1048576 - *liItr].name << ")";
                    } else if (*liItr <= -1024) {
                        cout << "(is-violated " << RPGBuilder::getPreferences()[-1024 - *liItr].name << ")";
                    } else {
                        cerr << "Unexpected variable value: " << *liItr << std::endl;
                        exit(1);
                    }
                }
            }
        }
    }
}
#endif

void printStackTerm(list<double> & first, list<int> & second)
{
    static const int pneCount = RPGBuilder::getPNECount();
    
    list<double>::iterator ldItr = first.begin();
    list<double>::iterator ldEnd = first.end();

    if (ldItr == ldEnd) {
        cout << "0.0";
        return;
    }
    
    list<int>::iterator liItr = second.begin();

    for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
        if (term) cout << " + ";
        if (*liItr == -1) {
            cout << *ldItr;
        } else {
            if (*ldItr != 1.0) cout << *ldItr << "*";
            if (*liItr >= 0) {
                if (*liItr >= pneCount) {                    
                    cout << "-" << *(RPGBuilder::getPNE(*liItr - pneCount));
                } else {
                    cout << *(RPGBuilder::getPNE(*liItr));
                }
            } else {
                if (*liItr == -3) {
                    cout << "?duration";
                } else if (*liItr == -2) {
                    cout << "#t";
                } else if (*liItr == -19) {
                    cout << "-?duration";
                } else if (*liItr == -18) {
                    cout << "-#t";
                } else if (*liItr == -512) {
                    cout << "(is-violated never)";                    
                } else if (*liItr == -513) {
                    cout << "(is-violated always)";
                } else if (*liItr <= -1024) {
                    const int vtu = (*liItr <= -1048576 ? -1048576 - *liItr : -1024 - *liItr);
                    if (*liItr <= -1048576) {
                        cout << "-(is-violated " << RPGBuilder::getPreferences()[vtu].name << ")";
                    } else {
                        cout << "(is-violated " << RPGBuilder::getPreferences()[vtu].name << ")";
                    }
                } else {
                    cerr << "Unexpected variable ID " << *liItr << std::endl;
                    exit(1);
                }
            }
        }
    }
}

#ifdef STOCHASTICDURATIONS

void RPGBuilder::makeWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result)
{
    pair<list<double>, list<pair<int,PNE*> > > tmp;
    makeDurationWeightedSum(formula,tmp);
    
    list<double>::const_iterator wItr = tmp.first.begin();
    
    list<pair<int,PNE*> >::const_iterator tItr = tmp.second.begin();
    const list<pair<int,PNE*> >::const_iterator tEnd = tmp.second.end();
    
    for (; tItr != tEnd; ++tItr) {        
        if (tItr->second) {
            assert(EFT(tItr->second->getHead())->isStatic());
            result.first.push_back(*wItr * EFT(tItr->second->getHead())->getInitial(tItr->second->begin(), tItr->second->end()).second);
            result.second.push_back(-1);
        } else {
            result.first.push_back(*wItr);
            result.second.push_back(tItr->first);
        }
    }
    
    simplify(result);
}

typedef pair<list<double>, list<pair<int,PNE*> > > FormulaStackEntry;

pair<bool,double> entryIsConst(const FormulaStackEntry & e) {
    if (e.first.size() == 1 && !e.second.front().second && e.second.front().first == -1) {
        return make_pair(true, e.first.front());
    } else {
        return make_pair(false, std::numeric_limits< double >::signaling_NaN());
    }
}

const pair<int,PNE*> constFsEntry(-1,0);

void RPGBuilder::makeDurationWeightedSum(list<Operand> & formula, pair<list<double>, list<pair<int,PNE*> > > & result)
#else

void RPGBuilder::makeWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result)
{
    makeDurationWeightedSum(formula,result);
}

typedef pair<list<double>, list<int> > FormulaStackEntry;

pair<bool,double> entryIsConst(const FormulaStackEntry & e) {
    if (e.first.size() == 1 && e.second.front() == -1) {
        return make_pair(true, e.first.front());  
    } else {
        return make_pair(false, std::numeric_limits< double >::signaling_NaN());
    }
}

const int constFsEntry = -1;

void RPGBuilder::makeDurationWeightedSum(list<Operand> & formula, pair<list<double>, list<int> > & result)
#endif
{

    const bool stackDebug = false;

    if (stackDebug) cout << "Making weighted sum\n";
    
    if (formula.empty()) {
        if (stackDebug) {
            cout << "\tEmpty formula - returning 0.0\n";
        }
        FormulaStackEntry toReturn;
        toReturn.first.push_front(0.0);
        toReturn.second.push_front(constFsEntry);
        result = toReturn;
        return;
    }
    
    list<FormulaStackEntry> formulaStack;

    list<Operand>::iterator opItr = formula.begin();
    const list<Operand>::iterator opEnd = formula.end();

    for (int st = 0; opItr != opEnd; ++opItr, ++st) {
        if (stackDebug) cout << "Stack term " << st << "\n";
        const Operand & currOperand = *opItr;
        const math_op currMathOp = currOperand.numericOp;
        switch (currMathOp) {
        case RPGBuilder::NE_ADD: {
            FormulaStackEntry oldFront = formulaStack.front();
            formulaStack.pop_front();
            if (stackDebug) {
                cout << "+ operation, two terms were previously:\n";
                {
                    cout << "\t";
                    printStackTerm(oldFront.first, oldFront.second);
                    cout << "\n";
                }
                {
                    cout << "\t";
                    printStackTerm(formulaStack.front().first, formulaStack.front().second);
                    cout << "\n";
                }
            }

            formulaStack.front().first.insert(formulaStack.front().first.begin(), oldFront.first.begin(), oldFront.first.end());
            formulaStack.front().second.insert(formulaStack.front().second.begin(), oldFront.second.begin(), oldFront.second.end());
            if (stackDebug) {
                cout << "Result:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";

            }
            simplify(formulaStack.front());
            if (stackDebug) {
                cout << "Simplified:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";

            }
        }
        break;
        case RPGBuilder::NE_SUBTRACT: {
            FormulaStackEntry oldFront = formulaStack.front();
            formulaStack.pop_front();
            if (stackDebug) {
                cout << "- operation, two terms were previously:\n";
                {
                    cout << "\t";
                    printStackTerm(oldFront.first, oldFront.second);
                    cout << "\n";
                }
                {
                    cout << "\t";
                    printStackTerm(formulaStack.front().first, formulaStack.front().second);
                    cout << "\n";
                }
            }

            list<double>::iterator negItr = oldFront.first.begin();
            const list<double>::iterator negEnd = oldFront.first.end();
            for (; negItr != negEnd; ++negItr) *negItr = -1.0 * (*negItr);
            formulaStack.front().first.insert(formulaStack.front().first.begin(), oldFront.first.begin(), oldFront.first.end());
            formulaStack.front().second.insert(formulaStack.front().second.begin(), oldFront.second.begin(), oldFront.second.end());
            if (stackDebug) {
                cout << "Result:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";

            }

            simplify(formulaStack.front());
            if (stackDebug) {
                cout << "Simplified:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";

            }

        }
        break;
        case RPGBuilder::NE_MULTIPLY: { // at least one of the terms has to be entirely conflict, otherwise we have var x * var y
            FormulaStackEntry oldFront = formulaStack.front();
            formulaStack.pop_front();
            FormulaStackEntry oldSecondFront = formulaStack.front();
            formulaStack.pop_front();

            if (stackDebug) {
                cout << "* operation, two terms were previously:\n";
                {
                    cout << "\t";
                    printStackTerm(oldFront.first, oldFront.second);
                    cout << "\n";
                }
                {
                    cout << "\t";
                    printStackTerm(oldSecondFront.first, oldSecondFront.second);
                    cout << "\n";
                }
            }
            
            const bool firstIsConst = entryIsConst(oldFront).first;
            const bool secondIsConst = entryIsConst(oldSecondFront).first;

            if (firstIsConst && secondIsConst) {
                formulaStack.push_front(FormulaStackEntry());
                formulaStack.front().second.push_back(constFsEntry);
                formulaStack.front().first.push_back(entryIsConst(oldFront).second * entryIsConst(oldSecondFront).second);
            } else if (firstIsConst && !secondIsConst) {
                const double constVal = entryIsConst(oldFront).second;
                if (constVal == 0.0) {
                    formulaStack.push_front(FormulaStackEntry());
                    formulaStack.front().second.push_back(constFsEntry);
                    formulaStack.front().first.push_back(0.0);
                } else {
                    list<double>::iterator negItr = oldSecondFront.first.begin();
                    const list<double>::iterator negEnd = oldSecondFront.first.end();
                    for (; negItr != negEnd; ++negItr) {
                        *negItr = constVal * (*negItr);
                    }
                    formulaStack.push_front(oldSecondFront);
                }
            } else if (!firstIsConst && secondIsConst) {
                const double constVal = entryIsConst(oldSecondFront).second;
                if (constVal == 0.0) {
                    formulaStack.push_front(FormulaStackEntry());
                    formulaStack.front().second.push_back(constFsEntry);
                    formulaStack.front().first.push_back(0.0);
                } else {
                    list<double>::iterator negItr = oldFront.first.begin();
                    const list<double>::iterator negEnd = oldFront.first.end();
                    for (; negItr != negEnd; ++negItr) {
                        *negItr = constVal * (*negItr);
                    }
                    formulaStack.push_front(oldFront);
                }
            } else {
                string theOp;

                {
                    #ifdef STOCHASTICDURATIONS
                    theOp = "Non-linear expression";
                    #else
                    ostringstream o;
                    o << "(";
                    {
                        list<double>::iterator ldItr = oldFront.first.begin();
                        list<double>::iterator ldEnd = oldFront.first.end();

                        list<int>::iterator liItr = oldFront.second.begin();

                        for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
                            if (term) o << " + ";
                            if (*liItr == -1) {
                                o << *ldItr;
                            } else {
                                if (*ldItr != 1.0) o << *ldItr << "*";
                                if (*liItr >= 0) {
                                    o << *(RPGBuilder::getPNE(*liItr));
                                } else {
                                    if (*liItr == -3) {
                                        o << "?duration";
                                    } else if (*liItr == -2) {
                                        o << "#t";
                                    } else if (*liItr == -19) {
                                        o << "-?duration";
                                    } else if (*liItr == -18) {
                                        o << "-#t";
                                    }
                                }
                            }
                        }
                        o << ") * (";
                    }
                    {
                        list<double>::iterator ldItr = oldSecondFront.first.begin();
                        list<double>::iterator ldEnd = oldSecondFront.first.end();

                        list<int>::iterator liItr = oldSecondFront.second.begin();

                        for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
                            if (term) o << " + ";
                            if (*liItr == -1) {
                                o << *ldItr;
                            } else {
                                if (*ldItr != 1.0) o << *ldItr << "*";
                                if (*liItr >= 0) {
                                    o << *(RPGBuilder::getPNE(*liItr));
                                } else {
                                    if (*liItr == -3) {
                                        o << "?duration";
                                    } else if (*liItr == -2) {
                                        o << "#t";
                                    } else if (*liItr == -19) {
                                        o << "-?duration";
                                    } else if (*liItr == -18) {
                                        o << "-#t";
                                    }
                                }
                            }
                        }
                        o << ")";
                    }
                    theOp = o.str();
                    #endif
                    
                }
                postmortem_noQuadratic(theOp);
            }

            if (stackDebug) {
                cout << "Result:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";

            }
        }
        break;
        case RPGBuilder::NE_DIVIDE: {
            FormulaStackEntry oldFront = formulaStack.front();
            formulaStack.pop_front();
            const bool firstIsConst = entryIsConst(oldFront).first;
            if (!firstIsConst) {
                string theOp;

                {
                    #ifdef STOCHASTICDURATIONS
                    theOp = "Non-linear expression";
                    #else
                    ostringstream o;
                    o << "(";
                    {
                        list<double>::iterator ldItr = formulaStack.front().first.begin();
                        list<double>::iterator ldEnd = formulaStack.front().first.end();

                        list<int>::iterator liItr = formulaStack.front().second.begin();

                        for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
                            if (term) o << " + ";
                            if (*liItr == -1) {
                                o << *ldItr;
                            } else {
                                if (*ldItr != 1.0) o << *ldItr << "*";
                                if (*liItr >= 0) {
                                    o << *(RPGBuilder::getPNE(*liItr));
                                } else {
                                    if (*liItr == -3) {
                                        o << "?duration";
                                    } else if (*liItr == -2) {
                                        o << "#t";
                                    } else if (*liItr == -19) {
                                        o << "-?duration";
                                    } else if (*liItr == -18) {
                                        o << "-#t";
                                    }
                                }
                            }
                        }
                        o << ") / (";
                    }
                    {
                        list<double>::iterator ldItr = oldFront.first.begin();
                        list<double>::iterator ldEnd = oldFront.first.end();

                        list<int>::iterator liItr = oldFront.second.begin();

                        for (int term = 0; ldItr != ldEnd; ++ldItr, ++liItr, ++term) {
                            if (term) o << " + ";
                            if (*liItr == -1) {
                                o << *ldItr;
                            } else {
                                if (*ldItr != 1.0) o << *ldItr << "*";
                                if (*liItr >= 0) {
                                    o << *(RPGBuilder::getPNE(*liItr));
                                } else {
                                    if (*liItr == -3) {
                                        o << "?duration";
                                    } else if (*liItr == -2) {
                                        o << "#t";
                                    } else if (*liItr == -19) {
                                        o << "-?duration";
                                    } else if (*liItr == -18) {
                                        o << "-#t";
                                    }
                                }
                            }
                        }
                        o << ")";
                    }

                    theOp = o.str();
                    #endif
                }
                postmortem_noQuadratic(theOp);
            }

            const double constVal = entryIsConst(oldFront).second;
            if (stackDebug) {
                cout << "/ operation, two terms were previously:\n";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << " / constant value " << constVal << "\n";
            }
            if (constVal == 0) {
                postmortem_mathsError("division by zero error", "", WhereAreWeNow);
            }
            list<double>::iterator negItr = formulaStack.front().first.begin();
            const list<double>::iterator negEnd = formulaStack.front().first.end();
            for (; negItr != negEnd; ++negItr) {
                *negItr = (*negItr) / constVal;
            }
        }
        break;
        case RPGBuilder::NE_CONSTANT: {
            if (stackDebug) {
                cout << "Constant term - " << (currOperand.constantValue) << "\n";
            }

            formulaStack.push_front(FormulaStackEntry());
            formulaStack.front().first.push_front(currOperand.constantValue);
            formulaStack.front().second.push_front(constFsEntry);
        }
        break;
        case RPGBuilder::NE_FLUENT: {
            formulaStack.push_front(FormulaStackEntry());
            formulaStack.front().first.push_front(1.0);
            #ifdef STOCHASTICDURATIONS
            formulaStack.front().second.push_front(make_pair(currOperand.fluentValue, (PNE*)0));
            #else
            if (stackDebug) {
                cout << "Fluent " << currOperand.fluentValue << "\n";
            }

            formulaStack.front().second.push_front(currOperand.fluentValue);
            #endif
            break;
        }        
        #ifdef STOCHASTICDURATIONS
        case RPGBuilder::NE_STOCHASTIC_DURATION_TERM: {
            if (stackDebug) {
                cout << "Stochastic duration term - " << *(currOperand.durationVar) << "\n";
            }
            formulaStack.push_front(FormulaStackEntry());
            formulaStack.front().first.push_front(1.0);
            formulaStack.front().second.push_front(make_pair(-1, currOperand.durationVar));
            break;
        }            
        #endif
        case RPGBuilder::NE_VIOLATION: {

            map<string,list<int> >::iterator vID = prefNameToID.find(currOperand.isviolated);
            if (vID == prefNameToID.end()) {
                postmortem_isViolatedNotExist(currOperand.isviolated);
            }
            
            
            formulaStack.push_front(FormulaStackEntry());
            
            if (stackDebug) {
                cout << "Preferences with name " << currOperand.isviolated << ": " << vID->second.size() << endl;
            }
                           
            list<int>::const_iterator vidItr = vID->second.begin();
            const list<int>::const_iterator vidEnd = vID->second.end();
            
            for (; vidItr != vidEnd; ++vidItr) {
                if (stackDebug) {
                    cout << "\t" << *vidItr;
                }
                if (*vidItr == -513 || *vidItr == -512) {
                    formulaStack.front().first.push_front(1.0);
                    formulaStack.front().second.push_front(*vidItr);
                } else if (*vidItr != -1) {                   
                    formulaStack.front().first.push_front(1.0);
                    #ifdef STOCHASTICDURATIONS
                    formulaStack.front().second.push_front(make_pair(-1024 - *vidItr, (PNE*)0));
                    #else   
                    formulaStack.front().second.push_front(-1024 - *vidItr);
                    #endif
                } else {
                    formulaStack.front().first.push_front(0.0);
                    formulaStack.front().second.push_front(constFsEntry);
                }
            }                
            simplify(formulaStack.front());
            if (stackDebug) {
                cout << endl << "Result:\n\t";
                printStackTerm(formulaStack.front().first, formulaStack.front().second);
                cout << "\n";
                
            }
            break;
            
        }
        default:
            // this should never happen
            assert(false);
        }

    }

    result = formulaStack.front();

}

bool RPGBuilder::processPrecondition(RPGBuilder::BuildingNumericPreconditionData & commonData,
                                     RPGBuilder::NumericPrecondition & currPre,
                                     list<int> & conjunctiveList,
                                     list<int> & disjunctiveList,                                     
                                     const int & i, const Planner::time_spec & passTimeSpec)
{



    const bool debugRPGNum = (Globals::globalVerbosity & 16);

    if (debugRPGNum) {
        if (currPre.polarity) {
            cout << "Converting " << currPre << "\n";
        } else {
            cout << "Converting ¬" << currPre << "\n";
        }
    }

        

    pair<list<double>, list<int> > LHSvariable;
    pair<list<double>, list<int> > RHSvariable;

    makeWeightedSum(currPre.LHSformula, LHSvariable);

    if (debugRPGNum) {
        cout << "LHS is:\n\t";
        printStackTerm(LHSvariable.first, LHSvariable.second);
        cout << "\n";
    }

    makeWeightedSum(currPre.RHSformula, RHSvariable);


    if (debugRPGNum) {
        cout << "RHS is:\n\t";
        printStackTerm(RHSvariable.first, RHSvariable.second);
        cout << "\n";
    }



    list<pair<list<double>, list<int> > > finalLHS;
    list<VAL::comparison_op> finalOp;
    list<pair<list<double>, list<int> > > finalRHS;


    list<int> * destList = &conjunctiveList;
    
    if (currPre.polarity) {
        switch (currPre.op) {
            case VAL::E_GREATER: {
                makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);
                finalLHS.push_back(LHSvariable);
                finalOp.push_back(VAL::E_GREATER);
                finalRHS.push_back(RHSvariable);
            }
            break;
            case VAL::E_GREATEQ: {
                makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);
                finalLHS.push_back(LHSvariable);
                finalOp.push_back(VAL::E_GREATEQ);
                finalRHS.push_back(RHSvariable);
            }
            break;
            case VAL::E_LESS: {
                makeOneSided(RHSvariable, LHSvariable, commonData.negOffset);
                finalLHS.push_back(RHSvariable);
                finalOp.push_back(VAL::E_GREATER);
                finalRHS.push_back(LHSvariable);
            }
            break;
            case VAL::E_LESSEQ: {
                makeOneSided(RHSvariable, LHSvariable, commonData.negOffset);
                finalLHS.push_back(RHSvariable);
                finalOp.push_back(VAL::E_GREATEQ);
                finalRHS.push_back(LHSvariable);
            }
            break;
            case VAL::E_EQUALS: {
                pair<list<double>, list<int> > secondLHS(RHSvariable);
                pair<list<double>, list<int> > secondRHS(LHSvariable);

                makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);

                finalLHS.push_back(LHSvariable);
                finalOp.push_back(VAL::E_GREATEQ);
                finalRHS.push_back(RHSvariable);

                makeOneSided(secondLHS, secondRHS, commonData.negOffset);

                finalLHS.push_back(secondLHS);
                finalOp.push_back(VAL::E_GREATEQ);
                finalRHS.push_back(secondRHS);
            }
            break;
        }
    } else {
        switch (currPre.op) {
        case VAL::E_GREATER: {
            makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);
            finalLHS.push_back(LHSvariable);
            finalOp.push_back(VAL::E_LESSEQ);
            finalRHS.push_back(RHSvariable);
        }
        break;
        case VAL::E_GREATEQ: {
            makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);
            finalLHS.push_back(LHSvariable);
            finalOp.push_back(VAL::E_LESS);
            finalRHS.push_back(RHSvariable);
        }
        break;
        case VAL::E_LESS: {
            makeOneSided(RHSvariable, LHSvariable, commonData.negOffset);
            finalLHS.push_back(RHSvariable);
            finalOp.push_back(VAL::E_GREATEQ);
            finalRHS.push_back(LHSvariable);
        }
        break;
        case VAL::E_LESSEQ: {
            makeOneSided(RHSvariable, LHSvariable, commonData.negOffset);
            finalLHS.push_back(RHSvariable);
            finalOp.push_back(VAL::E_GREATER);
            finalRHS.push_back(LHSvariable);
        }
        break;
        case VAL::E_EQUALS: {
            pair<list<double>, list<int> > secondLHS(RHSvariable);
            pair<list<double>, list<int> > secondRHS(LHSvariable);
            
            makeOneSided(LHSvariable, RHSvariable, commonData.negOffset);
            
            finalLHS.push_back(LHSvariable);
            finalOp.push_back(VAL::E_GREATER);
            finalRHS.push_back(RHSvariable);
            
            makeOneSided(secondLHS, secondRHS, commonData.negOffset);
            
            finalLHS.push_back(secondLHS);
            finalOp.push_back(VAL::E_LESS);
            finalRHS.push_back(secondRHS);
            
            destList = &disjunctiveList;
        }
        break;
        }
    }

    {
        list<pair<list<double>, list<int> > >::iterator lhsItr = finalLHS.begin();
        const list<pair<list<double>, list<int> > >::iterator lhsEnd = finalLHS.end();
        list<VAL::comparison_op>::iterator opItr = finalOp.begin();
        list<pair<list<double>, list<int> > >::iterator rhsItr = finalRHS.begin();

        for (; lhsItr != lhsEnd; ++lhsItr, ++opItr, ++rhsItr) {
            if (debugRPGNum) {
                cout << "Storing built precondition\n";
                {
                    cout << "\t";
                    printStackTerm(lhsItr->first, lhsItr->second);
                    
                }
                if (*opItr == VAL::E_GREATER) {
                    cout << " > ";
                } else {
                    cout << " >= ";
                }
                {
                    printStackTerm(rhsItr->first, rhsItr->second);                        
                }
                cout << "\n";
            }
            
            pair<list<double>, list<int> > & currLHS = *lhsItr;
            pair<list<double>, list<int> > & currRHS = *rhsItr;
            VAL::comparison_op currOp = *opItr;

            int lVar = -1;
            double lConst = 0.0;
            bool lIsConst = false;

            double rConst = 0.0;
            bool rIsConst = false;

            {
                int rSize = currRHS.first.size();
                if (rSize == 1) {
                    if (currRHS.second.front() == -1) {
                        rIsConst = true;
                        rConst = currRHS.first.front();
                    }
                } else if (!rSize) {
                    rIsConst = true;
                }
            }

            assert(rIsConst);

            {
                int lSize = currLHS.first.size();
                if (lSize == 1) {
                    if (currLHS.second.front() == -1) {
                        lIsConst = true;
                        lConst = currLHS.first.front();
                    }
                } else if (!lSize) {
                    lIsConst = true;
                }
            }



            if (!lIsConst) {


                int lSize = currLHS.first.size();
                if (lSize > 1) {
                    int a = 0;
                    double constTerm = 0.0;

                    vector<double> wVector(lSize);
                    vector<int> vVector(lSize);

                    list<double>::iterator wItr = currLHS.first.begin();
                    const list<double>::iterator wEnd = currLHS.first.end();
                    list<int>::iterator vItr = currLHS.second.begin();

                    for (; wItr != wEnd; ++wItr, ++vItr) {
                        if (*vItr == -1) {
                            constTerm = *wItr;
                        } else {
                            wVector[a] = *wItr;
                            vVector[a] = *vItr;
                            ++a;
                        }
                    }
                    ArtificialVariable newAV(commonData.avCount, a, wVector, vVector, constTerm, rConst, false, false);
                    pair<set<ArtificialVariable>::iterator, bool> insResult = commonData.artificialVariableSet.insert(newAV);
                    if (insResult.second) {
                        ++commonData.avCount;
                    } else {
                        if (debugRPGNum) {
                            cout << "Existing AV: " << *(insResult.first) << "\n";
                        }
                        (const_cast<ArtificialVariable*>(&(*insResult.first)))->updateMax(rConst);
                    }
                    lVar = insResult.first->ID;
                    if (debugRPGNum) {
                        cout << "LHS = artificial variable " << lVar << "\n";
                    }
                } else if (lSize) {
                    const int vCheck = currLHS.second.front();
                    if (vCheck == -1) {
                        assert(false);  // see above
                        lConst = currLHS.first.front();
                        if (debugRPGNum) {
                            cout << "LHS = constant " << lConst << "\n";
                        }
                    } else {
                        lVar = vCheck;
                        lConst = currLHS.first.front();
                        if (debugRPGNum) {
                            cout << "LHS =";
                            if (lConst != 1.0) cout << " " << lConst << " *";
                            cout << " variable " << lVar << "\n";
                        }
                        assert(lConst > 0.0); // would be insane otherwise - the negative variables thing should have kicked in, and having 0*var as a function is just plain silly
                        const double newMaxNeed = rConst / lConst;
                        if (lVar >= 0) {
                            if (newMaxNeed > commonData.localMaxNeed[lVar]) commonData.localMaxNeed[lVar] = newMaxNeed;
                        }
                    }
                } else {
                    assert(false);  // see above
                    if (debugRPGNum) {
                        cout << "LHS is empty\n";
                    }
                    lConst = 0.0;
                    // do nothing - side is empty, bizarrely enough
                }
            } else {
                if (currOp == VAL::E_GREATER) {
                    if (lConst <= rConst) {
                        return false;
                    }
                } else {
                    if (lConst < rConst) {
                        return false;
                    }
                } 
            }

            if (lIsConst) {
                if (debugRPGNum) {
                    cout << "Tautologous condition - not bothering to create it\n";
                }
            } else {
                RPGNumericPrecondition newPrec(commonData.precCount, false, false, lVar, lConst, currOp, rConst);
                map<RPGNumericPrecondition, list<pair<int, Planner::time_spec> > >::iterator insResult = commonData.rpgNumericPreconditionSet.find(newPrec);
                if (insResult == commonData.rpgNumericPreconditionSet.end()) {
                    if (debugRPGNum) {
                        cout << "New RPGNumericPrecondition created, ID = " << newPrec.ID << "\n";
                        cout << "lv = " << newPrec.LHSVariable << ", lc = " << newPrec.LHSConstant << ", rv = " << newPrec.RHSVariable << ", rc = " << newPrec.RHSConstant << "\n";

                    }
                    list<pair<int, Planner::time_spec> > tmpList;
                    if (i >= 0) {
                        tmpList.push_back(pair<int, Planner::time_spec>(i, passTimeSpec));
                    }
                    commonData.rpgNumericPreconditionSet.insert(pair<RPGNumericPrecondition, list<pair<int, Planner::time_spec> > >(newPrec, tmpList));
                    destList->push_back(commonData.precCount);
                    ++commonData.precCount;
                    if (debugRPGNum) {
                        cout << "Registered that precondition applies to action " << i << "\n";
                        cout << "Registered that action uses precondition " << destList->back() << "\n";
                        cout << "precCount now " << commonData.precCount << "\n";

                    }
                } else {

                    if (debugRPGNum) {
                        cout << "RPGNumericPrecondition reused, ID = " << insResult->first.ID << "\n";
                        cout << "lv = " << insResult->first.LHSVariable << ", lc = " << insResult->first.LHSConstant << ", rv = " << insResult->first.RHSVariable << ", rc = " << insResult->first.RHSConstant << "\n";

                    }
                    if (i >= 0) {
                        insResult->second.push_back(pair<int, Planner::time_spec>(i, passTimeSpec));
                    }
                    destList->push_back(insResult->first.ID);
                    if (debugRPGNum) {
                        cout << "Registered that precondition applies to action " << i << "\n";
                        cout << "Registered that action uses precondition " << destList->back() << "\n";


                    }
                }
            }
        }

    }

    if (destList == &disjunctiveList && destList->size() == 1) {
        conjunctiveList.push_back(disjunctiveList.back());
        disjunctiveList.pop_back();
    }
    
    return true;
}



bool RPGBuilder::processPreconditions(RPGBuilder::BuildingNumericPreconditionData & commonData,
                                      list<NumericPrecondition> & currPreList, list<int> & destList,
                                      int & toIncrement,
                                      const int & i, const Planner::time_spec & passTimeSpec)
{



    const bool debugRPGNum = (Globals::globalVerbosity & 16);

    toIncrement = 0;

    list<NumericPrecondition>::iterator cpItr = currPreList.begin();
    const list<NumericPrecondition>::iterator cpEnd = currPreList.end();

    for (; cpItr != cpEnd; ++cpItr) {
        
        list<int> conjunctiveList;
        list<int> disjunctiveList;
        
        if (!processPrecondition(commonData, *cpItr, conjunctiveList, disjunctiveList, i, passTimeSpec)) {
            return false;
        }
        
        if (!disjunctiveList.empty()) {
            postmortem_noADL();
        }
        
        destList.insert(destList.end(),conjunctiveList.begin(),conjunctiveList.end());
        toIncrement += conjunctiveList.size();
    }

    if (debugRPGNum) {
        cout << "Action has " << toIncrement << " numeric preconditions\n";
    }
    
    return true;
}

void RPGBuilder::markRPGNumericPreconditionDesirable(const int & i) {
    
    static const int avOffset = 2 * RPGBuilder::getPNECount();
    
    if (rpgNumericPreconditions[i].desirable) {
        return;
    }
    
    rpgNumericPreconditions[i].desirable = true;
    
    if (rpgNumericPreconditions[i].LHSVariable >= avOffset) {
        rpgArtificialVariables[rpgNumericPreconditions[i].LHSVariable - avOffset].desirable = true;
    }
}

void RPGBuilder::markRPGNumericPreconditionUndesirable(const int & i) {
    
    static const int avOffset = 2 * RPGBuilder::getPNECount();
    
    if (rpgNumericPreconditions[i].undesirable) {
        return;
    }
    
    rpgNumericPreconditions[i].undesirable = true;
    
    if (rpgNumericPreconditions[i].LHSVariable >= avOffset) {
        rpgArtificialVariables[rpgNumericPreconditions[i].LHSVariable - avOffset].undesirable = true;
    }
}

void RPGBuilder::buildRPGNumericPreconditions()
{

    const bool debugRPGNum = (Globals::globalVerbosity & 16);

    BuildingNumericPreconditionData commonData;
    
    const int opCount = instantiatedOps.size();

    rpgVariableDependencies = vector<list<int> >(commonData.offset);

    actionsToRPGNumericStartPreconditions = vector<list<int> >(opCount);
    actionsToRPGNumericInvariants = vector<list<int> >(opCount);
    actionsToRPGNumericEndPreconditions = vector<list<int> >(opCount);

    initialUnsatisfiedNumericStartPreconditions = vector<int>(opCount);
    initialUnsatisfiedNumericInvariants = vector<int>(opCount);
    initialUnsatisfiedNumericEndPreconditions = vector<int>(opCount);

    for (int i = 0; i < opCount; ++i) {
 
        if (rogueActions[i]) {
            continue;
        }
        
        bool contradictoryPreconditions = false;
        
        for (int pass = 0; pass < 3; ++pass) {

            vector<list<NumericPrecondition> > * actionsToNumericPreconditions ;
            vector<list<int> > * actionsToRPGNumericPreconditions;
            vector<int> * initialUnsatisfiedNumericPreconditions;
            Planner::time_spec passTimeSpec;

            switch (pass) {

            case 0: {
                actionsToNumericPreconditions = &actionsToStartNumericPreconditions;
                actionsToRPGNumericPreconditions = &actionsToRPGNumericStartPreconditions;
                initialUnsatisfiedNumericPreconditions = &initialUnsatisfiedNumericStartPreconditions;
                passTimeSpec = Planner::E_AT_START;
                if (debugRPGNum) cout << "Building RPG Numeric Preconditions for start of " << *(instantiatedOps[i]) << "\n";
            }
            break;
            case 1: {
                actionsToNumericPreconditions = &actionsToNumericInvariants;
                actionsToRPGNumericPreconditions = &actionsToRPGNumericInvariants;
                initialUnsatisfiedNumericPreconditions = &initialUnsatisfiedNumericInvariants;
                passTimeSpec = Planner::E_OVER_ALL;
                if (debugRPGNum) cout << "Building RPG Numeric Preconditions for over all of " << *(instantiatedOps[i]) << "\n";
            }
            break;
            case 2: {
                actionsToNumericPreconditions = &actionsToEndNumericPreconditions;
                actionsToRPGNumericPreconditions = &actionsToRPGNumericEndPreconditions;
                initialUnsatisfiedNumericPreconditions = &initialUnsatisfiedNumericEndPreconditions;
                passTimeSpec = Planner::E_AT_END;
                if (debugRPGNum) cout << "Building RPG Numeric Preconditions for end of " << *(instantiatedOps[i]) << "\n";
            }
            break;
            default: {
                cout << "This should never happen\n";
                assert(false);
            }
            };

            

            if (!processPreconditions(commonData,
                                      (*actionsToNumericPreconditions)[i], (*actionsToRPGNumericPreconditions)[i],
                                      (*initialUnsatisfiedNumericPreconditions)[i], i, passTimeSpec)) {
                contradictoryPreconditions = true;
                break;
            }


        }

        if (!contradictoryPreconditions && !actionsToConditionalEffects[i].empty()) {
#ifndef NDEBUG
            const bool durative = (!fixedDurationExpressions[i].empty() || !maxDurationExpressions[i].empty() || !minDurationExpressions[i].empty());
#endif
            list<ProtoConditionalEffect*>::iterator ceItr = actionsToRawConditionalEffects[i].begin();
            const list<ProtoConditionalEffect*>::iterator ceEnd = actionsToRawConditionalEffects[i].end();
            list<ConditionalEffect>::iterator prcItr = actionsToConditionalEffects[i].begin();

            for (int ceID = 0; !contradictoryPreconditions && ceItr != ceEnd; ++ceItr, ++prcItr, ++ceID) {

                ProtoConditionalEffect * const currRaw = *ceItr;
                ConditionalEffect & currCE = *prcItr;

                for (int pass = 0; pass < 3; ++pass) {

                    list<NumericPrecondition> * actionsToNumericPreconditions;
                    int unsat = 0;
                    list<int> dest;
                    Planner::time_spec passTimeSpec;

                    switch (pass) {

                    case 0: {
                        actionsToNumericPreconditions = &(currRaw->startPrecNumeric);
                        passTimeSpec = Planner::E_AT_START;
                        break;
                    }
                    case 1: {
                        actionsToNumericPreconditions = &(currRaw->invNumeric);
                        passTimeSpec = Planner::E_OVER_ALL;                        
                        assert(durative || actionsToNumericPreconditions->empty());
                        break;
                    }
                    case 2: {
                        actionsToNumericPreconditions = &(currRaw->endPrecNumeric);
                        passTimeSpec = Planner::E_AT_END;
                        assert(durative || actionsToNumericPreconditions->empty());
                        break;
                    }
                    default: {
                        cout << "This should never happen\n";
                        assert(false);
                    }
                    }


                    if ((Globals::globalVerbosity & 32) &&  !actionsToNumericPreconditions->empty()) {
                        
                        cout << "Looking at " << actionsToNumericPreconditions->size() << " numeric conditions on conditional effect " << ceID << " of " << i << endl;
                    }

                    if (!processPreconditions(commonData, *actionsToNumericPreconditions, dest, unsat, -2, passTimeSpec)) {
                        if (Globals::globalVerbosity & 32) {
                            cout << "Contradictory preconditions on conditional effect " << ceID << " of " << i << endl;
                        }
                        contradictoryPreconditions = true;
                        break;
                    }

                    list<int>::iterator destItr = dest.begin();
                    const list<int>::iterator destEnd = dest.end();

                    for (; destItr != destEnd; ++destItr) {
                        currCE.addCondition(*destItr, passTimeSpec, i);
                        assert(durative || (passTimeSpec == Planner::E_AT_START));                        
                    }
                }
            }
        }
        
        if (contradictoryPreconditions) {
            pruneIrrelevant(i);
        }

    }


    { // now do the goals

        if (debugRPGNum) {
            cout << "Considering numeric goals\n";
        }

        list<NumericPrecondition>::iterator goalNumItr = numericGoals.begin();
        const list<NumericPrecondition>::iterator goalNumEnd = numericGoals.end();

        list<double>::const_iterator goalDeadItr = numericGoalDeadlines.begin();
        
        for (; goalNumItr != goalNumEnd; ++goalNumItr, ++goalDeadItr) {

            list<NumericPrecondition> justOne;
            justOne.push_back(*goalNumItr);

            int unsat = 0;
            list<int> dest;

            if (processPreconditions(commonData, justOne, dest, unsat, -1, Planner::E_AT)) {
                

                const int destSize = dest.size();

                if (destSize == 2) {
                    if (debugRPGNum) cout << "Evaluated to pair " << dest.front() << ", " << dest.back() << "\n";
                    numericRPGGoals.push_back(pair<int, int>(dest.front(), dest.back()));
                    rpgNumericGoalDeadlines.push_back(*goalDeadItr);
                } else if (destSize == 1) {
                    if (debugRPGNum) cout << "Evaluated to single goal " << dest.front() << "\n";
                    numericRPGGoals.push_back(pair<int, int>(dest.front(), -1));
                    rpgNumericGoalDeadlines.push_back(*goalDeadItr);
                }
                
            } else {
                cout << "Problem cannot be solved: a numeric goal " << *goalNumItr << " evaluates to false\n";
                exit(0);
            }
        }

    }

    PreferenceHandler::substituteRPGNumericPreconditions(commonData);

    assert((int) commonData.rpgNumericPreconditionSet.size() == commonData.precCount);

    rpgNumericPreconditions = vector<RPGNumericPrecondition>(commonData.precCount);
    rpgNumericPreconditionsToActions = vector<list<pair<int, Planner::time_spec> > >(commonData.precCount);

    rpgArtificialVariables = vector<ArtificialVariable>(commonData.avCount - commonData.offset);
    rpgArtificialVariablesToPreconditions = vector<list<int> >(commonData.avCount - commonData.offset);
    rpgNegativeVariablesToPreconditions = vector<list<int> >(commonData.negOffset);
    rpgPositiveVariablesToPreconditions = vector<list<int> >(commonData.negOffset);

    maxNeeded = vector<double>(commonData.avCount);

    for (int i = 0; i < commonData.offset; ++i) {
        maxNeeded[i] = commonData.localMaxNeed[i];
    }

    {
        set<ArtificialVariable>::iterator avsItr = commonData.artificialVariableSet.begin();
        const set<ArtificialVariable>::iterator avsEnd = commonData.artificialVariableSet.end();

        for (; avsItr != avsEnd; ++avsItr) {
            const int oIndex = avsItr->ID - commonData.offset;
            rpgArtificialVariables[oIndex] = *avsItr;
            maxNeeded[avsItr->ID] = avsItr->maxNeed;
            if (debugRPGNum) cout << "Storing AV with ID " << avsItr->ID << " at index " << oIndex << "\n";
            {
                const int afflim = avsItr->size;
                for (int aff = 0; aff < afflim; ++aff) {
                    const int affVar = avsItr->fluents[aff];
                    if (affVar >= 0) {
                        rpgVariableDependencies[affVar].push_back(avsItr->ID);
                    }
                }
            }
        }
    }

    {
        map<RPGNumericPrecondition, list<pair<int, Planner::time_spec> > >::iterator rnpItr = commonData.rpgNumericPreconditionSet.begin();
        const map<RPGNumericPrecondition, list<pair<int, Planner::time_spec> > >::iterator rnpEnd = commonData.rpgNumericPreconditionSet.end();

        for (; rnpItr != rnpEnd; ++rnpItr) {
            const RPGNumericPrecondition & currPrec = rnpItr->first;
            const int currID = currPrec.ID;
            rpgNumericPreconditions[currID] = currPrec;
            rpgNumericPreconditionsToActions[currID] = rnpItr->second;

            if (debugRPGNum) cout << "Precondition ID: " << currID << "\n";

            {
                const int var = currPrec.LHSVariable;
                if (var >= commonData.offset) {
                    rpgArtificialVariablesToPreconditions[var-commonData.offset].push_back(currID);
                } else if (var >= commonData.negOffset) {
                    rpgNegativeVariablesToPreconditions[var-commonData.negOffset].push_back(currID);
                } else if (var >= 0) {
                    rpgPositiveVariablesToPreconditions[var].push_back(currID);
                }
            }



            if (debugRPGNum) {
                cout << "Built precondition " << currPrec << "\n";
                cout << "Applies to actions:\n";
                list<pair<int, Planner::time_spec> >::iterator ataItr = rpgNumericPreconditionsToActions[currID].begin();
                const list<pair<int, Planner::time_spec> >::iterator ataEnd = rpgNumericPreconditionsToActions[currID].end();
                for (; ataItr != ataEnd; ++ataItr) {
                    cout << "\t" << ataItr->first << " " << *(instantiatedOps[ataItr->first]) << " " << (ataItr->second == Planner::E_AT_START ? "start" : (ataItr->second == Planner::E_AT_END ? "end" : "over all")) << "\n";
                }
            }
        }

    }

    {
    
        
        set<int>::const_iterator desItr = commonData.desirable.begin();
        const set<int>::const_iterator desEnd = commonData.desirable.end();
        
        for (; desItr != desEnd; ++desItr) {
            markRPGNumericPreconditionDesirable(*desItr);
        }                
    }

    {            
        set<int>::const_iterator desItr = commonData.undesirable.begin();
        const set<int>::const_iterator desEnd = commonData.undesirable.end();
        
        for (; desItr != desEnd; ++desItr) {
            markRPGNumericPreconditionUndesirable(*desItr);
        }                
    }

    numericAchievedInLayer = vector<EpsilonResolutionTimestamp>(commonData.precCount,EpsilonResolutionTimestamp::undefined());
    numericAchievedInLayerReset = vector<EpsilonResolutionTimestamp>(commonData.precCount,EpsilonResolutionTimestamp::undefined());
    numericAchievedBy = vector<ActionFluentModification*>(commonData.precCount,(ActionFluentModification*) 0);
    numericAchievedByReset = vector<ActionFluentModification*>(commonData.precCount,(ActionFluentModification*) 0);
    
    negativeNumericAchievedInLayer = vector<EpsilonResolutionTimestamp>(commonData.precCount,EpsilonResolutionTimestamp::undefined());
    negativeNumericAchievedInLayerReset = vector<EpsilonResolutionTimestamp>(commonData.precCount,EpsilonResolutionTimestamp::undefined());
    negativeNumericAchievedBy = vector<ActionFluentModification*>(commonData.precCount,(ActionFluentModification*) 0);
    negativeNumericAchievedByReset = vector<ActionFluentModification*>(commonData.precCount,(ActionFluentModification*) 0);
    
    
    if (debugRPGNum) {
        cout << "All done!\n";
    }

}

void RPGBuilder::buildRPGNumericEffects()
{

    const bool localDebug = (Globals::globalVerbosity & 16);

    const int opCount = instantiatedOps.size();

    const int negOffset = pnes.size();

    realVariablesToRPGEffects = vector<list<int> >(negOffset * 2);

    actionsToRPGNumericStartEffects = vector<list<int> >(opCount);
    actionsToRPGNumericEndEffects = vector<list<int> >(opCount);

    map<RPGNumericEffect, list<pair<int, Planner::time_spec> > > rpgNumericEffectSet;


    const list<pair<int, Planner::time_spec> > emptyList;

    int effID = 0;

    for (int act = 0; act < opCount; ++act) {

        if (rogueActions[act] == RPGBuilder::OT_INVALID_ACTION) {
            continue;
        }
        
        ostringstream actnameos;
        actnameos << *(RPGBuilder::getInstantiatedOp(act));
        
        linearDiscretisation[act] = buildLE(actionsToStartNumericEffects[act], actnameos.str());
                                        
        if (rogueActions[act] != RPGBuilder::OT_NORMAL_ACTION) {
            continue;
        }
        

        bool doingMainEffects = true;

        list<ProtoConditionalEffect*>::iterator ceItr = actionsToRawConditionalEffects[act].begin();
        const list<ProtoConditionalEffect*>::iterator ceEnd = actionsToRawConditionalEffects[act].end();
        list<ConditionalEffect>::iterator prcItr = actionsToConditionalEffects[act].begin();

        while (doingMainEffects || ceItr != ceEnd) {

            for (int pass = 0; pass < 2; ++pass) {

                list<NumericEffect> & numEffs = (doingMainEffects
                                                 ? (pass ? actionsToEndNumericEffects[act] : actionsToStartNumericEffects[act])
                                                 : (pass ? (*ceItr)->endNumericEff : (*ceItr)->startNumericEff));

                list<NumericEffect>::iterator neItr = numEffs.begin();
                const list<NumericEffect>::iterator neEnd = numEffs.end();

                for (; neItr != neEnd; ++neItr) {

                    if (localDebug) {
                        if (doingMainEffects) {
                            cout << "Action " << act << " has " << (pass ? "end" : "start") << " effect:\n";
                        } else {
                            cout << "Conditional effect of action " << act << " has " << (pass ? "end" : "start") << " effect:\n";
                        }
                    }

                    NumericEffect & currEffect = *neItr;

                    pair<list<double>, list<int> > weightedSum;

                    makeWeightedSum(currEffect.formula, weightedSum);

                    if (currEffect.op == VAL::E_DECREASE) {
                        list<double>::iterator dlItr = weightedSum.first.begin();
                        const list<double>::iterator dlEnd = weightedSum.first.end();

                        for (; dlItr != dlEnd; ++dlItr) {
                            if (*dlItr != 0.0) *dlItr = 0.0 - *dlItr;
                        }
                    }

                    {
                        list<double>::iterator dlItr = weightedSum.first.begin();
                        list<int>::iterator ilItr = weightedSum.second.begin();
                        const list<double>::iterator dlEnd = weightedSum.first.end();

                        for (; dlItr != dlEnd; ++dlItr, ++ilItr) {
                            if (*dlItr < 0.0) { // for negative weights
                                if (*ilItr == -3) {
                                    *dlItr = 0.0 - *dlItr;
                                    *ilItr = -19;
                                } else if (*ilItr == -19) {
                                    *dlItr = 0.0 - *dlItr;
                                    *ilItr = -3;
                                } else if (*ilItr == -2) {
                                    *dlItr = 0.0 - *dlItr;
                                    *ilItr = -18;
                                } else if (*ilItr == -18) {
                                    *dlItr = 0.0 - *dlItr;
                                    *ilItr = -2;
                                } else if (*ilItr >= 0) {
                                    *ilItr += negOffset;
                                    *dlItr = 0.0 - *dlItr;
                                }
                            }

                        }
                    }


                    int lSize = weightedSum.first.size();

                    double constTerm = 0.0;

                    int a = 0;

                    vector<double> wVector(lSize);
                    vector<int> vVector(lSize);

                    list<double>::iterator wItr = weightedSum.first.begin();
                    const list<double>::iterator wEnd = weightedSum.first.end();
                    list<int>::iterator vItr = weightedSum.second.begin();

                    for (; wItr != wEnd; ++wItr, ++vItr) {
                        if (*vItr == -1) {
                            constTerm = *wItr;
                        } else {
                            wVector[a] = *wItr;
                            vVector[a] = *vItr;
                            ++a;
                        }
                    }

                    RPGNumericEffect rpgEffect(effID, currEffect.fluentIndex, currEffect.op == VAL::E_ASSIGN, wVector, vVector, a, constTerm);

                    pair<map<RPGNumericEffect, list<pair<int, Planner::time_spec> > >::iterator, bool> insItr
                    = rpgNumericEffectSet.insert(pair<RPGNumericEffect, list<pair<int, Planner::time_spec> > >(rpgEffect, emptyList));

                    if (insItr.second) {
                        {
                            list<double>::iterator dlItr = weightedSum.first.begin();
                            list<int>::iterator ilItr = weightedSum.second.begin();
                            const list<double>::iterator dlEnd = weightedSum.first.end();

                            for (; dlItr != dlEnd; ++dlItr, ++ilItr) {
                                if (*ilItr >= 0) {
                                    realVariablesToRPGEffects[*ilItr].push_back(insItr.first->first.ID);
                                }

                            }
                        }
                        ++effID;
                    }

                    if (doingMainEffects) {
                        insItr.first->second.push_back(pair<int, Planner::time_spec>(act, (pass ? Planner::E_AT_END : Planner::E_AT_START)));
                        (pass ? actionsToRPGNumericEndEffects : actionsToRPGNumericStartEffects)[act].push_back(insItr.first->first.ID);
                    } else {
                        (*prcItr).addNumericEffect(insItr.first->first.ID, (pass ? Planner::E_AT_END : Planner::E_AT_START), act);
                    }



                    if (localDebug) {

                        cout << "\t" << *(getPNE(currEffect.fluentIndex)) << " ";
                        if (currEffect.op == VAL::E_ASSIGN) {
                            cout << "= ";
                        } else {
                            cout << "+= ";
                        }

                        list<double>::iterator wItr = weightedSum.first.begin();
                        const list<double>::iterator wEnd = weightedSum.first.end();
                        list<int>::iterator vItr = weightedSum.second.begin();
                        bool isFirst = true;
                        for (; wItr != wEnd; ++wItr, ++vItr) {
                            if (!isFirst) cout << " + ";
                            if (*vItr == -1) {
                                cout << *wItr;
                            } else if (*vItr == -3) {
                                cout << "(" << *wItr << " * ?duration)";
                            } else if (*vItr == -19) {
                                cout << "(" << *wItr << " * -?duration)";
                            } else if (*vItr == -2) {
                                cout << "(" << *wItr << " * #t)";
                            } else if (*vItr == -18) {
                                cout << "(" << *wItr << " * -#t)";
                            } else if (*vItr < 0) {
                                cout << "(" << *wItr << " * <special>)";
                            } else if (*vItr >= negOffset) {
                                cout << "-";
                                if (*wItr != 1.0) cout << "(" << *wItr << " * ";
                                cout << *(getPNE(*vItr - negOffset));
                                if (*wItr != 1.0) cout << ")";
                            } else {
                                if (*wItr != 1.0) cout << "(" << *wItr << " * ";
                                cout << *(getPNE(*vItr));
                                if (*wItr != 1.0) cout << ")";
                            }
                            isFirst = false;
                        }
                        cout << "\n";
                        if (insItr.second) cout << "Effect hasn't been seen before anywhere\n";
                    }
                }
            }
            if (doingMainEffects) {
                doingMainEffects = false;
            } else {
                ++ceItr;
                ++prcItr;
            }
            
        }

        rpgNumericEffects = vector<RPGNumericEffect>(effID);
        rpgNumericEffectsToActions = vector<list<pair<int, Planner::time_spec> > >(effID);

        map<RPGNumericEffect, list<pair<int, Planner::time_spec> > >::iterator effItr = rpgNumericEffectSet.begin();
        const map<RPGNumericEffect, list<pair<int, Planner::time_spec> > >::iterator effEnd = rpgNumericEffectSet.end();

        for (; effItr != effEnd; ++effItr) {

            const RPGNumericEffect & currEff = effItr->first;
            const int currID = currEff.ID;

            rpgNumericEffects[currID] = effItr->first;
            rpgNumericEffectsToActions[currID] = effItr->second;

        }

    };

}

struct NiceFormOfPrecondition {
    int originalID;
    map<int,double> weightedSum;
    VAL::comparison_op op;
    double rhs;
    
    NiceFormOfPrecondition(const int & i) : originalID(i) {
        static const int pneCount = RPGBuilder::getPNECount();
        const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[i];
        
        op = currPre.op;
        rhs = currPre.RHSConstant;
        
        if (currPre.LHSVariable == -19) {
            weightedSum.insert(make_pair(-3, -1.0));
        } else if (currPre.LHSVariable < pneCount) {
            assert(currPre.LHSVariable == -3 || currPre.LHSVariable >= 0);
            weightedSum.insert(make_pair(currPre.LHSVariable, 1.0));
        } else if (currPre.LHSVariable < 2 * pneCount) {
            weightedSum.insert(make_pair(currPre.LHSVariable - pneCount, -1.0));
        } else {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
            rhs -= currAV.constant;
            for (int s = 0; s < currAV.size; ++s) {
                if (currAV.fluents[s] == -19) {
                    weightedSum.insert(make_pair(-3, -currAV.weights[s]));
                } else if (currAV.fluents[s] < pneCount) {
                    assert(currAV.fluents[s] == -3 || currAV.fluents[s] >= 0);
                    weightedSum.insert(make_pair(currAV.fluents[s], currAV.weights[s]));
                } else {
                    weightedSum.insert(make_pair(currAV.fluents[s] - pneCount, -currAV.weights[s]));
                }
            }
        }
    }
    
    bool isTheOppositeOf(const NiceFormOfPrecondition & other) const {
        if (fabs(rhs + other.rhs) > 0.0000001) {
            return false;
        }
        
        if (op == other.op) { // must have >= and >, in some combination
            return false;
        }
        
        map<int,double>::const_iterator tItr = weightedSum.begin();
        const map<int,double>::const_iterator tEnd = weightedSum.end();
        
        map<int,double>::const_iterator t2Itr = other.weightedSum.begin();
        const map<int,double>::const_iterator t2End = other.weightedSum.end();
        
        for (; tItr != tEnd && t2Itr != t2End; ++tItr, ++t2Itr) {
            if (tItr->first != t2Itr->first) {
                return false;
            }
            if (fabs(tItr->second + t2Itr->second) > 0.0000001) {
                return false;
            }
        }
        
        return (tItr == tEnd && t2Itr == t2End);
    }
};

map<int, list<RPGBuilder::IntegralContinuousEffect> > RPGBuilder::actionsToIntegralConditionalEffects;

void RPGBuilder::detectConditionalEffectsThatEncodeIntegralOutcomes()
{
    const int opCount = instantiatedOps.size();

    static const bool localDebug = false;
    
    for (int act = 0; act < opCount; ++act) {
        
        if (rogueActions[act] == RPGBuilder::OT_INVALID_ACTION) {
            continue;
        }
            
        if (actionsToConditionalEffects[act].empty()) {
            continue;
        }
        
        const int outcomeCount = actionsToConditionalEffects[act].size();
        
        if (outcomeCount < 2) {
            continue;
        }
        
        vector<ConditionalEffect*> outcomes(actionsToConditionalEffects[act].size(), 0);
        
        {
            if (localDebug) {
                cout << outcomeCount << " outcomes: [";
            }
            bool sound = true;
            
            list<ConditionalEffect>::iterator ceItr = actionsToConditionalEffects[act].begin();
            const list<ConditionalEffect>::iterator ceEnd = actionsToConditionalEffects[act].end();
            
            for (int oc = 0; ceItr != ceEnd; ++ceItr, ++oc) {
                if (localDebug) {
                    cout << " " << oc;
                }
                outcomes[oc] = &(*ceItr);
                assert(outcomes[oc]);
                if (outcomes[oc]->getNumericPreconditions().size() != 2) {
                    if (localDebug) {
                        cout << *(RPGBuilder::getInstantiatedOp(act)) << " doesn't have two numeric preconditions\n";
                    }                    
                    sound = false;
                    break;
                }
                if (!outcomes[oc]->getPropositionalConditions().empty()) {
                    if (localDebug) {
                        cout << *(RPGBuilder::getInstantiatedOp(act)) << " has propositional conditions\n";
                    }
                    sound = false;
                    break;
                }
            }
            
            if (localDebug) {
                cout << " ]\n";
            }
            
            if (!sound) {
                continue;
            }
            
        }
            
        vector<int> ordered;
        vector<pair<NiceFormOfPrecondition, Planner::time_spec> > leftPrecondition;
        vector<pair<NiceFormOfPrecondition, Planner::time_spec> > rightPrecondition;
        
        ordered.reserve(outcomeCount);
        leftPrecondition.reserve(outcomeCount);
        rightPrecondition.reserve(outcomeCount);
        
        // find an end point - do we have an outcome which has a precondition that nothing else has the 'opposite' of
        
        int ocEndPoint = -1;
        for (int oc = 0; oc < outcomeCount; ++oc) {
            assert(outcomes[oc]);
            list<pair<int, Planner::time_spec> >::const_iterator pItr = outcomes[oc]->getNumericPreconditions().begin();            
            const list<pair<int, Planner::time_spec> >::const_iterator pEnd = outcomes[oc]->getNumericPreconditions().end();
        
            for (int pID = 0; pItr != pEnd; ++pItr, ++pID) {
                
                const NiceFormOfPrecondition here(pItr->first);

                bool foundOpposite = false;
                
                for (int oc2 = 1; oc2 < outcomeCount; ++oc2) {
                    
                    assert(outcomes[oc2]);
                    
                    list<pair<int, Planner::time_spec> >::const_iterator p2Itr = outcomes[oc2]->getNumericPreconditions().begin();            
                    const list<pair<int, Planner::time_spec> >::const_iterator p2End = outcomes[oc2]->getNumericPreconditions().end();
                    
                    for (; p2Itr != p2End; ++p2Itr) {
                        if (pItr->second != p2Itr->second) {
                            continue;
                        }
                        if (NiceFormOfPrecondition(p2Itr->first).isTheOppositeOf(here)) {
                            if (localDebug) {
                                cout << "The opposite of " << RPGBuilder::getNumericPreTable()[pItr->first] << " is " << RPGBuilder::getNumericPreTable()[p2Itr->first] << endl;
                            }
                            foundOpposite = true;
                            break;
                        }
                    }
                    
                    if (p2Itr != p2End) {
                        break;
                    }
                }
                
                if (!foundOpposite) {
                    if (localDebug) {
                        cout << "Not found anything opposite to " << RPGBuilder::getNumericPreTable()[pItr->first] << ", so outcome " << oc << " is an end point\n";
                    }
                    ocEndPoint = oc;
                    ordered.push_back(ocEndPoint);
                    leftPrecondition.push_back(make_pair(here, pItr->second));
                    if (pID == 0) {
                        rightPrecondition.push_back(make_pair(NiceFormOfPrecondition(outcomes[oc]->getNumericPreconditions().back().first),
                                                                                    outcomes[oc]->getNumericPreconditions().back().second));
                    } else {
                        rightPrecondition.push_back(make_pair(NiceFormOfPrecondition(outcomes[oc]->getNumericPreconditions().front().first),
                                                                                    outcomes[oc]->getNumericPreconditions().front().second));
                    } 
                    
                    break;
                }
            }
            
            if (ocEndPoint != -1) {
                break;
            }
        }
        
        if (ocEndPoint == -1) {
            continue;
        }

        if (localDebug) {
            cout << *(RPGBuilder::getInstantiatedOp(act)) << " has a left-most outcome\n";
        }
                                            
        
        int toVisit = 0;
        
        bool sound = true;
        
        while (toVisit != -1) {
            const int oc = ordered[toVisit];
            const int nowVisiting = toVisit;
            toVisit = -1;
            
            vector<int> adjacent(2,-1);
            //vector<int> adjacentBecause(2, -1);

            for (int pID = 0; pID < 2; ++pID) {
                
                if (localDebug) {
                    if (pID) {
                        cout << "At " << nowVisiting << ", outcome " << oc << ", looking to the left of " << RPGBuilder::getNumericPreTable()[leftPrecondition[nowVisiting].first.originalID] << endl;
                    } else {
                        cout << "At " << nowVisiting << ", outcome " << oc << ", looking to the right of " << RPGBuilder::getNumericPreTable()[rightPrecondition[nowVisiting].first.originalID] << endl;
                    }
                }
                const pair<NiceFormOfPrecondition, Planner::time_spec> & here = (pID == 0 ? rightPrecondition[nowVisiting] : leftPrecondition[nowVisiting]);

                bool foundOpposite = false;
                
                for (int oc2 = 0; oc2 < outcomeCount; ++oc2) {                    
                    if (oc == oc2) {
                        continue;
                    }
                    list<pair<int, Planner::time_spec> >::const_iterator p2Itr = outcomes[oc2]->getNumericPreconditions().begin();            
                    const list<pair<int, Planner::time_spec> >::const_iterator p2End = outcomes[oc2]->getNumericPreconditions().end();
                    
                    for (int preID = 0; p2Itr != p2End; ++p2Itr, ++preID) {
                        if (here.second != p2Itr->second) {
                            continue;
                        }
                        const NiceFormOfPrecondition comp(p2Itr->first);
                        if (comp.isTheOppositeOf(here.first)) {
                            if (adjacent[pID] == -1) {
                                if (localDebug) {
                                    cout << "- The opposite is outcome " << oc2 << ": " << RPGBuilder::getNumericPreTable()[p2Itr->first] << endl;
                                }
                                
                                adjacent[pID] = oc2;
                                //adjacentBecause[pID] = preID;
                            } else {
                                if (localDebug) {
                                    cout << "Found two outcomes adjacent on the same side\n";
                                }
                                sound = false;
                            }
                            break;
                        }
                    }                                        
                }
                                
            }
            
            if (!sound) {
                continue;
            }
            
            if (adjacent[0] == -1 && adjacent[1] == -1) {
                if (localDebug) {
                    cout << "Cannot find any outcomes adjacent to " << nowVisiting << endl;
                }
                sound = false;
            } else if (adjacent[0] != -1 && adjacent[1] == -1) {
                // have found something with something adjacent on the right but not on the left
                if (ordered.size() != 1) {
                    if (localDebug) {
                        cout << "Only the left-most member should have no left outcomes\n";
                    }
                    sound = false;
                }
                ordered.push_back(adjacent[0]);
                //leftBecomes = adjacentBecause[0];
                toVisit = nowVisiting + 1;
                
            } else if (adjacent[0] != -1 && adjacent[1] != -1) {
                // have found something with something adjacent on both sides
                if (ordered.size() == 1 || ordered.size() == outcomeCount) { // at the ends
                    if (localDebug) {
                        cout << "The end-most member shouldn't have two adjacent outcomes\n";
                    }
                    sound = false;
                } else {
                    if (adjacent[1] != ordered[nowVisiting -1]) {
                        if (localDebug) {
                            cout << "Not right to the the left-adjacent outcome\n";
                        }
                        sound = false;
                    } else {
                        ordered.push_back(adjacent[0]);
                        //leftBecomes = adjacentBecause[0];
                        toVisit = nowVisiting + 1;
                        if (localDebug) {
                            cout << "Next in sequence, position " << toVisit << ", is outcome " << ordered.back() << endl;
                        }
                    }                     
                }
            } else if (adjacent[0] == -1 && adjacent[1] != -1) {
                if (ordered.size() != outcomeCount) { // should be on the right hand end
                    if (localDebug) {
                        cout << "Only the right-most outcome should have no outcomes to the right\n";
                    }
                    
                    sound = false;
                } else if (adjacent[1] != ordered[nowVisiting - 1]) {
                    if (localDebug) {
                        cout << "The penultimate outcome is not to the left of the rightmost outcome\n";
                    }
                    sound = false;
                }
            }
            
            if (toVisit == nowVisiting + 1) {
                int done = 0;
                list<pair<int, Planner::time_spec> >::const_iterator p2Itr = outcomes[ordered.back()]->getNumericPreconditions().begin();            
                const list<pair<int, Planner::time_spec> >::const_iterator p2End = outcomes[ordered.back()]->getNumericPreconditions().end();
                
                for (; p2Itr != p2End; ++p2Itr) {
                    
                    if (p2Itr->second != rightPrecondition[nowVisiting].second) {
                        continue;
                    }
                    const NiceFormOfPrecondition comp(p2Itr->first);
                    
                    if (comp.isTheOppositeOf(rightPrecondition[nowVisiting].first)) { 
                        leftPrecondition.push_back(make_pair(comp, p2Itr->second));
                        ++done;
                        if (localDebug) {
                            cout << "* Its left precondition is " << RPGBuilder::getNumericPreTable()[p2Itr->first] << endl;
                        }
                    } else {
                        rightPrecondition.push_back(make_pair(comp, p2Itr->second));
                        ++done;
                        if (localDebug) {
                            cout << "* Its right precondition is " << RPGBuilder::getNumericPreTable()[p2Itr->first] << endl;
                        }
                    }
                    
                }
                assert(done == 2);
            }
        }
        
        if (!sound || ordered.size() != outcomeCount) {
            continue;
        }
        
        const double leftDifference = leftPrecondition[1].first.rhs - leftPrecondition[0].first.rhs;
        const double rightDifference = rightPrecondition[1].first.rhs - rightPrecondition[0].first.rhs;
        
        if (localDebug) {
            cout << "Proposed left difference is " << leftDifference << endl;
        }
        
        for (int oc = 2; oc < outcomeCount; ++oc) {
            if (fabs((leftPrecondition[oc].first.rhs - leftPrecondition[oc-1].first.rhs) - leftDifference) > 0.0000001) {
                sound = false;
            }
        }
        if (!sound) {
            continue;
        }        
                
        // we now know the left bound is constant + integer times difference
                
        
        vector<map<int, int> > startEffectsDueToOutcome(outcomeCount);
        vector<map<int, int> > endEffectsDueToOutcome(outcomeCount);
        
        for (int oc = 0; oc < outcomeCount; ++oc) {
            list<pair<int, Planner::time_spec> >::const_iterator effItr = outcomes[oc]->getNumericEffects().begin();
            const list<pair<int, Planner::time_spec> >::const_iterator effEnd = outcomes[oc]->getNumericEffects().end();
            
            for (; effItr != effEnd; ++effItr) {
                if (effItr->second == Planner::E_AT_START) {
                    startEffectsDueToOutcome[oc].insert(make_pair(RPGBuilder::getNumericEff()[effItr->first].fluentIndex, effItr->first));
                } else {
                    endEffectsDueToOutcome[oc].insert(make_pair(RPGBuilder::getNumericEff()[effItr->first].fluentIndex, effItr->first));
                }
            }
        }
        
        map<int,double> startDifference;
        map<int,double> endDifference;
        
        for (int pass = 0; sound && pass < 2; ++pass) {
            const vector<map<int,int> > & effMap = (pass ? endEffectsDueToOutcome : startEffectsDueToOutcome);
            map<int,double> & differenceMap = (pass ? endDifference : startDifference);                        
            
            for (int oc = 1; sound && oc < outcomeCount; ++oc) {
                map<int,int>::const_iterator thisEffItr = effMap[oc].begin();
                const map<int,int>::const_iterator thisEffEnd = effMap[oc].end();

                map<int,int>::const_iterator otherEffItr = effMap[oc-1].begin();
                const map<int,int>::const_iterator otherEffEnd = effMap[oc-1].end();
                
                for (; thisEffItr != thisEffEnd && otherEffItr != otherEffEnd; ++thisEffItr, ++otherEffItr) {
                    
                    if (thisEffItr->first != otherEffItr->first) {
                        sound = false;
                        break;
                    }
                    
                    const RPGBuilder::RPGNumericEffect & thisEff = RPGBuilder::getNumericEff()[thisEffItr->second];
                    const RPGBuilder::RPGNumericEffect & otherEff = RPGBuilder::getNumericEff()[otherEffItr->second];
                    
                    if (thisEff.isAssignment != otherEff.isAssignment) {
                        sound = false;
                        break;
                    }
                    
                    if (thisEff.size != otherEff.size) {
                        sound = false;
                        break;
                    }
                    
                    map<int,double> thisWS;
                    
                    {                        
                        for (int s = 0; s < thisEff.size; ++s) {
                            thisWS.insert(make_pair(thisEff.variables[s], thisEff.weights[s]));
                        }
                    }
                        
                    {                        
                        for (int s = 0; s < otherEff.size; ++s) {
                            map<int,double>::const_iterator wsItr = thisWS.find(otherEff.variables[s]);
                            if (wsItr == thisWS.end()) {
                                sound = false;
                                break;
                            }
                            if (fabs(otherEff.weights[s] - wsItr->second) > 0.0000001) {
                                sound = false;
                                break;
                            }
                        }
                    }
                                                                    
                    if (oc == 1) {
                        differenceMap.insert(make_pair(thisEffItr->first, thisEff.constant - otherEff.constant));
                    } else {
                        map<int,double>::const_iterator wsItr = differenceMap.find(thisEffItr->first);
                        if (wsItr == differenceMap.end()) {
                            sound = false;
                            break;
                        }
                        if (fabs((thisEff.constant - otherEff.constant) - wsItr->second) > 0.0000001) {
                            sound = false;
                            break;
                        }
                    }
                    
                }
            }
        }
        
        if (!sound) {
            continue;
        }
        
        list<IntegralContinuousEffect> & toUpdate = actionsToIntegralConditionalEffects[act];
        
        toUpdate.push_back(IntegralContinuousEffect(act, outcomeCount - 1,
                                                    leftPrecondition[0].first.originalID, leftPrecondition[0].second, leftDifference,
                                                    rightPrecondition[0].first.originalID, rightDifference));
        
        {
            map<int,int>::const_iterator effItr = startEffectsDueToOutcome[0].begin();
            const map<int,int>::const_iterator effEnd = startEffectsDueToOutcome[0].end();
            
            map<int,int>::const_iterator reffItr = startEffectsDueToOutcome[outcomeCount - 1].begin();

            map<int,double>::const_iterator diffItr = startDifference.begin();
            
            for (; effItr != effEnd; ++effItr, ++reffItr) {
                assert(effItr->first == diffItr->first);
                assert(reffItr->first == effItr->first);
                toUpdate.back().addStartEffect(effItr->second, diffItr->second, reffItr->second);
            }
            
        }

        {
            for (int oc = 0; oc < outcomeCount; ++oc) {
                map<int,int>::const_iterator effItr = startEffectsDueToOutcome[oc].begin();
                const map<int,int>::const_iterator effEnd = startEffectsDueToOutcome[oc].end();
                list<int> dest;
                
                for (; effItr != effEnd; ++effItr) {
                    dest.push_back(effItr->second);
                }
                
                toUpdate.back().addStartEffectsForOutcome(oc,dest);
            }
        }
        
        {
            for (int oc = 0; oc < outcomeCount; ++oc) {
                map<int,int>::const_iterator effItr = endEffectsDueToOutcome[oc].begin();
                const map<int,int>::const_iterator effEnd = endEffectsDueToOutcome[oc].end();
                list<int> dest;
                
                for (; effItr != effEnd; ++effItr) {
                    dest.push_back(effItr->second);
                }
                
                toUpdate.back().addEndEffectsForOutcome(oc,dest);
            }
        }
        
                
        
        {
            map<int,int>::const_iterator effItr = endEffectsDueToOutcome[0].begin();
            const map<int,int>::const_iterator effEnd = endEffectsDueToOutcome[0].end();
            
             map<int,int>::const_iterator reffItr = endEffectsDueToOutcome[outcomeCount - 1].begin();
            
            map<int,double>::const_iterator diffItr = endDifference.begin();
            
            for (; effItr != effEnd; ++effItr) {
                assert(effItr->first == diffItr->first);
                toUpdate.back().addEndEffect(effItr->second, diffItr->second, reffItr->second);
            }
            
        }
        
        actionsToConditionalEffects[act].clear();
        
        if (localDebug || true) {            
            cout << *(RPGBuilder::getInstantiatedOp(act)) << " has an integral outcome series encoded using conditional effects\n";
        }
    }
    
}

bool RPGBuilder::IntegralContinuousEffect::satisfied(const Planner::time_spec & ts, const vector<double> & min, const vector<double> & max,
                                         const double & minDur, const double & maxDur, pair<int,int> & outcomeBracket) const
{
    
    if (ts != leftPreconditionTS) {
        return false;
    }

    static const bool debug = false;
        
    double evaluatedLHS = 0.0;
    double rhs = 0.0;
    
    double minLHS = 0.0;
    double minrhs = 0.0;
    
    static const int pneCount = RPGBuilder::getPNECount();
    const RPGBuilder::RPGNumericPrecondition & currPre = RPGBuilder::getNumericPreTable()[leftPrecondition];
    
    minrhs = rhs = currPre.RHSConstant;
    
    if (debug) {
        cout << "Seeing if an ICE attached to " << *(RPGBuilder::getInstantiatedOp(parentAction)) << " based around " << currPre << " fires\n";
    }
    
    if (currPre.LHSVariable == -19) {
        evaluatedLHS = -minDur;
        minLHS = -maxDur;
        if (debug) {
            cout << "+ -?duration : " << -maxDur << " to " << -minDur << endl;
        }
    } else if (currPre.LHSVariable == -3) {
        evaluatedLHS = maxDur;
        minLHS = minDur;
        if (debug) {
            cout << "+ ?duration : " << minDur << " to " << maxDur << endl;
        }
        
    } else {
        assert(currPre.LHSVariable >= 0);
        
        if (currPre.LHSVariable < pneCount) {
            evaluatedLHS = max[currPre.LHSVariable];
            minLHS = min[currPre.LHSVariable];
            if (debug) {
                cout << "+ " << *(RPGBuilder::getPNE(currPre.LHSVariable)) << " : " << minLHS << " to " << evaluatedLHS << endl;
            }
            
        } else if (currPre.LHSVariable < 2 * pneCount) {
            evaluatedLHS = -min[currPre.LHSVariable - pneCount];
            minLHS = -max[currPre.LHSVariable - pneCount];
            if (debug) {
                cout << "+ -" << *(RPGBuilder::getPNE(currPre.LHSVariable)) << " : " << minLHS << " to " << evaluatedLHS << endl;
            }
            
        } else {
            const RPGBuilder::ArtificialVariable & currAV = RPGBuilder::getArtificialVariable(currPre.LHSVariable);
            
            rhs -= currAV.constant;
            minrhs -= currAV.constant;
            
            for (int s = 0; s < currAV.size; ++s) {
                if (currAV.fluents[s] == -19) {
                    evaluatedLHS -= currAV.weights[s] * minDur;
                    minLHS -= currAV.weights[s] * maxDur;
                    if (debug) {
                        cout << "+ " << currAV.weights[s] << " * -?duration : " << -currAV.weights[s] * maxDur << " to " << -currAV.weights[s] * minDur << endl;
                    }
                    
                } else if (currAV.fluents[s] == -3) {
                    evaluatedLHS += currAV.weights[s] * maxDur;
                    minLHS += currAV.weights[s] * minDur;
                    if (debug) {
                        cout << "+ " << currAV.weights[s] << " * ?duration : " << currAV.weights[s] * minDur << " to " << currAV.weights[s] * maxDur << endl;
                    }
                    
                } else {
                    assert(currAV.fluents[s] >= 0);
                    if (currAV.fluents[s] < pneCount) {
                        evaluatedLHS += currAV.weights[s] * max[currAV.fluents[s]];
                        minLHS += currAV.weights[s] * min[currAV.fluents[s]];
                        
                        if (debug) {
                            cout << "+ " << currAV.weights[s] << " * " <<  *(RPGBuilder::getPNE(currAV.fluents[s])) << " : " << currAV.weights[s] * min[currAV.fluents[s]] << " to " << currAV.weights[s] * max[currAV.fluents[s]] << endl;
                        }
                        
                    } else {
                        evaluatedLHS -= currAV.weights[s] * min[currAV.fluents[s] - pneCount];
                        minLHS -= currAV.weights[s] * max[currAV.fluents[s] - pneCount];
                        
                        if (debug) {
                            cout << "- " << currAV.weights[s] << " * " <<  *(RPGBuilder::getPNE(currAV.fluents[s] - pneCount)) << " : " << -currAV.weights[s] * max[currAV.fluents[s] - pneCount] << " to " << -currAV.weights[s] * min[currAV.fluents[s] * pneCount] << endl;
                        }
                        
                    } 
                
                }
            }
        }     
    }
    
    if (debug) {
        cout << "- Evaluated LHS to " << evaluatedLHS << "\n";
    }
    
    double localLeftPreconditionDifference = leftPreconditionDifference;
    
    if (leftPreconditionDifference < 0.0) {
    
        rhs += outcomes * leftPreconditionDifference;
        minrhs += outcomes * leftPreconditionDifference;
        
        localLeftPreconditionDifference = -leftPreconditionDifference;
    }
    
    double diff = evaluatedLHS - rhs;
    if (currPre.op == VAL::E_GREATEQ ? diff < 0.0 : diff <= 0.0) {
        if (debug) {
            cout << "  - No way to satisfy precondition\n";
        }
        return false;
    }
    
    outcomeBracket.first = 0;
    
    double mindiff = minLHS - minrhs;
    
    if (currPre.op == VAL::E_GREATEQ ? mindiff >= 0.0 : mindiff > 0) {
        outcomeBracket.first = floor(mindiff / localLeftPreconditionDifference);
        
        if (currPre.op == VAL::E_GREATER && mindiff < outcomeBracket.first * localLeftPreconditionDifference) {
            --outcomeBracket.first;
            if (outcomeBracket.first < 0) {
                outcomeBracket.first = 0;
            }
        }
        
        if (debug) {
            cout << "  - Range can start at " << outcomeBracket.first << endl;
        }
        
    }
    
    int endAt;
    
    if (currPre.op == VAL::E_GREATER ? diff > (outcomes * localLeftPreconditionDifference) : diff >= (outcomes * localLeftPreconditionDifference)) {
        if (debug) {
            cout << "  - Saturated outcomes - can end at " << outcomes << endl;
        }
        endAt = outcomes;
    } else {
                  
        endAt = floor(diff / localLeftPreconditionDifference);
                
        if (endAt > outcomes) {
            endAt = outcomes;
        }
        
        if (currPre.op == VAL::E_GREATER && diff < endAt * localLeftPreconditionDifference) {
            --endAt;
        }
        
        if (debug) {
            cout << "  - Range can end at " << outcomeBracket.first << endl;
        }
    }                                
    
    assert(currPre.op == VAL::E_GREATEQ ? evaluatedLHS >= (rhs + endAt * localLeftPreconditionDifference)
                                        : evaluatedLHS >  (rhs + endAt * localLeftPreconditionDifference)  );
    
    if (endAt < outcomes) {
        assert(currPre.op == VAL::E_GREATEQ ? evaluatedLHS < (rhs + (endAt + 1) * localLeftPreconditionDifference)
                                            : evaluatedLHS <=  (rhs + (endAt + 1) * localLeftPreconditionDifference)  );
        
    }
    
    outcomeBracket.second = endAt;
        
    if (leftPreconditionDifference < 0.0) {
        const pair<int,int> replacement(outcomes - outcomeBracket.second, outcomes - outcomeBracket.first);
        outcomeBracket = replacement;
    }
        
    
    return true;
}
 
 
void RPGBuilder::IntegralContinuousEffect::workOutSuitablePreconditionRelaxation()
{
    calculateRelaxedOutcomes = true;
    
    const NiceFormOfPrecondition cond(leftPrecondition);
    
    const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
    {
        map<int,double>::const_iterator wsItr = cond.weightedSum.begin();
        const map<int,double>::const_iterator wsEnd = cond.weightedSum.end();
        
        for (; wsItr != wsEnd; ++wsItr) {
            if (wsItr->first == -3) {
                continue;
            }
            if (tickers.find(wsItr->first) == tickers.end()) {
                calculateRelaxedOutcomes = false;
                return;
            }
        }
    }

    static const int pneCount = RPGBuilder::getPNECount();
        
    vector<double> dummyMin(pneCount);
    vector<double> dummyMax(pneCount);
    
    if (!tickers.empty()) {
        map<int,double>::const_iterator tItr = tickers.begin();
        const map<int,double>::const_iterator tEnd = tickers.end();
        
        for (; tItr != tEnd; ++tItr) {
            if (tItr->second >= 0.0) {
                dummyMin[tItr->first] = 0.0;
                dummyMax[tItr->first] = DBL_MAX;
            } else {
                dummyMin[tItr->first] = -DBL_MAX;
                dummyMax[tItr->first] = 0.0;
            }
        }
    }
    
    pair<int,int> outcomeBracket(-1,-1);
            
    const bool fires = satisfied(leftPreconditionTS, dummyMin, dummyMax,
                                 RPGBuilder::getOpMinDuration(parentAction, -1),
                                 RPGBuilder::getOpMaxDuration(parentAction, -1),
                                 outcomeBracket);
    
    if (outcomeBracket.first > 0 || outcomeBracket.second < outcomes) {
        cout << "Only keeping outcomes " << outcomeBracket.first << " to " << outcomeBracket.second << " of " << *(RPGBuilder::getInstantiatedOp(parentAction)) << endl;
    }
    
    minimalOutcome = outcomeBracket.first;
    outcomes = outcomeBracket.second;
            
}

void RPGBuilder::IntegralContinuousEffect::getRelaxedStartEffects(list<int> & writeTo, const double & currLayer) const
{
    if (minimalOutcome == -1) {
        return;
    }
    
    if (leftPreconditionTS != Planner::E_AT_START) {
        return;
    }
    
    if (!calculateRelaxedOutcomes) {
        writeTo = relaxedStartEffects;
        return;
    }

    static const int pneCount = RPGBuilder::getPNECount();
    
    static vector<double> dummyMin(pneCount);
    static vector<double> dummyMax(pneCount);
    
    
    const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
        
    if (!tickers.empty()) {
        map<int,double>::const_iterator tItr = tickers.begin();
        const map<int,double>::const_iterator tEnd = tickers.end();
        
        for (; tItr != tEnd; ++tItr) {
            if (tItr->second >= 0.0) {
                dummyMin[tItr->first] = currLayer * tItr->second;
                dummyMax[tItr->first] = DBL_MAX;
            } else {
                dummyMin[tItr->first] = -DBL_MAX;
                dummyMax[tItr->first] = currLayer * tItr->second;
            }
        }
    }

    pair<int,int> outcomeBracket(-1,-1);
    
    const bool fires = satisfied(Planner::E_AT_START, dummyMin, dummyMax,
                                 RPGBuilder::getOpMinDuration(parentAction, -1),
                                 RPGBuilder::getOpMaxDuration(parentAction, -1),
                                 outcomeBracket);

    if (fires) {
        for (int oc = outcomeBracket.first; oc <= outcomeBracket.second; ++oc) {
            writeTo.insert(writeTo.end(), startEffectsForOutcome[oc].begin(), startEffectsForOutcome[oc].end());
        }
    }
                                                                                                                                                       
}

void RPGBuilder::IntegralContinuousEffect::getRelaxedEndEffects(list<int> & writeTo, const double & currLayer) const
{
    
    if (minimalOutcome == -1) {
        return;
    }
    
    if (leftPreconditionTS != Planner::E_AT_END) {
        return;
    }
    
    if (!calculateRelaxedOutcomes) {
        writeTo = relaxedEndEffects;
        return;
    }

    static const int pneCount = RPGBuilder::getPNECount();
    
    static vector<double> dummyMin(pneCount);
    static vector<double> dummyMax(pneCount);
    
    
    const map<int,double> & tickers = NumericAnalysis::getVariablesThatAreTickers();
        
    if (!tickers.empty()) {
        map<int,double>::const_iterator tItr = tickers.begin();
        const map<int,double>::const_iterator tEnd = tickers.end();
        
        for (; tItr != tEnd; ++tItr) {
            if (tItr->second >= 0.0) {
                dummyMin[tItr->first] = currLayer * tItr->second;
                dummyMax[tItr->first] = DBL_MAX;
            } else {
                dummyMin[tItr->first] = -DBL_MAX;
                dummyMax[tItr->first] = currLayer * tItr->second;
            }
        }
    }

    pair<int,int> outcomeBracket(-1,-1);
    
    const bool fires = satisfied(Planner::E_AT_END, dummyMin, dummyMax,
                                 RPGBuilder::getOpMinDuration(parentAction, -1),
                                 RPGBuilder::getOpMaxDuration(parentAction, -1),
                                 outcomeBracket);

    if (fires) {
        for (int oc = outcomeBracket.first; oc <= outcomeBracket.second; ++oc) {
            writeTo.insert(writeTo.end(), endEffectsForOutcome[oc].begin(), endEffectsForOutcome[oc].end());
        }
    }
                                                                                                                                                       
}


void RPGBuilder::buildMetric(VAL::metric_spec * ms)
{

    if (!ms || !Globals::optimiseSolutionQuality) return;
    
    static const bool metricDebug = false;

    theMetric = new Metric(ms->opt == E_MINIMIZE);
    list<Operand> tmpFormula;
    ExpressionBuilder builder(tmpFormula, 0, 0);
    const bool metricIsValid = builder.buildFormula(const_cast<VAL::expression*>(ms->expr));
    if (!metricIsValid) {
        postmortem_invalidMetric();
    }
    pair<list<double>, list<int> > result;
    WhereAreWeNow = PARSE_METRIC;
    RPGBuilder::makeWeightedSum(tmpFormula, result);
    WhereAreWeNow = PARSE_UNKNOWN;
    theMetric->weights = result.first;
    theMetric->variables = result.second;
    
    const int varCount = getPNECount();
    
    list<int>::iterator varItr = theMetric->variables.begin();
    const list<int>::iterator varEnd = theMetric->variables.end();
    
    list<double>::iterator wItr = theMetric->weights.begin();
        
    while (varItr != varEnd) {
        if (*varItr == -1) {
            
            theMetric->constant = *wItr;
            
            const list<int>::iterator varPrev = varItr; ++varItr;
            const list<double>::iterator wPrev = wItr; ++wItr;
            
            theMetric->variables.erase(varPrev);
            theMetric->weights.erase(wPrev);
            
            if (metricDebug) {
                cout << "Metric constant term is " << theMetric->constant << endl;
            }
        } else if (*varItr >= 0) {
            if (*varItr >= varCount) {
                *varItr -= varCount;
                *wItr *= -1;
            }
            metricVars.insert(*varItr);
            
            if (metricDebug) {
                cout << "+ " << *(RPGBuilder::getPNE(*varItr)) << " * " << *wItr << endl;
            }
            ++varItr;
            ++wItr;
        } else if (*varItr > -1024) {
            if (*varItr <= -512) {
                
                if (*varItr <= -528) {
                    *varItr += 16;
                    if (*wItr != 0.0) *wItr = -*wItr;
                }
                
                if (*varItr == -512) {
                    // is the variable denoting preferences that are tautologous - i.e. evaluates to 0,
                    // so we do nothing
                    if (metricDebug) {
                        cout << "Ignoring tautologous-preference term\n";
                    }
                } else if (*varItr == -513) {                        
                    permanentPreferenceViolations = *wItr;                        
                    if (metricDebug) {
                        cout << "Permanent violation cost: " << *wItr << endl;
                    }
                } else {
                    cout << "Internal error - variable " << *varItr << " isn't one of -512 or -513\n";
                    exit(1);
                }
                
                const list<int>::iterator varPrev = varItr; ++varItr;
                const list<double>::iterator wPrev = wItr; ++wItr;
                
                theMetric->variables.erase(varPrev);
                theMetric->weights.erase(wPrev);
                
            } else if (*varItr <= -17) {
                *varItr += 16;
                metricVars.insert(*varItr);                    
                if (*wItr != 0.0) *wItr = -*wItr;
                if (metricDebug) {
                    cout << "+ weight on special var " << *varItr << " of " << *wItr << endl;
                }
                ++varItr; ++wItr;
                                            
            } else {
                metricVars.insert(*varItr);
                if (metricDebug) {
                    cout << "+ weight on special var " << *varItr << " of " << *wItr << endl;
                }
                ++varItr; ++wItr;                                            
            }
                            
        } else {
            const int vtu = (*varItr <= -1048576 ? -1048576 - *varItr : -1024 - *varItr);
            const double wtu = (*wItr == 0.0 ? 0.0 : (*varItr <= -1048576 ? -*wItr : *wItr));
            
            //cout << "Changed cost of preference " << preferences[vtu].name << " from " << preferences[vtu].cost << " to ";
            
            preferences[vtu].cost += wtu;
            
            if (metricDebug) {
                cout << "+ weight on preference " << preferences[vtu].name << ":" << vtu << " of " << wtu << endl;
            }
            
            //cout << preferences[vtu].cost << endl;
            
            const list<int>::iterator varPrev = varItr; ++varItr;
            const list<double>::iterator wPrev = wItr; ++wItr;
            
            theMetric->variables.erase(varPrev);
            theMetric->weights.erase(wPrev);
            
        }
    }
    
#ifndef NDEBUG
    list<int>::iterator var2Itr = theMetric->variables.begin();
    const list<int>::iterator var2End = theMetric->variables.end();
    
    for (; var2Itr != var2End; ++var2Itr) {
        assert(*var2Itr > -1024);
    }
#endif

}

};
