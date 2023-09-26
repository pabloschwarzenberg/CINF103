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

#include "NNF.h"
#include "DebugWriteController.h"
#include "RPGBuilder.h"

#include "colours.h"

using namespace Inst;
using namespace VAL;

using std::endl;

namespace Planner {

void NNFPartialVisitor::visit_AND(NNFNode_AND * andNode) {
    NNFContainerNode::iterator childItr = andNode->begin();
    const NNFContainerNode::iterator childEnd = andNode->end();

    for (;childItr != childEnd; ++childItr) {
        (*childItr)->visit(this);
    }
};

void NNFPartialVisitor::visit_OR(NNFNode_OR * orNode) {
    NNFContainerNode::iterator childItr = orNode->begin();
    const NNFContainerNode::iterator childEnd = orNode->end();

    for (;childItr != childEnd; ++childItr) {
        (*childItr)->visit(this);
    }
};
void NNFPartialVisitor::visit_NOT_Literal(NNFNode_NOT_Literal *) {};
void NNFPartialVisitor::visit_Literal(NNFNode_Literal *) {};
void NNFPartialVisitor::visit_NOT_Numeric(NNFNode_NOT_Numeric *) {};
void NNFPartialVisitor::visit_Numeric(NNFNode_Numeric *) {};
void NNFPartialVisitor::visit_RPGNumeric(NNFNode_RPGNumeric *) {};


NNFNode * NNFNode_AND::negate() {

    NNFNode_OR * const toReturn = new NNFNode_OR();
    iterator itr = begin();
    iterator itrEnd = end();

    for (; itr != itrEnd; ++itr) {
        toReturn->addChild((*itr)->negate());
        delete *itr;
    }
    clear();

    return toReturn;
};

NNFNode * NNFNode_OR::negate() {

    NNFNode_AND * const toReturn = new NNFNode_AND();
    iterator itr = begin();
    iterator itrEnd = end();

    for (; itr != itrEnd; ++itr) {
        toReturn->addChild((*itr)->negate());
        delete *itr;
    }
    clear();

    return toReturn;
};

NNFNode * NNFNode_Literal::negate() {
    NNFNode * const toReturn = new NNFNode_NOT_Literal(lit,ts);
    lit = 0;
    return toReturn;
};

NNFNode * NNFNode_NOT_Literal::negate() {
    NNFNode * const toReturn = new NNFNode_Literal(lit,ts);
    lit = 0;
    return toReturn;

};

NNFNode * NNFNode_Numeric::negate() {
    NNFNode * const toReturn = new NNFNode_NOT_Numeric(pre,ts);
    pre = 0;
    return toReturn;
};

NNFNode * NNFNode_NOT_Numeric::negate() {
    NNFNode * const toReturn = new NNFNode_Numeric(pre,ts);
    pre = 0;
    return toReturn;
};

NNFNode * NNFNode_RPGNumeric::negate() {
    std::cerr << "Fatal internal error: once the final numeric preconditions have been substituted into NNF, it should not be negated\n";
    exit(1);
    return 0;
};


const bool nnfCollectDebug = false;
int nnfCollectDebugIndent = 0;

class ChildResultStack  {
  
    protected:
        
        list<pair<NNFNode*,bool> > stack;
    
    public:
        
        virtual void push_back(const pair<NNFNode*,bool> & e)
        {
            stack.push_back(e);
        }
    
        virtual void get_result(pair<NNFNode*,bool> & e)
        {
            e = stack.back();
            stack.pop_back();
        }
};



class NNFGoalCollector : public VisitController {

private:

    VAL::TypeChecker * tc;
    VAL::goal * rootGoal;
    FastEnvironment * fe;
    bool debug;

    ChildResultStack justCreated;
    list<VAL::time_spec> currTS;
    // each pair:
    // first - the NNFNode created, if there is one, or...
    // second - true if the NNFNode was tautologous, false otherwise

public:

    NNFGoalCollector(VAL::goal * g,FastEnvironment * f,VAL::TypeChecker * t = 0)
        : tc(t), rootGoal(g), fe(f) {
        debug = (Globals::globalVerbosity & 16);
    }

    pair<NNFNode*, bool> makeNNF() {
        rootGoal->visit(this);
        pair<NNFNode*, bool> toReturn;
        justCreated.get_result(toReturn);
        return toReturn;
    }

    virtual void visit_simple_goal(simple_goal * p)  {
        VAL::extended_pred_symbol * const asEPS = EPS(p->getProp()->head);
        assert(asEPS);
        pred_symbol* const currParent = asEPS->getParent();
        
        pred_symbol* const eqPred = VAL::current_analysis->pred_tab.symbol_probe("=");

        
        if(eqPred == currParent) {
            Literal tmp(p->getProp(),fe);

            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "Equality";
                cout.flush();
            }
            //validateLiteral(&tmp);

            VAL::LiteralParameterIterator<VAL::parameter_symbol_list::iterator> tmpBegin = tmp.begin();
            
            VAL::parameter_symbol * a = *tmpBegin;
            ++tmpBegin;
            VAL::parameter_symbol * b = *tmpBegin;

            justCreated.push_back(pair<NNFNode*,bool>(0,(a == b)));

            if (nnfCollectDebug) {
                cout << ", comparing " << a->getName() << " to " << b->getName() << ": evaluates to ";
                if (a == b) {
                    cout << "true\n";
                } else {
                    cout << "false\n";
                }
            }
            
            return;
        };


        Literal * l = new Literal(p->getProp(),fe);
        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "Literal: " << *l << " (" << p->getProp()->head << "/" << current_analysis->pred_tab.symbol_get(p->getProp()->head->getName());
            VAL::LiteralParameterIterator<VAL::parameter_symbol_list::iterator> itr = l->begin();
            VAL::LiteralParameterIterator<VAL::parameter_symbol_list::iterator> itrEnd = l->end();
            
            for (; itr != itrEnd; ++itr) {
                cout << " " << *itr;
            }
            cout << ")\n";
            cout.flush();
        }
        
        validateLiteral(l);

        Literal * const addLit = instantiatedOp::findLiteral(l);

        if (addLit) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << " - looked it up and got " << addLit << " - ";
                cout.flush();
                cout << *addLit;
                cout << endl;
            }
            
            const pair<bool,bool> & staticInfo = RPGBuilder::isStatic(addLit);
            VAL::time_spec tsToUse = (currTS.empty() ? VAL::E_AT : currTS.back());
            
            if (staticInfo.first) {
                if (nnfCollectDebug) {
                    if (staticInfo.second) {
                        cout << string(nnfCollectDebugIndent, ' ') << "     - Fact is statically true\n";
                    } else {
                        cout << string(nnfCollectDebugIndent, ' ') << "     - Fact is statically false\n";
                    }
                }
                justCreated.push_back(pair<NNFNode*,bool>(0, staticInfo.second));
            } else {
                justCreated.push_back(pair<NNFNode*,bool>(new NNFNode_Literal(addLit, tsToUse),true));
            }

        } else {
            // cout << "Contradictory goal in goal formula: " << *l << " does not exist\n";
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << " - doesn't exist\n";
            }
        }

        delete l; l = 0;
    
    }
    
    virtual void visit_comparison(comparison * c) {
        VAL::time_spec tsToUse = (currTS.empty() ? VAL::E_AT : currTS.back());
        justCreated.push_back(pair<NNFNode*,bool>(new NNFNode_Numeric(new RPGBuilder::NumericPrecondition(c->getOp(), const_cast<VAL::expression*>(c->getLHS()), const_cast<VAL::expression*>(c->getRHS()), fe, tc),tsToUse), true));
        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "Numeric comparison\n";            
        }
    }

    virtual void visit_qfied_goal(qfied_goal * p) {

        if (nnfCollectDebug) {
            if (p->getQuantifier() == E_FORALL) {
                cout << string(nnfCollectDebugIndent, ' ') << "forall goal\n";
            } else {
                cout << string(nnfCollectDebugIndent, ' ') << "exists goal\n";
            } 
        
        }        
        vector<vector<VAL::const_symbol*>::const_iterator> vals(p->getVars()->size());
        vector<vector<VAL::const_symbol*>::const_iterator> starts(p->getVars()->size());
        vector<vector<VAL::const_symbol*>::const_iterator> ends(p->getVars()->size());
        vector<VAL::var_symbol *> vars(static_cast<const id_var_symbol_table*>(p->getSymTab())->numSyms());
        
        if (fe) {
            fe->extend(vars.size());
        } else {
            fe = new FastEnvironment(vars.size());
        }
        
        int i = 0;
        int c = 1;
        for(var_symbol_list::const_iterator pi = p->getVars()->begin();
                pi != p->getVars()->end();++pi,++i) {

            if(instantiatedOp::getValues().find((*pi)->type) == instantiatedOp::getValues().end()) {
                instantiatedOp::getValues()[(*pi)->type] = tc->range(*pi);
            }
            
            vals[i] = starts[i] = instantiatedOp::getValues()[(*pi)->type].begin();
            ends[i] = instantiatedOp::getValues()[(*pi)->type].end();
            if(ends[i]==starts[i]) {
                justCreated.push_back(pair<NNFNode*,bool>(0,p->getQuantifier() == E_FORALL));
                if (nnfCollectDebug) {
                    cout << string(nnfCollectDebugIndent, ' ') << " - Is necessarily empty\n";
                }
                return;
            }
            (*fe)[(*pi)] = *(vals[i]);
            vars[i] = *pi;
            c *= instantiatedOp::getValues()[(*pi)->type].size();
        }

        NNFContainerNode * branchNode;
        if (p->getQuantifier() == E_FORALL) {
            branchNode = new NNFNode_AND();
        } else {
            branchNode = new NNFNode_OR();
        }

        bool contradiction = false;
        bool tautology = false;


        --i;
        while(vals[i] != ends[i]) {
            // This is inefficient because it creates a copy of the environment even if the copy is never used.
            // In practice, this should not be a problem because a quantified effect presumably uses the variables
            // it quantifies.
            FastEnvironment * ecpy = fe;
            fe = fe->copy();
            nnfCollectDebugIndent += 2;
            p->getGoal()->visit(this);
            nnfCollectDebugIndent -= 2;
            fe = ecpy;

            pair<NNFNode*,bool> oldBack;
            justCreated.get_result(oldBack);
            
            if (oldBack.first) {
                branchNode->addChild(oldBack.first);
            } else {
                if (p->getQuantifier() == E_FORALL) {
                    if ((contradiction = !oldBack.second)) {
                        break;
                    }
                } else {
                    if ((tautology = oldBack.second)) {                        
                        break;
                    }
                }
            }

            int x = 0;
            ++vals[0];
            if(vals[0] != ends[0]) (*fe)[vars[0]] = *(vals[0]);
            
            while(x < i && vals[x] == ends[x]) {
                vals[x] = starts[x];
                (*fe)[vars[x]] = *(vals[x]);
                ++x;
                ++vals[x];
                if(vals[x] != ends[x]) (*fe)[vars[x]] = *(vals[x]);
            }
        }

        if (contradiction || (p->getQuantifier() == E_EXISTS && branchNode->empty()) ) {
            if (nnfCollectDebug) {
                if (!contradiction) cout << "Exists quantifier's children are all false - must be false\n";
            }
            
            delete branchNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            return;
        }

        if (tautology || (p->getQuantifier() == E_FORALL && branchNode->empty()) ) {
            if (nnfCollectDebug) {
                if (branchNode->empty()) cout << "Forall quantifier has no potentially false children - must be true\n";
            }
            delete branchNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
            return;
        }

        if (nnfCollectDebug) {
            cout << "quantifier could evaluate to either true or false\n";
        }
        
        justCreated.push_back(pair<NNFNode*,bool>(branchNode,true));

    }

    virtual void visit_conj_goal(conj_goal * p)  {
        const goal_list * goals = p->getGoals();
        if (goals->empty()) {
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "and has no children - must be true\n";
            }
            return;
        }

        NNFNode_AND * const andNode = new NNFNode_AND();

        bool contradiction = false;

        pc_list<goal*>::const_iterator goalItr = goals->begin();
        const pc_list<goal*>::const_iterator goalEnd = goals->end();

        for (int ci = 1; goalItr != goalEnd; ++goalItr, ++ci) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "and node child " << ci << endl;
            }
            nnfCollectDebugIndent += 2;
            (*goalItr)->visit(this);
            nnfCollectDebugIndent -= 2;
            pair<NNFNode*, bool> oldBack;
            justCreated.get_result(oldBack);
            if (oldBack.first) {
                andNode->addChild(oldBack.first);
            } else {
                if ((contradiction = !oldBack.second)) break;
            }            
        }

        if (contradiction) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "and has a child that must be false so must, itself, be false\n";
            }
            delete andNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            return;
        }

        if (andNode->empty()) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "and has no possibly untrue children - must be true\n";
            }
            delete andNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
            return;
        }
        
        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "and could evaluate to either true or false\n";
        }
        
        justCreated.push_back(pair<NNFNode*,bool>(andNode,true));
        
    }
    
    virtual void visit_disj_goal(disj_goal * p) {
        const goal_list * goals = p->getGoals();
        if (goals->empty()) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "or has no children - must be false\n";
            }
            
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            return;
        }

        NNFNode_OR * const orNode = new NNFNode_OR();

        bool tautology = false;

        pc_list<goal*>::const_iterator goalItr = goals->begin();
        const pc_list<goal*>::const_iterator goalEnd = goals->end();

        for (; goalItr != goalEnd; ++goalItr) {
            nnfCollectDebugIndent += 2;
            (*goalItr)->visit(this);
            nnfCollectDebugIndent -= 2;
            pair<NNFNode*, bool> oldBack;
            justCreated.get_result(oldBack);
            if (oldBack.first) {
                orNode->addChild(oldBack.first);
            } else {
                if ((tautology = oldBack.second)) break;
            }            
        }

        if (tautology) {
            delete orNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
            return;
        }

        if (orNode->empty()) {
            delete orNode;
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            return;
        }
        justCreated.push_back(pair<NNFNode*,bool>(orNode,true));

    }

    virtual void visit_imply_goal(imply_goal * p) {
        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "Implication\n";
        }
        
        nnfCollectDebugIndent += 2;
        p->getAntecedent()->visit(this);
        nnfCollectDebugIndent -= 2;
        
        pair<NNFNode*, bool> lhsBack;
        justCreated.get_result(lhsBack);
        
        NNFNode* lhs = lhsBack.first;
        const bool lhsdeterminedToBe = lhsBack.second;
        

        if (!lhs) {
            if (lhsdeterminedToBe) {
                if (nnfCollectDebug) {
                    cout << string(nnfCollectDebugIndent, ' ') << "Antecedent of implication is true: simplifying to just the consequent\n";
                }                                
                p->getConsequent()->visit(this); // A => B && A = true  =  B
                return;
            } else {
                if (nnfCollectDebug) {
                    cout << string(nnfCollectDebugIndent, ' ') << "Antecedent of implication is false: ex falso quodlibet, so can skip consequent and assume truth\n";
                }
                justCreated.push_back(pair<NNFNode*,bool>(0,true)); // A => B && A = false   = true
                return;
            }
        }

        nnfCollectDebugIndent += 2;
        p->getConsequent()->visit(this);
        nnfCollectDebugIndent += 2;
        
        pair<NNFNode*, bool> rhsBack;
        justCreated.get_result(rhsBack);
        
        NNFNode* rhs = rhsBack.first;
        const bool rhsdeterminedToBe = rhsBack.second;
        

        if (!rhs) {
            if (rhsdeterminedToBe) {
                if (nnfCollectDebug) {
                    cout << string(nnfCollectDebugIndent, ' ') << "Consequent of implication is true, so implication is true\n";
                }
                delete lhs;
                justCreated.push_back(pair<NNFNode*,bool>(0,true)); // anything => true  = true
                return;
            } else {
                if (nnfCollectDebug) {
                    cout << string(nnfCollectDebugIndent, ' ') << "Consequent of implication is false, so replacing with negation of the antecedent\n";
                }
                NNFNode * negated = lhs->negate();
                delete lhs;
                justCreated.push_back(pair<NNFNode*,bool>(negated,true)); // anything => true  = !anything
                return;
            }
        }

        NNFNode_OR * impliesNode = new NNFNode_OR();
        NNFNode * negated = lhs->negate();
        delete lhs;
        impliesNode->addChild(negated); //  A => B
        impliesNode->addChild(rhs);     //  = (!A) || B

        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "Returning implication in the form ¬A v B\n";
        }
        
        justCreated.push_back(pair<NNFNode*,bool>(impliesNode,true));
    }


    virtual void visit_timed_goal(timed_goal * p) {
        currTS.push_back(p->getTime());
        p->getGoal()->visit(this);
        currTS.pop_back();
    }
    
    virtual void visit_neg_goal(neg_goal * p) {    
        if (nnfCollectDebug) {
            cout << string(nnfCollectDebugIndent, ' ') << "negation goal\n";
        }
        nnfCollectDebugIndent += 2;
        p->getGoal()->visit(this);
        nnfCollectDebugIndent += 2;
        
        pair<NNFNode*, bool> posBack;
        justCreated.get_result(posBack);
        
        if (posBack.first) {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "Negating child, and returning\n";
            }
            justCreated.push_back(pair<NNFNode*,bool>(posBack.first->negate(),true));
            delete posBack.first;
        } else {
            if (nnfCollectDebug) {
                cout << string(nnfCollectDebugIndent, ' ') << "Flipping truth value of child with known value - is now ";
                if (posBack.second) {
                    cout << "false\n";
                } else {
                    cout << "true\n";
                }
            }
            justCreated.push_back(pair<NNFNode*,bool>(0,!posBack.second));
        }
    }


};

class NNFStaticReducer : public NNFVisitor {

protected:

    vector<pair<bool,bool> > * staticLiterals;
    vector<pair<bool,bool> > * staticNumerics;;
    list<pair<bool,bool> > justCreated;

    NNFStaticReducer() : staticLiterals(0) {};


public:

    NNFStaticReducer(vector<pair<bool,bool> > & s, const bool & b) : staticLiterals(0), staticNumerics(0) {
        if (b) {
            staticNumerics = &s;
        } else {
            staticLiterals = &s;
        }
    };

    NNFStaticReducer(vector<pair<bool,bool> > & lit,vector<pair<bool,bool> > & num) : staticLiterals(&lit), staticNumerics(&num) {};


    virtual pair<NNFNode*,bool> pruneStatic(NNFNode * const root) {
        root->visit(this);
        pair<bool,bool> answer = justCreated.back();
        if (answer.first) {
            delete root;
            return pair<NNFNode*,bool>(0,answer.second);
        } else {
            return pair<NNFNode*,bool>(root,answer.second);
        }
    };

    virtual void visit_AND(NNFNode_AND * andNode) {
        NNFContainerNode::iterator childItr = andNode->begin();
        const NNFContainerNode::iterator childEnd = andNode->end();

        bool contradiction = false;

        while (childItr != childEnd) {
            (*childItr)->visit(this);            
            if (justCreated.back().first) {
                if (!justCreated.back().second) {
                    contradiction = true;
                    break;
                } else {
                    childItr = andNode->eraseChild(childItr);
                }
            } else {
                ++childItr;
            }
            justCreated.pop_back();
        }

        if (contradiction) {
            justCreated.push_back(pair<bool,bool>(true,false));
        } else if (andNode->empty()) {
            justCreated.push_back(pair<bool,bool>(true,true));
        } else {
            justCreated.push_back(pair<bool,bool>(false,true));
        }
    }

    virtual void visit_OR(NNFNode_OR * orNode) {

        NNFContainerNode::iterator childItr = orNode->begin();
        const NNFContainerNode::iterator childEnd = orNode->end();

        bool tautology = false;

        while (childItr != childEnd) {
            (*childItr)->visit(this);    
            if (justCreated.back().first) {
                if (justCreated.back().second) {
                    tautology = true;
                    break;
                } else {
                    childItr = orNode->eraseChild(childItr);
                }
            } else {
                ++childItr;
            }
            justCreated.pop_back();
        }

        if (tautology) {
            justCreated.push_back(pair<bool,bool>(true,true));
        } else if (orNode->empty()) {
            justCreated.push_back(pair<bool,bool>(true,false));
        } else {
            justCreated.push_back(pair<bool,bool>(false,true));
        }

    }
    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
        if (!staticLiterals) {
            justCreated.push_back(pair<bool,bool>(false,true));
        } else {
            const int currLitID = litNode->getLiteral()->getStateID();
            assert(currLitID != -1);
            if ((*staticLiterals)[currLitID].first) {
                justCreated.push_back(pair<bool,bool>(true,!(*staticLiterals)[currLitID].second));
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
            }
        }
    }
    virtual void visit_Literal(NNFNode_Literal * litNode) {
        if (!staticLiterals) {
            justCreated.push_back(pair<bool,bool>(false,true));
        } else {
            const int currLitID = litNode->getLiteral()->getStateID();
            assert(currLitID != -1);
            if ((*staticLiterals)[currLitID].first) {
    //            cout << "In NNF, " << *(litNode->getLiteral()) << " is static and " <<staticLiterals[currLitID].second << "\n";
                justCreated.push_back(pair<bool,bool>(true,(*staticLiterals)[currLitID].second));
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
            }
        }
    }

    virtual void visit_NOT_Numeric(NNFNode_NOT_Numeric *) {
        justCreated.push_back(pair<bool,bool>(false,true));
    }
    virtual void visit_Numeric(NNFNode_Numeric *) {
        justCreated.push_back(pair<bool,bool>(false,true));
    }
    virtual void visit_RPGNumeric(NNFNode_RPGNumeric * n) {
        if (!staticNumerics) {
            justCreated.push_back(pair<bool,bool>(false,true));
        } else {
            const int currPreID = n->getPre();
            if ((*staticNumerics)[currPreID].first) {
                justCreated.push_back(pair<bool,bool>(true,(*staticNumerics)[currPreID].second));
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
            }
        }
    }


};


class NNFCollectRequiredFacts : public NNFPartialVisitor {

protected:

    set<int> & mustBeTrue;
    set<int> & mustBeFalse;

public:

    NNFCollectRequiredFacts(set<int> & mbt, set<int> & mbf)
        : mustBeTrue(mbt), mustBeFalse(mbf) {
    }


    virtual void visit_OR(NNFNode_OR * orNode) {
        if (orNode->empty()) {
            return;
        }
        if (orNode->size() == 1) {
            NNFContainerNode::iterator childItr = orNode->begin();        
            (*childItr)->visit(this);
            return;
        }
        
        set<int> & properMBT = mustBeTrue;
        set<int> & properMBF = mustBeFalse;
        
        set<int> isectTrue;
        set<int> isectFalse;
        
        NNFContainerNode::iterator childItr = orNode->begin();
        const NNFContainerNode::iterator childEnd = orNode->end();
        
        mustBeTrue = isectTrue;
        mustBeFalse = isectFalse;
        
        (*childItr)->visit(this);
        
        ++childItr;
        
        for (; childItr != childEnd; ++childItr) {
            
            set<int> localTrue;
            set<int> localFalse;
            
            mustBeTrue = localTrue;
            mustBeFalse = localFalse;
            
            (*childItr)->visit(this);
            
            set<int> resTrue;
            set<int> resFalse;
            
            std::set_intersection(localTrue.begin(), localTrue.end(), isectTrue.begin(), isectTrue.end(), std::insert_iterator<set<int> >(resTrue, resTrue.begin()));
            std::set_intersection(localFalse.begin(), localFalse.end(), isectFalse.begin(), isectFalse.end(), std::insert_iterator<set<int> >(resFalse, resFalse.begin()));
            
            resTrue.swap(isectTrue);
            resFalse.swap(isectFalse);
            
        }
        
        mustBeTrue = properMBT;
        mustBeFalse = properMBF;
        
        mustBeTrue.insert(isectTrue.begin(), isectTrue.end());
        mustBeFalse.insert(isectFalse.begin(), isectFalse.end());
        
    }
    
    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
        mustBeFalse.insert(litNode->getLiteral()->getStateID());
    }
    
    virtual void visit_Literal(NNFNode_Literal * litNode) {
        mustBeTrue.insert(litNode->getLiteral()->getStateID());
    }
};


const bool simplifyDebug = false;
int simplifyIndent = 0;

class NNFSimplifyDownwards : public NNFVisitor {

protected:

    bool merged;    
    list<bool> deleteChild;

    static NNFNode* newRoot;    
    static list<NNFContainerNode*> unaryParent;
public:

    const bool & beenMerged() const { return merged; };

    NNFSimplifyDownwards() : merged(false) {};

    virtual void visit_AND(NNFNode_AND * andNode);
    virtual void visit_OR(NNFNode_OR * orNode);
    
    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * n)
    {
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << "¬" << *(n->getLiteral()) << endl;
        }
        deleteChild.push_back(false);
    };
    
    virtual void visit_Literal(NNFNode_Literal * n)
    {
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << *(n->getLiteral()) << endl;
        }
        deleteChild.push_back(false);
    };
    
    virtual void visit_NOT_Numeric(NNFNode_NOT_Numeric * n)
    {
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << "¬" << n->getPre() << endl;
        }        
        deleteChild.push_back(false);
    };
    
    virtual void visit_Numeric(NNFNode_Numeric * n)
    {
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << n->getPre() << endl;
        }                
        deleteChild.push_back(false);
    };
    
    virtual void visit_RPGNumeric(NNFNode_RPGNumeric * n)
    {
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << RPGBuilder::getNumericPreTable()[n->getPre()] << endl;
        }        
        
        deleteChild.push_back(false);
    };


    virtual NNFNode* simplify(NNFNode * root) {
        simplifyIndent = 1;
        
        if (simplifyDebug) {
            cout << "Simplifying:\n";
        }
        
        newRoot = 0;
        unaryParent.clear();
        root->visit(this);
        if (deleteChild.back()) {
            delete root;
            root = 0;
        }
        if (newRoot) root = newRoot;
        return root;
    };

};

NNFNode* NNFSimplifyDownwards::newRoot;    
list<NNFContainerNode*> NNFSimplifyDownwards::unaryParent;
    
class NNFMergeANDDownwards : public NNFSimplifyDownwards {


protected:

    NNFNode_AND * parent;

public:
    NNFMergeANDDownwards(NNFNode_AND * a) : parent(a) {};
    
    virtual void visit_AND(NNFNode_AND * andNode) {

        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << COLOUR_light_blue << "and node within and node\n" << COLOUR_default;
        }
        
        simplifyIndent += 2;
        
        list<NNFNode*> children;
        andNode->stealChildren(children);

        unaryParent.push_back(parent);

        list<NNFNode*>::iterator childItr = children.begin();
        const list<NNFNode*>::iterator childEnd = children.end();

        for (; childItr != childEnd; ++childItr) {
            NNFMergeANDDownwards localMerger(parent);
            (*childItr)->visit(&localMerger);
            if (localMerger.beenMerged()) {
                delete *childItr;
            } else {
                const bool deleteIt = localMerger.deleteChild.back();
                localMerger.deleteChild.pop_back();
                if (deleteIt) {
                    delete *childItr;
                } else {
                    parent->addChild(*childItr);
                }
            }
            
        }

        unaryParent.pop_back();

        merged = true;
        
        simplifyIndent -= 2;
    }

};

class NNFMergeORDownwards : public NNFSimplifyDownwards {

protected:

    NNFNode_OR * parent;

public:
    NNFMergeORDownwards(NNFNode_OR * a) : parent(a) {};
    
    virtual void visit_OR(NNFNode_OR * orNode) {
        
        if (simplifyDebug) {
            cout << string(simplifyIndent, ' ') << COLOUR_light_blue << "or node within or node\n" << COLOUR_default;
        }
        
        simplifyIndent += 2;
        list<NNFNode*> children;
        orNode->stealChildren(children);

        unaryParent.push_back(parent);

        list<NNFNode*>::iterator childItr = children.begin();
        const list<NNFNode*>::iterator childEnd = children.end();

        for (; childItr != childEnd; ++childItr) {
            NNFMergeORDownwards localMerger(parent);
            (*childItr)->visit(&localMerger);
            if (localMerger.beenMerged()) {
                delete *childItr;
            } else {
                const bool deleteIt = localMerger.deleteChild.back();
                localMerger.deleteChild.pop_back();
                if (deleteIt) {
                    delete *childItr;
                } else {
                    parent->addChild(*childItr);
                }
            }
            
        }

        unaryParent.pop_back();

        merged = true;
        
        simplifyIndent -= 2;
    }

};

void NNFSimplifyDownwards::visit_AND(NNFNode_AND * andNode) {
    if (simplifyDebug) {
        cout << string(simplifyIndent, ' ') << "and node\n";
    }
        
    simplifyIndent += 2;
    
    list<NNFNode*> children;
    andNode->stealChildren(children);

    unaryParent.push_back(andNode);

    list<NNFNode*>::iterator childItr = children.begin();
    const list<NNFNode*>::iterator childEnd = children.end();

    for (; childItr != childEnd; ++childItr) {
        NNFMergeANDDownwards localMerger(andNode);
        (*childItr)->visit(&localMerger);
        if (localMerger.beenMerged()) {
            delete *childItr;
        } else {
            const bool deleteIt = localMerger.deleteChild.back();
            localMerger.deleteChild.pop_back();
            if (deleteIt) {
                delete *childItr;
            } else {
                andNode->addChild(*childItr);
            }
        }
        
    }

    unaryParent.pop_back();

    if (andNode->empty()) {
        deleteChild.push_back(true);
    } else if (andNode->size() > 1) {
        deleteChild.push_back(false);
    } else {
        list<NNFNode*> children;
        andNode->stealChildren(children);
    
        NNFNode * const onlyChild = children.front();

        if (unaryParent.empty()) { // root node
            newRoot = onlyChild;
        } else {
            unaryParent.back()->addChild(onlyChild);
        }
        deleteChild.push_back(true);
    }
    merged = false;
    
    simplifyIndent -= 2;
}

void NNFSimplifyDownwards::visit_OR(NNFNode_OR* orNode) {
    if (simplifyDebug) {
        cout << string(simplifyIndent, ' ') << "or node\n";
    }
    simplifyIndent += 2;
    list<NNFNode*> children;
    orNode->stealChildren(children);

    unaryParent.push_back(orNode);

    list<NNFNode*>::iterator childItr = children.begin();
    const list<NNFNode*>::iterator childEnd = children.end();

    for (; childItr != childEnd; ++childItr) {
        NNFMergeORDownwards localMerger(orNode);
        (*childItr)->visit(&localMerger);
        if (localMerger.beenMerged()) {
            delete *childItr;
        } else {
            const bool deleteIt = localMerger.deleteChild.back();
            localMerger.deleteChild.pop_back();
            if (deleteIt) {
                delete *childItr;
            } else {
                orNode->addChild(*childItr);
            }
        }
        
    }

    unaryParent.pop_back();

    if (orNode->empty()) {
        deleteChild.push_back(true);
    } else if (orNode->size() > 1) {
        deleteChild.push_back(false);
    } else {
        list<NNFNode*> children;
        orNode->stealChildren(children);
    
        NNFNode * const onlyChild = children.front();

        if (unaryParent.empty()) { // root node
            newRoot = onlyChild;
        } else {
            unaryParent.back()->addChild(onlyChild);
        }
        deleteChild.push_back(true);
    }
    merged = false;
    simplifyIndent -= 2;
}



class NNFPruneUnreachable : public NNFStaticReducer {

protected:

    LiteralSet & initialState;

public:

    NNFPruneUnreachable(LiteralSet & i) : initialState(i) {};

    virtual pair<NNFNode*,bool> pruneUnreachable(NNFNode * const root) {
        root->visit(this);
        pair<bool,bool> answer = justCreated.back();
        if (answer.first) {
            delete root;
            return pair<NNFNode*,bool>(0,answer.second);
        } else {
            return pair<NNFNode*,bool>(root,answer.second);
        }
    };

    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {

        Literal* const currLit = litNode->getLiteral();

        const pair<bool,bool> & currStatic = RPGBuilder::isStatic(currLit);

        if (currStatic.first) {
            if (currStatic.second) {
                justCreated.push_back(pair<bool,bool>(true,false));
                return;
            } else {
                justCreated.push_back(pair<bool,bool>(true,true));
                return;
            }
        }
        const int fID = currLit->getStateID();
        assert(fID != -1);
        
        if (initialState.find(currLit) == initialState.end()) {            
            if (RPGBuilder::getEffectsToActions()[fID].empty()) {
                justCreated.push_back(pair<bool,bool>(true,true));
                return;
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
                return;
            }
        } else {
            if (RPGBuilder::getNegativeEffectsToActions()[fID].empty()) {
                justCreated.push_back(pair<bool,bool>(true,false));
                return;
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
                return;

            }
        }
    }

    virtual void visit_Literal(NNFNode_Literal * litNode) {
        Literal* const currLit = litNode->getLiteral();

        const pair<bool,bool> & currStatic = RPGBuilder::isStatic(currLit);

        if (currStatic.first) {
            if (!currStatic.second) {
                justCreated.push_back(pair<bool,bool>(true,false));
                return;
            } else {
                justCreated.push_back(pair<bool,bool>(true,true));
                return;
            }
        }
        const int fID = currLit->getStateID();
        assert(fID != -1);
                        
        if (initialState.find(currLit) == initialState.end()) {
            if (RPGBuilder::getEffectsToActions()[fID].empty()) {
                justCreated.push_back(pair<bool,bool>(true,false));
                return;
            } else {
                justCreated.push_back(pair<bool,bool>(false,true));
                return;
            }
        } else {
            justCreated.push_back(pair<bool,bool>(false,true));
            return;
        }
    }


};

class NNFUtils::NNFRPGNumericSubstituter : public NNFVisitor {

protected:

    RPGBuilder::BuildingNumericPreconditionData & commonData;
    list<pair<NNFNode*,bool> > justCreated;


public:

    NNFRPGNumericSubstituter(RPGBuilder::BuildingNumericPreconditionData & c) : commonData(c) {};

    virtual pair<NNFNode*,bool> substitute(NNFNode * const root) {
        root->visit(this);
        pair<NNFNode*,bool> answer = justCreated.back();
        if (answer.first) {
            if (answer.first != root) delete root;
            return answer;
        } else {
            delete root;
            return answer;
        }
    };

    virtual void visit_AND(NNFNode_AND * andNode) {
        NNFContainerNode::iterator childItr = andNode->begin();
        const NNFContainerNode::iterator childEnd = andNode->end();

        bool contradiction = false;

        while (childItr != childEnd) {
            (*childItr)->visit(this);            
            if (justCreated.back().first) {
                if (justCreated.back().first != *childItr) {
                    delete *childItr;
                    *childItr = justCreated.back().first;
                }
                ++childItr;
            } else {
                if (!justCreated.back().second) {
                    contradiction = true;
                    break;
                } else {
                    childItr = andNode->eraseChild(childItr);
                }
                
            }
            justCreated.pop_back();
        }

        if (contradiction) {
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
        } else if (andNode->empty()) {
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
        } else {
            justCreated.push_back(pair<NNFNode*,bool>(andNode,true));
        }
    }

    virtual void visit_OR(NNFNode_OR * orNode) {
        NNFContainerNode::iterator childItr = orNode->begin();
        const NNFContainerNode::iterator childEnd = orNode->end();

        bool tautology = false;

        while (childItr != childEnd) {
            (*childItr)->visit(this);            
            if (justCreated.back().first) {
                if (justCreated.back().first != *childItr) {
                    delete *childItr;
                    *childItr = justCreated.back().first;
                }
                ++childItr;
            } else {
                if (justCreated.back().second) {
                    tautology = true;
                    break;
                } else {
                    childItr = orNode->eraseChild(childItr);
                }
                
            }
            justCreated.pop_back();
        }

        if (tautology) {
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
        } else if (orNode->empty()) {
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
        } else {
            justCreated.push_back(pair<NNFNode*,bool>(orNode,true));
        }

    }
    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
        justCreated.push_back(pair<NNFNode*,bool>(litNode,true));
    }
    virtual void visit_Literal(NNFNode_Literal * litNode) {
        justCreated.push_back(pair<NNFNode*,bool>(litNode,true));
    }

    virtual void processNumeric(RPGBuilder::NumericPrecondition & justOne, const VAL::time_spec & ts) {
        
        list<int> conjunctiveDest;
        list<int> disjunctiveDest;

        const bool evaluateOkay = RPGBuilder::processPrecondition(commonData, justOne, conjunctiveDest, disjunctiveDest, -3, Planner::E_AT);
    
        if (!evaluateOkay) {
            justCreated.push_back(pair<NNFNode*,bool>(0,false));
            return;            
        }
        if (!conjunctiveDest.empty()) {
            
            assert(disjunctiveDest.empty());
            if (conjunctiveDest.size() == 1) {
                NNFNode * newNode = new NNFNode_RPGNumeric(conjunctiveDest.front(),ts);
                justCreated.push_back(pair<NNFNode*,bool>(newNode, true));
            } else {                
                NNFNode_AND* const conj = new NNFNode_AND();
                
                conj->addChild(new NNFNode_RPGNumeric(conjunctiveDest.front(),ts));
                conj->addChild(new NNFNode_RPGNumeric(conjunctiveDest.back(),ts));
                
                justCreated.push_back(pair<NNFNode*,bool>(conj,true));                
            }
            
        } else if (!disjunctiveDest.empty()) {
            
            assert(disjunctiveDest.size() == 2);
            NNFNode_OR* const disj = new NNFNode_OR();
            
            disj->addChild(new NNFNode_RPGNumeric(disjunctiveDest.front(),ts));
            disj->addChild(new NNFNode_RPGNumeric(disjunctiveDest.back(),ts));
            
            justCreated.push_back(pair<NNFNode*,bool>(disj,true));
        
        } else {
            justCreated.push_back(pair<NNFNode*,bool>(0,true));
        } 
    
    }

    virtual void visit_Numeric(NNFNode_Numeric * r) {

        processNumeric(*(r->getPre()),r->getTS());

    }

    virtual void visit_NOT_Numeric(NNFNode_NOT_Numeric * r) {

        RPGBuilder::NumericPrecondition tmp(*(r->getPre()));
        tmp.polarity = !tmp.polarity;
        
        processNumeric(tmp,r->getTS());
    }

    virtual void visit_RPGNumeric(NNFNode_RPGNumeric *r) {
        justCreated.push_back(pair<NNFNode*,bool>(r,true));
    }


};


class NNFUtils::NNFMarkRPGNumericDesirable : public NNFPartialVisitor {

protected:
    
    RPGBuilder::BuildingNumericPreconditionData & commonData;
    const bool desirable;
    const bool undesirable;
    
public:

    NNFMarkRPGNumericDesirable(RPGBuilder::BuildingNumericPreconditionData & c, const bool & d, const bool & u) : commonData(c), desirable(d), undesirable(u) {};

    
    virtual void visit_RPGNumeric(NNFNode_RPGNumeric *r) {
        if (desirable) {
            commonData.desirable.insert(r->getPre());
        } else {
            commonData.undesirable.insert(r->getPre());
        }
        
        if (undesirable) {
            commonData.undesirable.insert(r->getPre());
        }
    }


};




pair<NNFNode*,bool> NNFUtils::buildNNF(VAL::TypeChecker * tc, FastEnvironment * fe, VAL::goal * g) {    
    NNFGoalCollector c(g,fe,tc);
    return c.makeNNF();
};


pair<NNFNode*,bool> NNFUtils::pruneStaticLiterals(NNFNode* const root,vector<pair<bool,bool> > & staticLiterals) {
    NNFStaticReducer c(staticLiterals,false);
    return c.pruneStatic(root);
};

pair<NNFNode*,bool> NNFUtils::pruneStaticNumerics(NNFNode* const root,vector<pair<bool,bool> > & staticNumerics) {
    NNFStaticReducer c(staticNumerics,true);
    return c.pruneStatic(root);
};


pair<NNFNode*,bool> NNFUtils::pruneUnreachable(NNFNode* const root,LiteralSet & initialState) {
    NNFPruneUnreachable c(initialState);
    return c.pruneUnreachable(root);
};

pair<NNFNode*,bool> NNFUtils::substituteRPGNumerics(NNFNode* const root,const bool & desirable,const bool & undesirable,RPGBuilder::BuildingNumericPreconditionData & commonData) {
    NNFRPGNumericSubstituter c(commonData);
    
    const pair<NNFNode*,bool> toReturn(c.substitute(root));
    
    if (toReturn.first) {
        NNFMarkRPGNumericDesirable c(commonData, desirable, undesirable);
        toReturn.first->visit(&c);
    }
    
    return toReturn;
    
};

void NNFUtils::findFactsDefinitelyNeeded(NNFNode * const root, set<int> & mustBeTrue, set<int> & mustBeFalse) {
    NNFCollectRequiredFacts c(mustBeTrue, mustBeFalse);
    root->visit(&c);
}

int NNF_Flat::currCell = -1;

NNF_Flat::NNF_Flat(const list<pair<int,int> > & usr, const list<pair<Cell, int> > & cellAndParent, const list<bool> & r)
   : unsatSize(usr.size()), unsatReset(new int[unsatSize]), unsat(new int[unsatSize]), fragilityTrue(new int[unsatSize]), fragilityFalse(new int[unsatSize]),
     cellIsAnd(new bool[unsatSize]), cellCount(cellAndParent.size()+unsatSize), parentID(new int[cellCount]), cells(new Cell[cellCount]), resetSize(unsatSize * sizeof(int))  {

    list<pair<int,int> >::const_iterator usItr = usr.begin();
    const list<pair<int,int> >::const_iterator usEnd = usr.end();

    for (int i = 0; usItr != usEnd; ++usItr, ++i) {
        unsatReset[i] = usItr->first;
        parentID[i] = usItr->second;
    }

    list<pair<Cell, int> >::const_iterator cellItr = cellAndParent.begin();
    const list<pair<Cell, int> >::const_iterator cellEnd = cellAndParent.end();
    
    for (int i = unsatSize; cellItr != cellEnd; ++cellItr, ++i) {
        cells[i] = cellItr->first;
        parentID[i] = cellItr->second;
    }

    assert(r.size() == ((unsigned int) unsatSize));
    
    list<bool>::const_iterator caItr = r.begin();
    const list<bool>::const_iterator caEnd = r.end();
    
    for (int i = 0; caItr != caEnd; ++caItr, ++i) {
        cellIsAnd[i] = *caItr;
    }
    

    reset();

};


void NNF_Flat::write(ostream & o) const {
    list<pair<int,int> > printStack;
    printStack.push_back(pair<int,int>(0,0));
    
    while (!printStack.empty()) {
        const int cellIndex = printStack.front().first;
        const int indent = printStack.front().second;
        printStack.pop_front();

        if (cells[cellIndex].isCell()) {
            for (int i = 0; i < indent; ++i) o << "    ";
            if (!cells[cellIndex].polarity) o << "¬";
            if (cells[cellIndex].lit) o << *(cells[cellIndex].lit);
            const int numID = cells[cellIndex].num;
            if (numID != -1) o << RPGBuilder::getNumericPreTable()[numID];
            o << "\n";
        } else {
            for (int i = 0; i < indent; ++i) o << "    ";
            o << "[" << unsatReset[cellIndex] << "]\n";
            for (int i = cellIndex + 1; i < cellCount; ++i) {
                if (parentID[i] == cellIndex) {
                    printStack.push_front(pair<int,int>(i,indent+1));
                }
            }
        }
    }
};

ostream & operator <<(ostream & o, const NNF_Flat & f) {
    f.write(o);
    return o;
};

class NNFFlattener : public NNFVisitor {

protected:

    list<pair<int,int> > unsat;
    list<pair<NNF_Flat::Cell, int> > cells;
    list<bool> cellIsAnd;
    int currParent;
    int leafCount;
    int nodeCount;
    list<bool> childDefaultSatisfied;

    
public:

    NNFFlattener() : currParent(-1),leafCount(0),nodeCount(0) {};

    virtual NNF_Flat * flatten(NNFNode * const root) {
        root->visit(this);

        if (!leafCount) {
            return 0;
        }

        if (!nodeCount) {
            cells.front().second = 0;
            if (cells.front().first.polarity) {
                unsat.push_back(make_pair(1,-1));
                cellIsAnd.push_back(true);
            } else {
                unsat.push_back(make_pair(0,-1));
                cellIsAnd.push_back(true);
            }
        }

        return new NNF_Flat(unsat,cells,cellIsAnd);
    };

    virtual void visit_AND(NNFNode_AND * andNode) {
        
        const int parentOfThis = currParent;

        unsat.push_back(make_pair(andNode->size(),parentOfThis));
        cellIsAnd.push_back(true);
        
        int & localunsat = unsat.back().first;
        const int thisID = nodeCount++;

        currParent = thisID;

        NNFContainerNode::iterator childItr = andNode->begin();
        const NNFContainerNode::iterator childEnd = andNode->end();

        for (; childItr != childEnd; ++childItr) {
            (*childItr)->visit(this);
            if (childDefaultSatisfied.back()) {
                --localunsat;
            }
            childDefaultSatisfied.pop_back();
        }
        childDefaultSatisfied.push_back(localunsat == 0);

        currParent = parentOfThis;
    }

    virtual void visit_OR(NNFNode_OR * orNode) {
        
        const int parentOfThis = currParent;

        unsat.push_back(make_pair(1,parentOfThis));
        cellIsAnd.push_back(false);
        
        int & localunsat = unsat.back().first;
        const int thisID = nodeCount++;

        currParent = thisID;

        NNFContainerNode::iterator childItr = orNode->begin();
        const NNFContainerNode::iterator childEnd = orNode->end();

        for (; childItr != childEnd; ++childItr) {
            (*childItr)->visit(this);
            if (childDefaultSatisfied.back()) {
                --localunsat;
            }
            childDefaultSatisfied.pop_back();
        }
        childDefaultSatisfied.push_back(localunsat <= 0);

        currParent = parentOfThis;

    }
    virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
        cells.push_back(make_pair(NNF_Flat::Cell(litNode->getLiteral(),false), currParent));
        childDefaultSatisfied.push_back(true);
        ++leafCount;
    }
    virtual void visit_Literal(NNFNode_Literal * litNode) {
        cells.push_back(make_pair(NNF_Flat::Cell(litNode->getLiteral(),true), currParent));
        childDefaultSatisfied.push_back(false);
        ++leafCount;
    }


    virtual void visit_Numeric(NNFNode_Numeric * r) {
        cout << "Error - Numeric Nodes should have been subsituted with RPG Numeric Nodes by now\n";
        assert(false);
    }

    virtual void visit_NOT_Numeric(NNFNode_NOT_Numeric * r) {
        cout << "Error - NOT Numeric Nodes should have been subsituted with NOT RPG Numeric Nodes by now\n";
        assert(false);
    }

    virtual void visit_RPGNumeric(NNFNode_RPGNumeric *r) {
        cells.push_back(make_pair(NNF_Flat::Cell(r->getPre(),true), currParent));
        childDefaultSatisfied.push_back(false);
        ++leafCount;
    }


};




NNF_Flat * NNFUtils::flattenNNF(NNFNode* const root) {
    NNFFlattener c;
    return c.flatten(root);
};

NNFNode* NNFUtils::simplifyNNF(NNFNode* const root) {
    NNFSimplifyDownwards c;
    return c.simplify(root);
};

int nnfWriteIndent = 0;

ostream& NNFNode_AND::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << "and:\n";
    nnfWriteIndent += 2;
    
    list<NNFNode*>::const_iterator cItr = children.begin();
    const list<NNFNode*>::const_iterator cEnd = children.end();
    
    for (; cItr != cEnd; ++cItr) (*cItr)->write(o);
    
    nnfWriteIndent -= 2;
    
    return o;
}

ostream& NNFNode_OR::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << "or:\n";
    nnfWriteIndent += 2;
    
    list<NNFNode*>::const_iterator cItr = children.begin();
    const list<NNFNode*>::const_iterator cEnd = children.end();
    
    for (; cItr != cEnd; ++cItr) (*cItr)->write(o);
    
    nnfWriteIndent -= 2;
    return o;
}

ostream& NNFNode_Literal::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << *lit << endl;
    return o;
}

ostream& NNFNode_NOT_Literal::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << "¬" << *lit << endl;
    return o;
}

ostream& NNFNode_Numeric::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << *pre << endl;
    return o;
    
}

ostream& NNFNode_NOT_Numeric::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << "¬" << *pre << endl;
    return o;
}


ostream& NNFNode_RPGNumeric::write(ostream& o)
{
    o << string(nnfWriteIndent, ' ') << RPGBuilder::getNumericPreTable()[pre] << endl;
    return o;
    
}


};
