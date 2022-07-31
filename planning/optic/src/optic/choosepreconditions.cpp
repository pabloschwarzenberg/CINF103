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

#include "choosepreconditions.h"
#include "NNF.h"

namespace Planner {
    
const bool chooseDebug = false;
    
class ChoosePreconditions {
    
public:
    
    class CommonSatisfactionVisitor : public NNFVisitorAfterRPGNumerics {


    protected:

        ChoosePreconditions * const parent;
        
        virtual void visit_AND_internal(NNFContainerNode * andNode) {
            NNFContainerNode::iterator childItr = andNode->begin();
            const NNFContainerNode::iterator childEnd = andNode->end();
            
            for (;childItr != childEnd; ++childItr) {
                (*childItr)->visit(this);
                if (!parent->wasSatisfied.back()) {
                    break;
                }
            }
        }
        
        virtual void visit_OR_internal(NNFContainerNode * orNode) {
            double bestSuccTimeSeen = DBL_MAX;
            bool anyTrueSeen = false;
            set<int> bestChosenPropositions;
            set<int> bestChosenNegativePropositions;
            set<int> bestChosenNumerics;
            
            if (chooseDebug) {
                cout << "Or node:\n";
            }
            
            NNFContainerNode::iterator childItr = orNode->begin();
            const NNFContainerNode::iterator childEnd = orNode->end();
            
            for (;childItr != childEnd; ++childItr) {
                parent->chosenPropositions.push_back(set<int>());
                parent->chosenNegativePropositions.push_back(set<int>());
                parent->chosenNumerics.push_back(set<int>());
                parent->availableAtTime.push_back(0.0);
                parent->wasSatisfied.push_back(true);
                
                (*childItr)->visit(this);
                
                if (parent->wasSatisfied.back()) {
                    if (chooseDebug) {
                        cout << "- Child was true\n";
                    }
                    anyTrueSeen = true;
                    if (parent->availableAtTime.back() < bestSuccTimeSeen) {
                        bestSuccTimeSeen = parent->availableAtTime.back();
                        bestChosenPropositions.swap(parent->chosenPropositions.back());
                        bestChosenNegativePropositions.swap(parent->chosenNegativePropositions.back());
                        bestChosenNumerics.swap(parent->chosenNumerics.back());
                        if (chooseDebug) {
                            cout << "Best numerics now:";
                            set<int>::const_iterator sItr = bestChosenNumerics.begin();
                            const set<int>::const_iterator sEnd = bestChosenNumerics.end();
                            
                            for (; sItr != sEnd; ++sItr) {
                                cout << " " << *sItr << ":" << RPGBuilder::getNumericPreTable()[*sItr];
                            }                                
                            cout << std::endl;
                        }
                        
                    }
                } else {
                    if (chooseDebug) {
                        cout << "- Child was false\n";
                    }
                }

                parent->chosenPropositions.pop_back();
                parent->chosenNegativePropositions.pop_back();
                parent->chosenNumerics.pop_back();
                parent->availableAtTime.pop_back();
                parent->wasSatisfied.pop_back();
                
                if (bestSuccTimeSeen == 0.0) {
                    break;
                }
            }
            
            if (!anyTrueSeen) {
                if (chooseDebug) {
                    cout << "No children were true, so Or node overall is false\n";
                }
                parent->wasSatisfied.back() = false;
                return;
            }

            parent->chosenPropositions.back().insert(bestChosenPropositions.begin(), bestChosenPropositions.end());
            parent->chosenNegativePropositions.back().insert(bestChosenNegativePropositions.begin(), bestChosenNegativePropositions.end());
            parent->chosenNumerics.back().insert(bestChosenNumerics.begin(), bestChosenNumerics.end());
            
            if (bestSuccTimeSeen > parent->availableAtTime.back()) {
                parent->availableAtTime.back() = bestSuccTimeSeen;
            }
            
        }
        
        virtual void visit_NOT_Literal_internal(const int & litID) {
            
            double atTime;
            
            const StateFacts::const_iterator fItr = parent->theState.first.find(litID);
            if (fItr != parent->theState.first.end()) {
                parent->wasSatisfied.back() = false;
                return;
            }
            
            #ifdef ENABLEDERIVED
            const set<int>::const_iterator f2Itr = parent->derivedState.find(litID);
            if (f2Itr != parent->derivedState.end()) {            
                parent->wasSatisfied.back() = false;
                return;            
            }
            #endif
        
            parent->chosenNegativePropositions.back().insert(litID);
        
            #ifdef ENABLEDERIVED
            if (DerivedPredicatesEngine::canBeDerived(litID)) {
                atTime = parent->negativeDerivedAtTime[litID];
            } else {        
            #endif
                const StateFacts::const_iterator rfItr = parent->theState.retired.find(litID);
                if (rfItr == parent->theState.retired.end()) {
                    // is false initially, and never deleted
                    return;
                }        
                atTime = parent->minTimestamps[fItr->second.negativeAvailableFrom.stepID] + 0.001;
            #ifdef ENABLEDERIVED
            }
            #endif
            
            if (atTime > parent->availableAtTime.back()) {
                parent->availableAtTime.back() = atTime;
            }
            
        }
        
        virtual void visit_Literal_internal(const int & litID) {
            double atTime;

            const StateFacts::const_iterator fItr = parent->theState.first.find(litID);
            if (fItr != parent->theState.first.end()) {
                parent->chosenPropositions.back().insert(litID);
                if (fItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::BEFORE) {
                    // true in the initial state
                    return;
                }
                atTime = parent->minTimestamps[fItr->second.availableFrom.stepID] + 0.001;
                if (atTime > parent->availableAtTime.back()) {
                    parent->availableAtTime.back() = atTime;
                }
                return;
            }
            
            #ifdef ENABLEDERIVED
            const set<int>::const_iterator f2Itr = parent->derivedState.find(litID);
            if (f2Itr != parent->derivedState.end()) {            
                parent->chosenPropositions.back().insert(litID);
                atTime = parent->derivedAtTime[litID];
                if (atTime > parent->availableAtTime.back()) {
                    parent->availableAtTime.back() = atTime;
                }                  
                return;
            }
            #endif
            
            parent->wasSatisfied.back() = false;
        }
        
        virtual void visit_RPGNumeric_internal(const int & preID) {
            const pair<map<int,pair<bool,double> >::iterator,bool> insPair = parent->numericPreTrueAtTime.insert(make_pair(preID,make_pair(true,0.0)));
            if (insPair.second) {
                RPGBuilder::RPGNumericPrecondition & numPre = RPGBuilder::getNumericPreTable()[preID];
                const bool isSatisfied = insPair.first->second.first = numPre.isSatisfiedWCalculate(parent->theState.secondMin, parent->theState.secondMax);
                if (chooseDebug) {
                    if (isSatisfied) {
                        cout << "Numeric precondition " << preID << " evaluation: is true\n";
                    } else {
                        cout << "Numeric precondition " << preID << " evaluation: is false\n";
                    }
                }
                if (isSatisfied) {
                    insPair.first->second.second = earliestPointForNumericPrecondition(numPre, parent->theState, parent->minTimestamps).toDouble();
                }
            }
            if (!insPair.first->second.first) {
                if (chooseDebug) {
                    cout << "Numeric precondition " << preID << " is false\n";
                }
                parent->wasSatisfied.back() = false;
                return;
            }
            parent->chosenNumerics.back().insert(preID);
            
            const double atTime = insPair.first->second.second;
            
            if (chooseDebug) {
                cout << "Numeric precondition " << preID << " is true at " << atTime << std::endl;
            }
            
            if (atTime > parent->availableAtTime.back()) {
                parent->availableAtTime.back() = atTime;
            }     
        }
        
        CommonSatisfactionVisitor(ChoosePreconditions * p)
            : parent(p) {
        }
        
    public:
                 
    };
        
    class SatisfyAPrecondition : public CommonSatisfactionVisitor {
    
    public:
    
        SatisfyAPrecondition(ChoosePreconditions * p)
            : CommonSatisfactionVisitor(p) {
        }
        
        
        virtual void visit_AND(NNFNode_AND * andNode) {        
            visit_AND_internal(andNode);
        }
            
        virtual void visit_OR(NNFNode_OR * orNode) {            
            visit_OR_internal(orNode);
        }
        
        virtual void visit_NOT_Literal(NNFNode_NOT_Literal * negLitNode) {            
            visit_NOT_Literal_internal(negLitNode->getLiteral()->getStateID());
            
        }
        
        virtual void visit_Literal(NNFNode_Literal * litNode) {
            visit_Literal_internal(litNode->getLiteral()->getStateID());
        }
                
        virtual void visit_RPGNumeric(NNFNode_RPGNumeric * npNode) {
            visit_RPGNumeric_internal(npNode->getPre());
        }
    };
    
    class UnsatisfyAPrecondition : public CommonSatisfactionVisitor {
        
    public:
            
        UnsatisfyAPrecondition(ChoosePreconditions * p)
            : CommonSatisfactionVisitor(p)
        {
        }
        
        virtual void visit_AND(NNFNode_AND * andNode) {
            visit_OR_internal(andNode);
        }
        
        virtual void visit_OR(NNFNode_OR * orNode) {
            visit_AND_internal(orNode);
        }
        
        virtual void visit_Literal(NNFNode_Literal * litNode) {
            visit_NOT_Literal_internal(litNode->getLiteral()->getStateID());
        }
        
        virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
            visit_Literal_internal(litNode->getLiteral()->getStateID());
        }
        
        virtual void visit_RPGNumeric(NNFNode_RPGNumeric * npNode) {
            std::cerr << "Not yet implemented: unsatisfying numeric preconditions\n";
            exit(1);
            //visit_NOT_RPGNumeric_internal(npNode->getPre());
        }                
    };
    
protected:

    MinimalState & theState;
    #ifdef ENABLEDERIVED
    const set<int> & derivedState;
    #endif
    
    const vector<double> & minTimestamps;
    
    #ifdef ENABLEDERIVED
    const vector<double> & derivedAtTime;    
    const vector<double> & negativeDerivedAtTime;    
    const vector<int> & derivedInLayer;
    #endif
    
    list<set<int> > chosenPropositions;
    list<set<int> > chosenNegativePropositions;
    list<set<int> > chosenNumerics;
    list<double> availableAtTime;
    list<bool> wasSatisfied;

    map<int,pair<bool,double> > numericPreTrueAtTime;
    map<int,pair<bool,double> > numericPreFalseAtTime;
       
    SatisfyAPrecondition * const satisfier;
    UnsatisfyAPrecondition * const unsatisfier;
    
public:
    
    ChoosePreconditions(MinimalState & s,
                        #ifdef ENABLEDERIVED
                        const set<int> & ds,
                        #endif
                        const vector<double> & mtIn
                        #ifdef ENABLEDERIVED
                        ,
                        const vector<double> & datIn, const vector<double> & ndatIn,
                        const vector<int> & dil
                        #endif
                       )
        : theState(s),
          #ifdef ENABLEDERIVED
          derivedState(ds),
          #endif
          minTimestamps(mtIn),
          #ifdef ENABLEDERIVED
          derivedAtTime(datIn), negativeDerivedAtTime(ndatIn),
          derivedInLayer(dil),
          #endif
          satisfier(new SatisfyAPrecondition(this)),
          unsatisfier(new UnsatisfyAPrecondition(this)) {
    }
    
    ~ChoosePreconditions() {
        delete satisfier;
        delete unsatisfier;
    }
    
    pair<bool,double> collect(const list<Literal*> & pres, const list<Literal*> & negPres,
                              set<int> & propositions, set<int> & negativePropositions,
                              set<int> & numerics) {

        pair<bool,double> toReturn(true, 0.0);
        
        for (int pass = 0; pass < 2; ++pass) {
            const list<Literal*> & reserve = (pass == 1 ? negPres : pres);
            
            list<Literal*>::const_iterator precItr = reserve.begin();
            const list<Literal*>::const_iterator precEnd = reserve.end();
            
            for (int litID; precItr != precEnd; ++precItr) {
                litID = (*precItr)->getStateID();
                #ifdef ENABLEDERIVED
                if (!DerivedPredicatesEngine::canBeDerived(litID)) {
                #endif
                    double atTime = 0.0;
                    const StateFacts::const_iterator fItr = theState.first.find(litID);
                    if (pass) {
                        if (fItr != theState.first.end()) {
                            return make_pair(false, DBL_MAX);                            
                        }
                        negativePropositions.insert(litID);
                        const StateFacts::const_iterator rfItr = theState.retired.find(litID);
                        if (rfItr != theState.retired.end()) {
                            atTime = minTimestamps[fItr->second.negativeAvailableFrom.stepID] + 0.001;
                        }
                        
                    } else {                        
                        if (fItr == theState.first.end()) {
                            return make_pair(false, DBL_MAX);                            
                        }
                        propositions.insert(litID);
                        if (fItr->second.availableFrom.beforeOrAfter == StepAndBeforeOrAfter::AFTER) {
                            atTime = minTimestamps[fItr->second.availableFrom.stepID] + 0.001;
                        }
                    }
                #ifdef ENABLEDERIVED
                } else {
                    
                    const set<int>::const_iterator fItr = derivedState.find(litID);
                    
                    
                }
                #endif
            }
        }
        
        
    }
    
    pair<bool,double> collect(NNFNode* toVisit, const bool & satisfyNNF,
                              NNFPreconditionChooser::Supporters & chosen) {
    

        assert(chosenPropositions.empty());
        assert(chosenNegativePropositions.empty());
        assert(chosenNumerics.empty());
        assert(availableAtTime.empty());
        assert(wasSatisfied.empty());

        chosenPropositions.push_back(set<int>());
        chosenNegativePropositions.push_back(set<int>());
        chosenNumerics.push_back(set<int>());
        availableAtTime.push_back(0.0);
        wasSatisfied.push_back(true);
        
        
        if (satisfyNNF) {
            toVisit->visit(satisfier);
        } else {
            toVisit->visit(unsatisfier);
        }
        
        assert(chosenPropositions.size() == 1);       
        assert(chosenNumerics.size() == 1);
        
        if (!wasSatisfied.back()) {
            chosenPropositions.clear();
            chosenNegativePropositions.clear();
            chosenNumerics.clear();
            availableAtTime.clear();
            wasSatisfied.clear();        
            return make_pair(false, DBL_MAX);
        }
        
        if (chooseDebug) {
            cout << "Chosen numerics:";
            {
                set<int>::const_iterator sItr = chosenNumerics.back().begin();
                const set<int>::const_iterator sEnd = chosenNumerics.back().end();
                
                for (; sItr != sEnd; ++sItr) {
                    cout << " " << *sItr << ":" << RPGBuilder::getNumericPreTable()[*sItr];
                }                                
            }
            cout << std::endl;
            
        }
        
        chosen.propositions.insert(chosenPropositions.back().begin(), chosenPropositions.back().end());
        chosen.negativePropositions.insert(chosenNegativePropositions.back().begin(), chosenNegativePropositions.back().end());
        chosen.numerics.insert(chosenNumerics.back().begin(), chosenNumerics.back().end());
        
        const double achievedAtTime = availableAtTime.back();
        
        chosenPropositions.clear();
        chosenNegativePropositions.clear();
        chosenNumerics.clear();
        availableAtTime.clear();
        wasSatisfied.clear();
        
        #ifdef ENABLEDERIVED
        set<int> extraPropositions;
        set<int> extraNegativePropositions;
        
        for (int derivationPolarity = 0; derivationPolarity < 2; ++derivationPolarity) {
            
            set<int> & loopOver = (derivationPolarity == 1 ? negativePropositions : propositions);
            
            set<int>::iterator loItr = loopOver.begin();
            const set<int>::iterator loEnd = loopOver.end();
            
            while (loItr != loEnd) {
                if (!DerivedPredicatesEngine::canBeDerived(*loItr)) {
                    ++loItr;
                    continue;
                }
                
                const set<int> & appropriateRules = DerivedPredicatesEngine::rulesWillDerive(*loItr);
                
                if (derivationPolarity == 0) {
                    
                    // must find a rule that achieves *loItr, i.e. a derived fact
                    
                    double bestSuccTimeSeen = DBL_MAX;
                    bool anyTrueSeen = false;
                    set<int> bestChosenPropositions;
                    set<int> bestChosenNegativePropositions;
                    set<int> bestChosenNumerics;
                    
                    
                    set<int>::const_iterator arItr = appropriateRules.begin();
                    const set<int>::const_iterator arEnd = appropriateRules.end();
                    
                    for (; arItr != arEnd; ++arItr) {
                        set<int> candidateChosenPropositions;
                        set<int> candidateChosenNegativePropositions;
                        set<int> candidateChosenNumerics;
                        
                        NNFNode * const rule = DerivedPredicatesEngine::getDerivationRules(*arItr);
                        
                        // recursively see if this rule's conditions can be satisfied
                        
                        const pair<bool,double> couldBeDerived
                                = collect(rule, true,
                                          candidateChosenPropositions, candidateChosenNegativePropositions,
                                          candidateChosenNumerics, candidateChosenNegativePropositions);
                    
                        if (couldBeDerived.first) {
                            anyTrueSeen = true;
                            if (couldBeDerived.second < bestSuccTimeSeen) {
                                // if this is now the earliest option, keep it
                                bestSuccTimeSeen = couldBeDerived.second;
                                bestChosenPropositions.swap(candidateChosenPropositions);
                                bestChosenNegativePropositions.swap(candidateChosenNegativePropositions);
                                bestChosenNumerics.swap(candidateChosenNumerics);
                                if (bestSuccTimeSeen <= derivedAtTime[*loItr] + 0.0001) {
                                    // found one of the earliest rules
                                    break;
                                }
                            }
                        }

                       
                    }
                    
                    assert(anyTrueSeen);
                    assert(bestSuccTimeSeen <= derivedAtTime[*loItr] + 0.0001);                

                    extraPropositions.insert(bestChosenPropositions.begin(), bestChosenPropositions.end());
                    extraNegativePropositions.insert(bestChosenNegativePropositions.begin(), bestChosenNegativePropositions.end());
                    numerics.insert(bestChosenNumerics.begin(), bestChosenNumerics.end());
                    
                } else {
                    
                    // must inviolate all rules that achieve *loItr, i.e. a negative derived fact
                    
                    set<int>::const_iterator arItr = appropriateRules.begin();
                    const set<int>::const_iterator arEnd = appropriateRules.end();
                    
                    for (; arItr != arEnd; ++arItr) {
                        set<int> bestChosenPropositions;
                        set<int> bestChosenNegativePropositions;
                        set<int> bestChosenNumerics;
                        
                        NNFNode * const rule = DerivedPredicatesEngine::getDerivationRules(*arItr);
                        
                        // recursively see if this rule's conditions can be satisfied
                        
                        const pair<bool,double> couldBeDerived
                                = collect(rule, false,
                                          bestChosenPropositions, bestChosenNegativePropositions,
                                          bestChosenNumerics, bestChosenNegativePropositions);
                    
                        // the rule *must* be negatable
                        
                        assert(couldBeDerived.first);
                      
                        extraPropositions.insert(bestChosenPropositions.begin(), bestChosenPropositions.end());
                        extraNegativePropositions.insert(bestChosenNegativePropositions.begin(), bestChosenNegativePropositions.end());
                        numerics.insert(bestChosenNumerics.begin(), bestChosenNumerics.end());
                       
                    }
                }
                
                
                const set<int>::iterator loDel = loItr++;
                loopOver.erase(loDel);
                
            }
            
            if (!DerivedPredicatesEngine::areDerivedPredicatesEverNegativePreconditions()) {
                break;
            }
            
        }
        
        chosen.propositions.insert(extraPropositions.begin(), extraPropositions.end());
        chosen.negativePropositions.insert(extraNegativePropositions.begin(), extraNegativePropositions.end());
        
        #endif
        
        return make_pair(true, achievedAtTime);
        
    }          
};

static const bool collectDebug = false;

class CollectPreconditions : public NNFVisitorAfterRPGNumerics {


    protected:
        
        list<bool> childSatisfaction;
        MinimalState & theState;
        NNFPreconditionChooser::Supporters & support;
        
    public:
        virtual void visit_AND(NNFNode_AND * andNode) {
            
            if (collectDebug) {
                cout << "Collecting: visiting AND\n";
                if (childSatisfaction.back()) {
                    cout << "Still true\n";
                } else {
                    cout << "Known to be false\n";
                }
            }
            NNFContainerNode::iterator childItr = andNode->begin();
            const NNFContainerNode::iterator childEnd = andNode->end();
            
            for (;childItr != childEnd; ++childItr) {
                (*childItr)->visit(this);
                if (collectDebug) {
                    if (childSatisfaction.back()) {
                        cout << "Still true\n";
                    } else {
                        cout << "Now known to be false\n";
                    }
                }
            }
        }
        
        virtual void visit_OR(NNFNode_OR * orNode) {

            if (collectDebug) {
                cout << "Collecting: visiting OR\n";
            }
            bool thisSatisfaction = false;
            
            NNFContainerNode::iterator childItr = orNode->begin();
            const NNFContainerNode::iterator childEnd = orNode->end();
            
            for (;childItr != childEnd; ++childItr) {
                
                childSatisfaction.push_back(true);
                (*childItr)->visit(this);
                
                if (collectDebug) {
                    if (childSatisfaction.back()) {
                        cout << "Child was true\n";
                    } else {
                        cout << "Child was false\n";
                    }
                }
                
                
                thisSatisfaction = (thisSatisfaction || childSatisfaction.back());
                childSatisfaction.pop_back();
                
                if (collectDebug) {
                    if (thisSatisfaction) {
                        cout << "This now true\n";
                    } else {
                        cout << "This now false\n";
                    }
                }
                
            }
            
            if (collectDebug) {
                if (thisSatisfaction) {
                    cout << "OR is satisfied\n";
                } else {
                    cout << "OR is unsatisfied\n";
                }
            }
            childSatisfaction.back() = (childSatisfaction.back() && thisSatisfaction);
        }
        
        virtual void visit_NOT_Literal(NNFNode_NOT_Literal * litNode) {
            
            const int litID = litNode->getLiteral()->getStateID();
            if (theState.first.find(litID) != theState.first.end()) {
                if (collectDebug) {
                    cout << "Visited negative literal " << *(RPGBuilder::getLiteral(litID)) << " - not true as we have it\n";
                }
                childSatisfaction.back() = false;
            } else {
                if (collectDebug) {
                    cout << "Visited negative literal " << *(RPGBuilder::getLiteral(litID)) << " - true as we don't have it\n";
                }
            }
            
            support.negativePropositions.insert(litID);
        
        }
        
        virtual void visit_Literal(NNFNode_Literal * litNode) {
            const int litID = litNode->getLiteral()->getStateID();
            if (theState.first.find(litID) == theState.first.end()) {
                childSatisfaction.back() = false;
                if (collectDebug) {
                    cout << "Visited literal " << *(RPGBuilder::getLiteral(litID)) << " - not true as we don't have it\n";
                }
            } else {
                if (collectDebug) {
                    cout << "Visited literal " << *(RPGBuilder::getLiteral(litID)) << " - true as we have it\n";
                }
            }
            support.propositions.insert(litID);
        }
        
        virtual void visit_RPGNumeric(NNFNode_RPGNumeric * rpgNode) {
            const int preID = rpgNode->getPre();
            RPGBuilder::RPGNumericPrecondition & numPre = RPGBuilder::getNumericPreTable()[preID];
             
            if (!numPre.isSatisfiedWCalculate(theState.secondMin, theState.secondMax)) {
                if (collectDebug) {
                    cout << "Visited " << numPre << " - not true\n";
                }
                childSatisfaction.back() = false;
            } else {
                if (collectDebug) {
                    cout << "Visited " << numPre << " - is true\n";
                }
            }
            support.numerics.insert(preID);
        }
        
        
        
        CollectPreconditions(MinimalState & s, NNFPreconditionChooser::Supporters & sup)
            : theState(s), support(sup) {
        }
        
        bool collect(NNFNode * toVisit) {
            childSatisfaction.push_back(true);
            toVisit->visit(this);            
            return childSatisfaction.back();
        }
        
};
    
namespace NNFPreconditionChooser {
    pair<bool,double> satisfyNNFEarly(MinimalState & s, const vector<double> & minTimestamps, NNFNode* toVisit,
                                      Supporters & chosen) {

        if (toVisit) {
        
            ChoosePreconditions c(s, minTimestamps);
        
            return c.collect(toVisit, true, chosen);
            
        } else {
            static const pair<bool, double> toReturn(true,0.0);
            
            return toReturn;
        }

    }
    
    bool collectNNFDependencies(MinimalState & s, NNFNode* toVisit,
                                Supporters & chosen) {

        if (toVisit) {
        
            if (collectDebug) {
                cout << "Visiting NNF tree rooted at " << toVisit << std::endl;
            }
            CollectPreconditions c(s, chosen);
        
            if (!collectDebug) {
                return c.collect(toVisit);
            } else {
                if (c.collect(toVisit)) {
                    cout << "Returning true\n";
                    return true;
                } else {
                    cout << "Returning false\n";
                    return false;
                }
            }
            
        } else {            
            if (collectDebug) {
                cout << "Not visiting NNF tree rooted at " << toVisit << " - returning true\n";
            }
            return true;
        }

    }
};

};
