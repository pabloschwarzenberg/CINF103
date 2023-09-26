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

#ifndef PREFERENCEHANDLER_H
#define PREFERENCEHANDLER_H

#include "RPGBuilder.h"
#include "NNF.h"
#include "choosepreconditions.h"

namespace Planner {

struct ConditionAndPolarity {
    
    int first;
    bool second;
    bool polarity;
    
    ConditionAndPolarity()
        : first(-1), second(false), polarity(true)
    {
    }

    ConditionAndPolarity(const int & a, const bool & b, const bool & c)
        : first(a), second(b), polarity(c)
    {
    }
};
    
class PreferenceFSA {

protected:
    
    uint prefIdx;
    string switchVarName;
    RPGBuilder::Constraint * pref;

    PreferenceFSA(const int & i, RPGBuilder::Constraint * const p);

    int triggerType;
    int goalType;
    
    /**
     *  Work out whether the goal/trigger of a preference is satisfied in the
     *  given state.  Setting partIdx to 1 checks the trigger; to 0, the goal.
     */
    virtual bool goalOrTriggerIsSatisfied(const MinimalState *, const int & partIdx);
    
    virtual void satisfyAtLowCost(const NNF_Flat *,
                                  const vector<list<CostedAchieverDetails> > &, const vector<EpsilonResolutionTimestamp> &,
                                  const vector<EpsilonResolutionTimestamp> *,
                                  list<list<Literal*> > &, list<list<Literal*> > &, list<list<int> >* );
        
public:
    virtual const vector<vector<int> >* getComparisonData() = 0;

    virtual void getPreconditionsToSatisfy(list<Literal*> & pres, list<Literal*> & negativePres, list<int> * numericPres,
                                           const bool & theTrigger,
                                           const EpsilonResolutionTimestamp & factLayerTime,
                                           const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                           const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);
                                          
                                          
    

    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen) __attribute__((warn_unused_result)) = 0;
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &) = 0;
    virtual double currentCost(const MinimalState * theState, const int & flag) {
        return currentCost(theState->preferenceStatus, flag);
    }
    
    virtual void currentViolations(const MinimalState * s, string & v) {
        if (fabs(currentCost(s,3)) > 0.0) {
            v += " " + pref->name;
        }
    }
    
    virtual void currentViolations(const vector<AutomatonPosition::Position> & s, string & v) {
        if (fabs(currentCost(s,3)) > 0.0) {
            v += " " + pref->name;
        }
    }
    
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &) = 0;
    virtual double reachableCost(const MinimalState * theState, const int & flag) {
        return reachableCost(theState->preferenceStatus, flag);
    }
    
    virtual double GCost(const MinimalState *, const int &) = 0;
    //virtual void populateFactToPreferenceMappings();
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &) = 0;
    
    virtual void getCostsOfDeletion(const MinimalState &, map<int, set<int> > &, map<int, map<double, set<int> > > &)
    {
    }
    virtual void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &)
    {
    }
    
    /** @brief Called when a goal/trigger has become satisfied during RPG expansion
    *
    *  When a goal/trigger has become true, it may lead to the the costs of facts in the RPG being reduced.  For instance,
    *  for the preference (sometime-before a b), if b has been satisfied, this function is called; and <code>SometimeBeforeFSA::updateCosts</code>
    *  will note that adding the fact a no longer violates that preference.
    */
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &,
                             map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &)
    {
    }
    
    /** @brief Get goals needed to satisfy this preference in RPG extraction */
    virtual void getDesiredGoals(list<list<Literal*> > &/* positiveLiterals*/, list<list<Literal*> > &/* negativeLiterals*/,
                                 list<list<int> > */* positiveNumeric*/,
                                 const MinimalState &,
                                 const vector<vector<NNF_Flat*> > &,
                                 const vector<list<CostedAchieverDetails> > &, const vector<EpsilonResolutionTimestamp> &/* negativeLiteralAchievedInLayer*/,
                                 const vector<EpsilonResolutionTimestamp> *)
    {
    }
    
    virtual void becomesUnreachableAtTime(const MinimalState &, map<EpsilonResolutionTimestamp, list<int> > &)
    {
    }
};

class AlwaysFSA : public PreferenceFSA {

public:
    AlwaysFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);

    
    virtual const vector<vector<int> >* getComparisonData();
    
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps,  list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getCostsOfDeletion(const MinimalState &, map<int, set<int> > &, map<int, map<double, set<int> > > &);

};

class AtEndFSA : public PreferenceFSA {


public:
    AtEndFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);

    virtual const vector<vector<int> >* getComparisonData();
    
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                list<list<int> > * desiredNumeric,
                                 const MinimalState & startState,
                                 const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                 const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                 const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);

};

class SometimeFSA : public PreferenceFSA {

public:
    SometimeFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);

    virtual const vector<vector<int> >* getComparisonData();

    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                 list<list<int> > * desiredNumeric,
                                 const MinimalState & startState,
                                 const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                 const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                 const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);

};

class AtMostOnceFSA : public PreferenceFSA {
    set<pair<int,Planner::time_spec> > actionsImplyingTrigger;
    int triggerPartCount;
    bool addingOneThingCanTrigger;
    list<ConditionAndPolarity> addingThisWouldTrigger;
public:
    AtMostOnceFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);
    
    virtual const vector<vector<int> >* getComparisonData();
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &);

    
};

class SometimeBeforeFSA : public PreferenceFSA {

    set<pair<int,Planner::time_spec> > actionsImplyingTrigger;
    int triggerPartCount;
    
    bool addingOneThingCanTrigger;
    list<ConditionAndPolarity> addingThisWouldTrigger;
public:
    SometimeBeforeFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);

    virtual const vector<vector<int> >* getComparisonData();
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);
    
    
};

class SometimeAfterFSA : public PreferenceFSA {
    set<pair<int,Planner::time_spec> > actionsImplyingTrigger;
    int triggerPartCount;
    bool addingOneThingCanTrigger;
    list<ConditionAndPolarity> addingThisWouldTrigger;
public:
    SometimeAfterFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn, const VAL::constraint_sort shouldBe=VAL::E_SOMETIMEAFTER);

    virtual const vector<vector<int> >* getComparisonData();
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);
    virtual void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                 list<list<int> > * desiredNumeric,
                                 const MinimalState & startState,
                                 const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                 const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                 const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);

};

class WithinFSA : public PreferenceFSA {
    
public:
    WithinFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);

    virtual const vector<vector<int> >* getComparisonData();

    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    virtual void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                 list<list<int> > * desiredNumeric,
                                 const MinimalState & startState,
                                 const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                 const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                 const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);
    
    virtual void becomesUnreachableAtTime(const MinimalState &, map<EpsilonResolutionTimestamp, list<int> > &);
};

class AlwaysWithinFSA : public SometimeAfterFSA {

public:
    AlwaysWithinFSA(const int & i, RPGBuilder::Constraint * const p, AutomatonPosition::Position & initPosn);
    
    virtual const vector<vector<int> >* getComparisonData();
    
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &);
    virtual void updateCosts(const MinimalState &, const bool &, vector<AutomatonPosition::Position> &, map<int, AddingConstraints > &, map<int, map<double, AddingConstraints > > &, list<pair<int,int> > &);
    virtual void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                 list<list<int> > * desiredNumeric,
                                 const MinimalState & startState,
                                 const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                 const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                 const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);

};

class PreconditionPref : public PreferenceFSA {
    
public:
    PreconditionPref(const int & i, RPGBuilder::Constraint * const p);
        
    virtual const vector<vector<int> >* getComparisonData()
    {
        return 0;
    }
    virtual bool update(MinimalState *, const pair<bool,bool> & goalOrTriggerChanged, const vector<double> & minTimestamps, list<NNFPreconditionChooser::Supporters> & chosen);
    virtual double currentCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual void currentViolations(const MinimalState *, string &)
    {
    }
    virtual double reachableCost(const vector<AutomatonPosition::Position> &, const int &);
    virtual double GCost(const MinimalState *, const int &);
    virtual void getUnsatisfiedConditionCounts(const MinimalState &, vector<NNF_Flat*> &);
    
    
};


class PreferenceHandler {
protected:
    friend class PreferenceFSA;
    static vector<const vector<vector<int> >* > comparisonData;
    static vector<PreferenceFSA*> automata;
    static vector<AutomatonPosition::Position> initialAutomataPositions;
    
    static vector<list<LiteralCellDependency<pair<int,bool> > > > preconditionsToPrefs;
    static vector<list<LiteralCellDependency<pair<int,bool> > > > negativePreconditionsToPrefs;
    static vector<list<LiteralCellDependency<pair<int,bool> > > > numericPreconditionsToPrefs;
    
    static vector<vector<pair<int, bool> > > mappingFromFactsToPreferences;
    static vector<vector<pair<int, bool> > > mappingFromNumericFactsToPreferences;
    
    static set<pair<int,bool> > defaultTruePrefParts;
    static vector<int> relevantNumericPreconditions;
    static vector<bool> numericVariableAffectsPreferences;
    
    static void initPTRTable();    
    static int ptrTableInit;
    static bool temporalPreferences;
    
    static list<int> withinPreferences;
    static list<int> sometimePreferences;
    static list<int> preferencesInNonDefaultPositionsInitially;
    
public:

    static bool preferenceDebug;
    static bool recordPreconditionViolations;
    
    static map<int,int> preconditionViolations;
    
    static void buildAutomata();
    static const vector<AutomatonPosition::Position> & getInitialAutomataPositions()
    {
        return initialAutomataPositions;
    }

    /** @brief Return <code>true</code> if there are temporal preferences. */
    static const bool & anyTemporalPreferences() {
        return temporalPreferences;
    }

    static list<int> & getListOfWithinPreferences() {
        return withinPreferences;
    }
    
    static list<int> & getListOfSometimePreferences() {
        return sometimePreferences;
    }
    
    static const vector<bool> & getWhichNumericVariablesAffectPreferences() {
        return numericVariableAffectsPreferences;
    }
    
    /** @brief Update violation counters of any relevant precondition preferences.
     *
     * @param theState]in]  The current state
     * @param act[in]       The action about to be applied in that state
     * @param minTimestamps[in]  Time-stamps of the steps to reach <code>theState</code>
     * @param chosen[out]   Support for the relevant precondition preferences.
     */
    static void aboutToApply(MinimalState & theState, const ActionSegment & act,
                             const vector<double> & minTimestamps, 
                             list<NNFPreconditionChooser::Supporters> & chosen);
    
    /** @brief Update preference automata after an action has been applied.
     *
     * @param theState[in]  The state following the application of an action    
     * @param minTimestamps[in]  Time-stamps of the steps to reach <code>theState</code>
     * @param newLiterals[in]  Facts added by the action that were not true previously
     * @param newNegativeLiterals[in]  Facts deleted by the action that were previously true
     * @param affectedNumericVariables[in]  Numeric variables affected by the effects of the action
     * @param chosen[out]   Support for the relevant preferences whose automata positions have changed.
     */
    static bool update(MinimalState & theState, const vector<double> & minTimestamps,
                       const set<int> & newLiterals, const set<int> & newNegativeLiterals, 
                       const set<int> & affectedNumericVariables,
                       list<NNFPreconditionChooser::Supporters> & chosen)  __attribute__((warn_unused_result));
    
    static double getCurrentCost(const MinimalState & theState, const int flag=3);
    static double getCurrentCost(const int & specificPreference, const MinimalState & theState, const int flag=3);
    static double getCurrentCost(const int & specificPreference, const vector<AutomatonPosition::Position> & positions, const int flag=3);
    static double getCurrentCost(const double & prefPreconditionViolations, const vector<AutomatonPosition::Position> & positions, const int flag=3);
    
    static string getCurrentViolations(const MinimalState & theState);
    static string getCurrentViolations(const vector<AutomatonPosition::Position> & positions);
    static double getReachableCost(const MinimalState & theState, const int flag=3);
    static double getReachableCost(const int & specificPreference, const MinimalState & theState, const int flag=3);
    static double getReachableCost(const int & specificPreference, const vector<AutomatonPosition::Position> & positions, const int flag=3);
    static double getG(const MinimalState & theState, const int flag=3);
    
    static const list<int> & getPreferencesInNonDefaultPositionsInitially() {
        return preferencesInNonDefaultPositionsInitially;
    }

    static const vector<list<LiteralCellDependency<pair<int,bool> > > > * getPreconditionsToPrefs()
    {
        return &preconditionsToPrefs;
    }
    
    static const vector<list<LiteralCellDependency<pair<int,bool> > > > * getNegativePreconditionsToPrefs()
    {
        return &negativePreconditionsToPrefs;
    }
    
    static const vector<list<LiteralCellDependency<pair<int,bool> > > > * getNumericPreconditionsToPrefs()
    {
        return &numericPreconditionsToPrefs;
    }
    

    static void getUnsatisfiedConditionCounts(const MinimalState &, vector<vector<NNF_Flat*> > &, map<EpsilonResolutionTimestamp, list<int> > & withinPreferencesUnreachableAtTime);

    static void getCostsOfDeletion(const MinimalState &, map<int, set<int> > & prefCostOfDeletingFact, map<int, map<double, set<int> > > & prefCostOfChangingNumberA);
    static void getCostsOfAdding(const MinimalState &, map<int, AddingConstraints > & prefCostOfAddingFact, map<int, map<double, AddingConstraints > > & prefCostOfChangingNumberB);
    
    static void updateCostsAndPreferenceStatus(const MinimalState &,
                                               const pair<int,bool> & whatHasBeenSatisfied,
                                               vector<AutomatonPosition::Position> & optimisticAutomataPositions,
                                               map<int, AddingConstraints > & prefCostOfAddingFact,
                                               map<int, map<double, AddingConstraints > > & prefCostOfChangingNumberB,
                                               list<pair<int,int> > & preferencesThatNowHaveNoAddCosts);
                                               
                                               
    
    // Functions for integrating preferences into the LP

    static double markUnreachables(MinimalState &, const list<int> &);
    
    static void getDesiredGoals(list<list<Literal*> > & desiredPositive, list<list<Literal*> > & desiredNegative,
                                list<list<int> > * desiredNumeric,
                                const MinimalState & startState,
                                const vector<vector<NNF_Flat*> > & unsatisfiedPreferenceConditions,
                                const vector<AutomatonPosition::Position> & optimisticAutomatonPositions,
                                /*vector<list<PreferenceSetAndCost> > * literalCosts,*/
                                const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);

    static void getPreconditionsToSatisfy(list<Literal*> & pres, list<Literal*> & negativePres,
                                          list<int> * numPres,
                                          const pair<int,bool> & satisfied, const EpsilonResolutionTimestamp & factLayerTime,
                                          const vector<list<CostedAchieverDetails> > & literalCosts, const vector<EpsilonResolutionTimestamp> & negativeLiteralAchievedInLayer,
                                          const vector<EpsilonResolutionTimestamp> * numericAchievedInLayer);
                                                            
                                                            
    static void initialiseNNF();
    static void flattenNNF();    
    static void collectRequiredFactsInNNF(const int & pref, const bool & wasTheTrigger, set<int> & requiredPositive, set<int> & requiredNegative);
    static void collectAllFactsInNNF(const int & pref, const bool & wasTheTrigger, set<int> & requiredPositive, set<int> & requiredNegative);
    static bool couldBeBeneficialToOppose(const int & pref, const bool & wasTheTrigger);
    static bool couldBeBeneficialToSupport(const int & pref, const bool & wasTheTrigger);
    static void pruneStaticLiterals(vector<pair<bool,bool> > & staticLiterals);    
    
    static void substituteRPGNumericPreconditions(RPGBuilder::BuildingNumericPreconditionData & commonData);
    static inline int compareStatusOfPref(const int & prefIdx, const AutomatonPosition::Position & a, const AutomatonPosition::Position & b) {
        return ((*comparisonData[prefIdx])[(int) a][(int) b]);
    }
    
    static bool constraintsAreSatisfied(const vector<AutomatonPosition::Position> & automataPositions);
    
};

extern bool canBeSatisfied(const AutomatonPosition::Position & p);
extern bool isSatisfied(const AutomatonPosition::Position & p);

};

#endif // PREFERENCEHANDLER_H
