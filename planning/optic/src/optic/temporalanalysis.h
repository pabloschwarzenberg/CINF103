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

//
// C++ Interface: temporalanalysis
//
// Description:
//
//
// Author: Amanda Coles, Andrew Coles, Maria Fox, Derek Long <firstname.lastname@cis.strath.ac.uk>, (C) 2009
//
// Copyright: See COPYING file that comes with this distribution
//
//
#ifndef PLANNERTEMPORALANALYSIS_H
#define PLANNERTEMPORALANALYSIS_H

#include "RPGBuilder.h"

namespace Planner
{

class TemporalAnalysis;

class TILTimeline {
    
public:
    
    friend class TemporalAnalysis;
    
    struct AddedOrDeleted {
        
        bool added;
        bool deleted;
        
        AddedOrDeleted()
            : added(false), deleted(false) {
        }
                    
        AddedOrDeleted(const bool & b)
            : added(b), deleted(!b) {
        }
                                    
    };
    
    typedef map<double, AddedOrDeleted> TimelineData;
    
    typedef TimelineData::const_iterator const_iterator;
    typedef TimelineData::const_reverse_iterator const_reverse_iterator;    
    
private:
    
    /** @brief Time-stamped TIL events on the fact */
    TimelineData happenings;

    bool onlyEverAddedByTILs;
    bool onlyEverDeletedByTILs;
    bool allReferencesToItDeleteIt;
    bool closedEnded;
    int numberOfWindows;
    const_iterator firstAdder;
    const_iterator firstDeletor;
    const_iterator lastDeletor;
        
public:
    
    TILTimeline()
        : onlyEverAddedByTILs(true), onlyEverDeletedByTILs(true),
          allReferencesToItDeleteIt(false), closedEnded(false), numberOfWindows(-1)
    {
    }
    
    const bool & isOnlyEverAddedByTILs() const {
        return onlyEverAddedByTILs;    
    }
    
    const bool & isOnlyEverDeletedByTILs() const {
        return onlyEverDeletedByTILs;    
    }
  
    const bool & isOnlyEverReferredToThenDeleted() const {
        return allReferencesToItDeleteIt;
    }
  
    inline const_iterator begin() const {
        return happenings.begin();
    }
  
    inline const_iterator end() const {
        return happenings.end();
    }

    inline const_reverse_iterator rbegin() const {
        return happenings.rbegin();
    }
  
    inline const_reverse_iterator rend() const {
        return happenings.rend();
    }
    
    inline const const_iterator & getFirstAdder() const {
        return firstAdder;
    }
      
    inline const const_iterator & getFirstDeletor() const {
        return firstDeletor;
    }
    
    inline const const_iterator & getLastDeletor() const {
        return lastDeletor;
    }
    
    const_iterator firstAdderSuitableForTime(const double & t) const {
        const_iterator toReturn = happenings.upper_bound(t); // find the next point on the timeline after t
        if (toReturn != happenings.begin()) { // but actually we want the point before then, so roll backwards
            --toReturn;
        }
        for (; toReturn != happenings.end() && !toReturn->second.added; ++toReturn) ; // roll forwards until we're after an adder
        return toReturn;
    }
    
    const_iterator firstDeletorAfterTime(const double & t) const {
        const_iterator toReturn = happenings.upper_bound(t);
        for (; toReturn != happenings.end() && !toReturn->second.deleted; ++toReturn) ;
        return toReturn;
    }
        
};
    
class TemporalAnalysis
{

private:
    static vector<bool> startEndSkip;
    
    static map<int, list<pair<double, double> > > windows;
    static vector<vector<pair<double, double> > > actionTSBounds;
    static LiteralSet initialState;
    static bool yesGoalSoftDeadlinesHaveMonotonicallyWorseningCosts;
    
    static void recogniseHoldThroughoutDeleteAtEndIdiom(LiteralSet & factsIdentified);
        
    
    #ifdef POPF3ANALYSIS
    static bool endNumericEffectsAreCompressionSafe(const list<int> & effects,
                                                    vector<bool> & allInteractionWithVarIsCompressionSafe);
    static void markCompressionSafetyConditions(const int & actID, const list<int> & effects,
                                                vector<set<int> > & actionsDependingOnVarBeingCompressionSafe);
    static void markAffectedVariablesAsNotCompressionSafe(const list<int> & effects,
                                                          vector<bool> & allInteractionWithVarIsCompressionSafe,
                                                          set<int> & newlyUnsafe);
    #endif

    /** @brief A timeline on the given TIL-manipulated fact */
    static bool anythingTILManipulated;
    static map<int, TILTimeline> timelineOnTILs;
        
    static map<int, list<int> > actionStartUsesAbstractedFact;
    static map<int, list<int> > actionOverAllUsesAbstractedFact;
    static map<int, list<int> > actionEndUsesAbstractedFact;
    
    static vector<bool> factIsAbstract;
    
    static bool initialisedGlobalActionDurationBounds;
    static vector<pair<double,double> > globalActionDurationBounds;
    
public:

    static bool abstractTILsWherePossible; 
    
    static void dummyDeadlineAnalysis();
    static void processTILDeadlines();
    static void findGoalDeadlines(list<Literal*> &, list<double> &);
    
    /** @brief Find soft goal deadlines.
     *
     *  Look at within preferences and collate facts upon which they absolutely depend.
     * 
     * @param factRelevantToWithinPreferences[out] Facts mapped to relevant within preference IDs
     * @param negativeFactRelevantToWithinPreferences[out] Negative facts mapped to relevant within preference IDs
     */
    static void findGoalSoftDeadlines(map<int, list<int> > & factRelevantToWithinPreferences,
                                      map<int, list<int> > & negativeFactRelevantToWithinPreferences);
    

    static void reboundSingleAction(const int & actID, const vector<pair<double,double> > & durationBounds, bool & keep, pair<double,double> & startBounds, pair<double,double> & endBounds, const bool workingGlobally=false);
    
    
    static void findActionTimestampLowerBounds();
    static void findCompressionSafeActions();
    
    static void buildTimelinesOnTILs();
    static void reboundActionsGivenTILTimelines();
    
    static void recalculateDurationsFromBounds(const bool workingGlobally=true);
    
    static vector<vector<pair<double, double> > > & getActionTSBounds() {
        return actionTSBounds;
    }
    
    static const bool & isAnythingTILManipulated() {
        return anythingTILManipulated;
    }
    
    static const list<pair<double, double> > * factIsVisibleInWindows(const Literal* const l) {
        map<int, list<pair<double, double> > >::const_iterator wItr = windows.find(l->getStateID());
        if (wItr == windows.end()) return 0;
        return &(wItr->second);
    }
    
    static void suggestNewStartLowerBound(const int & a, const double & d) {
        if (actionTSBounds[a][0].first < d) {
            actionTSBounds[a][0].first = d;
        }
        #ifdef ENABLE_DEBUGGING_HOOKS
        if (RPGBuilder::getRPGDEs(a).empty()) {
            Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second);
        } else {
            Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second, actionTSBounds[a][1].first, actionTSBounds[a][1].second);
        }
        #endif
    }

    static void suggestNewEndLowerBound(const int & a, const double & d) {
        if (actionTSBounds[a][1].first < d) {
            actionTSBounds[a][1].first = d;
        }
        #ifdef ENABLE_DEBUGGING_HOOKS
        if (RPGBuilder::getRPGDEs(a).empty()) {
            Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second);
        } else {
            Globals::checkActionBounds(a, actionTSBounds[a][0].first, actionTSBounds[a][0].second, actionTSBounds[a][1].first, actionTSBounds[a][1].second);
        }
        #endif
    }

    static bool actionIsNeverApplicable(const int & a);
    static bool okayToStart(const int & a, const double & ts) {
        return (ts <= actionTSBounds[a][0].second);
    }

    static bool okayToEnd(const int & a, const double & ts) {
        return (ts <= actionTSBounds[a][1].second);
    }

    static bool canSkipToEnd(const int & i) {
        assert(i >= 0);
        #ifndef NDEBUG 
        if ((size_t) i >= startEndSkip.size()) {
            std::cerr << "Fatal internal error: asked whether action index " << i << " is start--end skippable.\n";
            std::cerr << "Size of relevant array: " << startEndSkip.size() << ".  Number of actions: " << Inst::instantiatedOp::howMany() << ".\n";
            exit(1);
        }
        #endif
        return startEndSkip[i];
    };
    
    static const map<int, TILTimeline> & getTILTimelines() {
        return timelineOnTILs;
    }
    
    static const TILTimeline * timelineOnTILFact(const int & fID) {
        map<int, TILTimeline>::const_iterator tItr = timelineOnTILs.find(fID);
        if (tItr == timelineOnTILs.end()) {
            return 0;
        }
        return &(tItr->second);
    }
    
    static void pullInAbstractTILs(MinimalState & theState, list<FFEvent> & planToAddDummyStepsTo);

    static const map<int, list<int> > & getAbstractFactsUsedByActionStart() {
        return actionStartUsesAbstractedFact;
    }
    
    static const map<int, list<int> > & getAbstractFactsUsedByActionOverAll() {
        return actionOverAllUsesAbstractedFact;
    }
    
    static const map<int, list<int> > & getAbstractFactsUsedByActionEnd() {
        return actionEndUsesAbstractedFact;
    }
        
    static const vector<bool> & getFactIsAbstract() {
        return factIsAbstract;
    }
        
    /** @brief Build a table of action duration bounds given the limit on remaining cost.
     * 
     * For action with duration-dependent effects on cost, then if cost is monotonically worsening, the actions' durations are limited.
     * This computes the limits, based on 'for an action to be executed, it can itself consume no more than the remaining cost'.
     * 
     * @param costLimit[in]  The limit on remaining cost.  As with numeric limits, everything is compiled to reward.  Thus, if minimising cost,
     *                       and we have an incumbent solution of cost 1000 and a new partial solution of cost 900, the cost limit is -100:
     *                       no action can decrease the plan reward (i.e. increase its cost) by more than -100 (100).  If the cost limit is
     *                       -DBL_MAX, the theoretical min and max durations are return assuming cost is ignored.
     * 
     * @param actionDurationBounds[out]  A table of action duration bounds.
     * 
     */ 
    static void doDurationLimitingEffectAnalysis(const double & costLimit, vector<pair<double,double> > & actionDurationBounds);
    
    static void doGlobalDurationLimitingEffectAnalysis();
        
};

}

#endif
