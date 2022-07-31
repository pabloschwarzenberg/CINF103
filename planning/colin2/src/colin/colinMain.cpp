#include <cstdio>
#include <iostream>
#include <iomanip>
#include <fstream>
#include "ptree.h"
#include <assert.h>
#include <FlexLexer.h>
#include "instantiation.h"
#include "SimpleEval.h"
#include "DebugWriteController.h"
#include "typecheck.h"
#include "TIM.h"
#include "FuncAnalysis.h"

//#include "graphconstruct.h"
#include "RPGBuilder.h"
#include "FFSolver.h"
#include "globals.h"
#ifdef TOTALORDERSTATES
#include "colintotalordertransformer.h"
#else
#include "totalordertransformer.h"
#include "partialordertransformer.h"
#endif
#include "lpscheduler.h"
#include "numericanalysis.h"

#ifdef STOCHASTICDURATIONS
#include "StochasticDurations.h"
#endif

#include <sys/times.h>

#include <sstream>

// ALD
#include <unistd.h>

// ALD: for memory usage and time
//********
#include <sys/resource.h>
#include <chrono>
//********
////////////

using std::ifstream;
using std::ofstream;
using std::cerr;
using std::endl;
using std::ostringstream;
using std::string;

using namespace TIM;
using namespace Inst;
using namespace VAL;
using namespace Planner;

namespace VAL
{
bool ContinueAnyway;
bool ErrorReport;
bool InvariantWarnings;
bool LaTeX;
bool makespanDefault;
};

void usage(char * argv[])
{
    cout << "COLIN, Release 2\n";
    cout << "By releasing this code we imply no warranty as to its reliability\n";
    cout << "and its use is entirely at your own risk.\n\n";
    #ifdef STOCHASTICDURATIONS
    cout << "Usage: " << argv[0] << " [OPTIONS] <success fraction> domainfile problemfile [planfile, if -r specified]\n\n";
    #else
    cout << "Usage: " << argv[0] << " [OPTIONS] domainfile problemfile [planfile, if -r specified]\n\n";
    #endif
    cout << "Options are: \n\n";
    cout << "\t" << "-citation" << "\t" << "Display citation to relevant conference paper (ICAPS 2010);\n";
    cout << "\t" << "-b" << "\t\t" << "Disable best-first search - if EHC fails, abort;\n";
    cout << "\t" << "-E" << "\t\t" << "Skip EHC: go straight to best-first search;\n";
    cout << "\t" << "-e" << "\t\t" << "Use standard EHC instead of steepest descent;\n";
    cout << "\t" << "-h" << "\t\t" << "Disable helpful-action pruning;\n";
    cout << "\t" << "-k" << "\t\t" << "Disable compression-safe action detection;\n";
    cout << "\t" << "-M" << "\t\t" << "Disable the tie-breaking in search that favours plans with shorter makespans;\n";
    cout << "\t" << "-F" << "\t\t" << "Full FF helpful actions (rather than just those in the RP applicable in the current state);\n";
    cout << "\t" << "-r" << "\t\t" << "Read in a plan instead of planning;\n";
    cout << "\t" << "-T" << "\t\t" << "Rather than building a partial order, build a total-order\n";
    cout << "\t" << "-a" << "\t\t" << "Plan output file\n";
    cout << "\t" << "-y" << "\t\t" << "Timing output file\n";
    cout << "\t" << "-x" << "\t\t" << "Relaxed planning\n";
    #ifdef STOCHASTICDURATIONS
    cout << "\t" << "-f<t>" << "\t\t" << "Force a deadline of t on each goal;\n";
    cout << "\t" << "-M<duration manager><samples>" << "\t\t" << "Use the named duration manager and number of samples (default: montecarlo10000)\n";
    #endif
    cout << "\t" << "-v<n>" << "\t\t" << "Verbose to degree n (n defaults to 1 if not specified).\n";
    cout << "\t" << "-L<n>" << "\t\t" << "LP verbose to degree n (n defaults to 1 if not specified).\n";
};

list<FFEvent> * readPlan(char* filename);



int main(int argc, char * argv[])
{

    FAverbose = false;

    int argcount = 1;

    FF::steepestDescent = false;
    FF::incrementalExpansion = false;
    FF::invariantRPG = false;
    FF::WAStar = false;
    FF::doubleU = 4.00;
    FF::timeWAStar = true;
    FF::biasG = false;
    FF::openListOrderLowMakespanFirst = false;
    LPScheduler::hybridBFLP = false;

    bool benchmark = false;
    bool readInAPlan = false;
    bool postHocTotalOrder = false;
    bool debugPreprocessing = false;
    bool postHocScheduleToMetric = false;
    
    #ifdef STOCHASTICDURATIONS
    const char * const defaultDurationManager = "montecarlo";
 
    const char * durationManagerString = defaultDurationManager;
    #endif

    FF::useDominanceConstraintsInStateHash = true;
    LPScheduler::hybridBFLP = true;

    Globals::totalOrder = true;
    RPGBuilder::modifiedRPG = false;
    FF::tsChecking = true;

    LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction = true;

    const char* output_file = 0;
    const char* timing_output_file_name = 0;
    const char* relaxed_plan_actions_output = 0;
    const char* relaxed_actions_output = 0;
    
    while (argcount < argc && argv[argcount][0] == '-') {

        string remainder(&(argv[argcount][1]));
        if (remainder == "citation") {

            cout << "Citation for the 2012 JAIR Article on COLIN:\n\n";
            cout << "@ARTICLE{colescolinjair,\n";
            cout << "\tauthor = \"A. J. Coles and A. I. Coles and M. Fox and D. Long\",\n";
            cout << "\ttitle = \"COLIN: Planning with Continuous Linear Numeric Change\",\n";
            cout << "\tjournal = \"Journal of Artificial Intelligence Research\",\n";
            cout << "\tyear = \"2012\",\n";
            cout << "\tvolume = \"44\",\n";
            cout << "\tpages = \"1--96\"\n";
            cout << "}\n\n";

            cout << "For the 2009 IJCAI paper on COLIN:\n\n";

            cout << "@CONFERENCE{colescolinijcai,\n";
            cout << "\tauthor = \"A. J. Coles and A. I. Coles and M. Fox and D. Long\",\n";
            cout << "\ttitle = \"Temporal Planning in Domains with Linear Processes\",\n";
            cout << "\tbooktitle = \"Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 09)\",\n";
            cout << "\tyear = \"2009\",\n";
            cout << "\tpublisher = \"AAAI Press\",\n";
            cout << "\tmonth = \"July\"\n";
            cout << "}\n\n";

            cout << "COLIN, in turn, is built on CRIKEY3, which does not support continuous numeric effects.  It is still\n";
            cout << "relevant, though, as if COLIN is given a problem which does not use continuous numeric effects or actions\n";
            cout << "with duration-dependent effects, it uses an STP, as in CRIKEY3.\n\n";

            cout << "@CONFERENCE{colescrikey3aaai,\n";
            cout << "\tauthor = \"A. I. Coles and M. Fox and D. Long and A. J. Smith\",\n";
            cout << "\ttitle = \"Planning with Problems Requiring Temporal Coordination\",\n";
            cout << "\tbooktitle = \"Proceedings of the Twenty-Third AAAI Conference on Artificial Intelligence (AAAI 08)\",\n";
            cout << "\tyear = \"2008\",\n";
            cout << "\tpublisher = \"AAAI Press\",\n";
            cout << "\tmonth = \"July\"\n";
            cout << "}\n\n";

            cout << "--------------------------------------------------------------------------------\n\n";

        } else {

            switch (argv[argcount][1]) {
            #ifdef POPF3ANALYSIS
            case 'l': {
                NumericAnalysis::doGoalLimitAnalysis = false;
                break;
            }
            #endif
            case '2': {
                RPGBuilder::noSelfOverlaps = true;
                break;
            }
            case 'D': {
                Globals::paranoidScheduling = true;
                break;
            }
            case 'd': {
                FF::nonDeletorsFirst = true;
                break;
            }
            case 'P': {
                Globals::profileScheduling = true;
                break;
            }
            case 'g': {
                RPGHeuristic::setGuidance(&(argv[argcount][2]));
                break;
            }
            case '/': {
                LPScheduler::workOutFactLayerZeroBoundsStraightAfterRecentAction = false;
                break;
            }
            case 'G': {
                FF::biasG = true;
                break;
            }
            case '8': {
                FF::biasD = true;
                break;
            }
            case 'S': {
                RPGBuilder::sortedExpansion = true;
                break;
            }
            case 'F': {
                RPGBuilder::fullFFHelpfulActions = true;
                break;
            }
            #ifdef STOCHASTICDURATIONS
            case 'f': {
                solutionDeadlineTime = atof(&(argv[argcount][2]));
                break;
            }
            case 'M': {
                durationManagerString = &(argv[argcount][2]);
                break;
            }
            #else
            case 'M': {
                FF::makespanTieBreak = false;
                break;
            }
            #endif
            case 'b': {
                FF::bestFirstSearch = false;
                break;
            }
            case 'B': {
                benchmark = true;
                break;
            }
            case 'e': {
                FF::steepestDescent = true;
                break;
            }
            case 'E': {
                FF::skipEHC = true;
                break;
            }
            case 'k': {
                RPGBuilder::doSkipAnalysis = false;
                break;
            }
            case 'c': {
                RPGBuilder::modifiedRPG = false;
                break;
            }
            case 'C': {
                FF::allowCompressionSafeScheduler = true;
                break;
            }
            #ifdef ENABLE_DEBUGGING_HOOKS
            case 'H': {
                debugPreprocessing = true;
                break;
            }
            #endif
            case 'h': {
                FF::helpfulActions = false;
                break;
            }
            case 'i': {
                FF::firstImprover = true;
                break;
            }
            case 'O': {
                FF::startsBeforeEnds = false;
                break;
            }
            case 'o': {
                LPScheduler::optimiseOrdering = false;
                break;
            }
            case 'p': {
                FF::pruneMemoised = false;
                break;
            }
            case 'R': {
                FF::invariantRPG = true;
                break;
            }
            case 'q': {
                FF::useDominanceConstraintsInStateHash = false;
                break;
            }
            case 'T': {
                Globals::totalOrder = true;
                RPGBuilder::modifiedRPG = false;
                FF::tsChecking = true;
                if (argv[argcount][2] == 'T') {
                    postHocTotalOrder = true;
                }
                break;
            }
            case 't': {
                FF::tsChecking = false;
                break;
            }
            case 'X': {
                NumericAnalysis::readBounds = true;
                break;
            }
            case 'Q': {
                postHocScheduleToMetric = true;
                break;
            }
            case 'v': {
                if (argv[argcount][2] != 0) {
                    Globals::writeableVerbosity = atoi(&(argv[argcount][2]));
                } else {
                    cout << "No verbosity level specified with -v, defaulting to 1\n";
                    Globals::writeableVerbosity = 1;
                }
                break;
            }
            case 'L': {
                if (argv[argcount][2] != 0) {
                    LPScheduler::lpDebug = atoi(&(argv[argcount][2]));
                } else {
                    LPScheduler::lpDebug = 255;
                }
                break;
            }
            case 'W': {
                FF::doubleU = atof(&(argv[argcount][2]));
                break;
            }
            case 'I': {
                LPScheduler::hybridBFLP = false;
                break;
            }
            case 'r': {
                readInAPlan = true;
                break;
            }
            case 's': {
                FF::planMustSucceed = true;
                break;
            }
            case 'z': {
                FF::zealousEHC = false;
                break;
            }
            case 'Z': {
                RPGHeuristic::printRPGAsDot = true;
                break;
            }
            #ifdef POPF3ANALYSIS
            case 'n': {
                Globals::optimiseSolutionQuality = true;
                break;
            }
            #endif
            case 'a': { // ALD: plan output file...a was left
                output_file = argv[++argcount];
                break;
            }
            case 'y': { // ALD: record information on memory and timing
                timing_output_file_name = argv[++argcount];
                break;
            }
            case 'x': { // ALD: generate and output relaxed plan actions
                relaxed_plan_actions_output = argv[++argcount];
                relaxed_actions_output = argv[++argcount];
                break;
            }
            case 'j': { // ALD: check if a relaxed plan for the problem exists
                Globals::rpOnly = true;
                break;
            }
            default:
                cout << "Unrecognised command-line switch '" << argv[argcount][1] << "'\n";
                usage(argv);
                exit(0);

            }

        }
        ++argcount;
    }

    // ALD
    std::chrono::system_clock::time_point start = std::chrono::system_clock::now();

    #ifdef STOCHASTICDURATIONS
    const int expectFromHere = 3;
    #else 
    const int expectFromHere = 2;
    #endif

    if (argcount + ((readInAPlan || debugPreprocessing) ? expectFromHere + 1 : expectFromHere) > argc) {
        usage(argv);
        exit(0);
    }

    #ifdef STOCHASTICDURATIONS
    solutionDeadlinePercentage = atof(argv[argcount]);
    ++argcount;
    #endif

    performTIMAnalysis(&argv[argcount]);

    cout << std::setprecision(3) << std::fixed;

    #ifdef STOCHASTICDURATIONS
    setDurationManager(durationManagerString);
    #endif

    #ifdef TOTALORDERSTATES
    MinimalState::setTransformer(new TotalOrderTransformer());
    #else    
    if (Globals::totalOrder) {
        MinimalState::setTransformer(new TotalOrderTransformer());
    } else {
        MinimalState::setTransformer(new PartialOrderTransformer());
    }
    #endif

    #ifdef ENABLE_DEBUGGING_HOOKS    
    if (debugPreprocessing) {
        Globals::planFilename = argv[argc - 1];
    }
    #endif
    
    #ifdef POPF3ANALYSIS
    const bool realOpt = Globals::optimiseSolutionQuality;
    Globals::optimiseSolutionQuality = (Globals::optimiseSolutionQuality || postHocScheduleToMetric);
    #endif
    
    set<string> relaxed_actions;
    RPGBuilder::initialise(&relaxed_actions);

    #ifdef POPF3ANALYSIS
    Globals::optimiseSolutionQuality = realOpt;
    #endif
    
    #ifdef STOCHASTICDURATIONS
    initialiseDistributions();            
    setSolutionDeadlineTimeToLatestGoal();
    #endif
    
    
    bool reachesGoals;
    
    Solution planAndConstraints;
    
    list<FFEvent> * & spSoln = planAndConstraints.plan;

    if(relaxed_plan_actions_output || Globals::rpOnly)
    {
      map<double, ActionLevel> relaxed_plan = FF::get_relaxed_plan();

      // don't need output
      if(Globals::rpOnly)
        return 0;

      ofstream plan_output(relaxed_plan_actions_output);
      ofstream actions_output(relaxed_actions_output);
      for(map<double, ActionLevel>::const_reference e : relaxed_plan)
      {
        plan_output << e.first << endl;
        for(const string& s : e.second.plan_actions)
          plan_output << s << endl;

        actions_output << e.first << endl;
        for(const string& a : e.second.possible_actions)
          actions_output << a << endl;
      }


      if(timing_output_file_name)
      {
        struct rusage r;
        getrusage(RUSAGE_SELF, &r);
        std::chrono::system_clock::time_point end = std::chrono::system_clock::now();
        std::ofstream output(timing_output_file_name);
        output << r.ru_maxrss << "," << std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
      }
      
      return 0;
    }

    if (readInAPlan) {
        spSoln = readPlan(argv[argc - 1]);
        reachesGoals = true;
#ifndef NDEBUG
        spSoln = FF::doBenchmark(reachesGoals, spSoln, false);
#endif
    } else {
        planAndConstraints = FF::search(reachesGoals);
    }

    if (spSoln) {
        
        for (int pass = 0; pass < 2; ++pass) {
            if (pass) {
                if (!postHocScheduleToMetric) break;
                #ifndef TOTALORDERSTATES                                                
                if (!spSoln->empty()) {
                    if (Globals::totalOrder && !postHocTotalOrder) {
                        MinimalState::setTransformer(new PartialOrderTransformer());
                        Globals::totalOrder = false;
                        FF::tsChecking = false;
                    }
                    assert(planAndConstraints.constraints);
                    spSoln = FF::reprocessPlan(spSoln, planAndConstraints.constraints);
                    planAndConstraints.constraints = 0;
                }
                cout << ";;;; Post-hoc optimised solution\n";
                #endif
            } else {
                cout << ";;;; Solution Found\n";
                cout << "; States evaluated: " << RPGHeuristic::statesEvaluated << endl;
                cout << "; Cost: " << planAndConstraints.quality << endl;
            }
            
            if(output_file)
            {
                std::ofstream o_file(output_file);
                FFEvent::printPlan(*spSoln, RPGHeuristic::statesEvaluated, planAndConstraints.quality, o_file);
            }
            else
            {
                FFEvent::printPlan(*spSoln);
            }
        }

        if (benchmark) {
            FF::doBenchmark(reachesGoals, spSoln);
        }

        if(timing_output_file_name)
        {
            struct rusage r;
            getrusage(RUSAGE_SELF, &r);
            std::chrono::system_clock::time_point end = std::chrono::system_clock::now();
            std::ofstream output(timing_output_file_name);
            output << r.ru_maxrss << "," << std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        }

        return 0;
    } else {
        cout << ";; Problem unsolvable!\n";
        tms refReturn;
        times(&refReturn);
        double secs = ((double)refReturn.tms_utime + (double)refReturn.tms_stime) / ((double) sysconf(_SC_CLK_TCK));

        int twodp = (int)(secs * 100.0);
        int wholesecs = twodp / 100;
        int centisecs = twodp % 100;

        cout << "; Time " << wholesecs << ".";
        if (centisecs < 10) cout << "0";
        cout << centisecs << "\n";
        return 1;
    }


}

extern int yyparse();
extern int yydebug;

void split(const int & insAt, list<FFEvent>::iterator insStart, const list<FFEvent>::iterator & insItr, const list<FFEvent>::iterator & insEnd)
{

    {
        for (; insStart != insItr; ++insStart) {
            int & currPWS = insStart->pairWithStep;
            if (currPWS != -1) {
                if (currPWS >= insAt) {
                    ++currPWS;
                }
            }
        }
    }
    {
        list<FFEvent>::iterator insPost = insItr;
        for (; insPost != insEnd; ++insPost) {
            int & currPWS = insPost->pairWithStep;
            if (currPWS != -1) {
                if (insPost->time_spec == VAL::E_AT_START) {
                    ++currPWS;
                } else if (insPost->time_spec == VAL::E_AT_END) {
                    if (currPWS >= insAt) {
                        ++currPWS;
                    }
                }
            }
        }
    }
}

namespace VAL
{
extern yyFlexLexer* yfl;
};

list<FFEvent> * readPlan(char* filename)
{
    static const bool debug = true;

    ifstream * const current_in_stream = new ifstream(filename);
    if (!current_in_stream->good()) {
        cout << "Exiting: could not open plan file " << filename << "\n";
        exit(1);
    }

    VAL::yfl = new yyFlexLexer(current_in_stream, &cout);
    yyparse();

    VAL::plan * const the_plan = dynamic_cast<VAL::plan*>(top_thing);

    delete VAL::yfl;
    delete current_in_stream;



    if (!the_plan) {
        cout << "Exiting: failed to load plan " << filename << "\n";
        exit(1);
    };

    if (!theTC->typecheckPlan(the_plan)) {
        cout << "Exiting: error when type-checking plan " << filename << "\n";
        exit(1);
    }

    list<FFEvent> * const toReturn = new list<FFEvent>();

    pc_list<plan_step*>::const_iterator planItr = the_plan->begin();
    const pc_list<plan_step*>::const_iterator planEnd = the_plan->end();

    for (int idebug = 0, i = 0; planItr != planEnd; ++planItr, ++i, ++idebug) {
        plan_step* const currStep = *planItr;

        instantiatedOp * const currOp = instantiatedOp::findInstOp(currStep->op_sym, currStep->params->begin(), currStep->params->end());
        if (!currOp) {
            const instantiatedOp * const debugOp = instantiatedOp::getInstOp(currStep->op_sym, currStep->params->begin(), currStep->params->end());
            cout << "Exiting: step " << idebug << " in the input plan uses the action " << *(debugOp) << ", which the instantiation code in the planner does not recognise.\n";
            exit(1);
        }
        const int ID = currOp->getID();

        if (RPGBuilder::getRPGDEs(ID).empty()) {// non-durative action
            FFEvent toInsert(currOp, 0.001, 0.001);
            const double ts = currStep->start_time;
            if (debug) cout << "; input " << ts << ": " << *currOp << " (id=" << ID << "), non-temporal";
            toInsert.lpTimestamp = ts;
            toInsert.lpMinTimestamp = ts;
            int insAt = 0;
            list<FFEvent>::iterator insItr = toReturn->begin();
            const list<FFEvent>::iterator insEnd = toReturn->end();
            for (; insItr != insEnd; ++insItr, ++insAt) {
                if (ts < insItr->lpTimestamp) {
                    split(insAt, toReturn->begin(), insItr, insEnd);
                    toReturn->insert(insItr, toInsert);
                    break;
                }
            }
            if (insItr == insEnd) {
                toReturn->push_back(toInsert);
            }
            if (debug) cout << " putting at step " << insAt << "\n";
        } else {
            int startIdx = -1;
            list<FFEvent>::iterator startIsAt = toReturn->end();
            const double actDur = currStep->duration;
            for (int pass = 0; pass < 2; ++pass) {
                if (pass) assert(startIdx >= 0);
                const double ts = (pass ? currStep->start_time + actDur : currStep->start_time);
                if (debug) {
                    cout << "; input " << ts << ": " << *currOp;
                    if (pass) {
                        cout << " end";
                    } else {
                        cout << " start";
                    }
                    cout << " (id=" << ID << ")";
                }
                FFEvent toInsert = (pass ? FFEvent(currOp, startIdx, actDur, actDur) : FFEvent(currOp, actDur, actDur));
                toInsert.lpTimestamp = ts;
                toInsert.lpMinTimestamp = ts;

                list<FFEvent>::iterator insItr = toReturn->begin();
                const list<FFEvent>::iterator insEnd = toReturn->end();
                int insAt = 0;
                for (; insItr != insEnd; ++insItr, ++insAt) {
                    if (ts < insItr->lpTimestamp) {
                        split(insAt, toReturn->begin(), insItr, insEnd);
                        const list<FFEvent>::iterator dest = toReturn->insert(insItr, toInsert);
                        if (pass) {
                            startIsAt->pairWithStep = insAt;
                            if (debug) cout << " putting at step " << insAt << ", pairing with " << startIdx << "\n";
                        } else {
                            startIsAt = dest;
                            startIdx = insAt;
                            if (debug) cout << " putting at step " << insAt << "\n";
                        }
                        break;
                    }
                }
                if (insItr == insEnd) {
                    toReturn->push_back(toInsert);
                    if (pass) {
                        startIsAt->pairWithStep = insAt;
                        if (debug) cout << " putting at step " << insAt << ", pairing with " << startIdx << "\n";
                    } else {
                        startIsAt = toReturn->end();
                        --startIsAt;
                        startIdx = insAt;
                        if (debug) cout << " putting at step " << insAt << "\n";
                    }
                }

            }
        }
    }

    const vector<RPGBuilder::FakeTILAction*> & tils = RPGBuilder::getTILVec();
    const int tilCount = tils.size();

    for (int t = 0; t < tilCount; ++t) {
        FFEvent toInsert(t);
        const double tilTS = tils[t]->duration;
        toInsert.lpMaxTimestamp = tilTS;
        toInsert.lpMinTimestamp = tilTS;
        toInsert.lpTimestamp = tilTS;

        if (debug) {
            cout << "TIL " << toInsert.divisionID << " goes at " << tilTS << endl;
        }
        
        list<FFEvent>::iterator insItr = toReturn->begin();
        const list<FFEvent>::iterator insEnd = toReturn->end();
        for (int insAt = 0; insItr != insEnd; ++insItr, ++insAt) {
            if (tilTS < insItr->lpTimestamp) {
                split(insAt, toReturn->begin(), insItr, insEnd);
                toReturn->insert(insItr, toInsert);
                break;
            }
        }
        if (insItr == insEnd) {
            toReturn->push_back(toInsert);
        }
    }

    if (debug) {
        list<FFEvent>::iterator insItr = toReturn->begin();
        const list<FFEvent>::iterator insEnd = toReturn->end();
        
        for (int i = 0; insItr != insEnd; ++insItr, ++i) {
            cout << i << ": ";
            if (insItr->action) {
                cout << *(insItr->action);
                if (insItr->time_spec == VAL::E_AT_START) {
                    cout << " start\n";
                } else {
                    cout << " end\n";
                }
            } else {
                cout << "TIL " << insItr->divisionID << endl;
            }
        }
    }

    return toReturn;
};

