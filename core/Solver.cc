/***************************************************************************************[Solver.cc]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010, Niklas Sorensson

Glucose is Copyrighted  G. Audemard and L. Simon 2009-2015 (See www.labri.fr/users/lsimon/glucose)
Some parts are from Chanseok Oh's MiniSat Patch Series -- Copyright (c) 2015, Chanseok Oh
Some parts are from K. Sakallah, J.M. Silva
Integration of different techniques were made by J. Giraldez, J. Elffers, J. Nordstrom, L. Simon 2016-2017

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include <vector>
#include "utils/System.h" // For the CPU time
#include "mtl/Sort.h"
#include "core/Solver.h"

using namespace Minisat;

#define endl "\n"

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static StringOption opt_fileout  (_cat, "fileout", "File to write the output (if empty value, it prints in stdout)", "");
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full,3=random, 4=opposite)", 2, IntRange(0, 4));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static BoolOption    opt_disable_learning  (_cat, "dis-learn",   "Disable the learning procedure, follows a simple backtrack search, not using any info from the conflict analysis", false);
static BoolOption    opt_disable_deletion  (_cat, "dis-deletion","Disable clause deletion in the learning procedure", false);
static BoolOption    opt_disable_restart   (_cat, "dis-restart", "Disable random restart", false);
static BoolOption    opt_apply_pure_lit    (_cat, "pure",        "Assign pure literals prior to search", false);
static BoolOption    opt_CHB              (_cat, "CHB",        "Use CHB (Conflict History-based Branching Heuristic) as branching heuristic", false);
static DoubleOption  opt_CHB_a      (_cat, "CHB-a",     "The 'a' value for the CHB heuristics",  0.7, DoubleRange(0, false, HUGE_VAL, false));
static BoolOption    opt_LRB               (_cat, "LRB", "Use LRB (Learning Rate Based) as branching heuristic", false);
static DoubleOption  opt_lrb_step_size     (_cat, "lrb-step-size",   "LRB: Initial step size",      0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_lrb_step_size_dec (_cat, "lrb-step-size-dec","LRB: Step size decrement",   0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_lrb_min_step_size (_cat, "lrb-min-step-size","LRB: Minimal step size",     0.06,     DoubleRange(0, false, 1, false));
static BoolOption    opt_lbd_score      (_cat, "lbd-score","Use LBD clause base reduction scoring", false);
static BoolOption    opt_glucose_frequency     (_cat, "glucose-freq",         "Use LBD clause base reduction frequency strategy", false);
static BoolOption    opt_minisat_frequency  (_cat, "minisat-freq",         "Use original minisat deletion frequency strategy", true);
static BoolOption    opt_activity_score  (_cat, "vsids-score",         "Use original minisat deletion strategy for scoring clauses", true);
static BoolOption    opt_lbd_restarts      (_cat, "lbd-restarts","Use LBD-based restarts", false);
static BoolOption    opt_fixed_order      (_cat, "fixed-order","Uses the static, fixed branching order 1,2,3,...", false);
static IntOption     opt_first_reduce_db(_cat, "firstReduceDB", "The number of conflicts before the first reduce DB", 2000, IntRange(0, INT32_MAX));
static IntOption     opt_inc_reduce_db(_cat, "incReduceDB", "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static DoubleOption     opt_factor_reduce_db(_cat, "factorReduceDB", "Factor for reduce DB (used in CE:lin)", 1.2, DoubleRange(0.0, false, HUGE_VAL, false));


BoolOption          opt_binary            (_cat, "binary", "binary clause special handling", true); // make this to false for Minisat
static BoolOption   opt_extra_var_act_bump (_cat, "extraVarBump", "Extra Bump of variable activity (like in Glucose), related to LBD.", false); // Make this to false for Minisat-like

// To make things clear, the options used in the paper are here.
static const char* _catTheory = "THEORY PARAMETERS"; // Options to be handled by the experimentation on theoretical problems
static StringOption opt_RE_restartPolicy  (_catTheory, "RE", "Restart Policy in ('no', 'lbd', 'luE1', 'luE3')", "");
static StringOption opt_CL_clauseLearning (_catTheory, "CL", "Clause Learning Variants in ('1uip', 'Luip')", "");
static StringOption opt_VD_variableDecision (_catTheory, "VD", "Variable Decision Heuristics in ('fix', 'rnd', 'chb', 'df99', 'df95', 'df80', 'df65', 'lrb')", "");
static StringOption opt_PH_phaseHeuristics(_catTheory, "PH", "Phase Saving Heuristics in ('dynrnd', 'fix0', 'fixrnd', 'ctr', 'std')", "");
static StringOption opt_CE_clauseErasure(_catTheory, "CE", "Clause Erasure Policy (when and how many clauses to remove) in ('no', 'lin', 'glu', 'min', 'dpll')", "");
static StringOption opt_CA_clauseAssessment(_catTheory, "CA", "Clause Assessment Policy (scoring clauses) in ('none', 'rnd', 'vsids', 'lbd')", "");

void Solver::handleTheoryOptions() {
  fprintf(fileout,"c WARNING: Please use only Theory Options, or general options that are compatible with.\n");
  if (opt_random_var_freq > 0)
    fprintf(fileout,"c WARNING random-var-freq is not 0. Branching heuristics is not compatible.\n");
  // handles the restart policy
  if (strlen(opt_RE_restartPolicy) > 0) {
    if (!strcmp(opt_RE_restartPolicy,"no")) {
      opt_lbd_restarts = false;
      opt_disable_restart = true;
      luby_restart = false;
    } else if (!strcmp(opt_RE_restartPolicy,"lbd")) {
      compute_lbd= true;
      opt_lbd_restarts = true;
      opt_disable_restart = false;
      luby_restart = false;
    } else if (!strcmp(opt_RE_restartPolicy,"luE2")) {
      opt_lbd_restarts = false;
      opt_disable_restart = false;
      luby_restart = true;
      restart_first = 100;
      restart_inc = 2;
    } else if (!strcmp(opt_RE_restartPolicy,"luE3")) {
      opt_lbd_restarts = false;
      opt_disable_restart = false;
      luby_restart = true;
      restart_first = 1000;
      restart_inc = 2;
    } else {
      fprintf(fileout,"c WARNING wrong RE argument\n");
    }
  }
  if(!opt_lbd_restarts && !luby_restart && !opt_disable_restart){
	  fprintf(fileout,"c ERROR: No RE (restart) option defined!\n");
	  exit(-1);
  }

  // handles the CL parameter
  if (strlen(opt_CL_clauseLearning) > 0) {
    if (!strcmp(opt_CL_clauseLearning, "1uip"))
      lastUIP = false;
    else if (!strcmp(opt_CL_clauseLearning, "Luip"))
      lastUIP = true;
    else
      fprintf(fileout,"c WARNING wrong CL argument\n");
  }

  if (strlen(opt_VD_variableDecision) > 0) {
    if (!strcmp(opt_VD_variableDecision, "fix")) {
      opt_fixed_order = true;
	  randomBranching = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "rnd")) {
      randomBranching = true;
      // the random branching is just: assign a random value to the activity each time a value is
      // pushed back in the heap (also : don't varbump anything)
      opt_fixed_order = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "chb")) {
      CHB = true;
      opt_fixed_order = false;
	  randomBranching = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "df99")) {
      var_decay = 0.99;
      opt_fixed_order = false;
      randomBranching = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "df95")) {
      var_decay = 0.95;
      opt_fixed_order = false;
      randomBranching = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "df80")) {
      var_decay = 0.80;
	  opt_fixed_order = false;
      randomBranching = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "df65")) {
      var_decay = 0.65;
	  opt_fixed_order = false;
      randomBranching = false;
	  CHB = false;
	  LRB = false;
    } else if (!strcmp(opt_VD_variableDecision, "lrb")) {
      LRB = true;
	  opt_fixed_order = false;
      randomBranching = false;
	  CHB = false;
    } else
      fprintf(fileout,"c WARNING wrong VD argument\n");
  }

  if (strlen(opt_PH_phaseHeuristics) > 0) {
    if (!strcmp(opt_PH_phaseHeuristics, "dynrnd")) {
      rnd_pol = true;
      phase_saving = 3; // I assign it but this argument just set rnd_pol to true in the constructor
    } else if (!strcmp(opt_PH_phaseHeuristics, "fix0")) {
      // init of the polarity vector is needed, and done in solve_
      rnd_pol = false;
      phase_saving = 0; // don't update anything in the polarity
    } else if (!strcmp(opt_PH_phaseHeuristics, "fixrnd")) {
      // init of the polarity vector is needed, and done in solve_
      rnd_pol = false;
      phase_saving = 0; // don't update anything in the polarity
    } else if (!strcmp(opt_PH_phaseHeuristics, "ctr")) {
      rnd_pol = false;
      phase_saving = 4;
    } else if (!strcmp(opt_PH_phaseHeuristics, "std")) {
      rnd_pol = false;
      phase_saving = 2;
    } else
      fprintf(fileout,"c WARNING wrong PH argument\n");
  }

  if (strlen(opt_CE_clauseErasure) > 0) {
    if (!strcmp(opt_CE_clauseErasure, "no")) {
      opt_disable_deletion=true;
      opt_glucose_frequency = false;
      opt_minisat_frequency = false;
      ce_lin = false;
	  dpll = false;
    } else if (!strcmp(opt_CE_clauseErasure, "min")) { // Glucose but keeping linear of clauses
      ce_lin = false;
      opt_disable_deletion=false;
      opt_glucose_frequency = false;
	  dpll = false;
      opt_minisat_frequency = true;
      learntsize_factor = (double)1/(double)3; // Just making these 2 constants clearly appearing
      // First reduction will occur after having learning m / 3 clauses (1/3 of original clauses)
      learntsize_inc = 1.1;
    } else if (!strcmp(opt_CE_clauseErasure, "glu")) { // Glucose but keeping square root
      compute_lbd = true;
      opt_disable_deletion = opt_minisat_frequency = ce_lin = dpll = false;
      opt_glucose_frequency = true;
      nbclausesbeforereduce = opt_first_reduce_db;
      incReduceDB = opt_inc_reduce_db;
    } else if (!strcmp(opt_CE_clauseErasure, "lin")) {
      opt_disable_deletion = opt_glucose_frequency= opt_minisat_frequency = dpll = false;
      ce_lin = true;
      nbclausesbeforereduce = opt_first_reduce_db;
      factorReduceDB = opt_factor_reduce_db;
    } else if (!strcmp(opt_CE_clauseErasure, "dpll")) {
      opt_disable_deletion=true; // no more need this now, only clauses of size 2 are kept
      opt_glucose_frequency = opt_minisat_frequency = ce_lin = false;
      dpll = true;
      ccmin_mode = 0; // Force no minimization here
      opt_binary = false; // No binary clause minimization
    } else
      fprintf(fileout,"c WARNING wrong CE argument\n");
  }

  if (strlen(opt_CA_clauseAssessment) > 0) {
    if (!strcmp(opt_CA_clauseAssessment, "rnd")) {
      ca_random = true;
      ca_lbd = ca_vsids = false;
    } else if (!strcmp(opt_CA_clauseAssessment, "vsids")) {
      ca_vsids = true;
      ca_lbd = ca_random = false;
    } else if (!strcmp(opt_CA_clauseAssessment, "lbd")) {
      compute_lbd = true;
      ca_lbd = true;
      ca_vsids = ca_random = false;
    } else if(!strcmp(opt_CA_clauseAssessment, "none")){ // for CE=dpll
    	ca_lbd = ca_vsids = ca_random = false;
    } else
      fprintf(fileout,"c WARNING wrong CA argument\n");
  }
}

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (opt_phase_saving==3)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)
  , compute_lbd      (opt_lbd_score || opt_glucose_frequency || opt_lbd_restarts)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

  , learntsize_output_cnt   (50)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , sumDecisionLevels(0), sumTrailSize(0), nbBin(0), nbUn(0), sumBackJumpSize(0)
  , statsNbResolutions(0), statsNbMergedLiterals(0), tot_literals_binary(0)
  , nbOriginalSeenInConflicts(0), nbLearntSeenInConflicts(0), nbRemovedSeenInConflicts(0), nbRemovedClauses(0)
  , nbUIP(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , watchesBin         (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

  , global_lbd_sum     (0)
  , lbd_queue          (50)
  , trail_sz_queue     (5000)
  , nbclausesbeforereduce(opt_first_reduce_db)
  , incReduceDB(opt_inc_reduce_db)
  , factorReduceDB(opt_factor_reduce_db)
  , curRestart(1)



  , MYFLAG            (0)
  , lastUIP (false)

     	//CHB
     , CHB(opt_CHB)
     , chb_a(opt_CHB_a)
     , chb_m(0.9)
     , chb_da(1e-6)
     , chb_ae(0.06)
     , chb_c (0)
     , chb_p (0)
//     , chb_b (0)

     // LRB
     , LRB(opt_LRB)
     , lrb_step_size        (opt_lrb_step_size)
     , lrb_step_size_dec    (opt_lrb_step_size_dec)
     , lrb_min_step_size    (opt_lrb_min_step_size)

     , randomBranching(false)
     , nbReduceDB(0)
     , json(true)
     , dpll(false)
     , ca_vsids(opt_activity_score)
     , ca_random(false)
     , ca_lbd(opt_lbd_score)
     , ce_lin(false)
    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  , filenameout(opt_fileout)
{
	if(!strcmp(filenameout, ""))
		fileout = stdout;
	else
		fileout = fopen(filenameout, "w");
 handleTheoryOptions();

 std::ios::sync_with_stdio(false);
}


Solver::~Solver()
{
	//fclose(fileout);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    if (opt_binary) {
	watchesBin.init(mkLit(v, false));
	watchesBin.init(mkLit(v, true ));
    }
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    /* lit_clause.init(mkLit(v, false)); */
    /* lit_clause.init(mkLit(v, true)); */
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    unresolved.push(0);
    unresolved.push(0);
    //DIS_index.push(-1);
    seen     .push(0);
    permDiff    .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    if (CHB)
      chb_lconf.push(0);
    if(LRB){
      lrb_picked.push(0);
      lrb_conflicted.push(0);
      lrb_almost_conflicted.push(0);
      lrb_canceled.push(0);
      lrb_total_actual_rewards.push(0);
      lrb_total_actual_count.push(0);
    }
    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}

void Solver::attachClause(CRef cr) {
    twoLitWatch(cr);
}

void Solver::twoLitWatch(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = (opt_binary && c.size() == 2) ? watchesBin : watches;
    ws[~c[0]].push(Watcher(cr, c[1]));
    ws[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    removeTwoLitWatch(cr, strict);
}

void Solver::removeTwoLitWatch(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = (opt_binary && c.size() == 2) ? watchesBin : watches;

    if (strict){
        remove(ws[~c[0]], Watcher(cr, c[1]));
        remove(ws[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        ws.smudge(~c[0]);
        ws.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];

    nbRemovedClauses ++;
    if (c.is_seen_analysis())
      nbRemovedSeenInConflicts++;
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)){
        Lit implied = c.size() != 2 ? c[0] : (value(c[0]) == l_True ? c[0] : c[1]);
        vardata[var(implied)].reason = CRef_Undef; }
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//

void Solver::cancelUntilLRB(int level) {
      if (decisionLevel() > level){
	    if (dpll) { // Removing the clauses still in the stack of learnt clauses
	      dpll_ca.reduceSizeTo(dpll_ca_size_for_level[level]);
	      dpll_ca_size_for_level.shrink(dpll_ca_size_for_level.size() - level);
	    }
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
          Var      x  = var(trail[c]);
          uint64_t age = conflicts - lrb_picked[x];
          if (age > 0) {
            double reward = ((double) lrb_conflicted[x]) / ((double) age);
            double adjusted_reward = ((double) (lrb_conflicted[x] + lrb_almost_conflicted[x])) / ((double) age);
            double old_activity = activity[x];
            activity[x] = lrb_step_size * adjusted_reward + ((1 - lrb_step_size) * old_activity);
            if (order_heap.inHeap(x)) {
              if (activity[x] > old_activity)
                order_heap.decrease(x);
              else
                order_heap.increase(x);
            }
            lrb_total_actual_rewards[x] += reward;
            lrb_total_actual_count[x] ++;
          }
          lrb_canceled[x] = conflicts;
          assigns [x] = l_Undef;
	      if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last())){
			  if(reason(var(trail[c])) == CRef_Undef) // it is a decision
			      polarity[x] = sign(trail[c]);
			  else // it is a propagation. special treatment for PH:ctr
	        	  polarity[x] = (phase_saving == 4 ? !sign(trail[c]) : sign(trail[c]));
		  }
          insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
      }
}

void Solver::cancelUntilOriginal(int level) {
  if (decisionLevel() > level){
    if (dpll) { // Removing the clauses still in the stack of learnt clauses
      dpll_ca.reduceSizeTo(dpll_ca_size_for_level[level]);
      dpll_ca_size_for_level.shrink(dpll_ca_size_for_level.size() - level);
    }
    for (int c = trail.size()-1; c >= trail_lim[level]; c--){
      Var      x  = var(trail[c]);
      assigns [x] = l_Undef;
      if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last())){
		  if(reason(var(trail[c])) == CRef_Undef) // it is a decision
		      polarity[x] = sign(trail[c]);
		  else // it is a propagation. special treatment for PH:ctr
        	  polarity[x] = (phase_saving == 4 ? !sign(trail[c]) : sign(trail[c]));
	  }
      if (randomBranching)
        activity[x] = drand(random_seed);
      insertVarOrder(x);
    }
    qhead = trail_lim[level];
    trail.shrink(trail.size() - trail_lim[level]);
    trail_lim.shrink(trail_lim.size() - level);
  }
}




//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        } else {
          if (LRB){
            next = order_heap[0];
            uint64_t age = conflicts - lrb_canceled[next];
            while (age > 0) {
              double decay = pow(0.95, age);
              activity[next] *= decay;
              if (order_heap.inHeap(next)) {
                order_heap.increase(next);
              }
              lrb_canceled[next] = conflicts;
              next = order_heap[0];
              age = conflicts - lrb_canceled[next];
            }
          }
          next = order_heap.removeMin();
        }

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.

|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)

        Clause &c = (dpll && p!=lit_Undef && tmpReason(var(p)))?dpll_ca[confl]:ca[confl];

        // Prints to trace the fact that we are using this clause
        // Format will be U x where
        // x = current CRef of clause
        if(REFUTATION_TRACING) std::cout << "U " << confl << endl;

        // Just maintains stats about the clauses seen in conflict analysis
        if (!c.is_seen_analysis()) {
            c.set_seen_analysis(true);
            if (c.learnt())
                nbLearntSeenInConflicts++;
            else
                nbOriginalSeenInConflicts++;
        }
        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (opt_binary && p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }

        if (!ca_random && /*!opt_DLIS && */ c.learnt())
            claBumpActivity(c);

        // Update LBD if improved.
        if (compute_lbd && c.learnt() && c.lbd() > 2){
            int lbd = computeLBD(c);
            if (lbd + 1 < c.lbd()){
                if (c.lbd() <= 30 && ca_lbd ) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd); }
        }

        statsNbResolutions++;
        std::vector<Lit> skipped;

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (seen[var(q)]) {
                statsNbMergedLiterals++;
            } else {
                if (level(var(q)) > 0) {
                    // We just bump the variable for VSIDS cases
                    if (/*!opt_DLIS &&*/ !opt_fixed_order) {
                        if (CHB)
                            chb_lconf[var(q)] = conflicts;
                        else if (!randomBranching)
                            varBumpActivity(var(q));
                    }
                    if(LRB)
                        lrb_conflicted[var(q)]++;
                    seen[var(q)] = 1;
                    if (level(var(q)) >= decisionLevel()) {
                        if (opt_extra_var_act_bump && reason(var(q)) != CRef_Undef && caReason(var(q)).learnt())
                            lastDecisionLevel.push(q);
                        pathC++;
                    } else {
                        out_learnt.push(q);
                    }
                } else {
                    assert(level(var(q)) == 0);
                    skipped.push_back(q);
                }
            }
        }

        // Print to the trace the fact that we are skipping literals
        // Format will be S n x y, where
        // n = the number of skipped literals
        // x, y = skipped literals
        if(REFUTATION_TRACING && skipped.size() > 0)
        {
            std::cout << "S " << skipped.size();
            for(Lit l : skipped) std::cout << " " << l;
            std::cout << endl;
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

        if (lastUIP && pathC==0) nbUIP++;
    }while ((pathC > 0) || (lastUIP && confl != CRef_Undef));

    statsNbResolutions--; // don't count the first iteration as a resolution

    if (lastUIP) assert(pathC==0); // Just checking that for this special mode of operation

    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        std::vector<Lit> minimized_literals;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++) {
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level)) {
                out_learnt[j++] = out_learnt[i];
            } else {
                minimized_literals.push_back(out_learnt[i]);
            }
        }

        if(REFUTATION_TRACING && (minimized_literals.size() > 0)) {
            // Print to the trace the fact that we minimize away literals
            // using mode 2
            // Format will be MNM2 n x y, where
            // n = the number of literals
            // x, y = literals
            std::cout << "MNM2 " << minimized_literals.size();
            for(int i=0; i < minimized_literals.size(); i++) std::cout << " " << minimized_literals[i];
            std::cout << endl;
        }

    }else if (ccmin_mode == 1){
        std::vector<Lit> minimized_literals;

        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Var v = var(out_learnt[i]);
                Clause &c = (dpll && tmpReason(v))?dpll_ca[reason(v)]:ca[reason(v)];

                bool minimized = true;

                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
                {
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        minimized = false;
                        break;
                    } else if(level(var(c[k])) == 0) {
                        // Literals at level 0 need to be minimized away
                        // (minisat implicitly ignored them)
                        minimized_literals.push_back(c[k]);
                    }
                }

                if(REFUTATION_TRACING && minimized) minimized_literals.push_back(out_learnt[i]);
            }
        }

        if(REFUTATION_TRACING && minimized_literals.size() > 0) {
            // Print to the trace the fact that we minimize away literals
            // Format will be MNM n x y, where
            // n = the number of literals
            // x, y = literals
            std::cout << "MNM " << minimized_literals.size();
            for(int i=0; i < minimized_literals.size(); i++) std::cout << " " << minimized_literals[i];
            std::cout << endl;
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    if (opt_binary && out_learnt.size() <= 30) {
        minimisationWithBinaryResolution(out_learnt);
    }

    tot_literals_binary += out_learnt.size();

    out_lbd = computeLBD(out_learnt);

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    if(LRB){
        seen[var(p)] = true;
        for(int i = out_learnt.size() - 1; i >= 0; i--) {
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if (rea != CRef_Undef) {
                Clause& reaC = (dpll && tmpReason(v))?dpll_ca[rea]:ca[rea]; // FIXME: with DPLL option
                for (int i = 0; i < reaC.size(); i++) {
                    Lit l = reaC[i];
                    if (!seen[var(l)]) {
                        seen[var(l)] = true;
                        lrb_almost_conflicted[var(l)]++;
                        analyze_toclear.push(l);
                    }
                }
            }
        }
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    if (opt_extra_var_act_bump) {
        // Don't bump the variables if we are in fixed order
        if (lastDecisionLevel.size() > 0 /*&& !opt_DLIS*/ && !opt_fixed_order){
            for (int i = 0; i< lastDecisionLevel.size(); i++) {
                Var v = var(lastDecisionLevel[i]);
                if (caReason(v).lbd() < out_lbd) {
                    if (CHB) // FIXME Note: I don't get his extra bump for CHB...
                        // This is taken from tc_glucose but I don't understand the side effect of this
                        chb_lconf[var(lastDecisionLevel[i])]  = conflicts;
                    else if (!randomBranching && !LRB)
                        varBumpActivity(var(lastDecisionLevel[i]));
                }
            }
        }
        lastDecisionLevel.clear();
    }
}


/******************************************************************
 * Minimisation with binary reolution
 ******************************************************************/
void Solver::minimisationWithBinaryResolution(vec<Lit> &out_learnt) {

    // Find the LBD measure (it will be recomputed outside this function)
    unsigned int lbd = computeLBD(out_learnt);
    Lit p = ~out_learnt[0];

    if (lbd <= 6) {
        MYFLAG++;

        for (int i = 1; i < out_learnt.size(); i++) {
            permDiff[var(out_learnt[i])] = MYFLAG;
        }

        vec<Watcher>& wbin = watchesBin[p];
        int nb = 0;
        for (int k = 0; k < wbin.size(); k++) {
            Lit imp = wbin[k].blocker;
            if (permDiff[var(imp)] == MYFLAG && value(imp) == l_True) {
                nb++;
                permDiff[var(imp)] = MYFLAG - 1;
                std::cout << "U " << wbin[k].cref << endl;
            }
        }
        int l = out_learnt.size() - 1;
        if (nb > 0) {
            for (int i = 1; i < out_learnt.size() - nb; i++) {
                if (permDiff[var(out_learnt[i])] != MYFLAG) {
                    Lit p = out_learnt[l];
                    out_learnt[l] = out_learnt[i];
                    out_learnt[i] = p;
                    l--;
                    i--;
                }
            }

            out_learnt.shrink(nb);

        }
    }
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Var v = var(analyze_stack.last());

        Clause &c = (dpll && tmpReason(v))?dpll_ca[reason(v)]:ca[reason(v)];
        analyze_stack.pop();

        // Special handling for binary clauses like in 'analyze()'.
        if (c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = caReason(x);
                for (int j = c.size() == 2 ? 0 : 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from, bool dpll)
{
    if(REFUTATION_TRACING && (from != CRef_Undef)) std::cout << "P " << p << " " << from << endl;

    assert(value(p) == l_Undef);
	if(LRB){
		lrb_picked[var(p)] = conflicts;
	    uint64_t age = conflicts - lrb_canceled[var(p)];
	    if (age > 0) {
	        double decay = pow(0.95, age);
	        activity[var(p)] *= decay;
	        if (order_heap.inHeap(var(p))) {
	            order_heap.increase(var(p));
	        }
	    }
		lrb_conflicted[var(p)] = 0;
		lrb_conflicted[var(p)] = 0;
		lrb_almost_conflicted[var(p)] = 0;
	}
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel(), dpll);
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    if (opt_binary)
	watchesBin.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

	if (opt_binary) {
	    vec<Watcher>& ws_bin = watchesBin[p];  // Propagate binary clauses first.
	    for (int k = 0; k < ws_bin.size(); k++){
		Lit the_other = ws_bin[k].blocker;
		if (value(the_other) == l_False){
		    confl = ws_bin[k].cref;
		    return confl;
		}else if(value(the_other) == l_Undef) {
            /*// Prints to the trace the fact that we propagate this literal
            // Format will be P l x, where
            // l = literal that is propagated
            // x = CRef of clause it was propagated via
            if(REFUTATION_TRACING) std::cout << "P " << the_other << " " << ws_bin[k].cref << endl;*/
            uncheckedEnqueue(the_other, ws_bin[k].cref);
	    }
        }
	}

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else{
                uncheckedEnqueue(first, cr);
            }

        NextClause:;
        }
        ws.shrink(i - j);
    }

    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        if (ca[x].size() == 2) return 0;
        if (ca[y].size() == 2) return 1;

        return ca[x].activity() < ca[y].activity();
    }
};
struct reduceDB_lt_LBD {
    ClauseAllocator& ca;
    reduceDB_lt_LBD(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        if (ca[x].size() == 2) return 0;
        if (ca[y].size() == 2) return 1;

        if (ca[x].lbd() > ca[y].lbd()) return 1;
        if (ca[x].lbd() < ca[y].lbd()) return 0;

        return ca[x].activity() < ca[y].activity();
    }
};
void Solver::reduceDB()
{
    int     i, j;

    nbReduceDB++;
    if ( ca_lbd || opt_glucose_frequency || ce_lin) {
	sort(learnts, reduceDB_lt_LBD(ca));
        if ((opt_glucose_frequency || ce_lin ) && learnts.size() > 0) {
          // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
          if(ca[learnts[learnts.size() / 2]].lbd()<=3) {nbclausesbeforereduce += 1000;}
          if(ca[learnts.last()].lbd()<=5)  nbclausesbeforereduce +=1000;
        }
    }
    if (ca_vsids) {
	// I know that in some cases we can sort the same array twice (ca_vsids + opt_glucose_frequency)
       	sort(learnts, reduceDB_lt(ca));
    }else if(ca_random){
    	// Random permutation of learnt clauses
      for(i = learnts.size()-1; i >=0; i--){
        int c = (int)(drand(random_seed) * (i+1)); //Randon number in [0,i]
        // Swap
        CRef aux = learnts[c];
        learnts[c] = learnts[i];
        learnts[i] = aux;
      }
    }

    int limit = learnts.size() / 2;
    for (i = j = 0; i < learnts.size(); i++){
      Clause& c = ca[learnts[i]];
      if (c.size() > 2 && (c.lbd() > 2 || !ca_lbd) && (c.removable() || !ca_lbd) && !locked(c) && i < limit){
        // Print to the trace the fact that we remove this clause
        // Format will be R x, where
        // x = CRef of removed clause
        if(REFUTATION_TRACING) std::cout << "R " << learnts[i] << endl;
        removeClause(learnts[i]);
      }else{
		  if (ca_lbd  && !c.removable())
			  limit++;
		  c.removable(true);
        learnts[j++] = learnts[i]; }
    }

    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c)) {
            // Print to the trace the fact that we remove this clause
            // Format will be R x, where
            // x = CRef of removed clause
            if(REFUTATION_TRACING) std::cout << "R " << cs[i] << endl;
            removeClause(cs[i]);
        } else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [void]
|
|  Description:
|    Assign literals that occur with only one polarity in the formula. These literals are called
|    pure literals.
|________________________________________________________________________________________________@*/
void Solver::assignPureLiteral()
{
    int i, j, v;
    char * var_list = (char*) calloc(nVars(), sizeof(char));

    for (i = 0; i < clauses.size(); i++){
        Clause& c = ca[clauses[i]];
        for (j = 0; j < c.size(); j++){
            if (value(c[j]) != l_Undef) continue;
            v = var(c[j]);
            if (sign(c[j])) var_list[v] |= 0x02;
            else            var_list[v] |= 0x01;
        }
    }

    for (v = 0; v < nVars(); v++){
        if (var_list[v] == 0x01) {
            Lit p = mkLit(v); uncheckedEnqueue(p); }
        else if (var_list[v] == 0x02) {
            Lit p = ~mkLit(v); uncheckedEnqueue(p); }
    }
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    if (opt_apply_pure_lit) assignPureLiteral();
    checkGarbage();
    rebuildOrderHeap();


    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


void Solver::jsonReport(){
    static uint32_t reportNumber = 1;

    fprintf(fileout,"\"CPU\":%.2f, ", cpuTime());

    fprintf(fileout,"\"conflicts\":%d, ", (int)conflicts);
    fprintf(fileout,"\"activeVars\":%d, ", (int)(int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]));
    fprintf(fileout,"\"activeClauses\":%d, ", nClauses());
    fprintf(fileout,"\"nbReduceDB\":%d, ", nbReduceDB);
    fprintf(fileout,"\"restarts\":%d, ", (int)starts);
    fprintf(fileout,"\"decisionsK\":%d, ", (int)(decisions/1000));
    fprintf(fileout,"\"propagationsK\":%d, ", (int)(propagations/1000));
    fprintf(fileout,"\"caMemoryK\":%d, ", (int)((ca.size()*ClauseAllocator::Unit_Size)/1000));
    fprintf(fileout,"\"confLiteralsK\":%d, ", (int)(tot_literals/1000));
    fprintf(fileout,"\"confMaxLiteralsK\":%d, ", (int)(max_literals/1000));
    fprintf(fileout,"\"learnts\":%d, ", nLearnts());
    fprintf(fileout,"\"unaryLearnts\":%d, ", (int)nbUn);
    fprintf(fileout,"\"unaryFound\":%d, ", trail_lim.size() == 0 ? trail.size() : trail_lim[0]);
    fprintf(fileout,"\"binaryLearnts\":%d, ", (int)nbBin);
    fprintf(fileout,"\"maxLearnts\":%d ", (int)max_learnts);
    fprintf(fileout,"\"nbRemovedClauses\":%d, ", (int)nbRemovedClauses);
    fprintf(fileout,"\"nbOriginalSeenInConflicts\":%d, ", (int)nbOriginalSeenInConflicts);
    fprintf(fileout,"\"nbLearntSeenInConflicts\":%d, ", (int)nbLearntSeenInConflicts);
    fprintf(fileout,"\"nbRemovedSeenInConflicts\":%d, ", (int)nbRemovedSeenInConflicts);
	fprintf(fileout,"\"dpllLearnts\":%d, ", dpll_ca.numClauses());
    if (lastUIP)
      fprintf(fileout,"\"nbUIP\":%d, ", (int)nbUIP);

    if (conflicts >0) {
      fprintf(fileout,"\"avgDecisionLevel\":%.2lf, ", (double)sumDecisionLevels/(double)conflicts);
      fprintf(fileout,"\"avgTrailSize\":%.2lf, ", (double)sumTrailSize/(double)conflicts);
      fprintf(fileout,"\"avgBackjumpSize\":%.2lf, ", (double)sumBackJumpSize/(double)conflicts);
      fprintf(fileout,"\"avgLBD\":%.2lf, ", (double)global_lbd_sum/(double)conflicts);
      fprintf(fileout,"\"avgNbResolution\":%.2lf, ", (double)statsNbResolutions/(double)conflicts);
      fprintf(fileout,"\"avgMergedLiterals\":%.2lf, ", (double)statsNbMergedLiterals/(double)conflicts);
      fprintf(fileout,"\"avgUIPClauseSize\":%.2lf, ", (double)max_literals/(double)conflicts);
      fprintf(fileout,"\"avgMinimizedLearntClauseSize\":%.2lf, ", (double)tot_literals/(double)conflicts);
      fprintf(fileout,"\"avgLearntClauseSize\":%.2lf, ", (double)tot_literals_binary/(double)conflicts);
    }
    fprintf(fileout,"\"reportNumber\":%d", (int)reportNumber++);
}

void Solver::jsonFinalReportOutOfMem(){
  fprintf(fileout,"c FINALJSON {");
  fprintf(fileout,"\"finalStatus\":\"OUTOFMEMORY\", ");
  jsonReport();
  fprintf(fileout,"}\n");
}

void Solver::jsonFinalReport(lbool status){
  fprintf(fileout,"c FINALJSON {");
  fprintf(fileout,"\"finalStatus\":\"%s\", ", status==l_True?"SAT":status==l_False?"UNSAT":"INDETERMINATE");
  jsonReport();
  fprintf(fileout,"}\n");
}
/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    int         lbd;
    vec<Lit>    learnt_clause;
    vec<int>    visited_levels;
    starts++;

    if (CHB) chb_p = trail.size();

    for (;;){
        CRef confl = propagate();
        if (CHB) {
            double m1 = (confl == CRef_Undef)? chb_m : 1;
            for(int i = chb_p; i < trail.size(); i++) {
                Var v = var(trail[i]);
                double r = m1 / (conflicts - chb_lconf[v] + 1.);
                varChangeActivity(v, (1 - chb_a) * activity[v] + chb_a * r);
            }
        }
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if(LRB){
                if (lrb_step_size > lrb_min_step_size)
                    lrb_step_size -= lrb_step_size_dec;
            }
            sumDecisionLevels += decisionLevel();
            sumTrailSize += trail.size();

            if (decisionLevel() == 0) {
                // Print to the trace the fact that we have the final conflict
                // Format will be C x, where
                // x = CRef of the final conflict clause
                if(REFUTATION_TRACING) std::cout << "C " << confl << endl;
                return l_False;
            }

            if(CHB && chb_a > chb_ae){ chb_a -= chb_da;}

            if (opt_lbd_restarts) {
                trail_sz_queue.push(trail.size());
                // Prevent restarts for a while if many variables are being assigned.
                if (conflicts > 10000 && lbd_queue.full() && trail.size() > 1.4 * trail_sz_queue.avg())
                    lbd_queue.clear();
            }
            if (opt_disable_learning) {
                int junk;
                if (visited_levels.size() == 0) return l_False;
                backtrack_level = visited_levels.last() - 1;
                visited_levels.pop();
                Lit p = trail[trail_lim[backtrack_level]];
                analyze(confl, learnt_clause, junk, lbd);
                // Here this is a dummy backtrack level (no informations from the conflict analysis is used)
                sumBackJumpSize+=decisionLevel()-backtrack_level;
                cancelUntil(backtrack_level);
                if (opt_lbd_restarts) {
                    lbd_queue.push(lbd);
                }
                global_lbd_sum += lbd;
                newDecisionLevel();
                uncheckedEnqueue(~p);
            } else {
                learnt_clause.clear();
                analyze(confl, learnt_clause, backtrack_level, lbd);
                if (opt_lbd_restarts) {
                    lbd_queue.push(lbd);
                }
                global_lbd_sum += lbd;
                sumBackJumpSize+=decisionLevel()-backtrack_level;
                cancelUntil(backtrack_level);

                // Prints to the trace the fact that we backtracked
                // Format will be B l, where
                // l = level that is backtracked to
                if(REFUTATION_TRACING) std::cout << "B " << backtrack_level << endl;

                if (CHB) chb_p = trail.size();

                if (learnt_clause.size() == 1){
                    nbUn++;
                    // Prints to the trace the fact that we learned this unit
                    // Format will be LU l, where
                    // l = the literal that was learned
                    if(REFUTATION_TRACING) std::cout << "LU " << learnt_clause[0] << endl;
                    assert(backtrack_level == 0);
                    uncheckedEnqueue(learnt_clause[0]);
                }else if (dpll && learnt_clause.size() > 2) { // We keep binary clauses as CDCL solver does
                    CRef cr = dpll_ca.pushClause(learnt_clause);
                    assert(dpll_ca.numClauses() <= nVars());
                    // Prints to the trace the fact that we learned this clause
                    // Format will be L x y a b c, where
                    // x = the CRef of the learned clause
                    // y = the number of literals
                    // a, b, c = literals
                    if(REFUTATION_TRACING) std::cout << "L " << cr << " " << ca[cr] << endl;
                    uncheckedEnqueue(learnt_clause[0], cr, true);
                }else {
                    if (learnt_clause.size()==2) nbBin++;
                    CRef cr = ca.alloc(learnt_clause, true);
                    if (compute_lbd)
                        ca[cr].set_lbd(lbd);

                    learnts.push(cr);
                    attachClause(cr);
                    if (ca_random)
                        ca[cr].activity() = drand(random_seed);
                    else
                        claBumpActivity(ca[cr]);

                    // Prints to the trace the fact that we learned this clause
                    // Format will be L x y a b c, where
                    // x = the CRef of the learned clause
                    // y = the number of literals
                    // a, b, c = literals
                    if(REFUTATION_TRACING) std::cout << "L " << cr << " " << ca[cr] << endl;
                    uncheckedEnqueue(learnt_clause[0], cr);
                }

                if(learnt_clause.size() == 1)
                {
                    assert(backtrack_level == 0);
                    // Prints to the trace the fact that we will propagate
                    // this via the newly learned unit
                    // Format will be PU l, where
                    // l = unit that is propagated
                    if(REFUTATION_TRACING) std::cout << "PU " << learnt_clause[0] << endl;
                }
            }

            if (!opt_fixed_order) {
                varDecayActivity();
            }
            claDecayActivity();

            if (--learntsize_output_cnt == 0) {// frequency for outputs.
                if (conflicts < 250)
                    learntsize_output_cnt = 50;
                else if (conflicts < 1000)
                    learntsize_output_cnt = 250;
                else  if (conflicts < 10000)
                    learntsize_output_cnt = 2500;
                else if (conflicts < 100000)
                    learntsize_output_cnt = 25000;
                else if (conflicts < 1000000)
                    learntsize_output_cnt = 200000;
                else
                    learntsize_output_cnt = 500000;
                if (verbosity >= 1) {
                    if (json) {
                        fprintf(fileout,"c JSON {");
                        jsonReport();
                        fprintf(fileout,"}\n");
                    } else {
                        fprintf(fileout,"| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                                (int)conflicts,
                                (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                                (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
                    }

                }
            }


            if (--learntsize_adjust_cnt == 0){ // Minisat way of adjusting the frequencies
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;
            }
        } else{
            // NO CONFLICT

            // Handling restarts
            // A few possible restart strategies
            if ( (!withinBudget()) || // this is a strong "restart" to early end the computation
                    // Other case: classical Minisat (set with nof_conflicts)
                    (!opt_lbd_restarts && nof_conflicts >= 0 && conflictC >= nof_conflicts) ||
                    // lbd-like restarts:
                    (opt_lbd_restarts && lbd_queue.full() && lbd_queue.avg() * 0.8 > global_lbd_sum / conflicts)
               ) {
                if (opt_lbd_restarts)
                    lbd_queue.clear();
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            // Handling ReduceDB calls
            if (!opt_disable_deletion) {
                // Minisat-like: CE:min
                if (!opt_glucose_frequency && !ce_lin && opt_minisat_frequency &&
                        learnts.size()-nAssigns() >= max_learnts) {
                    reduceDB();
                }
                // Glucose-like: CE:glu and CE:lin
                if ((opt_glucose_frequency || ce_lin) && !opt_minisat_frequency &&
                        (conflicts >= ((unsigned int) curRestart * nbclausesbeforereduce) && learnts.size() > 0)) {
                    curRestart = (conflicts / nbclausesbeforereduce) + 1;
                    reduceDB();
                    // Case of CE:glu
                    if(opt_glucose_frequency)
                        nbclausesbeforereduce += incReduceDB;
                    // Case of CE:lin
                    else if (ce_lin)
                        nbclausesbeforereduce *= factorReduceDB;
                }
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef) {
                    // Model found:
                    // assert(trail.size() == nVars());
                    return l_True; }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            if (CHB) chb_p = trail.size();
            uncheckedEnqueue(next);

            // Prints to the trace the fact that we made a decision
            // Format will be D l, where
            // l = the literal that is decided
            if(REFUTATION_TRACING) std::cout << "D " << next << endl;

            if (opt_disable_learning) visited_levels.push(decisionLevel());
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    /* assert(!opt_disable_2LW); // No more in this implementation */

    // For fixed order, simply update the activity with the reverse order of the variable ranking
    if (opt_fixed_order) {
	for(int i=0;i<nVars();i++)
	    activity[i] = nVars() - i;
	rebuildOrderHeap();
    } else if (randomBranching) {
      for(int i=0;i<nVars();i++)
          activity[i] = drand(random_seed);
      rebuildOrderHeap();
    }


    if (!strcmp(opt_PH_phaseHeuristics,"fix0")) {
        for(int i=0;i<nVars();i++)
            polarity[i] = true; // branch on false literal
    } else if (!strcmp(opt_PH_phaseHeuristics,"fixrnd")) {
        for(int i=0;i<nVars();i++)
            polarity[i] = drand(random_seed) < 0.5; // branch on false literal
    } else {
      for(int i=0;i<nVars();i++)
          polarity[i] = true; // branch on false literal as the usual initialization for all other options
    }

    if (verbosity >= 1){
        fprintf(fileout,"============================[ Search Statistics ]==============================\n");
        fprintf(fileout,"| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        fprintf(fileout,"|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        fprintf(fileout,"===============================================================================\n");
    }

    // Trace the number of vars
    // Format will be NV n, where
    // n = the number of vars
    if(REFUTATION_TRACING) std::cout << "NV " << nVars() << endl;

    // Trace all initial clauses
    // Format is I x y a b c, where
    // x = the CRef (which could change later)
    // y = the number of literals
    // a, b, c = literals
    if(REFUTATION_TRACING) {
        for(int i=0; i < clauses.size(); i++) {
            std::cout << "I " << clauses[i] << " " << ca[clauses[i]] << endl;
        }
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = -1;
        if (!opt_disable_restart)
            rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search((int)rest_base * restart_first);
        if (!withinBudget()) break;
        if (asynch_interrupt) break;
        curr_restarts++;
        // Print to the trace the fact that we restarted
        if(REFUTATION_TRACING) std::cout << "RS" << endl;
    }

    if (json)
      jsonFinalReport(status);

    if (verbosity >= 1)
        fprintf(fileout,"===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

  	cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        fprintf(fileout,"Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    if (opt_binary)
	watchesBin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
	    if (opt_binary) {
		vec<Watcher>& ws_bin = watchesBin[p];
		for (int j = 0; j < ws_bin.size(); j++)
		    ca.reloc(ws_bin[j].cref, to);
	    }
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && !tmpReason(v) && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);

    // Print to the trace the fact that relocation is complete
    if(REFUTATION_TRACING) std::cout << "RD" << endl;
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        fprintf(fileout,"|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
