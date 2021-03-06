(*  Title:      Sequents/prover.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Simple classical reasoner for the sequent calculus, based on "theorem packs".
*)


(*Higher precedence than := facilitates use of references*)
infix 4 add_safes add_unsafes;

structure Cla =
struct

datatype pack = Pack of thm list * thm list;

val trace = Unsynchronized.ref false;

(*A theorem pack has the form  (safe rules, unsafe rules)
  An unsafe rule is incomplete or introduces variables in subgoals,
  and is tried only when the safe rules are not applicable.  *)

fun less (rl1,rl2) = (nprems_of rl1) < (nprems_of rl2);

val empty_pack = Pack([],[]);

fun warn_duplicates [] = []
  | warn_duplicates dups =
      (warning (cat_lines ("Ignoring duplicate theorems:" ::
          map Display.string_of_thm_without_context dups));
       dups);

fun (Pack(safes,unsafes)) add_safes ths   = 
    let val dups = warn_duplicates (inter Thm.eq_thm_prop ths safes)
        val ths' = subtract Thm.eq_thm_prop dups ths
    in
        Pack(sort (make_ord less) (ths'@safes), unsafes)
    end;

fun (Pack(safes,unsafes)) add_unsafes ths = 
    let val dups = warn_duplicates (inter Thm.eq_thm_prop unsafes ths)
        val ths' = subtract Thm.eq_thm_prop dups ths
    in
        Pack(safes, sort (make_ord less) (ths'@unsafes))
    end;

fun merge_pack (Pack(safes,unsafes), Pack(safes',unsafes')) =
        Pack(sort (make_ord less) (safes@safes'), 
             sort (make_ord less) (unsafes@unsafes'));


fun print_pack (Pack(safes,unsafes)) =
  writeln (cat_lines
   (["Safe rules:"] @ map Display.string_of_thm_without_context safes @
    ["Unsafe rules:"] @ map Display.string_of_thm_without_context unsafes));

(*Returns the list of all formulas in the sequent*)
fun forms_of_seq (Const(@{const_name "SeqO'"},_) $ P $ u) = P :: forms_of_seq u
  | forms_of_seq (H $ u) = forms_of_seq u
  | forms_of_seq _ = [];

(*Tests whether two sequences (left or right sides) could be resolved.
  seqp is a premise (subgoal), seqc is a conclusion of an object-rule.
  Assumes each formula in seqc is surrounded by sequence variables
  -- checks that each concl formula looks like some subgoal formula.
  It SHOULD check order as well, using recursion rather than forall/exists*)
fun could_res (seqp,seqc) =
      forall (fn Qc => exists (fn Qp => Term.could_unify (Qp,Qc)) 
                              (forms_of_seq seqp))
             (forms_of_seq seqc);


(*Tests whether two sequents or pairs of sequents could be resolved*)
fun could_resolve_seq (prem,conc) =
  case (prem,conc) of
      (_ $ Abs(_,_,leftp) $ Abs(_,_,rightp),
       _ $ Abs(_,_,leftc) $ Abs(_,_,rightc)) =>
          could_res (leftp,leftc) andalso could_res (rightp,rightc)
    | (_ $ Abs(_,_,leftp) $ rightp,
       _ $ Abs(_,_,leftc) $ rightc) =>
          could_res (leftp,leftc)  andalso  Term.could_unify (rightp,rightc)
    | _ => false;


(*Like filt_resolve_tac, using could_resolve_seq
  Much faster than resolve_tac when there are many rules.
  Resolve subgoal i using the rules, unless more than maxr are compatible. *)
fun filseq_resolve_tac rules maxr = SUBGOAL(fn (prem,i) =>
  let val rls = filter_thms could_resolve_seq (maxr+1, prem, rules)
  in  if length rls > maxr  then  no_tac
          else (*((rtac derelict 1 THEN rtac impl 1
                 THEN (rtac identity 2 ORELSE rtac ll_mp 2)
                 THEN rtac context1 1)
                 ORELSE *) resolve_tac rls i
  end);


(*Predicate: does the rule have n premises? *)
fun has_prems n rule =  (nprems_of rule = n);

(*Continuation-style tactical for resolution.
  The list of rules is partitioned into 0, 1, 2 premises.
  The resulting tactic, gtac, tries to resolve with rules.
  If successful, it recursively applies nextac to the new subgoals only.
  Else fails.  (Treatment of goals due to Ph. de Groote) 
  Bind (RESOLVE_THEN rules) to a variable: it preprocesses the rules. *)

(*Takes rule lists separated in to 0, 1, 2, >2 premises.
  The abstraction over state prevents needless divergence in recursion.
  The 9999 should be a parameter, to delay treatment of flexible goals. *)

fun RESOLVE_THEN rules =
  let val [rls0,rls1,rls2] = partition_list has_prems 0 2 rules;
      fun tac nextac i state = state |>
             (filseq_resolve_tac rls0 9999 i 
              ORELSE
              (DETERM(filseq_resolve_tac rls1 9999 i) THEN  TRY(nextac i))
              ORELSE
              (DETERM(filseq_resolve_tac rls2 9999 i) THEN  TRY(nextac(i+1))
                                            THEN  TRY(nextac i)))
  in  tac  end;



(*repeated resolution applied to the designated goal*)
fun reresolve_tac rules = 
  let val restac = RESOLVE_THEN rules;  (*preprocessing done now*)
      fun gtac i = restac gtac i
  in  gtac  end; 

(*tries the safe rules repeatedly before the unsafe rules. *)
fun repeat_goal_tac (Pack(safes,unsafes)) = 
  let val restac  =    RESOLVE_THEN safes
      and lastrestac = RESOLVE_THEN unsafes;
      fun gtac i = restac gtac i  
                   ORELSE  (if !trace then
                                (print_tac "" THEN lastrestac gtac i)
                            else lastrestac gtac i)
  in  gtac  end; 


(*Tries safe rules only*)
fun safe_tac (Pack(safes,unsafes)) = reresolve_tac safes;

val safe_goal_tac = safe_tac;   (*backwards compatibility*)

(*Tries a safe rule or else a unsafe rule.  Single-step for tracing. *)
fun step_tac (pack as Pack(safes,unsafes)) =
    safe_tac pack  ORELSE'
    filseq_resolve_tac unsafes 9999;


(* Tactic for reducing a goal, using Predicate Calculus rules.
   A decision procedure for Propositional Calculus, it is incomplete
   for Predicate-Calculus because of allL_thin and exR_thin.  
   Fails if it can do nothing.      *)
fun pc_tac pack = SELECT_GOAL (DEPTH_SOLVE (repeat_goal_tac pack 1));


(*The following two tactics are analogous to those provided by 
  Provers/classical.  In fact, pc_tac is usually FASTER than fast_tac!*)
fun fast_tac pack =
  SELECT_GOAL (DEPTH_SOLVE (step_tac pack 1));

fun best_tac pack  = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, size_of_thm) 
               (step_tac pack 1));

end;


open Cla;
