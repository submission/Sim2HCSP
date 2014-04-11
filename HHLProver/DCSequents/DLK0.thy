(* I borrow the implementation by 
    [Title:      Sequents/LK0.thy
     Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
     Copyright   1993  University of Cambridge]

But make a modification to adapt to our application. 
*)

header {* Classical First-Order Sequent Calculus *}

theory DLK0
imports DSequents
begin

consts Trueprop :: "two_seqi"

syntax
 "_Trueprop" :: "two_seqe" ("((_)/ |- (_))" [6,6] 5)

parse_translation {* [(@{syntax_const "_Trueprop"}, two_seq_tr @{const_syntax Trueprop})] *}
print_translation {* [(@{const_syntax Trueprop}, two_seq_tr' @{syntax_const "_Trueprop"})] *}


axioms

  (*Structural rules: contraction, thinning, exchange [Soren Heilmann] *)

  contRS: "$H |- $E, $S, $S, $F ==> $H |- $E, $S, $F"
  contLS: "$H, $S, $S, $G |- $E ==> $H, $S, $G |- $E"

  thinRS: "$H |- $E, $F ==> $H |- $E, $S, $F"
  thinLS: "$H, $G |- $E ==> $H, $S, $G |- $E"

  exchRS: "$H |- $E, $R, $S, $F ==> $H |- $E, $S, $R, $F"
  exchLS: "$H, $R, $S, $G |- $E ==> $H, $S, $R, $G |- $E"

  cut:   "[| $H |- $E, P;  $H, P |- $E |] ==> $H |- $E"

 axioms
 (*Propositional rules*)

  basic: "$H, P, $G |- $E, P, $F"

  conjR: "[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P [&] Q, $F"
  conjL: "$H, P, Q, $G |- $E ==> $H, P [&] Q, $G |- $E"

  disjR: "$H |- $E, P, Q, $F ==> $H |- $E, P [|] Q, $F"
  disjL: "[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P [|] Q, $G |- $E"
 
  impR:  "$H, P |- $E, Q, $F ==> $H |- $E, P [-->] Q, $F"
  impL:  "[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P [-->] Q, $G |- $E"

  notR:  "$H, P |- $E, $F ==> $H |- $E, [~] P, $F"
  notL:  "$H, $G |- $E, P ==> $H, [~] P, $G |- $E"

  FalseL: "$H, WFalse, $G |- $E"

  True_def: "WTrue == WFalse [-->] WFalse"
  iff_def:  "P [<->] Q == (P [-->] Q) [&] (Q [-->] P)"

 axioms
  (*Quantifiers*)

  allR:  "(!!x.$H |- $E, P(x), $F) ==> $H |- $E, WALL x P(x), $F"
  allL:  "$H, P(x), $G, WALL x P(x) |- $E ==> $H, WALL x P(x), $G |- $E"

  exR:   "$H |- $E, P(x), $F, WEX x P(x) ==> $H |- $E, WEX  x P(x), $F"
  exL:   "(!!x.$H, P(x), $G |- $E) ==> $H, WEX x P(x), $G |- $E"

 axioms
 (*Equality*)

  refl:  "$H |- $E, a [=] a, $F"
  subst: "$H(a), $G(a) |- $E(a) ==> $H(b), a [=] b, $G(b) |- $E(b)"

  (* Reflection *)

  eq_reflection:  "|- x [=] y ==> (x==y)"
  iff_reflection: "|- P [<->] Q ==> (P==Q)"


(** Structural Rules on formulas **)

(*contraction*)

lemma contR: "$H |- $E, P, P, $F ==> $H |- $E, P, $F"
  by (rule contRS)

lemma contL: "$H, P, P, $G |- $E ==> $H, P, $G |- $E"
  by (rule contLS)

(*thinning*)

lemma thinR: "$H |- $E, $F ==> $H |- $E, P, $F"
  by (rule thinRS)

lemma thinL: "$H, $G |- $E ==> $H, P, $G |- $E"
  by (rule thinLS)

(*exchange*)

lemma exchR: "$H |- $E, Q, P, $F ==> $H |- $E, P, Q, $F"
  by (rule exchRS)

lemma exchL: "$H, Q, P, $G |- $E ==> $H, P, Q, $G |- $E"
  by (rule exchLS)

ML {*
(*Cut and thin, replacing the right-side formula*)
fun cutR_tac ctxt s i =
  res_inst_tac ctxt [(("P", 0), s) ] @{thm cut} i  THEN  rtac @{thm thinR} i

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac ctxt s i =
  res_inst_tac ctxt [(("P", 0), s)] @{thm cut} i  THEN  rtac @{thm thinL} (i+1)
*}


(** If-and-only-if rules **)
lemma iffR: 
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P [<->] Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL: 
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P [<->] Q, $G |- $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemma iff_refl: "$H |- $E, (P [<->] P), $F"
  apply (rule iffR basic)+
  done

lemma TrueR: "$H |- $E, WTrue, $F"
  apply (unfold True_def)
  apply (rule impR)
  apply (rule basic)
  done

(*(*Descriptions*)
lemma the_equality:
  assumes p1: "$H |- $E, P(a), $F"
    and p2: "!!x. $H, P(x) |- $E, x=a, $F"
  shows "$H |- $E, (THE x. P(x)) = a, $F"
  apply (rule cut)
   apply (rule_tac [2] p2)
  apply (rule The, rule thinR, rule exchRS, rule p1)
  apply (rule thinR, rule exchRS, rule p2)
  done
*)

(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma allL_thin: "$H, P(x), $G |- $E ==> $H, WALL x P(x), $G |- $E"
  apply (rule allL)
  apply (erule thinL)
  done

lemma exR_thin: "$H |- $E, P(x), $F ==> $H |- $E, WEX x P(x), $F"
  apply (rule exR)
  apply (erule thinR)
  done

(*The rules of LK*)

ML {*
val prop_pack = empty_pack add_safes
                [@{thm basic}, @{thm refl}, @{thm TrueR}, @{thm FalseL},
                 @{thm conjL}, @{thm conjR}, @{thm disjL}, @{thm disjR}, @{thm impL}, @{thm impR},
                 @{thm notL}, @{thm notR}, @{thm iffL}, @{thm iffR}];

val LK_pack = prop_pack add_safes   [@{thm allR}, @{thm exL}]
                        add_unsafes [@{thm allL_thin}, @{thm exR_thin}, @{thm the_equality}];

val LK_dup_pack = prop_pack add_safes   [@{thm allR}, @{thm exL}]
                            add_unsafes [@{thm allL}, @{thm exR}, @{thm the_equality}];


fun lemma_tac th i =
    rtac (@{thm thinR} RS @{thm cut}) i THEN REPEAT (rtac @{thm thinL} i) THEN rtac th i;
*}

method_setup fast_prop = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac prop_pack))) *}
method_setup fast = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac LK_pack))) *}
method_setup fast_dup = {* Scan.succeed (K (SIMPLE_METHOD' (fast_tac LK_dup_pack))) *}
method_setup best = {* Scan.succeed (K (SIMPLE_METHOD' (best_tac LK_pack))) *}
method_setup best_dup = {* Scan.succeed (K (SIMPLE_METHOD' (best_tac LK_dup_pack))) *}


lemma mp_R:
  assumes major: "$H |- $E, $F, P [-->] Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule thinRS [THEN cut], rule major)
  apply (tactic "step_tac LK_pack 1")
  apply (rule thinR, rule minor)
  done

lemma mp_L:
  assumes major: "$H, $G |- $E, P [-->] Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule thinL [THEN cut], rule major)
  apply (tactic "step_tac LK_pack 1")
  apply (rule thinL, rule minor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma R_of_imp:
  assumes major: "|- P [-->] Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule mp_R)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

lemma L_of_imp:
  assumes major: "|- P [-->] Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule mp_L)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma backwards_impR:
  assumes prem: "$H, $G |- $E, $F, P [-->] Q"
  shows "$H, P, $G |- $E, Q, $F"
  apply (rule mp_L)
   apply (rule_tac [2] basic)
  apply (rule thinR, rule prem)
  done

lemma conjunct1: "|-P [&] Q ==> |-P"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma conjunct2: "|-P [&] Q ==> |-Q"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma spec: "|- (WALL x P(x)) ==> |- P(x)"
  apply (erule thinR [THEN cut])
  apply fast
  done


(** Equality **)

lemma sym: "|- a [=] b [-->] b [=] a"
  by (tactic {* safe_tac (LK_pack add_safes [@{thm subst}]) 1 *})

lemma trans: "|- a [=] b [-->] b [=] c [-->] a [=] c"
  by (tactic {* safe_tac (LK_pack add_safes [@{thm subst}]) 1 *})

(* Symmetry of equality in hypotheses *)
lemmas symL = sym [THEN L_of_imp, standard]

(* Symmetry of equality in hypotheses *)
lemmas symR = sym [THEN R_of_imp, standard]

lemma transR: "[| $H|- $E, $F, a [=] b;  $H|- $E, $F, b [=] c |] ==> $H|- $E, a [=] c, $F"
  by (rule trans [THEN R_of_imp, THEN mp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma def_imp_iff: "(A == B) ==> |- A [<->] B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A == B) ==> |- A [=] B"
  apply (unfold)
  apply (rule refl)
  done

(*New added axioms for formulas of our syntax*)
(*Arith*)
axiomatization where
Trans: "formT (f::fform) ==> |- f" and
Trans1: "(formT (f1::fform) ==> formT (f::fform)) ==> f1 |- f" and
Trans2: "(formT (f1::fform) & formT (f2::fform) ==> formT (f::fform)) ==> f1, f2 |- f" and
Trans3: "(formT (f1::fform) & formT (f2::fform) & formT (f3::fform) ==> formT (f::fform)) ==> f1, f2, f3 |- f" and
Trans4: "(formT (f1::fform) & formT (f2::fform) & formT (f3::fform) & formT (f4::fform) ==> formT (f::fform)) ==> f1, f2, f3, f4 |- f"

axiomatization where
TransR: "|- f ==> formT (f::fform)" and
TransR1: "f1 |- f ==> (formT (f1::fform) --> formT (f::fform))" and
TransR2: "f1, f2 |- f ==> (formT (f1::fform) & formT (f2::fform) --> formT (f::fform))" and
TransR3: "f1, f2, f3 |- f ==> (formT (f1::fform) & formT (f2::fform) & formT (f3::fform) --> formT (f::fform))"

axiomatization where 
le_square : "[|0<=a; (a::real)<=b; 0<=c; (c::real)<=d|] ==> a*c<=b*d"

lemma le_square1 : "[|0<=(a::real); a<=1|] ==> a*a<=1"
apply (cut_tac a=a and c=a and b=1 and d=1 in le_square,auto)
done

end
