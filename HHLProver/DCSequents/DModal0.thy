(*  Adapted from implementation by:
    Title:      Sequents/Modal0.thy
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

theory DModal0
imports DLK0
uses "Dmodal.ML"
begin

(*Think future which of "consts" and $datatype$ is better. *)
consts
  box           :: "fform => fform"       ("[]_" [50] 50)
  dia           :: "fform => fform"       ("<>_" [50] 50)
  strimp        :: "[fform, fform] => fform"   (infixr "--<" 25)
  streqv        :: "[fform, fform] => fform"   (infixr ">-<" 25)
  Lstar         :: "two_seqi"
  Rstar         :: "two_seqi"

syntax
  "_Lstar"      :: "two_seqe"   ("(_)|L>(_)" [6,6] 5)
  "_Rstar"      :: "two_seqe"   ("(_)|R>(_)" [6,6] 5)

ML {*
  fun star_tr c [s1, s2] = Const(c, dummyT) $ seq_tr s1 $ seq_tr s2;
  fun star_tr' c [s1, s2] = Const(c, dummyT) $ seq_tr' s1 $ seq_tr' s2;
*}

parse_translation {*
 [(@{syntax_const "_Lstar"}, star_tr @{const_syntax Lstar}),
  (@{syntax_const "_Rstar"}, star_tr @{const_syntax Rstar})]
*}

print_translation {*
 [(@{const_syntax Lstar}, star_tr' @{syntax_const "_Lstar"}),
  (@{const_syntax Rstar}, star_tr' @{syntax_const "_Rstar"})]
*}

defs
  strimp_def:    "P --< Q == [](P [-->] Q)"
  streqv_def:    "P >-< Q == (P --< Q) [&] (Q --< P)"


lemmas rewrite_rls = strimp_def streqv_def

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

lemmas safe_rls = basic conjL conjR disjL disjR impL impR notL notR iffL iffR
  and unsafe_rls = allR exL
  and bound_rls = allL exR

end
