header {*The sequent calculus for interval logic*}

theory ILSequent
imports DS4
begin


consts
(*Chop modality and interval variable *)
  chop            :: "[fform, fform] => fform"              (infixr "[^]" 38)
  l               :: exp

(*the special variable l is real*)
axiomatization where
ltrans : "l = RVar (''l'')" and
l_pos : "|- l[>=]Real 0"

axiomatization where
dia_def      : "<>P == WTrue [^] P [^] WTrue" and
box_def     : "[]P == [~] (<> ([~]P))"

(*datatype non = fform | exp*)


section {*Definitions and rules for rigid and chop-free.*}
consts
  RI            :: "'a  => prop"     ("(RI _)")
  CF           :: "fform => prop"     ("(CF _)")

(* Rules for RI and CF , the rules for all constructs are given, not just finalconsts.*)
axiomatization where
(* Rigid RI *)
RIfalse:           "RI WFalse" and
RIchopI:         "[| RI P :: fform; RI Q |]  ==> RI (P[^]Q)" and
RIchopE1:     "RI P[^]Q  ==> RI P::fform" and
RIchopE2:     "RI P[^]Q  ==> RI Q::fform" and
RIconjI:          "[| RI P; RI Q |] ==> RI P [&] Q" and
RIconjE1:      "RI P [&] Q  ==> RI P" and
RIconjE2:      "RI P [&] Q  ==> RI Q" and
RIdisjI:          "[| RI P; RI Q |] ==> RI P [|] Q" and
RIdisjE1:      "RI P [|] Q ==> RI P" and
RIdisjE2:      "RI P [|] Q ==> RI Q" and
RIimpI:         "[| RI P; RI Q |]  ==> RI P [-->] Q" and
RIimpE1:      "RI P[-->]Q  ==> RI P" and
RIimpE2:      "RI P[-->]Q  ==> RI Q" and
RInotI:         "RI P ==>  RI ([~]P)" and
RInotE:        "RI ([~]P)  ==>  RI P" 

axiomatization where
(* Quantifiers *)
RIallI:            "[| RI s;  RI P(s) |] ==> RI (ALL x. P(x))" and
RIallE:           "[| RI s; RI (ALL x. P(x)) |] ==> RI P(s)" and
RIequI:          "[| RI s; RI t |] ==> RI (s = t)" and
RIequE1:       "RI (s = t) ==> RI s" and
RIequE2:       "RI (s = t) ==> RI t" and
RInegI:          "RI s ==> RI (-s)" and 
RInegE:         "RI (-s) ==> RI s"  and
RIzero:          "RI 0" and  
RIone:           "RI 1" and
RIadd:            "[|RI s; RI t|] ==> RI (s+t)" and
RImult:            "[|RI s; RI t|] ==> RI (s*t)" and
RIdev:            "[|RI s; RI t|] ==> RI (s/t)" 


axiomatization where
(* Chop free CF *)
CFfalse:         "CF WFalse" and
CFimpI:         "[| CF P; CF Q |] ==> (CF P [-->] Q)"   and
CFimpE1:      "CF (P [-->] Q) ==> CF P" and
CFimpE2:      "CF (P [-->] Q) ==> CF Q" and
CFequ:           "CF (s [=] t)" and
CFconjI:        "[| CF P; CF Q |] ==> CF P[&]Q" and
CFconjE1:     "CF P[&]Q ==> CF P" and
CFconjE2:     "CF P[&]Q ==> CF Q" and
CFdisjI:        "[| CF P; CF Q |] ==> CF P[|]Q" and
CFdisjE1:     "CF P[|]Q ==> CF P" and
CFdisjE2:     "CF P[|]Q ==> CF Q" and
CFnotI:         "CF P ==> CF ([~]P)" and
CFnotE:        "CF ([~]P) ==> CF P" 

axiomatization where
(* Quantifiers *)
CFexI:            "CF P(s) ==> CF (WEX x P(x))" and
CFexE:           "CF (WEX x P(x)) ==> CF P(s)" and
CFallI:            "CF P(s) ==> CF (WALL x P(x))" and
CFallE:           "CF (WALL x P(x))  ==> CF P(s)" 

section {*Sequent rules for chop modality [Zhou and Hansen modified].*}
axiomatization where
LL2:                "[| RI s; RI t; $H, l [=] s [+] t |- $E |] ==> $H, (l [=] s) [^] (l [=] t) |- $E" and
RL2:                "[| RI s; RI t; $H |- l [=] s [+] t, $E |] ==> $H |- (l [=] s) [^] (l [=] t), $E" and

LL3:                " $H |- P, $E ==> $H  |- P [^] (l [=] (Real 0)), $E" and
RL3:                " $H, P [^] (l [=] Real 0) |- $E ==> $H, P |- $E" and
LL4:                " $H, P |- $E ==> $H, P [^] (l [=] Real 0) |- $E" and
RL4:                " $H |- P, $E ==> $H  |- P [^] (l [=] (Real 0)), $E" and
LL3a:                " $H, P |- $E ==> $H, (l [=] (Real 0)) [^] P |- $E" and
RL3a:                " $H |- P, $E ==> $H  |- (l [=] (Real 0)) [^] P, $E" and
LL1:                  "[| RI s; $H |- (l [=] s) [^] P, $E |] ==> $H, (l [=] s) [^] ([~]P) |- $E" and
RL1:                  "[| RI s; $H , (l [=] s) [^] P |- $E |] ==> $H |- (l [=] s) [^] ([~]P), $E" and
LL1a:                "[| RI s; $H |- P [^] (l [=] s) , $E |] ==> $H, ([~]P) [^] (l [=] s) |- $E" and
RL1a:                "[| RI s; $H , P [^] (l [=] s)  |- $E |] ==> $H |- ([~]P) [^] (l [=] s), $E" and 

LT1:                  "[| $H, P [^] Q |- $E;  $H, R [^] Q |- $E|] ==> $H, (P [|] R) [^] Q |- $E" and
RT1:                  "$H |- P [^] Q, R [^] Q, $E ==> $H |- (P [|] R) [^] Q, $E" and
LT1a:                "[| $H, P [^] Q |- $E;  $H, P [^] R |- $E|] ==> $H, P [^] (Q [|] R) |- $E" and
RT1a:                "$H |- P [^] Q, P [^] R, $E ==> $H |- P [^] (Q [|] R), $E" and

LA2:                 "$H, P [^] (Q [^] R) |- $E ==> $H, (P [^] Q) [^] R |- $E" and
RA2:                 "$H |- P [^] (Q [^] R), $E ==> $H |- (P [^] Q) [^] R, $E" 

axiomatization where
LB1:                  "(!!x. $H, (P(x) [^] Q) |- $E) ==> $H, ((WEX x P(x)) [^] Q) |- $E" and
RB1:                 "[|RI s; CF P(x); $H |- P(x) [^] Q, $E|] ==> $H |- (WEX x P(x)) [^] Q, $E" 

axiomatization where
LBr:                  "(!!x. $H, (P [^] Q(x)) |- $E) ==> $H, (P [^] (WEX x Q(x))) |- $E" and
RBr:                 "[|RI s; CF Q(x); $H |- P [^] Q(x), $E|] ==> $H |- P [^] (WEX x Q(x)), $E" 

(*Zouliang: add for conjunction*)
axiomatization where
LC1:                  "$H, P [^] Q, $E |- $F ==> $H, (P [&] R) [^] Q, $E |- $F" and
LC2:                  "$H, R [^] Q, $E |- $F ==> $H, (P [&] R) [^] Q, $E |- $F" and
LC3:                  "$H, Q [^] P, $E |- $F ==> $H, Q [^] (P [&] R), $E |- $F" and
LC4:                  "$H, Q [^] R, $E |- $F ==> $H, Q [^] (P [&] R), $E |- $F" and

TT:                    "WTrue [^] WTrue == WTrue" and
LT:                    "l[<](Real m) [^] WTrue == WTrue" and
LTa:                    "l[=](Real m) [^] WTrue == WTrue" and
CML:                   "[|$H, R [^] Q, $E |- $F; P|-R|] ==> $H, P [^] Q, $E |- $F" and
CMR:                   "[|$H, P [^] R, $E |- $F; Q|-R|] ==> $H, P [^] Q, $E |- $F"
end
