theory goal
	imports "processDef"
begin

(*Important formulae*)
definition HisP1 :: fform where
"HisP1 == (l [=] Real 0) [|] (high (plant_s_1[<=](Real 64000)))"

lemma ass1 : "|- l [=] Real 0 [^] l [=] Real 0 [-->] l [=] Real 0"
apply (rule impR)
apply (rule LL4)
apply (rule basic)
done

lemma ass2 : "(rn::real)>=0 ==> rn*rn+rn/2 + 1/32>=0"
by (metis add_increasing2 numeral_One zero_le_divide_iff zero_le_numeral zero_le_square)

lemma ass3 : "{WTrue}Skip{WTrue;l [=] Real 0}"
apply (rule Skip)
apply (rule impR)
apply (rule basic)
done

lemma ass4 : "(rn::real)>=0 ==> rn*rn+rn/2 + 1/32>=0"
by (metis add_increasing2 numeral_One zero_le_divide_iff zero_le_numeral zero_le_square)

lemma ass5 : "|- (l [=] Real 0 [|] high pn) [^]
        (l [=] Real 0 [|] high pn) [-->]
        l [=] Real 0 [|] high pn"
apply (rule impR)
apply (rule LT1)
apply (rule LT1a)
apply (rule disjR)
apply (cut_tac P="high pn" in thinR,auto)
apply (rule LL3a)
apply (rule basic)
apply (rule disjR)
apply (rule thinR)
apply (rule LL3a)
apply (rule basic)
apply (rule LT1a)
apply (rule disjR)
apply (rule thinR)
apply (rule LL4)
apply (rule basic)
apply (rule disjR)
apply (rule thinR)
apply (rule DCL3)
apply (rule basic)
done

lemma ass6 : "Pm**Suc(Suc(0)) == Pm;M;Pm"
apply (cut_tac Pm="Pm" and M="M" and am="1" in RepetitionN,auto)
apply (subgoal_tac "(Pm**(1)) == Pm",auto)
apply (subgoal_tac "Suc(Suc(0)) = 2",auto)
apply (cut_tac Pm="Pm" in Repetition1,auto)
done

lemma ass7 : "Pm**5 == Pm;M1;Pm;M2;Pm;M3;Pm;M4;Pm"
apply (cut_tac Pm="Pm" and M="M1" and am="4" in RepetitionN,auto)
apply (subgoal_tac "(Pm**(4)) == Pm;M2;Pm;M3;Pm;M4;Pm",auto)
apply (cut_tac Pm="Pm" and M="M2" and am="3" in RepetitionN,auto)
apply (subgoal_tac "(Pm**(3)) == Pm;M3;Pm;M4;Pm",auto)
apply (cut_tac Pm="Pm" and M="M3" and am="2" in RepetitionN,auto)
apply (subgoal_tac "(Pm**(2)) == Pm;M4;Pm",auto)
apply (subgoal_tac "Pm**Suc(Suc(0)) == Pm;M4;Pm")
apply (subgoal_tac "Suc(Suc(0)) = 2",auto)
apply (rule ass6)
done

lemma Init1: "{WTrue}PC1_1{plant_v_1 [=] Real 0 [&] plant_s_1 [=] Real 0;l [=] Real 0}"
apply (simp add: PC1_1_def)
apply (simp add: assertion1_def)
apply (cut_tac px="WTrue" and qx="plant_v_1[=](Real 0) [&] plant_s_1[=](Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: plant_v_1_def )
apply (rule Trans,auto)
apply (rule Assign,auto)
apply (simp add: plant_v_1_def plant_s_1_def)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule impR)
apply (rule LL3a)
apply (rule Trans1,auto)
done

lemma Init2: "{WTrue}((num:=(Real 0));assSF92;(E:=(String []));assSF93;(a:=(Real 0))){mInit;(l [=] (Real 0))}"
apply (simp add: assSF92_def)
apply (cut_tac px="WTrue" and qx="mInit" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (rule Trans, simp)
apply (cut_tac px="(num[=] (Real 0))" and qx="mInit" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF93_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def mInit_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (simp add: mInitRM1_def mInit_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (rule Trans, simp)
done

lemma Init3: "{WTrue}Pcontrol10{(done2[=](Real 0));l [=] Real 0}"
apply (simp add: Pcontrol10_def)
apply (rule Assign,auto)
apply (simp add: done2_def)
apply (rule Trans, auto)
done

lemma Init4: "{WTrue}Pcontrol13{(done3[=](Real 0));l [=] Real 0}"
apply (simp add: Pcontrol13_def)
apply (rule Assign,auto)
apply (simp add: done3_def)
apply (rule Trans, auto)
done

lemma Init5: "{WTrue}Pcontrol85{tInit;l [=] Real 0}"
apply (simp add: Pcontrol85_def)
apply (simp add: Pcontrol20_def)
apply (simp add: Pcontrol15_def Pcontrol16_def Pcontrol17_def Pcontrol18_def Pcontrol19_def)
apply (simp add: Pcontrol21_def)
apply (simp add: tInit_def)
apply (cut_tac px="WTrue" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (done1[=](Real 0)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF353_def assSF152_def)
apply (rule Sequence)
apply (cut_tac px="WTrue" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF149_def assSF123_def)
apply (rule Sequence)
(*1*)
apply (cut_tac px="WTrue" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF119_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF120_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF121_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF122_def assSF121_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF124_def assSF123_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v322_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF125_def assSF123_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v322_def v321_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF126_def assSF123_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v311_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF150_def)
apply (rule Sequence)
(*2*)
apply (simp add: assSF123_def assSF127_def assSF128_def assSF129_def assSF130_def assSF131_def assSF132_def assSF133_def)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF151_def assSF136_def)
apply (rule Sequence)
(*3*)
apply (simp add: assSF134_def assSF135_def assSF136_def assSF137_def assSF138_def assSF139_def assSF140_def)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def equal_greater_def)+
apply (rule Trans, simp)
(*4*)
apply (simp add: assSF141_def assSF142_def assSF143_def assSF144_def assSF145_def assSF146_def assSF147_def assSF148_def assSF136_def)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
(*4a*)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x2[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def actl2_def equal_greater_def)+
apply (rule Trans, simp)
(*5*)
apply (simp add: assSF354_def)
apply (cut_tac px="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0))" and qx="(C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (done1[=](Real 0)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
done

lemma Init6: "{WTrue}Pcontrol88{(done4[=](Real 0));l [=] Real 0}"
apply (simp add: Pcontrol88_def)
apply (rule Assign,auto)
apply (simp add: done4_def)
apply (rule Trans, auto)
done

lemma comm0Ass: "{mInitRM[&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT}(num:=(Real 1);assSF53;empty(EL);assSF54;(addL EL E);assSF55;empty(NL);assSF56;(addL NL (Real 1))){(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT;(l[=](Real 0))}"
apply (simp add: assSF53_def)
apply (cut_tac px="(s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and qx="(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule impR, rule basic)
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM_def impFT_def mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def e22_def e21_def mode33_def mode2_def mode3_def mode21_def mode22_def i_def x1_def x2_def actl3_def actl2a_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="(num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and qx="(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF54_def)
apply (rule Sequence)
apply (rule ListEmpty)
apply (cut_tac px="(EL[=](List []))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and qx="(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF55_def)
apply (rule Sequence)
apply (rule ListAdd)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and qx="(EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF56_def)
apply (rule Sequence)
apply (rule ListEmptya)
apply (rule ListAdda)
done

lemma arith1: "mInitRM1 [&] tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1)) |- [~] (done1 [=] Real 0 [&] s [>] e22)"
apply (cut_tac P="e22[=](Real 64000)[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))" in cut, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
by (smt real_minus_mult_self_le)

lemma arith2: "mInitRM1 [&] tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] (done1 [=] Real 0)  [&] (actl2a [=] (Real 1)) |- [~] (done1 [=] Real 0 [&] s [>] e32)"
apply (cut_tac P="e32[=](Real 64000)[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))" in cut, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
by (smt real_minus_mult_self_le)

lemma arith3: "mInitRM1 [&] tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] (done1 [=] Real 0) |- [~] (done1 [=] Real 0 [&] s [>] x2)"
apply (cut_tac P="x2[=](Real 64000)[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))" in cut, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
by (smt real_minus_mult_self_le)

lemma arith4: "(mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2 [=] Real 1)) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] Real -1) [&] (a [<=] Real 1) [&] (done1 [=] Real 1) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)) |- [~] (done1 [=] Real 0 [&] s [>] e22)"
apply (rule disjL)
apply (cut_tac P="e22[=](Real 64000)[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))" in cut, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
apply (smt real_minus_mult_self_le)
apply (cut_tac P="s[=]plant_s_1[&]e22[=](Real 64000)[&](impFT1 [|] impFT2)" in cut, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
by (smt ass2 real_minus_mult_self_le)

lemma core2: "{mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] Real 0)}Pcontrol76; assSF337 ; Pcontrol77; assSF338 ; Pcontrol78{mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2a [=] (Real 0)) [&] (s [=] plant_s_1);(l [=] Real 0)}"
(*to original*)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))" and qx="initAssF [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2a [=] (Real 0))[&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule impR, rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
apply (metis one_less_numeral_iff semiring_norm(75) zero_less_numeral)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply smt
apply (rule conjR, rule impR)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply (metis zero_neq_one)
apply (rule conjL, rule basic)
apply (rule impR, rule LL4, rule basic)
(*start*)
apply (simp add: assSF337_def)
apply (rule Sequence)
apply (simp add: Pcontrol76_def)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF318_def)
apply (rule Sequence)
(*core FB2*)
apply (simp add: FB2_def)
(*FB2-1*)
apply (simp add: Fcontrol4_def)
apply (simp add: assSF15_def assSF12_def)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (rule Sequence)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0)) [&] (T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
apply (rule impR, rule basic)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&](T[=](Real 1/8))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF13_def assSF12_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-2*)
apply (simp add: Fcontrol7_def)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF16_def assSF12_def)
apply (rule Sequence)
apply (simp add: Fcontrol5_def)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF17_def assSF12_def)
apply (rule Sequence)
apply (simp add: Fcontrol6_def)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-3*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF18_def assSF17_def)
apply (rule Sequence)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF14_def assSF12_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-4*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (simp add: Fcontrol8_def)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF19_def assSF17_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*FB22-5*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2a [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (simp add: Fcontrol9_def)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF20_def assSF17_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*FB22-6*)
apply (simp add: Fcontrol10_def)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*core path1*)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic)
apply (rule basic)
apply (rule disjR)
apply (cut_tac P="(done1[=](Real 1)[&]a[=](Real -1))" in thinR,auto)
prefer 2
apply (rule impR, rule basic)
apply (rule conjR, rule basic)
apply (cut_tac P="fv[<]vr1" in cut, auto)
apply (rule thinR)
apply (cut_tac P="done1 [=] Real 0" in cut, auto)
apply (rule thinR)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans3,simp)
apply (metis linorder_neqE_linordered_idom)
apply (rule conjR, rule basic)
apply (cut_tac P="v[*]v [+] (Real 1 / 2)[*]v [+] (Real 2)[*]T[*]T [+] (Real 2)[*]s [<=] (Real 128000)" in cut, auto)
prefer 2
apply (cut_tac P="s [=] plant_s_1" in cut, auto, rule basic)
apply (cut_tac P="v [=] plant_v_1" in cut, auto, rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans3,auto)
apply (rule thinR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="[~] (done1 [=] Real 0 [&] fv [>=] vr1)" in thinL,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans4,auto)
(*path1-1*)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&](T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR, rule disjR)
apply (rule thinR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)
apply (rule basic)
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF319_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule Trans1, auto)
apply (cut_tac px="initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&] (T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF320_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)
apply (rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&] (T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF321_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule basic)
apply (rule conjR, rule basic, rule basic)
(*core path2*)
apply (simp add: assSF338_def)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0)[&](actl2a [=] Real 0)[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8))[&](actl2a [=] Real 0)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&](done1[=](Real 1))[&](actl2a [=] Real 0)[&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule impR, rule basic)
apply (rule ass1)
apply (rule Sequence)
apply (simp add: Pcontrol77_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
prefer 2
apply (rule disjL)
apply (rule conjL)+
apply (rule conjR, rule disjR, rule basic)
apply (rule conjR)
apply (rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule disjR)
apply (rule thinR)
apply (cut_tac P="(a[=](Real -1))" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans1, simp add: a_def equal_less_def equal_greater_def)
apply (rule conjR, rule basic, rule basic)
apply (rule disjL)
prefer 2
apply (rule disjR, rule basic)
apply (rule disjR, cut_tac P="done1 [=] Real 1 [&] a [=] Real -1" in thinR,auto)
apply (rule conjL)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
(*path2-1*)
apply (cut_tac px="(initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF322_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)
apply (rule conjR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
apply (rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule basic)
apply (cut_tac px="(initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF323_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
prefer 2
apply (rule conjL)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (cut_tac px="(initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF324_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
prefer 2
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
prefer 2
apply (rule conjR)
apply (rule disjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule disjR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="RVar ''T'' [=] Real 1 / 8" in thinL, auto)
apply (cut_tac P="RVar ''actl2a'' [=] Real 0" in thinL, auto)
apply (rule disjL, rule  basic)
apply (rule thinR)
apply (rule Trans2, simp)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
prefer 2
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR)
prefer 2
apply (rule conjR, rule disjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule disjR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule disjL, rule basic)
apply (rule conjL, rule thinR)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule basic)
(*core path3*)
apply (simp add: Pcontrol78_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)
apply (rule conjR)
prefer 2
apply (cut_tac P="(done1 [=] Real 0 [|] done1 [=] Real 1)" in cut, auto)
apply (simp add: initAssF_def)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac P="(s [=] plant_s_1)" in cut, auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule notL, rule disjL, rule basic)
apply (rule disjL, rule basic)
apply (rule conjL)
apply (rule conjR, rule basic)+
apply (rule basic)
(*arith here*)
apply (rule disjR)
apply (cut_tac Q="done1[=](Real 1) [&] a[=](Real -1)" in disjL,auto)
apply (rule thinR)
apply (simp add: impFT2_def impFTO_def)
apply (rule conjL,rule conjR)
apply (rule basic)
apply (cut_tac P="(v [=] plant_v_1)" in cut, auto)
apply (rule basic)
apply (rule thinL,rule thinL,rule thinL,rule thinL)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule thinL)
apply (cut_tac P="RVar ''actl2a'' [=] Real 0" in thinL, auto)
apply (cut_tac P="RVar ''v'' [=] RVar ''plant_v_1''" in thinL, auto)
apply (rule Trans4,simp)
apply (subgoal_tac "rvar(''T'') = 1/8", simp)
apply (metis eq_divide_eq_numeral1(1) zero_neq_numeral)
apply (rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
apply (cut_tac P="RVar ''v'' [=] RVar ''plant_v_1''" in thinL, auto)
apply (rule Trans4,auto)
apply (rule basic)
apply (cut_tac P="impFT2" in thinR,auto)
apply (simp add: impFT1_def)
apply (rule conjR)
apply (cut_tac P="initAssF" in cut,auto)
apply (rule basic)
apply (rule thinL)
apply (cut_tac P=" done1 [=] Real 1 [&] a [=] Real -1" in thinL,auto)
apply (cut_tac P="done1 [=] Real 0 [|] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (cut_tac P="T [=] Real 1 / 8" in thinL,auto)
apply (cut_tac P="actl2a [=] Real 0" in thinL,auto)
apply (cut_tac P="[~] done1 [=] Real 0" in thinL,auto)
apply (cut_tac P="initAssF" in thinL,auto)
apply (simp add: impFTO_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule Trans3,auto)
apply (rule conjL, rule conjR, rule basic, rule basic)
(*arith end*)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
apply (cut_tac px="(initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((plant_v_1 [*] plant_v_1 [+] Real 1 / 2 [*] plant_v_1 [+] Real 2 [*] T [*] T [+] Real 2 [*] plant_s_1 [<=] Real 128000) [|] (done1 [=] Real 1) [&] (a [=] Real -1)) [&] ((done1 [=] Real 0) [|] (a [>=] Real -1) [&] (a [<=] Real 1)) [&] (T [=] Real 1 / 8) [&] (actl2a [=] Real 0)) [&] (done1 [=] Real 0)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule basic)
apply (rule conjR, rule impR, rule basic)
apply (rule ass1)
apply (simp add: assSF325_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
prefer 2
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac P="(plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))" in cut, auto)
prefer 2
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule Trans1, auto)
apply (rule conjL)+
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="((RVar ''done1'') [=] (Real 0)) [|] (((RVar ''a'') [>] (Real -1)) [|] ((RVar ''a'') [=] (Real -1))) [&] (((RVar ''a'') [<] (Real 1)) [|] ((RVar ''a'') [=] (Real 1)))" in thinL, auto)
apply (cut_tac P="RVar ''actl2a'' [=] Real 0" in thinL,auto)
apply (cut_tac P="plant_v_1 [*] plant_v_1 [+] (Real 1 / 2) [*] plant_v_1 [+] (Real 1 / 32) [+] (Real 2) [*] plant_s_1 [<=] (Real 128000)" in thinR,auto)
apply (rule disjL)
apply (rule Trans3, auto)
apply (subgoal_tac "rvar(''T'')=1/8",simp)
apply (metis nonzero_divide_eq_eq zero_neq_numeral)
apply (subgoal_tac "rvar(''T'')=1/8",simp)
apply (metis nonzero_divide_eq_eq zero_neq_numeral)
apply (cut_tac P="RVar ''T'' [=] Real 1 / 8" in thinL, auto)
apply (rule Trans2, auto)
apply (cut_tac px="initAssFC [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF326_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR, rule disjR, rule basic)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (cut_tac px="initAssF [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF327_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule disjR)
apply (rule conjR, rule basic)+
apply (rule thinR)
apply (rule conjR)
apply (cut_tac P="RVar ''C_A'' [=] Real 1" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans1, simp)
apply (rule basic)
apply (cut_tac P="RVar ''C_A'' [=] Real 1" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans4, simp)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR)
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic, rule basic)
done

lemma core1: "{mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1))} (Pcontrol55; assSF275 ; Pcontrol56; assSF276 ; Pcontrol57) {mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1);(l[=](Real 0))}"
(*to original*)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))" and qx="initAssF [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule impR, rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def)
apply (rule Trans1, simp)
apply (metis one_less_numeral_iff semiring_norm(75) zero_less_numeral)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply smt
apply (rule conjR, rule impR)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule Trans1, simp)
apply (metis zero_neq_one)
apply (rule conjL, rule basic)
apply (rule impR, rule LL4, rule basic)
(*start*)
apply (simp add: assSF275_def)
apply (rule Sequence)
apply (simp add: Pcontrol55_def)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF256_def)
apply (rule Sequence)
(*core FB22*)
apply (simp add: FB22_def)
(*FB22-1*)
apply (simp add: Fcontrol21_def)
apply (simp add: assSF44_def assSF41_def)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (rule Sequence)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0)) [&] (T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def equal_less_def equal_greater_def) 
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
apply (rule impR, rule basic)
apply (cut_tac px="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&](T[=](Real 1/8))" and qx="initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF42_def assSF41_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-2*)
apply (simp add: Fcontrol23_def)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF45_def assSF41_def)
apply (rule Sequence)
apply (simp add: Fcontrol22_def)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF46_def assSF41_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-3*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (simp add: Fcontrol24_def)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF47_def assSF46_def)
apply (rule Sequence)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF43_def assSF41_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def equal_greater_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans,simp)
apply smt
(*FB22-4*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (simp add: Fcontrol25_def)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF48_def assSF46_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*FB22-5*)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0))[&](actl2 [=] Real 0)[&]vr1 [<=] (Real 128000 [-] Real 2 [*] s) [+] Real 2 [*] T [*] T[&](T[=](Real 1/8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0)[&](actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8))" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
apply (simp add: Fcontrol26_def)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule ass1)
apply (simp add: assSF49_def assSF46_def)
apply (rule Sequence)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*FB22-6*)
apply (simp add: Fcontrol27_def)
apply (rule Assign)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans1,simp)
apply smt
apply (rule impR, rule basic)
(*core path1*)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic)
apply (rule basic)
apply (rule disjR)
apply (cut_tac P="(done1[=](Real 1)[&]a[=](Real -1))" in thinR,auto)
prefer 2
apply (rule impR, rule basic)
apply (rule conjR, rule basic)
apply (cut_tac P="fv[<]vr1" in cut, auto)
apply (rule thinR)
apply (cut_tac P="done1 [=] Real 0" in cut, auto)
apply (rule thinR)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans3,simp)
apply (metis linorder_neqE_linordered_idom)
apply (rule conjR, rule basic)
apply (cut_tac P="v[*]v [+] (Real 1 / 2)[*]v [+] (Real 2)[*]T[*]T [+] (Real 2)[*]s [<=] (Real 128000)" in cut, auto)
prefer 2
apply (cut_tac P="s [=] plant_s_1" in cut, auto, rule basic)
apply (cut_tac P="v [=] plant_v_1" in cut, auto, rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans3,auto)
apply (rule thinR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="[~] (done1 [=] Real 0 [&] fv [>=] vr1)" in thinL,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)
apply (rule Trans4,auto)
(*path1-1*)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&](T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR, rule disjR)
apply (rule thinR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)
apply (rule basic)
apply (rule impR, rule LL4, rule basic)
apply (simp add: assSF257_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule Trans1, auto)
apply (cut_tac px="initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&] (T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF258_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR, rule disjR, rule thinR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)
apply (rule basic)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&] (T [=] (Real 1 / 8))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((done1[=](Real 1)[&]a[=](Real -1))) [&] (T [=] (Real 1 / 8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF259_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR, rule Trans1, auto)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule basic)
apply (rule conjR, rule basic, rule basic)
(*core path2*)
apply (simp add: assSF276_def)
apply (cut_tac px="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&](done1[=](Real 0)[&](actl2 [=] Real 0)[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8))[&](actl2 [=] Real 0)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&](done1[=](Real 1))[&](actl2 [=] Real 0)[&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule impR, rule basic)
apply (rule ass1)
apply (rule Sequence)
apply (simp add: Pcontrol56_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
prefer 2
apply (rule disjL)
apply (rule conjL)+
apply (rule conjR, rule disjR, rule basic)
apply (rule conjR)
apply (rule basic, rule basic)
apply (rule conjL)+
apply (rule conjR, rule disjR)
apply (rule thinR)
apply (cut_tac P="(a[=](Real -1))" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans1, simp add: a_def equal_less_def equal_greater_def)
apply (rule conjR, rule basic, rule basic)
apply (rule disjL)
prefer 2
apply (rule disjR, rule basic)
apply (rule disjR, cut_tac P="done1 [=] Real 1 [&] a [=] Real -1" in thinR,auto)
apply (rule conjL)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
(*path2-1*)
apply (cut_tac px="(initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF260_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)
apply (rule conjR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
apply (rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule basic)
apply (cut_tac px="(initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF261_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
prefer 2
apply (rule conjL)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule disjR, rule basic)
apply (rule conjR, rule disjR, rule thinR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (cut_tac px="(initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0))" and qx="initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF262_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
prefer 2
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR)
prefer 2
apply (rule conjR)
apply (rule disjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule disjR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="RVar ''T'' [=] Real 1 / 8" in thinL, auto)
apply (cut_tac P="RVar ''actl2'' [=] Real 0" in thinL, auto)
apply (rule disjL, rule  basic)
apply (rule thinR)
apply (rule Trans2, simp)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
prefer 2
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR)
prefer 2
apply (rule conjR, rule disjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic, rule basic)
apply (rule disjR)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule disjL, rule basic)
apply (rule conjL, rule thinR)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule basic)
(*core path3*)
apply (simp add: Pcontrol57_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)
apply (rule conjR)
prefer 2
apply (cut_tac P="(done1 [=] Real 0 [|] done1 [=] Real 1)" in cut, auto)
apply (simp add: initAssF_def)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac P="(s [=] plant_s_1)" in cut, auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule notL, rule disjL, rule basic)
apply (rule disjL, rule basic)
apply (rule conjL)
apply (rule conjR, rule basic)+
apply (rule basic)
(*arith here*)
apply (rule disjR)
apply (cut_tac Q="done1[=](Real 1) [&] a[=](Real -1)" in disjL,auto)
apply (rule thinR)
apply (simp add: impFT2_def impFTO_def)
apply (rule conjL,rule conjR)
apply (rule basic)
apply (cut_tac P="(v [=] plant_v_1)" in cut, auto)
apply (rule basic)
apply (rule thinL,rule thinL,rule thinL,rule thinL)
apply (rule conjR)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule thinL)
apply (cut_tac P="RVar ''actl2'' [=] Real 0" in thinL, auto)
apply (cut_tac P="RVar ''v'' [=] RVar ''plant_v_1''" in thinL, auto)
apply (rule Trans4,simp)
apply (subgoal_tac "rvar(''T'') = 1/8", simp)
apply (metis eq_divide_eq_numeral1(1) zero_neq_numeral)
apply (rule thinL, rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
apply (cut_tac P="RVar ''v'' [=] RVar ''plant_v_1''" in thinL, auto)
apply (rule Trans4,auto)
apply (rule basic)
apply (cut_tac P="impFT2" in thinR,auto)
apply (simp add: impFT1_def)
apply (rule conjR)
apply (cut_tac P="initAssF" in cut,auto)
apply (rule basic)
apply (rule thinL)
apply (cut_tac P=" done1 [=] Real 1 [&] a [=] Real -1" in thinL,auto)
apply (cut_tac P="done1 [=] Real 0 [|] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (cut_tac P="T [=] Real 1 / 8" in thinL,auto)
apply (cut_tac P="actl2 [=] Real 0" in thinL,auto)
apply (cut_tac P="[~] done1 [=] Real 0" in thinL,auto)
apply (cut_tac P="initAssF" in thinL,auto)
apply (simp add: impFTO_def)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule Trans3,auto)
apply (rule conjL, rule conjR, rule basic, rule basic)
(*arith end*)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
apply (cut_tac px="(initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((plant_v_1 [*] plant_v_1 [+] Real 1 / 2 [*] plant_v_1 [+] Real 2 [*] T [*] T [+] Real 2 [*] plant_s_1 [<=] Real 128000) [|] (done1 [=] Real 1) [&] (a [=] Real -1)) [&] ((done1 [=] Real 0) [|] (a [>=] Real -1) [&] (a [<=] Real 1)) [&] (T [=] Real 1 / 8) [&] (actl2 [=] Real 0)) [&] (done1 [=] Real 0)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule basic)
apply (rule conjR, rule impR, rule basic)
apply (rule ass1)
apply (simp add: assSF263_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
prefer 2
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac P="(plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))" in cut, auto)
prefer 2
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule Trans1, auto)
apply (rule conjL)+
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="((RVar ''done1'') [=] (Real 0)) [|] (((RVar ''a'') [>] (Real -1)) [|] ((RVar ''a'') [=] (Real -1))) [&] (((RVar ''a'') [<] (Real 1)) [|] ((RVar ''a'') [=] (Real 1)))" in thinL, auto)
apply (cut_tac P="RVar ''actl2'' [=] Real 0" in thinL,auto)
apply (cut_tac P="plant_v_1 [*] plant_v_1 [+] (Real 1 / 2) [*] plant_v_1 [+] (Real 1 / 32) [+] (Real 2) [*] plant_s_1 [<=] (Real 128000)" in thinR,auto)
apply (rule disjL)
apply (rule Trans3, auto)
apply (subgoal_tac "rvar(''T'')=1/8",simp)
apply (metis nonzero_divide_eq_eq zero_neq_numeral)
apply (subgoal_tac "rvar(''T'')=1/8",simp)
apply (metis nonzero_divide_eq_eq zero_neq_numeral)
apply (cut_tac P="RVar ''T'' [=] Real 1 / 8" in thinL, auto)
apply (rule Trans2, auto)
apply (cut_tac px="initAssFC [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF264_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
prefer 2
apply (rule conjR)
apply (rule conjR, rule basic, rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR, rule disjR, rule basic)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (cut_tac px="initAssF [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1)" and qx="initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&] (done1 [=] Real 1) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR)
apply (rule Trans,auto)
apply (rule conjR)
apply (rule Trans,auto)
apply (rule ass1)
apply (simp add: assSF265_def)
apply (rule Sequence)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule disjR)
apply (rule conjR, rule basic)+
apply (rule thinR)
apply (rule conjR)
apply (cut_tac P="RVar ''C_A'' [=] Real 1" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans1, simp)
apply (rule basic)
apply (cut_tac P="RVar ''C_A'' [=] Real 1" in cut,auto)
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (rule Trans4, simp)
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule conjR)
prefer 2
apply (rule impR, rule basic)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR)
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic, rule basic)
done

lemma comm1AssA1: "{((mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))) [&] (done1 [=] Real 0) [&] (i [=] Real 2) [&] (s [>=] x1)}(actl2 := (Real 0); assSF277 ; actl2a := (Real 1); assSF278 ; a := C_b; assSF279 ; done1 := (Real 1)){(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1));(l[=](Real 0))}"
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule conjL)+
apply (rule disjL)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (cut_tac P="done1[=](Real 1)" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL)
apply (simp add: mInitRM1_def tInit_def initAssF_def initAssFC_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def vr2_def fv_def e33_def min_def equal_less_def equal_greater_def)+
apply (rule Trans4, simp)
apply (metis zero_neq_one)
apply (rule conjR)
apply (rule impR, rule disjR, rule basic)
apply (rule impR, rule LL4, rule basic)
(*start*)
apply (simp add: assSF277_def assSF278_def assSF279_def)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def tInitC_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="mInitRM1 [&] tInitC [&] impFT [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def tInitC_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="mInitRM1 [&] tInit [&] impFT [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def tInitC_def equal_greater_def)+
apply (rule Trans, simp)
apply smt
apply (rule Assign, auto)
apply (simp add: mInitRM1_def tInit_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def v332_def v312_def v232_def v231_def v222_def v221_def v212_def v211_def e33_def tInitC_def equal_greater_def)+
apply (rule Trans, simp)
by smt

lemma comm1Ass1: "{mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)}Pcontrol84; assSF357 ; done1 := (Real 0){mInitRM1 [&] tInit [&] (impFT1 [|] impFT2) [&] (a [<=] (Real 1)) [&] (a [>=] (Real -1));WTrue [&] l [=] Real 0}"
(*done1*)
apply (simp add: assSF357_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)" and qx="mInitRM1 [&] tInit [&] (impFT1 [|] impFT2) [&] (a [<=] (Real 1)) [&] (a [>=] (Real -1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
prefer 2
apply (rule Assign,auto)
apply (simp add: mInitRM1_def tInit_def impFT1_def impFT2_def equal_less_def equal_greater_def)
apply (simp add: tInit_def equal_less_def equal_greater_def)
apply (simp add: impFT1_def equal_less_def equal_greater_def)
apply (simp add: impFT2_def equal_less_def equal_greater_def)
apply (simp add: equal_less_def equal_greater_def)
apply (simp add: equal_less_def equal_greater_def)
apply (simp add: impFT1_def impFT2_def num_def s_def v_def mInitRM1_def tInit_def vBO2_def E_def E1_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def tInitRM_def i_def actl2_def actl2a_def)
apply (rule conjR, rule impR)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
(*main*)
apply (simp add: Pcontrol84_def)
apply (rule ConditionT)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
(*1*)
apply (simp add: assSF343_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (rule ConditionF)
apply (simp add: tInit_def)
apply (rule impR)
apply (rule conjL)+
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="s [=] plant_s_1" in thinL,auto)
apply (cut_tac P="v [=] plant_v_1" in thinL,auto)
apply (cut_tac P="impFT" in thinL,auto)
apply (cut_tac P="done1 [=] Real 0" in thinL,auto)
apply (rule Trans3, simp add: actl3_def)
apply (rule impR, rule basic)+
(*separate*)
apply (simp add: assSF348_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
(*2*)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
apply (rule impR, rule disjR, rule conjL)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (cut_tac P="((actl2[=](Real 1))[|](actl2a[=](Real 1)))" in cut,auto)
apply (simp add: tInit_def)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="tInitRM [&] (impFT1 [|] impFT2) [&] a [>=] Real -1 [&] a [<=] Real 1 [&] done1 [=] Real 1 [&] (actl2[=] (Real 0))[&](s [=] plant_s_1)" in thinR,auto)
apply (rule Trans2, simp add: actl2_def actl2a_def)
apply metis
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac px="(mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)) [&] (actl2a [=] (Real 1))" and qx="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (simp add: assSF344_def assSF343_def)
apply (rule Sequence)
(*here*)
apply (simp add: Pcontrol58_def)
apply (simp add: assSF266_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0)) [&] (actl2a [=] (Real 1))" and qx="mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2a [=] (Real 1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol42_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL, cut_tac P="actl2a [=] Real 1" in thinL, auto)
apply (rule arith3)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL)
apply (cut_tac P="tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] done1 [=] Real 0 [&] (actl2a [=] (Real 1))" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF345_def assSF344_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1))" and qx="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol59_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL)
apply (cut_tac P="tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] done1 [=] Real 0 [&] (actl2a [=] (Real 1))" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule impR, rule basic)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF346_def assSF344_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1))" and qx="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol60_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule arith1)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF347_def assSF344_def)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1))" and qx="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol61_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule arith2)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: Pcontrol62_def)
apply (rule ConditionT)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 1))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0))[&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)
apply (rule conjR, rule impR, rule disjR, rule basic)
apply (rule impR, rule basic)
apply (rule core1)
(*3*)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
apply (rule impR)
apply (rule conjL, rule disjL)
apply (rule notL)
apply (rule thinR)
apply (rule conjL)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR)
apply (rule conjL)+
apply (rule basic)
apply (simp add: assSF349_def assSF348_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule conjL, rule basic)
apply (rule conjR, rule impR, rule basic)
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
(*here*)
apply (simp add: Pcontrol79_def)
apply (simp add: assSF328_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and qx="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol63_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR)
apply (rule conjL, rule basic)
apply (rule impR, rule conjL, rule basic)
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR)
apply (rule conjL, rule basic)
apply (rule comm1AssA1)
(*here*)
apply (rule ConditionF)
apply (rule impR)
apply (rule disjL)
apply (rule conjL)
apply (cut_tac P="tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] done1 [=] Real 0 [&] actl2 [=] Real 1" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule conjL)
apply (cut_tac P="tInitRM [&] (impFT1 [|] impFT2) [&] a [>=] Real -1 [&] a [<=] Real 1 [&] done1 [=] Real 1 [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule impR, rule basic)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF350_def assSF348_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol80_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule disjL)
apply (cut_tac P="tInit" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, simp add: tInit_def)
apply (cut_tac P="i[=](Real 2)" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, rule Trans1, simp add: i_def)
apply (cut_tac P="tInitRM" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, simp add: tInitRM_def)
apply (cut_tac P="i[=](Real 2)" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, rule Trans1, simp add: i_def)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF351_def assSF348_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol81_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule disjL)
apply (rule conjL)
apply (cut_tac P="tInit [&] s [=] plant_s_1 [&] v [=] plant_v_1 [&] impFT [&] done1 [=] Real 0 [&] actl2 [=] Real 1" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule conjL)
apply (cut_tac P="tInitRM [&] (impFT1 [|] impFT2) [&] a [>=] Real -1 [&] a [<=] Real 1 [&] done1 [=] Real 1 [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1)" in thinL,auto)
apply (simp add: mInitRM1_def)
apply (rule conjL)
apply (cut_tac P="E [=] String [] [&] a [>=] Real -1 [&] a [<=] Real 1" in thinL,auto)
apply (rule Trans1, simp add: E1_def)
apply (rule impR, rule basic)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: assSF352_def assSF348_def)
apply (cut_tac px="(mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2 [=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1))" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))[^](l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, auto)
apply (rule Sequence)
apply (simp add: Pcontrol82_def)
apply (rule ConditionF)
apply (rule impR)
apply (rule arith4)
apply (rule impR, rule basic)+
(*here*)
apply (simp add: Pcontrol83_def)
apply (rule Condition)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL, rule basic)
apply (rule impR, rule conjL, rule disjL)
apply (rule notL)
apply (rule conjL)+
apply (rule basic)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule ConditionT)
apply (rule impR, rule conjL, rule basic)
apply (cut_tac px="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1 [=] Real 0) [&] (actl2a [=] Real 0)" and qx="mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2a [=] (Real 0)) [&] (s [=] plant_s_1)" and Hx="(l [=] (Real 0))" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR)
apply (rule conjL, rule disjL)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (cut_tac P="((actl2[=](Real 0))[|](actl2a[=](Real 0)))" in cut, auto)
apply (simp add: tInit_def)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL, rule thinL, rule thinL, rule thinL, rule thinL, rule thinL)
apply (cut_tac P="done1 [=] Real 0" in thinL, auto)
apply (rule Trans2, simp add: actl2_def actl2a_def)
apply (metis zero_neq_one)
apply (cut_tac P="done1 [=] Real 1" in cut, auto)
apply (rule conjL)+
apply (rule basic)
apply (rule thinL)
apply (rule Trans2, simp add: done1_def)
apply (metis zero_neq_one)
apply (rule conjR, rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
apply (rule core2)
done

lemma comm1Ass2: "{(EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}num := (num [+] (Real 1)); assSF62 ; delL NL; assSF63 ; addL NL num{(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);l [=] Real 0}"
apply (simp add: assSF62_def assSF63_def )
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: EL_def mInitRM1_def tInit_def mInitRM_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule ListDela)
apply (rule ListAdda)
done

lemma comm2Ass1: "{E2[=](String [])}Pcontrol8; assSF109 ; Pcontrol9; assSF110 ; done2 := (Real 0){E2 [=](String []);WTrue [&] (l [=] (Real 0))}"
apply (simp add: Pcontrol8_def Pcontrol9_def)
apply (simp add: assSF109_def)
apply (cut_tac px="E2 [=] String []" and qx="E2 [=] String []" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, simp)
apply (rule Sequence)
apply (rule ConditionF)
apply (rule impR, rule Trans1, simp add: E2_def)+
apply (cut_tac px="E2 [=] String []" and qx="E2 [=] String []" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, simp)
apply (simp add: assSF110_def)
apply (rule Sequence)
apply (rule ConditionF)
apply (rule impR, rule Trans1, simp add: E2_def)+
apply (rule Assign, auto)
apply (simp add: E2_def done2_def)
apply (rule Trans, simp)
done

(*the same to comm1Ass2*)
lemma comm2Ass2: "{(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}num := (num [+] Real 1); assSF69 ; delL NL; assSF70 ; addL NL num{(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);(l [=] (Real 0))}"
apply (simp add: assSF69_def assSF70_def )
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: EL_def mInitRM1_def tInit_def mInitRM_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule ListDela)
apply (rule ListAdda)
done

lemma comm3Ass1: "{E3[=]String []}Pcontrol12;assSF117;done3:=(Real 0){E3[=]String [];WTrue[&]l [=] Real 0}"
apply (simp add: Pcontrol12_def)
apply (cut_tac px="E3 [=] String []" and qx="E3 [=] String []" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, simp)
apply (simp add: assSF117_def)
apply (rule Sequence)
apply (rule ConditionF)
apply (rule impR, rule Trans1, simp add: E3_def)+
apply (rule Assign, auto)
apply (simp add: E3_def done3_def)
apply (rule Trans, simp)
done

(*the same to comm2Ass2*)
lemma comm3Ass2: "{(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}num := (num [+] Real 1); assSF76 ; delL NL; assSF77 ; addL NL num{(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);l [=] (Real 0)}"
apply (simp add: assSF76_def assSF77_def )
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: EL_def mInitRM1_def tInit_def mInitRM_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule ListDela)
apply (rule ListAdda)
done

(*the same to comm2Ass1*)
lemma comm4Ass1: "{E4 [=] String []}Pcontrol87; assSF364 ; done4 := (Real 0){E4[=]String [];WTrue [&] l [=] Real 0}"
apply (simp add: Pcontrol87_def)
apply (cut_tac px="E4 [=] String []" and qx="E4 [=] String []" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule Trans1, simp)
apply (simp add: assSF364_def)
apply (rule Sequence)
apply (rule ConditionF)
apply (rule impR, rule Trans1, simp add: E4_def)+
apply (rule Assign, auto)
apply (simp add: E4_def done4_def)
apply (rule Trans, simp)
done

(*the same to comm2Ass2*)
lemma comm4Ass2: "{(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}num := (num [+] Real 1); assSF83 ; delL NL; assSF84 ; addL NL num{(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);l [=] Real 0}"
apply (simp add: assSF83_def assSF84_def )
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule Assign, auto)
apply (simp add: EL_def mInitRM1_def tInit_def mInitRM_def initAssF_def impFTO_def impFT_def impFT1_def impFT2_def tInitRM_def E1_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def i_def x1_def x2_def done1_def actl2_def actl2a_def actl3_def plant_s_1_def plant_v_1_def s_def v_def T_def vr1_def e33_def min_def equal_less_def num_def equal_greater_def)+
apply (rule Trans, simp)
apply metis
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="(l[=]Real 0)[^](l[=]Real 0)" in ConsequenceS,auto)
prefer 2
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule LL4, rule basic)
apply (rule Sequence)
apply (rule ListDela)
apply (rule ListAdda)
done

lemma comm5Ass1: "{(EL[=](List []))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}num := (Real 0){(EL[=](List []))[&](num[=](Real 0)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);WTrue [&] l [=] Real 0}"
apply (rule Assign)
apply (simp add: mInitRM_def tInit_def impFT1_def impFT2_def equal_less_def equal_greater_def)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def i_def actl2_def actl2a_def)
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: impFT1_def impFT2_def num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans,auto)
done

lemma comm5Ass2: "{(EL[=](List []))[&](num[=](Real 0)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)}E := (String []){(EL[=](List []))[&](num[=](Real 0)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2);WTrue [&] l [=] Real 0}"
apply (rule Assign)
apply (simp add: mInitRM_def tInit_def impFT1_def impFT2_def equal_less_def equal_greater_def)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def i_def actl2_def actl2a_def)
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR)
apply (rule thinL)+
apply (rule Trans, auto)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: impFT1_def impFT2_def num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans,auto)
done

(*Goal for the whole process.*)
lemma goal : "{WTrue,WTrue,WTrue,WTrue,WTrue,WTrue} P {(plant_s_1[<=](Real 64000)),WTrue,WTrue,WTrue,WTrue,WTrue; (l [=] Real 0) [|] (high (plant_s_1[<=](Real 64000))),WTrue,WTrue,WTrue,WTrue,WTrue}"
(*return init and rep goal in this section*)
apply (simp add: P_def)
apply (simp add: PC1_def Pcontrol_def)
apply (simp add: Pcontrol7_def Pcontrol11_def Pcontrol14_def Pcontrol86_def Pcontrol89_def)
apply (simp add: assertion4_def assSF95_def assSF107_def assSF115_def assSF355_def assSF362_def)
apply (cut_tac Ha="HisP1" and Hb="WTrue" and Hc="WTrue" and Hd="WTrue" and He="WTrue" and Hf="WTrue" in ParallelSeq6,auto)
defer defer
apply (simp add: HisP1_def)
apply (rule impR, rule LL3a, rule basic)
apply (rule Trans,auto)+
defer
(*init*)
apply (rule Parallel26)
apply (rule Parallel25)
apply (rule Parallel24)
apply (rule Parallel23)
apply (simp add: PC1_init_def)
apply (simp add: assertion2_def)
apply (simp add: assSF94_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m=0 in Parallel3,auto)
apply (rule Parallel2)
apply (cut_tac px="WTrue" and qx="plant_v_1[=](Real 0)[&]plant_s_1[=](Real 0)" and Hx="(l [=] (Real 0))" in ConsequenceS,auto)
apply (rule Init1)
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule conjR, rule basic, rule basic)
apply (cut_tac px="WTrue" and qx="mInit" and Hx="(l [=] (Real 0))" in ConsequenceS,auto)
apply (rule Init2)
apply (rule conjR, rule impR, rule basic)+
apply (rule impR, rule conjR, rule basic, rule basic)
apply (simp add: PC1_2_def)
apply (simp add: commI1_def)
apply (cut_tac Init="WTrue" and pre="plant_v_1[=](Real 0) [&] plant_s_1[=](Real 0)" and x="control_1_0" in CommunicationI2a,auto)
apply (simp add: mInit_def plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def equal_greater_def)+
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (simp add: mInit_def plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def done2_def done3_def done4_def done1_def equal_greater_def aVal_def )
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule impR, rule LL4, rule conjL, rule basic)+
apply (rule Trans,auto)
apply (rule Init3)
apply (rule Init4)
apply (rule Init5)
apply (rule Init6)
(*rep*)
(*get rid of repetition*)
apply (cut_tac qa="(impF1 [|] impF2)[&]aVal" and qb="mInit" and qc="WTrue" and qd="WTrue" and qe="tInit" and qf="WTrue" and ra="(impF1 [|] impF2)[&]aVal" and rb="mInit" and rc="WTrue" and rd="WTrue" and re="tInit" and rf="WTrue" and Ha="HisP1" and Hb="WTrue" and Hc="WTrue" and Hd="WTrue" and He="WTrue" and Hf="WTrue" in Consequence6,auto)
defer
apply (rule conjR, rule Trans,auto)+
apply (rule Trans,auto)
apply (rule conjR)
apply (rule impR, rule conjL, rule disjL)
apply (simp add: plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def done2_def done3_def done4_def done1_def equal_greater_def aVal_def)
apply (rule Trans2, simp)
apply (smt real_minus_mult_self_le)
apply (cut_tac P="aVal" in thinL,auto)
apply (simp add: impF2_def)
apply (rule conjL, rule conjL)
apply (cut_tac P="control_1_0 [>=] Real -1 [&] control_1_0 [<=] Real 1" in thinL,auto)
apply (simp add: plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def done2_def done3_def done4_def done1_def equal_greater_def aVal_def)
apply (rule Trans2, simp)
apply (subgoal_tac "rvar(''plant_v_1'')>=0 ==> rvar(''plant_v_1'')*rvar(''plant_v_1'')+rvar(''plant_v_1'')/2 + 1/32>=0")
apply smt
apply (rule ass2,simp)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule RepetitionG6)
defer
apply (simp add: HisP1_def, rule ass5)
apply (rule Trans,auto)+
apply (cut_tac am=1 and an=0 and ao=0 and ap=0 and aq=0 and ar=0 in RepetitionA6,auto)
apply (cut_tac Qm="PC1_rep;((plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000)),HisP1);PC1_rep" and Qn="(Pcontrol1; assSF96 ; Pcontrol2; assSF97 ; Pcontrol3; assSF98 ; Pcontrol4; assSF99 ; Pcontrol5; assSF100 ; Pcontrol6)" and Qo="(BC_2??E2; assSF108 ; (Pcontrol8; assSF109 ; Pcontrol9; assSF110 ; done2 := (Real 0)); assSF111 ; BO_2!!(String []))" and Qp="(BC_3??E3; assSF116 ; (Pcontrol12; assSF117 ; done3 := (Real 0)); assSF118 ; BO_3!!(String []))" and Qq="(BC_1??E1; assSF356 ; (Pcontrol84; assSF357 ; done1 := (Real 0)); assSF358 ; BO_1!!(String []))" and Qr="(BC_4??E4; assSF363 ; (Pcontrol87; assSF364 ; done4 := (Real 0)); assSF365 ; BO_4!!(String []))" in Equality6,auto)
apply (rule ass6)
apply (rule Repetition1)+
(*get rid of communication*)
apply (simp add: Pcontrol1_def)
apply (simp add: assSF94_def assSF95_def assSF96_def assSF97_def assSF98_def)
apply (cut_tac Ha="HisP1" and Hb="WTrue" in ParallelSeq12a,auto)
(*comm0*)
defer defer
apply (simp add: HisP1_def, rule ass5)
apply (rule Trans,auto)
defer
apply (rule ConditionT2)
apply (rule Trans,simp add: mInit_def num_def)
apply (simp add: assSF52_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a,auto)
prefer 3
apply (rule Trans,auto)
prefer 2
apply (rule comm0Ass)
apply (simp add: PC1_rep_def)
(*interupt1*)
apply (simp add: assertion3_def PC1_3_def)
apply (simp add: assSF51_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="(high (plant_s_1[<=](Real 64000)))" and Hy="WTrue" and m="1/8" in Parallel3,auto)
apply (simp add: assSF50_def commI1_def)
apply (cut_tac Hy="l[=](Real 1/8)" and e="plant_s_1" and Hxm="WTrue" and Hx="WTrue" and H="l[=](Real 1/8)" and Init="aVal" and pre="(impF1 [|] impF2)" in CommunicationI1b,auto)
apply (simp add: s_def plant_s_1_def mInitRM_def C_a_def equal_less_def equal_greater_def)+
apply (rule Trans, auto)
apply (simp add: LTa, rule Trans, auto)
apply (simp add: s_def plant_s_1_def mInit_def mInitRM_def C_a_def equal_less_def equal_greater_def)
apply (rule Continue)
apply (simp add: equal_less_def)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (simp add: impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def)
apply (rule Trans, auto)
apply (simp add: impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def)
apply (rule Trans, auto)
apply (simp add: mInitRM_def C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def s_def)
apply (rule Trans, auto)
apply (rule impR, rule conjR)
apply (rule conjL, rule disjL)
apply (cut_tac P="WFalse" in cut,auto)
apply (rule thinR)
apply (rule Trans2,auto)
apply (simp add: ltrans)
apply (rule FalseL)
apply (cut_tac P="l [=] (Real 1/8)" in thinL,auto)
(*something*)
apply (rule DC18)
apply (rule conjL, rule thinL, rule conjL)
apply (cut_tac P="close(domain1)" in thinL,auto)
apply(rule disjL)
apply (simp add: plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def done2_def done3_def done4_def done1_def equal_greater_def aVal_def)
apply (rule Trans1, simp)
apply (smt real_minus_mult_self_le)
apply (simp add: impF2_def)
apply (rule conjL, rule conjL)
apply (cut_tac P="control_1_0 [>=] Real -1 [&] control_1_0 [<=] Real 1" in thinL,auto)
apply (simp add: plant_v_1_def plant_s_1_def control_1_0_def a_def impF1_def impF2_def equal_less_def done2_def done3_def done4_def done1_def equal_greater_def aVal_def)
apply (rule Trans2, simp)
apply (subgoal_tac "rvar(''plant_v_1'')>=0 ==> rvar(''plant_v_1'')*rvar(''plant_v_1'')+rvar(''plant_v_1'')/2 + 1/32>=0")
apply smt
apply (rule ass4,simp)
apply (rule Trans1,auto)
apply (rule impR, rule conjR)
apply (rule Trans1,auto)+
apply (rule Trans,auto)+
(*interupt2*)
apply (simp add: PC1_4_def commI1_def)
apply (cut_tac e="plant_v_1" and Init="WTrue" and pre="impF" in CommunicationI1a,auto)
apply (simp add: mInitRM_def C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def mInitRM_def s_def impFT_def)+
apply (rule Trans,auto)
apply (simp add: mInitRM_def C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def mInitRM_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (simp add: mInitRM_def C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def mInitRM_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (simp add: mInitRM_def C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def mInitRM_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (simp add: HisP1_def)
apply (rule impR, rule disjR, rule thinR)
apply (rule LL4, rule conjL, rule basic)
apply (rule impR, rule LL4, rule conjL, rule basic)+
(*comm1*)
apply (cut_tac Hb="WTrue" in ParallelSeq25a,auto)
prefer 3
apply (rule Trans,auto)
(*comm2*)
apply (cut_tac Hb="WTrue" in ParallelSeq23a,auto)
prefer 3
apply (rule Trans,auto)
prefer 2
apply (simp add: Pcontrol3_def)
apply (rule ConditionT2a)
apply (rule Trans,simp add: mInit_def num_def)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="WTrue" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (simp add: assSF64_def assSF108_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m=0 in Parallel3,auto)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="E2[=](String [])" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (rule CommunicationSim)
apply (simp add: E_def E2_def)
apply (simp add: E_def E2_def mInitRM_def)
apply (rule Trans,auto)+
apply (simp add: assSF111_def assSF108_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm2Ass1)
apply (simp add: assSF68_def assSF64_def)
apply (cut_tac ch="BO_2" and x="vBO2" in CommunicationC,auto)
apply (rule comm2Ass2)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def i_def actl2_def actl2a_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: impFT1_def impFT2_def num_def s_def v_def mInitRM_def tInit_def vBO2_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4, rule conjL, rule basic)+
apply (rule conjR, rule impR, rule basic)+
apply (rule Trans, auto)
(*comm3*)
apply (simp add: assSF99_def)
apply (cut_tac Hb="WTrue" in ParallelSeq23b,auto)
prefer 3
apply (rule Trans,auto)
prefer 2
apply (simp add: Pcontrol4_def)
apply (rule ConditionT2a)
apply (rule Trans,simp add: mInit_def num_def)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="WTrue" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (simp add: assSF71_def assSF116_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m=0 in Parallel3,auto)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="E3[=](String [])" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (rule CommunicationSim)
apply (simp add: E_def E3_def)
apply (simp add: E_def E3_def mInitRM_def)
apply (rule Trans,auto)+
apply (simp add: assSF118_def assSF116_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm3Ass1)
apply (simp add: assSF75_def assSF71_def)
apply (cut_tac ch="BO_3" and x="vBO3" in CommunicationC,auto)
apply (rule comm3Ass2)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO3_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def i_def actl2_def actl2a_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: impFT1_def impFT2_def num_def s_def v_def mInitRM_def tInit_def vBO3_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4, rule conjL, rule basic)+
apply (rule conjR, rule impR, rule basic)+
apply (rule Trans, auto)
(*comm4*)
apply (simp add: assSF100_def)
apply (cut_tac Hb="WTrue" in ParallelSeq23c,auto)
prefer 3
apply (rule Trans,auto)
prefer 2
apply (simp add: Pcontrol5_def)
apply (rule ConditionT2a)
apply (rule Trans,simp add: mInit_def num_def)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="WTrue" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (simp add: assSF78_def assSF363_def assSF77_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m=0 in Parallel3,auto)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and py="WTrue" and qx="(EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qy="E4[=](String [])" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (rule CommunicationSim)
apply (simp add: E_def E4_def)
apply (simp add: E_def E4_def mInitRM_def)
apply (rule Trans,auto)+
apply (simp add: assSF365_def assSF363_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm4Ass1)
apply (simp add: assSF82_def assSF78_def)
apply (cut_tac ch="BO_4" and x="vBO4" in CommunicationC,auto)
apply (rule comm4Ass2)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO4_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def i_def actl2_def actl2a_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def impFT1_def impFT2_def vBO4_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4, rule conjL, rule basic)+
apply (rule conjR, rule impR, rule basic)+
apply (rule Trans, auto)
(*comm5*)
apply (simp add: Pcontrol6_def)
apply (rule ConditionT2)
apply (rule Trans,simp add: mInit_def num_def)
apply (simp add: PC1_rep_def)
(*1*)
apply (simp add: assSF85_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List (tl([E]))))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="l[=](Real 0)" in ConsequenceS,auto)
apply (rule ListDel)
apply (rule impR)
apply (rule conjR)
apply (rule conjL)
apply (cut_tac P="(num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" in thinL,auto)
apply (rule Trans1,simp add: EL_def)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule impR, rule basic)+
apply (rule Trans, auto)
prefer 2 
apply (rule Trans, auto)
prefer 2 
apply (rule Trans, auto)
(*2*)
apply (simp add: assSF86_def assSF85_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (cut_tac px="(EL[=](List []))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and qx="(EL[=](List (tl([]))))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" and Hx="l[=](Real 0)" in ConsequenceS,auto)
apply (rule ListDela)
apply (rule conjR, rule impR, rule basic)+
apply (rule Trans, auto)
prefer 2 
apply (rule Trans, auto)
prefer 2
apply (rule impR, rule LL4, rule conjL, rule basic) 
(*3*)
apply (simp add: assSF90_def assSF87_def)
apply (cut_tac Gy="l[=](Real 0)" in Parallel1a,auto)
apply (rule ConditionT2)
apply (rule impR, rule conjL)
apply (cut_tac P="(num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" in thinL, auto)
apply (rule Empty)
prefer 3
apply (rule impR, rule LL4, rule basic)
prefer 2
apply (rule ConditionF)
apply (rule impR, rule conjL)
apply (cut_tac P="(num[=](Real 0)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2)" in thinL, auto)
apply (rule notR, rule notL)
apply (rule Empty)
apply (rule impR, simp add: mInit_def mInitRM_def)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule impR, rule basic)
(*4*)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm5Ass1)
prefer 2
apply (rule Trans, auto)
prefer 2
apply (rule impR, rule LL4, rule conjL, rule basic)
(*5*)
apply (simp add: assSF88_def assSF87_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm5Ass2)
prefer 2
apply (rule Trans, auto)
prefer 2
apply (rule impR, rule LL4, rule conjL, rule basic)
(*6*)
(*6a*)
apply (simp add: assertion3_def assSF89_def assSF87_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m="0" in Parallel3,auto)
apply (simp add: PC1_3_def commI1_def)
apply (cut_tac x="control_1_0" and Init="WTrue" and pre="plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000)" in CommunicationI2a,auto)
apply (simp add: mInitRM_def equal_less_def equal_greater_def)
apply (simp add: tInit_def equal_less_def equal_greater_def)
apply (simp add: impFT1_def equal_less_def equal_greater_def)
apply (simp add: impFT2_def equal_less_def equal_greater_def)
apply (rule Trans,auto)
apply (simp add: C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (simp add: C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (rule Trans,auto)+
(*5a2*)
apply (simp add: PC1_4_def commI1_def)
apply (simp add: impF_def)
apply (cut_tac x="control_1_0" and Init="WTrue" and pre="plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000)" in CommunicationI2a,auto)
apply (simp add: mInitRM_def equal_less_def equal_greater_def)
apply (simp add: tInit_def equal_less_def equal_greater_def)
apply (simp add: impFT1_def equal_less_def equal_greater_def)
apply (simp add: impFT2_def equal_less_def equal_greater_def)
apply (rule Trans,auto)
apply (simp add: C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (simp add: C_b_def C_A_def C_a_def v331_def e32_def actl3_def actl2_def done1_def v231_def v222_def v221_def v212_def v211_def e33_def e31_def e23_def equal_less_def equal_greater_def x1_def x2_def e22_def e21_def mode33_def mode32_def mode31_def mode23_def mode22_def mode21_def mode3_def mode2_def i_def x2_def x1_def actl3_def actl2a_def actl2_def E1_def actl2_def impF1_def impF2_def aVal_def domain1_def inv1_def plant_v_1_def plant_s_1_def control_1_0_def plant_and_1_def s_def impFT_def impF_def domain2_def inv2_def)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (rule Trans,auto)
apply (simp add: HisP1_def, rule impR, rule disjR)
apply (rule LL4, rule conjL, rule basic)
apply (rule impR, rule LL4, rule Trans1,auto)
(*focus on comm1*)
apply (simp add: Pcontrol2_def)
apply (rule ConditionT2a)
apply (rule Trans, auto)
apply (simp add: assSF57_def assSF356_def)
apply (cut_tac Mx="l[=](Real 0)" and My="l[=](Real 0)" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" and m="0" in Parallel3,auto)
apply (cut_tac px="(EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] impFT" and py="tInit" and qx="(EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] impFT" and qy="mInitRM1 [&] tInit [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFT [&] (done1[=](Real 0))" and Hx="l[=](Real 0)" and Hy="l[=](Real 0)" in ConsequenceP,auto)
apply (rule CommunicationSim)
apply (simp add: E_def E1_def mInitRM_def mInitRM1_def tInit_def impFT_def equal_less_def equal_greater_def)
apply (rule conjR, rule impR, rule basic)
apply (rule impR)
apply (simp add: tInit_def E_def E1_def mInitRM_def mInitRM1_def impFT_def a_def plant_v_1_def v_def s_def equal_less_def equal_greater_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def done1_def i_def actl2_def actl2a_def)
apply (rule conjL)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)+
apply (rule conjR)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule impR, rule basic)
apply (rule conjR)
apply (rule impR, rule basic)
apply (rule conjR)
apply (rule impR, rule basic)
apply (rule conjR, rule Trans, auto)
apply (rule Trans, auto)
apply (simp add: assSF358_def)
apply (cut_tac Hy="WTrue" and My="l[=](Real 0)" in Parallel4,auto)
apply (rule comm1Ass1)
apply (simp add: assSF61_def)
apply (cut_tac ch="BO_1" and x="vBO1" in CommunicationC,auto)
apply (simp add: tInit_def)
apply (simp add: equal_greater_def)
apply (simp add: equal_less_def)
apply (rule comm1Ass2)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def vBO4_def E_def a_def C_a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def vBO1_def i_def actl2_def actl2a_def)
apply (rule impR)
apply (rule conjL)+
apply (rule conjR, rule basic)+
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (rule conjR)
apply (rule conjR, rule basic)+
apply (rule basic)
apply (simp add: num_def s_def v_def mInitRM_def tInit_def impFT1_def impFT2_def vBO4_def E_def a_def C_b_def C_A_def v331_def e32_def e22_def x1_def x2_def done1_def actl3_def plant_s_1_def plant_v_1_def equal_greater_def equal_less_def EL_def)
apply (rule basic)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
apply (rule Trans, auto)
apply (rule Trans, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
apply (rule impR, rule LL4)
apply (rule Trans1, auto)
done

end
