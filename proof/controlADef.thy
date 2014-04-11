theory controlADef
	imports "controlVarDef"
begin

definition mInit :: fform where
"mInit == ((num[=] (Real 0)) [&] (E[=] (String [])) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)))"
definition mInitRM :: fform where
"mInitRM == ((E[=] (String [])) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)))"
definition mInitRM1 :: fform where
"mInitRM1 == ((E1[=] (String [])) [&] (E[=] (String [])) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)))"
definition tInit :: fform where
"tInit == (C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (done1[=](Real 0)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0))"
definition tInitC :: fform where
"tInitC == (C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (done1[=](Real 0)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] (actl3[=](Real 0))"
definition tInitRM :: fform where
"tInitRM == (C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0))"
definition impFT :: fform where
"impFT == (plant_v_1[>=](Real 0))[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))[&]((actl2[=](Real 0))[|](s[<](Real 33000)))[&](v [=] plant_v_1)"
definition impFT1 :: fform where
"impFT1 == (plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000)) [&] (a[=](Real -1))[&](v [=] plant_v_1)"
definition impFT2 :: fform where
"impFT2 == (plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000)) [&] (a[>=](Real -1) [&] (a[<=](Real 1)))[&](v [=] plant_v_1)"

definition initAssF :: fform where
"initAssF == (C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (i[=](Real 2)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0)) [&] (E1[=](String '''')) [&] (E[=](String '''')) [&] ((done1[=](Real 0)) [|] (done1[=](Real 1)))"
definition initAssFC :: fform where
"initAssFC == (C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (i[=](Real 2)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] (actl3[=](Real 0)) [&] (E1[=](String '''')) [&] (E[=](String '''')) [&] ((done1[=](Real 0)) [|] (done1[=](Real 1)))"

definition impFTO :: fform where
"impFTO == (plant_v_1[>=](Real 0))[&](v[*]v [+] (Real 2)[*]s[<=](Real 128000))"

definition assSF1 :: mid where
"assSF1 == (WTrue,l[=](Real 0))"
definition assSF2 :: mid where
"assSF2 == (WTrue,l[=](Real 0))"
definition assSF3 :: mid where
"assSF3 == (WTrue,l[=](Real 0))"
definition assSF4 :: mid where
"assSF4 == (WTrue,l[=](Real 0))"
definition assSF5 :: mid where
"assSF5 == (WTrue,l[=](Real 0))"
definition assSF6 :: mid where
"assSF6 == (WTrue,l[=](Real 0))"
definition assSF7 :: mid where
"assSF7 == (WTrue,l[=](Real 0))"
definition assSF8 :: mid where
"assSF8 == (WTrue,l[=](Real 0))"
definition assSF9 :: mid where
"assSF9 == (WTrue,l[=](Real 0))"
definition assSF10 :: mid where
"assSF10 == (WTrue,l[=](Real 0))"
definition assSF11 :: mid where
"assSF11 == (WTrue,l[=](Real 0))"
definition assSF12 :: mid where
"assSF12 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0)) [&] (T[=](Real 1/8)),l[=](Real 0))"
definition assSF13 :: mid where
"assSF13 == assSF12"
definition assSF14 :: mid where
"assSF14 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0) [&] (actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]T[=](Real 1/8),l[=](Real 0))"
definition assSF15 :: mid where
"assSF15 == assSF12"
definition assSF16 :: mid where
"assSF16 == assSF12"
definition assSF17 :: mid where
"assSF17 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0) [&] (actl2a [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]T[=](Real 1/8),l[=](Real 0))"
definition assSF18 :: mid where
"assSF18 == assSF17"
definition assSF19 :: mid where
"assSF19 == assSF17"
definition assSF20 :: mid where
"assSF20 == assSF17"
definition assSF21 :: mid where
"assSF21 == (WTrue,l[=](Real 0))"
definition assSF22 :: mid where
"assSF22 == (WTrue,l[=](Real 0))"
definition assSF23 :: mid where
"assSF23 == (WTrue,l[=](Real 0))"
definition assSF24 :: mid where
"assSF24 == (WTrue,l[=](Real 0))"
definition assSF25 :: mid where
"assSF25 == (WTrue,l[=](Real 0))"
definition assSF26 :: mid where
"assSF26 == (WTrue,l[=](Real 0))"
definition assSF27 :: mid where
"assSF27 == (WTrue,l[=](Real 0))"
definition assSF28 :: mid where
"assSF28 == (WTrue,l[=](Real 0))"
definition assSF29 :: mid where
"assSF29 == (WTrue,l[=](Real 0))"
definition assSF30 :: mid where
"assSF30 == (WTrue,l[=](Real 0))"
definition assSF31 :: mid where
"assSF31 == (WTrue,l[=](Real 0))"
definition assSF32 :: mid where
"assSF32 == (WTrue,l[=](Real 0))"
definition assSF33 :: mid where
"assSF33 == (WTrue,l[=](Real 0))"
definition assSF34 :: mid where
"assSF34 == (WTrue,l[=](Real 0))"
definition assSF35 :: mid where
"assSF35 == (WTrue,l[=](Real 0))"
definition assSF36 :: mid where
"assSF36 == (WTrue,l[=](Real 0))"
definition assSF37 :: mid where
"assSF37 == (WTrue,l[=](Real 0))"
definition assSF38 :: mid where
"assSF38 == (WTrue,l[=](Real 0))"
definition assSF39 :: mid where
"assSF39 == (WTrue,l[=](Real 0))"
definition assSF40 :: mid where
"assSF40 == (WTrue,l[=](Real 0))"
definition assSF41 :: mid where
"assSF41 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0)) [&] (T[=](Real 1/8)),l[=](Real 0))"
definition assSF42 :: mid where
"assSF42 == assSF41"
definition assSF43 :: mid where
"assSF43 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0) [&] (actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]T[=](Real 1/8),l[=](Real 0))"
definition assSF44 :: mid where
"assSF44 == assSF41"
definition assSF45 :: mid where
"assSF45 == assSF41"
definition assSF46 :: mid where
"assSF46 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]done1[=](Real 0) [&] (actl2 [=] Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]T[=](Real 1/8),l[=](Real 0))"
definition assSF47 :: mid where
"assSF47 == assSF46"
definition assSF48 :: mid where
"assSF48 == assSF46"
definition assSF49 :: mid where
"assSF49 == assSF46"
definition assSF50 :: mid where
"assSF50 == (mInitRM,l[=](Real 1/8))"
definition assSF51 :: mid where
"assSF51 == (mInitRM[&](s[=]plant_s_1),l[=](Real 1/8))"
definition assSF52 :: mid where
"assSF52 == (mInitRM[&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT,l[=](Real 1/8))"
definition assSF53 :: mid where
"assSF53 == ((num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT,l[=](Real 0))"
definition assSF54 :: mid where
"assSF54 == ((EL[=](List []))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT,l[=](Real 0))"
definition assSF55 :: mid where
"assSF55 == ((EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT,l[=](Real 0))"
definition assSF56 :: mid where
"assSF56 == ((EL[=](List [E]))[&](num[=](Real 1))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]mInitRM [&] impFT,l[=](Real 0))"
definition assSF57 :: mid where
"assSF57 == ((EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] impFT,WTrue)"
definition assSF58 :: mid where
"assSF58 == (WTrue,l[=](Real 0))"
definition assSF59 :: mid where
"assSF59 == (WTrue,l[=](Real 0))"
definition assSF60 :: mid where
"assSF60 == ((C_b [=] (Real -1)),l[=](Real 0))"
definition assSF61 :: mid where
"assSF61 == ((EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF62 :: mid where
"assSF62 == ((EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF63 :: mid where
"assSF63 == ((EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF64 :: mid where
"assSF64 == ((EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF65 :: mid where
"assSF65 == assSF64"
definition assSF66 :: mid where
"assSF66 == assSF64"
definition assSF67 :: mid where
"assSF67 == assSF64"
definition assSF68 :: mid where
"assSF68 == assSF64"
definition assSF69 :: mid where
"assSF69 == ((EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF70 :: mid where
"assSF70 == ((EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF71 :: mid where
"assSF71 == ((EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF72 :: mid where
"assSF72 == assSF64"
definition assSF73 :: mid where
"assSF73 == assSF64"
definition assSF74 :: mid where
"assSF74 == assSF64"
definition assSF75 :: mid where
"assSF75 == assSF71"
definition assSF76 :: mid where
"assSF76 == ((EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF77 :: mid where
"assSF77 == ((EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF78 :: mid where
"assSF78 == ((EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF79 :: mid where
"assSF79 == assSF77"
definition assSF80 :: mid where
"assSF80 == assSF77"
definition assSF81 :: mid where
"assSF81 == assSF77"
definition assSF82 :: mid where
"assSF82 == assSF78"
definition assSF83 :: mid where
"assSF83 == ((EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF84 :: mid where
"assSF84 == ((EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF85 :: mid where
"assSF85 == ((EL[=](List []))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF86 :: mid where
"assSF86 == assSF85"
definition assSF87 :: mid where
"assSF87 == ((EL[=](List []))[&](num[=](Real 0)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),(l[=](Real 0)))"
definition assSF88 :: mid where
"assSF88 == assSF87"
definition assSF89 :: mid where
"assSF89 == assSF87"
definition assSF90 :: mid where
"assSF90 == assSF87"
definition assSF91 :: mid where
"assSF91 == assSF64"
definition assSF92 :: mid where
"assSF92 == ((num[=] (Real 0)),l[=](Real 0))"
definition assSF93 :: mid where
"assSF93 == ((num[=] (Real 0)) [&] (E[=] (String [])),l[=](Real 0))"
definition assSF94 :: mid where
"assSF94 == (mInit,l[=](Real 0))"
definition assSF95 :: mid where
"assSF95 == (mInit,WTrue)"
definition assSF96 :: mid where
"assSF96 == ((EL[=](List [E]))[&](num[=](Real 1)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] impFT,WTrue)"
definition assSF97 :: mid where
"assSF97 == ((EL[=](List [E]))[&](num[=](Real 2)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF98 :: mid where
"assSF98 == ((EL[=](List [E]))[&](num[=](Real 3)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),WTrue)"
definition assSF99 :: mid where
"assSF99 == ((EL[=](List [E]))[&](num[=](Real 4)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF100 :: mid where
"assSF100 == ((EL[=](List [E]))[&](num[=](Real 5)) [&] (s[=]plant_s_1) [&] (v[=]plant_v_1) [&] mInitRM [&] tInit [&] (impFT1 [|] impFT2),l[=](Real 0))"
definition assSF101 :: mid where
"assSF101 == (WTrue,l[=](Real 0))"
definition assSF102 :: mid where
"assSF102 == (done2[=](Real 0),l[=](Real 0))"
definition assSF103 :: mid where
"assSF103 == (WTrue,l[=](Real 0))"
definition assSF104 :: mid where
"assSF104 == (WTrue,l[=](Real 0))"
definition assSF105 :: mid where
"assSF105 == ((done2[=](Real 0)),l[=](Real 0))"
definition assSF106 :: mid where
"assSF106 == ((done2[=](Real 0)),l[=](Real 0))"
definition assSF107 :: mid where
"assSF107 == ((done2[=](Real 0)),l[=](Real 0))"
definition assSF108 :: mid where
"assSF108 == (E2[=](String []),l[=](Real 0))"
definition assSF109 :: mid where
"assSF109 == (E2[=](String []),l[=](Real 0))"
definition assSF110 :: mid where
"assSF110 == (E2[=](String []),l[=](Real 0))"
definition assSF111 :: mid where
"assSF111 == assSF108"
definition assSF112 :: mid where
"assSF112 == assSF111"
definition assSF113 :: mid where
"assSF113 == ((done3[=](Real 0)),l[=](Real 0))"
definition assSF114 :: mid where
"assSF114 == ((done3[=](Real 0)),l[=](Real 0))"
definition assSF115 :: mid where
"assSF115 == ((done3[=](Real 0)),l[=](Real 0))"
definition assSF116 :: mid where
"assSF116 == (E3[=](String []),l[=](Real 0))"
definition assSF117 :: mid where
"assSF117 == (E3[=](String []),l[=](Real 0))"
definition assSF118 :: mid where
"assSF118 == assSF116"
definition assSF119 :: mid where
"assSF119 == ((C_b [=] (Real -1)),l[=](Real 0))"
definition assSF120 :: mid where
"assSF120 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)),l[=](Real 0))"
definition assSF121 :: mid where
"assSF121 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)),l[=](Real 0))"
definition assSF122 :: mid where
"assSF122 == assSF121"
definition assSF123 :: mid where
"assSF123 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)),l[=](Real 0))"
definition assSF124 :: mid where
"assSF124 == assSF123"
definition assSF125 :: mid where
"assSF125 == assSF123"
definition assSF126 :: mid where
"assSF126 == assSF123"
definition assSF127 :: mid where
"assSF127 == assSF123"
definition assSF128 :: mid where
"assSF128 == assSF123"
definition assSF129 :: mid where
"assSF129 == assSF123"
definition assSF130 :: mid where
"assSF130 == assSF123"
definition assSF131 :: mid where
"assSF131 == assSF123"
definition assSF132 :: mid where
"assSF132 == assSF123"
definition assSF133 :: mid where
"assSF133 == assSF123"
definition assSF134 :: mid where
"assSF134 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)),l[=](Real 0))"
definition assSF135 :: mid where
"assSF135 == assSF134"
definition assSF136 :: mid where
"assSF136 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)),l[=](Real 0))"
definition assSF137 :: mid where
"assSF137 == assSF136"
definition assSF138 :: mid where
"assSF138 == assSF136"
definition assSF139 :: mid where
"assSF139 == assSF136"
definition assSF140 :: mid where
"assSF140 == assSF136"
definition assSF141 :: mid where
"assSF141 == assSF136"
definition assSF142 :: mid where
"assSF142 == assSF136"
definition assSF143 :: mid where
"assSF143 == assSF136"
definition assSF144 :: mid where
"assSF144 == assSF136"
definition assSF145 :: mid where
"assSF145 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)),l[=](Real 0))"
definition assSF146 :: mid where
"assSF146 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x2[=](Real 64000)),l[=](Real 0))"
definition assSF147 :: mid where
"assSF147 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)),l[=](Real 0))"
definition assSF148 :: mid where
"assSF148 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl3[=](Real 0)),l[=](Real 0))"
definition assSF149 :: mid where
"assSF149 == assSF123"
definition assSF150 :: mid where
"assSF150 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)),l[=](Real 0))"
definition assSF151 :: mid where
"assSF151 == assSF136"
definition assSF152 :: mid where
"assSF152 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2a[=](Real 0)) [&] (actl3[=](Real 0)),l[=](Real 0))"
definition assSF153 :: mid where
"assSF153 == assSF125"
definition assSF154 :: mid where
"assSF154 == assSF137"
definition assSF155 :: mid where
"assSF155 == assSF154"
definition assSF156 :: mid where
"assSF156 == assSF154"
definition assSF157 :: mid where
"assSF157 == assSF154"
definition assSF158 :: mid where
"assSF158 == assSF154"
definition assSF159 :: mid where
"assSF159 == assSF154"
definition assSF160 :: mid where
"assSF160 == assSF154"
definition assSF161 :: mid where
"assSF161 == assSF154"
definition assSF162 :: mid where
"assSF162 == assSF154"
definition assSF163 :: mid where
"assSF163 == assSF154"
definition assSF164 :: mid where
"assSF164 == assSF154"
definition assSF165 :: mid where
"assSF165 == assSF154"
definition assSF166 :: mid where
"assSF166 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)),l[=](Real 0))"
definition assSF167 :: mid where
"assSF167 == assSF166"
definition assSF168 :: mid where
"assSF168 == assSF166"
definition assSF169 :: mid where
"assSF169 == assSF166"
definition assSF170 :: mid where
"assSF170 == assSF166"
definition assSF171 :: mid where
"assSF171 == assSF166"
definition assSF172 :: mid where
"assSF172 == assSF166"
definition assSF173 :: mid where
"assSF173 == assSF166"
definition assSF174 :: mid where
"assSF174 == assSF166"
definition assSF175 :: mid where
"assSF175 == assSF166"
definition assSF176 :: mid where
"assSF176 == assSF166"
definition assSF177 :: mid where
"assSF177 == assSF166"
definition assSF178 :: mid where
"assSF178 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (x2[=](Real 64000)),l[=](Real 0))"
definition assSF179 :: mid where
"assSF179 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)),l[=](Real 0))"
definition assSF180 :: mid where
"assSF180 == (mInit,l[=](Real 0))"
definition assSF181 :: mid where
"assSF181 == assSF180"
definition assSF182 :: mid where
"assSF182 == assSF154"
definition assSF183 :: mid where
"assSF183 == assSF166"
definition assSF184 :: mid where
"assSF184 == assSF166"
definition assSF185 :: mid where
"assSF185 == (WTrue,l[=](Real 0))"
definition assSF186 :: mid where
"assSF186 == (WTrue,l[=](Real 0))"
definition assSF187 :: mid where
"assSF187 == (WTrue,l[=](Real 0))"
definition assSF188 :: mid where
"assSF188 == (WTrue,l[=](Real 0))"
definition assSF189 :: mid where
"assSF189 == (WTrue,l[=](Real 0))"
definition assSF190 :: mid where
"assSF190 == (WTrue,l[=](Real 0))"
definition assSF191 :: mid where
"assSF191 == (WTrue,l[=](Real 0))"
definition assSF192 :: mid where
"assSF192 == (WTrue,l[=](Real 0))"
definition assSF193 :: mid where
"assSF193 == (WTrue,l[=](Real 0))"
definition assSF194 :: mid where
"assSF194 == (WTrue,l[=](Real 0))"
definition assSF195 :: mid where
"assSF195 == (WTrue,l[=](Real 0))"
definition assSF196 :: mid where
"assSF196 == (WTrue,l[=](Real 0))"
definition assSF197 :: mid where
"assSF197 == assSF89"
definition assSF198 :: mid where
"assSF198 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF199 :: mid where
"assSF199 == (((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2[=](Real 0)) [&] (actl3[=](Real 0)) [&] (E1[=](String '''')))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0)[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF200 :: mid where
"assSF200 == assSF198"
definition assSF201 :: mid where
"assSF201 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](a[=](Real -1))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF202 :: mid where
"assSF202 == (((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2[=](Real 0)) [&] (actl3[=](Real 0)) [&] (E1[=](String '''')))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](done1[=](Real 0)[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000)))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF203 :: mid where
"assSF203 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](done1[=](Real 0)[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000)))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF204 :: mid where
"assSF204 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF205 :: mid where
"assSF205 == (((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2[=](Real 0)) [&] (actl3[=](Real 0)) [&] (E1[=](String '''')))[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF206 :: mid where
"assSF206 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF207 :: mid where
"assSF207 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000)) [&] (a[>=](Real -1) [&] a[<=](Real 1))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF208 :: mid where
"assSF208 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0),l[=](Real 0))"
definition assSF209 :: mid where
"assSF209 == (WTrue,l[=](Real 0))"
definition assSF210 :: mid where
"assSF210 == (WTrue,l[=](Real 0))"
definition assSF211 :: mid where
"assSF211 == (WTrue,l[=](Real 0))"
definition assSF212 :: mid where
"assSF212 == (WTrue,l[=](Real 0))"
definition assSF213 :: mid where
"assSF213 == (WTrue,l[=](Real 0))"
definition assSF214 :: mid where
"assSF214 == (WTrue,l[=](Real 0))"
definition assSF215 :: mid where
"assSF215 == (WTrue,l[=](Real 0))"
definition assSF216 :: mid where
"assSF216 == (WTrue,l[=](Real 0))"
definition assSF217 :: mid where
"assSF217 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&](done1[=](Real 0)[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF218 :: mid where
"assSF218 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF219 :: mid where
"assSF219 == (WTrue,l[=](Real 0))"
definition assSF220 :: mid where
"assSF220 == (WTrue,l[=](Real 0))"
definition assSF221 :: mid where
"assSF221 == (WTrue,l[=](Real 0))"
definition assSF222 :: mid where
"assSF222 == (WTrue,l[=](Real 0))"
definition assSF223 :: mid where
"assSF223 == (WTrue,l[=](Real 0))"
definition assSF224 :: mid where
"assSF224 == (WTrue,l[=](Real 0))"
definition assSF225 :: mid where
"assSF225 == (WTrue,l[=](Real 0))"
definition assSF226 :: mid where
"assSF226 == (WTrue,l[=](Real 0))"
definition assSF227 :: mid where
"assSF227 == (WTrue,l[=](Real 0))"
definition assSF228 :: mid where
"assSF228 == (WTrue,l[=](Real 0))"
definition assSF229 :: mid where
"assSF229 == (WTrue,l[=](Real 0))"
definition assSF230 :: mid where
"assSF230 == (WTrue,l[=](Real 0))"
definition assSF231 :: mid where
"assSF231 == (WTrue,l[=](Real 0))"
definition assSF232 :: mid where
"assSF232 == (WTrue,l[=](Real 0))"
definition assSF233 :: mid where
"assSF233 == (WTrue,l[=](Real 0))"
definition assSF234 :: mid where
"assSF234 == (WTrue,l[=](Real 0))"
definition assSF235 :: mid where
"assSF235 == (WTrue,l[=](Real 0))"
definition assSF236 :: mid where
"assSF236 == (WTrue,l[=](Real 0))"
definition assSF237 :: mid where
"assSF237 == (WTrue,l[=](Real 0))"
definition assSF238 :: mid where
"assSF238 == (WTrue,l[=](Real 0))"
definition assSF239 :: mid where
"assSF239 == (WTrue,l[=](Real 0))"
definition assSF240 :: mid where
"assSF240 == (WTrue,l[=](Real 0))"
definition assSF241 :: mid where
"assSF241 == (WTrue,l[=](Real 0))"
definition assSF242 :: mid where
"assSF242 == (WTrue,l[=](Real 0))"
definition assSF243 :: mid where
"assSF243 == (WTrue,l[=](Real 0))"
definition assSF244 :: mid where
"assSF244 == (WTrue,l[=](Real 0))"
definition assSF245 :: mid where
"assSF245 == (WTrue,l[=](Real 0))"
definition assSF246 :: mid where
"assSF246 == (WTrue,l[=](Real 0))"
definition assSF247 :: mid where
"assSF247 == (WTrue,l[=](Real 0))"
definition assSF248 :: mid where
"assSF248 == (WTrue,l[=](Real 0))"
definition assSF249 :: mid where
"assSF249 == (WTrue,l[=](Real 0))"
definition assSF250 :: mid where
"assSF250 == (WTrue,l[=](Real 0))"
definition assSF251 :: mid where
"assSF251 == (WTrue,l[=](Real 0))"
definition assSF252 :: mid where
"assSF252 == (WTrue,l[=](Real 0))"
definition assSF253 :: mid where
"assSF253 == (WTrue,l[=](Real 0))"
definition assSF254 :: mid where
"assSF254 == (WTrue,l[=](Real 0))"
definition assSF255 :: mid where
"assSF255 == (WTrue,l[=](Real 0))"
definition assSF256 :: mid where
"assSF256 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF257 :: mid where
"assSF257 == (initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF258 :: mid where
"assSF258 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF259 :: mid where
"assSF259 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2 [=] Real 0) [&] (a[=](Real -1)) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF260 :: mid where
"assSF260 == ((initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF261 :: mid where
"assSF261 == ((initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF262 :: mid where
"assSF262 == (((initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0))[&](done1[=](Real 0)))[&](a[>=](Real -1) [&] (a[<=](Real 1))),l[=](Real 0))"
definition assSF263 :: mid where
"assSF263 == (initAssFC [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF264 :: mid where
"assSF264 == (initAssF [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2 [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF265 :: mid where
"assSF265 == (initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&](actl2 [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF266 :: mid where
"assSF266 == (mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2a [=] (Real 1)),l[=](Real 0))"
definition assSF267 :: mid where
"assSF267 == (WTrue,l[=](Real 0))"
definition assSF268 :: mid where
"assSF268 == (WTrue,l[=](Real 0))"
definition assSF269 :: mid where
"assSF269 == (WTrue,l[=](Real 0))"
definition assSF270 :: mid where
"assSF270 == (WTrue,l[=](Real 0))"
definition assSF271 :: mid where
"assSF271 == (WTrue,l[=](Real 0))"
definition assSF272 :: mid where
"assSF272 == (WTrue,l[=](Real 0))"
definition assSF273 :: mid where
"assSF273 == (WTrue,l[=](Real 0))"
definition assSF274 :: mid where
"assSF274 == (WTrue,l[=](Real 0))"
definition assSF275 :: mid where
"assSF275 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((done1 [=] Real 0) [&] (actl2 [=] (Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2 [=] (Real 0)),l[=](Real 0))"
definition assSF276 :: mid where
"assSF276 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2 [=] Real 0),l[=](Real 0))"
definition assSF277 :: mid where
"assSF277 == (mInitRM1 [&] tInitC [&] impFT [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1),l[=](Real 0))"
definition assSF278 :: mid where
"assSF278 == (mInitRM1 [&] tInit [&] impFT [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1),l[=](Real 0))"
definition assSF279 :: mid where
"assSF279 == (mInitRM1 [&] tInit [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (actl2 [=] (Real 0)) [&] (s [=] plant_s_1),l[=](Real 0))"
definition assSF280 :: mid where
"assSF280 == (WTrue,l[=](Real 0))"
definition assSF281 :: mid where
"assSF281 == (WTrue,l[=](Real 0))"
definition assSF282 :: mid where
"assSF282 == (WTrue,l[=](Real 0))"
definition assSF283 :: mid where
"assSF283 == (WTrue,l[=](Real 0))"
definition assSF284 :: mid where
"assSF284 == (WTrue,l[=](Real 0))"
definition assSF285 :: mid where
"assSF285 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0),l[=](Real 0))"
definition assSF286 :: mid where
"assSF286 == assSF208"
definition assSF287 :: mid where
"assSF287 == assSF208"
definition assSF288 :: mid where
"assSF288 == assSF208"
definition assSF289 :: mid where
"assSF289 == assSF208"
definition assSF290 :: mid where
"assSF290 == (mInit[&](impFT1[|]impFT2)[&](a[<=](Real 1))[&](a[>=](Real -1)),l[=](Real 0))"
definition assSF291 :: mid where
"assSF291 == (WTrue,l[=](Real 0))"
definition assSF292 :: mid where
"assSF292 == (mInit,l[=](Real 0))"
definition assSF293 :: mid where
"assSF293 == (mInit,l[=](Real 0))"
definition assSF294 :: mid where
"assSF294 == (mInit[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF295 :: mid where
"assSF295 == (WTrue,l[=](Real 0))"
definition assSF296 :: mid where
"assSF296 == (WTrue,l[=](Real 0))"
definition assSF297 :: mid where
"assSF297 == (WTrue,l[=](Real 0))"
definition assSF298 :: mid where
"assSF298 == assSF89"
definition assSF299 :: mid where
"assSF299 == assSF89"
definition assSF300 :: mid where
"assSF300 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2[=](Real 0)) [&] (actl2a[=](Real 1)) [&] (actl3[=](Real 0)),l[=](Real 0))"
definition assSF301 :: mid where
"assSF301 == (mInit,l[=](Real 0))"
definition assSF302 :: mid where
"assSF302 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT,l[=](Real 0))"
definition assSF303 :: mid where
"assSF303 == (mInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0),l[=](Real 0))"
definition assSF304 :: mid where
"assSF304 == assSF303"
definition assSF305 :: mid where
"assSF305 == assSF303"
definition assSF306 :: mid where
"assSF306 == assSF303"
definition assSF307 :: mid where
"assSF307 == assSF303"
definition assSF308 :: mid where
"assSF308 == (mInit[&](impFT1[|]impFT2)[&](a[<=](Real 1))[&](a[>=](Real -1)),l[=](Real 0))"
definition assSF309 :: mid where
"assSF309 == assSF308"
definition assSF310 :: mid where
"assSF310 == (mInit[&](a[<=](Real 1)) [&] (a[>=](Real -1)),l[=](Real 0))"
definition assSF311 :: mid where
"assSF311 == (mInit,l[=](Real 0))"
definition assSF312 :: mid where
"assSF312 == (mInit,l[=](Real 0.125))"
definition assSF313 :: mid where
"assSF313 == (mInit[&]s[=]plant_s_1,l[=](Real 0.125))"
definition assSF314 :: mid where
"assSF314 == (mInit[&]s[=]plant_s_1[&]v[=]plant_v_1[&]impFT,l[=](Real 0.125))"
definition assSF315 :: mid where
"assSF315 == (mInit[&](impFT1[|]impFT2)[&](a[<=](Real 1))[&](a[>=](Real -1)),WTrue)"
definition assSF316 :: mid where
"assSF316 == (mInit,WTrue)"
definition assSF317 :: mid where
"assSF317 == (WTrue,l[=](Real 0))"
definition assSF318 :: mid where
"assSF318 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] (done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&]vr1[<=]((Real 128000)[-](Real 2)[*]s)[+](Real 2)[*]T[*]T[&]fv[=](v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)[&](T[=](Real 1/8)),l[=](Real 0))"
definition assSF319 :: mid where
"assSF319 == (initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF320 :: mid where
"assSF320 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF321 :: mid where
"assSF321 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO [&] (actl2a [=] Real 0) [&] (a[=](Real -1)) [&] (T [=] (Real 1 / 8)),l[=](Real 0))"
definition assSF322 :: mid where
"assSF322 == ((initAssFC[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF323 :: mid where
"assSF323 == ((initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF324 :: mid where
"assSF324 == (((initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0))[&](done1[=](Real 0)))[&](a[>=](Real -1) [&] (a[<=](Real 1))),l[=](Real 0))"
definition assSF325 :: mid where
"assSF325 == (initAssFC [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF326 :: mid where
"assSF326 == (initAssF [&] ((plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000))) [&](actl2a [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF327 :: mid where
"assSF327 == (initAssF [&] (impFT1 [|] impFT2) [&] a [>=] (Real -1) [&] a [<=] (Real 1)[&](actl2a [=] Real 0) [&] (s [=] plant_s_1) [&] (v [=] plant_v_1),l[=](Real 0))"
definition assSF328 :: mid where
"assSF328 == ((mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2[=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2[=] (Real 0)) [&] (s [=] plant_s_1)),l[=](Real 0))"
definition assSF329 :: mid where
"assSF329 == (WTrue,l[=](Real 0))"
definition assSF330 :: mid where
"assSF330 == (WTrue,l[=](Real 0))"
definition assSF331 :: mid where
"assSF331 == (WTrue,l[=](Real 0))"
definition assSF332 :: mid where
"assSF332 == (WTrue,l[=](Real 0))"
definition assSF333 :: mid where
"assSF333 == (WTrue,l[=](Real 0))"
definition assSF334 :: mid where
"assSF334 == (WTrue,l[=](Real 0))"
definition assSF335 :: mid where
"assSF335 == (WTrue,l[=](Real 0))"
definition assSF336 :: mid where
"assSF336 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] (Real 0)),l[=](Real 0))"
definition assSF337 :: mid where
"assSF337 == (initAssF [&] (s [=] plant_s_1) [&] (v [=] plant_v_1) [&] impFTO [&] ((done1 [=] Real 0) [&] (actl2a [=] (Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](T[=](Real 1/8)) [&] (actl2a [=] (Real 0)),l[=](Real 0))"
definition assSF338 :: mid where
"assSF338 == (initAssF[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFTO[&]((plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 2)[*]T[*]T [+] (Real 2)[*]plant_s_1[<=](Real 128000))[|](done1[=](Real 1)[&]a[=](Real -1)))[&](done1[=](Real 0)[|]a[>=](Real -1) [&] (a[<=](Real 1)))[&](T[=](Real 1/8)) [&] (actl2a [=] Real 0),l[=](Real 0))"
definition assSF339 :: mid where
"assSF339 == (WTrue,l[=](Real 0))"
definition assSF340 :: mid where
"assSF340 == (WTrue,l[=](Real 0))"
definition assSF341 :: mid where
"assSF341 == (WTrue,l[=](Real 0))"
definition assSF342 :: mid where
"assSF342 == (WTrue,l[=](Real 0))"
definition assSF343 :: mid where
"assSF343 == (mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)),l[=](Real 0))"
definition assSF344 :: mid where
"assSF344 == (mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2a [=] (Real 1)),l[=](Real 0))"
definition assSF345 :: mid where
"assSF345 == assSF344"
definition assSF346 :: mid where
"assSF346 == assSF344"
definition assSF347 :: mid where
"assSF347 == assSF344"
definition assSF348 :: mid where
"assSF348 == ((mInitRM1 [&] tInit [&](s[=]plant_s_1)[&](v[=]plant_v_1) [&] impFT [&] (done1[=] (Real 0)) [&] (actl2[=] (Real 1))) [|] (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (done1 [=] (Real 1)) [&] (actl2[=] (Real 0))[&](s[=]plant_s_1)),l[=](Real 0))"
definition assSF349 :: mid where
"assSF349 == assSF348"
definition assSF350 :: mid where
"assSF350 == assSF348"
definition assSF351 :: mid where
"assSF351 == assSF348"
definition assSF352 :: mid where
"assSF352 == assSF348"
definition assSF353 :: mid where
"assSF353 == assSF152"
definition assSF354 :: mid where
"assSF354 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (e22[=](Real 64000)) [&] (i[=](Real 2)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] ((actl2[=](Real 0))[|](actl2a[=](Real 0))) [&] ((actl2[=](Real 1))[|](actl2a[=](Real 1))) [&] (actl3[=](Real 0)),l[=](Real 0))"
definition assSF355 :: mid where
"assSF355 == (tInit,l[=](Real 0))"
definition assSF356 :: mid where
"assSF356 == (mInitRM1 [&] tInit[&](s[=]plant_s_1)[&](v[=]plant_v_1)[&]impFT[&]done1[=](Real 0),l[=](Real 0))"
definition assSF357 :: mid where
"assSF357 == (mInitRM1 [&] tInitRM [&] (impFT1 [|] impFT2) [&] (a [>=] (Real -1)) [&] (a [<=] (Real 1)) [&] (s [=] plant_s_1),l[=](Real 0))"
definition assSF358 :: mid where
"assSF358 == (mInitRM1 [&] tInit[&](impFT1[|]impFT2)[&](a [<=] (Real 1)) [&] (a [>=] (Real -1)),l[=](Real 0))"
definition assSF359 :: mid where
"assSF359 == ((C_b [=] (Real -1)) [&] (C_A [=] (Real 1)) [&] (C_a [>=] (Real -1)) [&] (C_a [<=] (Real 1)) [&] (v331[=](Real 0)) [&] (e32[=](Real 64000)) [&] (x1[=](Real 32000)) [&] (x2[=](Real 64000)) [&] (actl2[=](Real 0)) [&] (actl3[=](Real 0))[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF360 :: mid where
"assSF360 == ((done4[=](Real 0)),l[=](Real 0))"
definition assSF361 :: mid where
"assSF361 == (WTrue,l[=](Real 0))"
definition assSF362 :: mid where
"assSF362 == ((done4[=](Real 0)),l[=](Real 0))"
definition assSF363 :: mid where
"assSF363 == (E4[=](String []),l[=](Real 0))"
definition assSF364 :: mid where
"assSF364 == (E4[=](String []),l[=](Real 0))"
definition assSF365 :: mid where
"assSF365 == assSF363"
definition assSF366 :: mid where
"assSF366 == (mInit[&](done1[=](Real 0)),l[=](Real 0))"
definition assSF367 :: mid where
"assSF367 == (WTrue,l[=](Real 0))"
definition assSF368 :: mid where
"assSF368 == ((done4[=](Real 0)),l[=](Real 0))"
definition assSF369 :: mid where
"assSF369 == (WTrue,l[=](Real 0))"
definition assSF370 :: mid where
"assSF370 == (WTrue,l[=](Real 0))"
definition assSF371 :: mid where
"assSF371 == (WTrue,l[=](Real 0))"
definition assSF372 :: mid where
"assSF372 == (WTrue,l[=](Real 0))"
definition assSF373 :: mid where
"assSF373 == (WTrue,l[=](Real 0))"
definition assSF374 :: mid where
"assSF374 == (WTrue,l[=](Real 0))"
definition assSF375 :: mid where
"assSF375 == (WTrue,l[=](Real 0))"
definition assSF376 :: mid where
"assSF376 == (WTrue,l[=](Real 0))"
definition assSF377 :: mid where
"assSF377 == (WTrue,l[=](Real 0))"
definition assSF378 :: mid where
"assSF378 == (WTrue,l[=](Real 0))"
definition assSF379 :: mid where
"assSF379 == (done4[=](Real 0),l[=](Real 0))"
definition assSF380 :: mid where
"assSF380 == (WTrue,l[=](Real 0))"
definition assSF381 :: mid where
"assSF381 == (WTrue,l[=](Real 0))"
definition assSF382 :: mid where
"assSF382 == (WTrue,l[=](Real 0))"
definition assSF383 :: mid where
"assSF383 == (WTrue,l[=](Real 0))"
definition assSF384 :: mid where
"assSF384 == (WTrue,l[=](Real 0))"
definition assSF385 :: mid where
"assSF385 == (WTrue,l[=](Real 0))"
definition assSF386 :: mid where
"assSF386 == (WTrue,l[=](Real 0))"
definition assSF387 :: mid where
"assSF387 == ((a[<=](Real 1)) [&] (a[>=](Real -1)),l[=](Real 0))"
definition assSF388 :: mid where
"assSF388 == (WTrue,l[=](Real 0))"
definition assSF389 :: mid where
"assSF389 == (WTrue,l[=](Real 0))"
definition assSF390 :: mid where
"assSF390 == (WTrue,l[=](Real 0))"
definition assSF391 :: mid where
"assSF391 == (WTrue,l[=](Real 0))"
definition assSF392 :: mid where
"assSF392 == (WTrue,l[=](Real 0))"
definition assSF393 :: mid where
"assSF393 == (WTrue,l[=](Real 0))"
definition assSF394 :: mid where
"assSF394 == (WTrue,l[=](Real 0))"
definition assSF395 :: mid where
"assSF395 == (WTrue,l[=](Real 0))"
definition assSF396 :: mid where
"assSF396 == (WTrue,l[=](Real 0))"
definition assSF397 :: mid where
"assSF397 == (WTrue,l[=](Real 0))"
definition assSF398 :: mid where
"assSF398 == (WTrue,l[=](Real 0))"
definition assSF399 :: mid where
"assSF399 == (WTrue,l[=](Real 0))"
definition assSF400 :: mid where
"assSF400 == ((done2[=](Real 0)),l[=](Real 0))"
definition assSF401 :: mid where
"assSF401 == (WTrue,l[=](Real 0))"
definition assSF402 :: mid where
"assSF402 == (done2[=](Real 0),l[=](Real 0))"
definition assSF403 :: mid where
"assSF403 == (WTrue,l[=](Real 0))"
definition assSF404 :: mid where
"assSF404 == (WTrue,l[=](Real 0))"
definition assSF405 :: mid where
"assSF405 == (WTrue,l[=](Real 0))"
end
