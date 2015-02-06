theory controlPDef
	imports "controlADef"
begin

(*Define the processes for fuctions.*)
definition min :: "exp => exp => exp" where"min(exp1, exp2) == (if formT(exp1[<]exp2) then exp1 else exp2)"
definition Fcontrol1 :: proc where
"Fcontrol1 == 
e31 := e32;assSF1;
e32 := e33;assSF2;
e33 := (e33 [+] (Real 32000));assSF3;
v311 := v321;assSF4;
v312 := v322"
definition Fcontrol2 :: proc where
"Fcontrol2 == 
v321 := v331;assSF5;
v322 := v332;assSF6;
v331 := (Real 255);assSF7;
v332 := (Real 250);assSF8;
mode31 := mode32"
definition Fcontrol3 :: proc where
"Fcontrol3 == 
mode32 := mode33;assSF9;
mode33 := (Real 0)"
definition FMA3 :: proc where
"FMA3 == Fcontrol1;assSF10;Fcontrol2;assSF11;Fcontrol3"
definition Fcontrol4 :: proc where
"Fcontrol4 == 
T := (Real 1/8);assSF12;
vr1 := ((v211 [+] (Real 2)[*]T) [*] (v211 [+] (Real 2)[*]T));assSF13;
vr1 := min(vr1, ((v221[*]v221[-](Real 2)[*]C_b[*]e21)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol5 :: proc where
"Fcontrol5 == 
vr1 := min(vr1, ((v231[*]v231[-](Real 2)[*]C_b[*]e22)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol6 :: proc where
"Fcontrol6 == 
vr1 := min(vr1, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e32) [+] (Real 2)[*]T[*]T))"
definition Fcontrol7 :: proc where
"Fcontrol7 == 
vr2 := ((v212 [+] (Real 2)[*]T) [*] (v212 [+] (Real 2)[*]T));assSF14;
vr2 := min(vr2, ((v222 [*]v222[-](Real 2)[*]C_b[*]e21)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol8 :: proc where
"Fcontrol8 == 
vr2 := min(vr2, ((v232 [*]v232[-](Real 2)[*]C_b[*]e22)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol9 :: proc where
"Fcontrol9 == 
vr2 := min(vr2, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e23) [+] (Real 2)[*]T[*]T))"
definition Fcontrol10 :: proc where
"Fcontrol10 == 
fv := (v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)"
definition FB2 :: proc where
"FB2 == Fcontrol4;assSF15;Fcontrol5;assSF16;Fcontrol6;assSF17;Fcontrol7;assSF18;Fcontrol8;assSF19;Fcontrol9;assSF20;Fcontrol10"
definition Fcontrol11 :: proc where
"Fcontrol11 == 
T := (Real 1/8);assSF21;
vr1 := ((v311 [+] (Real 2)[*]T) [*] (v311 [+] (Real 2)[*]T));assSF22;
vr1 := min(vr1, ((v321[*]v321[-](Real 2)[*]C_b[*]e31)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol12 :: proc where
"Fcontrol12 == 
vr1 := min(vr1, ((v331[*]v331[-](Real 2)[*]C_b[*]e32)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol13 :: proc where
"Fcontrol13 == 
vr1 := min(vr1, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e33) [+] (Real 2)[*]T[*]T))"
definition Fcontrol14 :: proc where
"Fcontrol14 == 
vr2 := ((v312 [+] (Real 2)[*]T) [*] (v312 [+] (Real 2)[*]T));assSF23;
vr2 := min(vr2, ((v322 [*]v322[-](Real 2)[*]C_b[*]e31)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol15 :: proc where
"Fcontrol15 == 
vr2 := min(vr2, ((v332 [*]v332[-](Real 2)[*]C_b[*]e32)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol16 :: proc where
"Fcontrol16 == 
vr2 := min(vr2, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e33) [+] (Real 2)[*]T[*]T))"
definition Fcontrol17 :: proc where
"Fcontrol17 == 
fv:=((v [+] (Real 2)[*]T)[*](v [+] (Real 2)[*]T))"
definition FB3 :: proc where
"FB3 == Fcontrol11;assSF24;Fcontrol12;assSF25;Fcontrol13;assSF26;Fcontrol14;assSF27;Fcontrol15;assSF28;Fcontrol16;assSF29;Fcontrol17"
definition Fcontrol18 :: proc where
"Fcontrol18 == 
e21 := e22;assSF30;
e22 := e23;assSF31;
e23 := (e23 [+] (Real 32000));assSF32;
v211 := v221;assSF33;
v212 := v222"
definition Fcontrol19 :: proc where
"Fcontrol19 == 
v221 := v231;assSF34;
v222 := v232;assSF35;
v231 := (Real 105);assSF36;
v232 := (Real 100);assSF37;
mode21 := mode22"
definition Fcontrol20 :: proc where
"Fcontrol20 == 
mode22 := mode23;assSF38;
mode23 := (Real 0)"
definition FMA2 :: proc where
"FMA2 == Fcontrol18;assSF39;Fcontrol19;assSF40;Fcontrol20"
definition Fcontrol21 :: proc where
"Fcontrol21 == 
T := (Real 1/8);assSF41;
vr1 := ((v211 [+] (Real 2)[*]T) [*] (v211 [+] (Real 2)[*]T));assSF42;
vr1 := min(vr1, (v311 [+] (Real 2)[*]T) [*] (v311 [+] (Real 2)[*]T))"
definition Fcontrol22 :: proc where
"Fcontrol22 == 
vr1 := min(vr1, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e33) [+] (Real 2)[*]T[*]T))"
definition Fcontrol23 :: proc where
"Fcontrol23 == 
vr1 := min(vr1, ((v331[*]v331[-](Real 2)[*]C_b[*]e32)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol24 :: proc where
"Fcontrol24 == 
vr2 := ((v212 [+] (Real 2)[*]T) [*] (v212 [+] (Real 2)[*]T));assSF43;
vr2 := min(vr2,(v312 [+] (Real 2)[*]T) [*] (v312 [+] (Real 2)[*]T))"
definition Fcontrol25 :: proc where
"Fcontrol25 == 
vr2 := min(vr2, ((v332 [*]v332[-](Real 2)[*]C_b[*]e32)[+](Real 2)[*]C_b[*]s [+] (Real 2)[*]T[*]T))"
definition Fcontrol26 :: proc where
"Fcontrol26 == 
vr2 := min(vr2, (((Real 2)[*]C_b[*]s[-](Real 2)[*]C_b[*]e33) [+] (Real 2)[*]T[*]T))"
definition Fcontrol27 :: proc where
"Fcontrol27 == 
fv := (v[*]v [+] (Real 1/2)[*]v [+] (Real 4)[*]T[*]T)"
definition FB22 :: proc where
"FB22 == Fcontrol21;assSF44;Fcontrol22;assSF45;Fcontrol23;assSF46;Fcontrol24;assSF47;Fcontrol25;assSF48;Fcontrol26;assSF49;Fcontrol27"
(*Define the process.*)
definition Pcontrol1 :: proc where
"Pcontrol1 == IF (num[=](Real 0)) (((<(WTrue) && (WTrue)>:(l[=](Real 0.125));assSF50;Ch_plant_s_1_1??s);assSF51;Ch_plant_v_1_1??v);assSF52;(num:=(Real 1);assSF53;empty(EL);assSF54;(addL EL E);assSF55;empty(NL);assSF56;(addL NL (Real 1))))"
definition Pcontrol2 :: proc where
"Pcontrol2 == IF (num[=](Real 1)) (BC_1!!E ;assSF57; ((BR_1??E;assSF58;(addL EL E);assSF59;(addL NL (Real 1));assSF60;num:=(Real 1)) [[ BO_1??vBO1);assSF61;num:=(num[+](Real 1));assSF62;delL(NL);assSF63;(addL NL num))"
definition Pcontrol3 :: proc where
"Pcontrol3 == IF (num[=](Real 2)) (BC_2!!E ;assSF64; ((BR_2??E;assSF65;(addL EL E);assSF66;(addL NL (Real 1));assSF67;num:=(Real 1)) [[ BO_2??vBO2);assSF68;num:=(num[+](Real 1));assSF69;delL(NL);assSF70;(addL NL num))"
definition Pcontrol4 :: proc where
"Pcontrol4 == IF (num[=](Real 3)) (BC_3!!E ;assSF71; ((BR_3??E;assSF72;(addL EL E);assSF73;(addL NL (Real 1));assSF74;num:=(Real 1)) [[ BO_3??vBO3);assSF75;num:=(num[+](Real 1));assSF76;delL(NL);assSF77;(addL NL num))"
definition Pcontrol5 :: proc where
"Pcontrol5 == IF (num[=](Real 4)) (BC_4!!E ;assSF78; ((BR_4??E;assSF79;(addL EL E);assSF80;(addL NL (Real 1));assSF81;num:=(Real 1)) [[ BO_4??vBO4);assSF82;num:=(num[+](Real 1));assSF83;delL(NL);assSF84;(addL NL num))"
definition Pcontrol6 :: proc where
"Pcontrol6 == IF (num[=](Real 5)) (delL(EL);assSF85;delL(NL);assSF86;IF isEmpty(EL) (num:=(Real 0);assSF87;E:=(String '''');assSF88;Ch_control_1_0!!a;assSF89;Ch_control_1_0!!a);assSF90;IF([~]isEmpty(EL)) (E:=readL(EL);assSF91;num:=readL(NL)))"
definition Pcontrol7 :: proc where
"Pcontrol7 == ((num:=(Real 0);assSF92;E:=(String '''');assSF93;(a:=(Real 0)));assSF94;Ch_control_1_0!!a);assSF95;(Pcontrol1;assSF96;Pcontrol2;assSF97;Pcontrol3;assSF98;Pcontrol4;assSF99;Pcontrol5;assSF100;Pcontrol6)*"
definition Pcontrol8 :: proc where
"Pcontrol8 == IF ((done2[=](Real 0))[&]E2[=](String ''LUA'')) (actRBC:=(Real 0);assSF101;actRBC:=(Real 1);assSF102;BR_2!!(String ''LU'');assSF103;done2:=(Real 1))"
definition Pcontrol9 :: proc where
"Pcontrol9 == 
IF ((done2[=](Real 0))[&]E2[=](String ''MAA3'')) (actRBC:=(Real 0);assSF104;actRBC:=(Real 1);assSF105;BR_2!!(String ''MAA3c'');assSF106;done2:=(Real 1))"
definition Pcontrol10 :: proc where
"Pcontrol10 == done2:=(Real 0)"
definition Pcontrol11 :: proc where
"Pcontrol11 == Pcontrol10;assSF107;(BC_2??E2;assSF108;(Pcontrol8;assSF109;Pcontrol9;assSF110;done2:=(Real 0));assSF111;BO_2!!(String ''''))*"
definition Pcontrol12 :: proc where
"Pcontrol12 == IF ((done3[=](Real 0))[&]E3[=](String ''MAA2'')) (actTCC:=(Real 0);assSF112;actTCC:=(Real 1);assSF113;BR_3!!(String ''MAA2c'');assSF114;done3:=(Real 1))"
definition Pcontrol13 :: proc where
"Pcontrol13 == done3:=(Real 0)"
definition Pcontrol14 :: proc where
"Pcontrol14 == Pcontrol13;assSF115;(BC_3??E3;assSF116;(Pcontrol12;assSF117;done3:=(Real 0));assSF118;BO_3!!(String ''''))*"
definition Pcontrol15 :: proc where
"Pcontrol15 == (C_b:=(Real -1));assSF119;(C_A:=(Real 1));assSF120;(C_a:=(Real -0.2));assSF121;(v332:=(Real 0));assSF122;(v331:=(Real 0));assSF123;(v322:=(Real 250));assSF124;(v321:=(Real 255));assSF125;
(v312:=(Real 250));assSF126;(v311:=(Real 255))"
definition Pcontrol16 :: proc where
"Pcontrol16 == (v232:=(Real 40));assSF127;(v231:=(Real 45));assSF128;(v222:=(Real 100));assSF129;(v221:=(Real 105));assSF130;
(v212:=(Real 100));assSF131;(v211:=(Real 105));assSF132;(e33:=(Real 96000));assSF133;(e32:=(Real 64000))"
definition Pcontrol17 :: proc where
"Pcontrol17 == (e31:=(Real 32000));assSF134;(e23:=(Real 96000));assSF135;
(e22:=(Real 64000));assSF136;(e21:=(Real 32000));assSF137;(mode33:=(Real 1));assSF138;(mode32:=(Real 0));assSF139;(mode31:=(Real 0));assSF140;(mode23:=(Real 1))"
definition Pcontrol18 :: proc where
"Pcontrol18 == 
(mode22:=(Real 0));assSF141;(mode21:=(Real 0));assSF142;(mode3:=(Real 0));assSF143;(mode2:=(Real 0));assSF144;(i:=(Real 2));assSF145;(x2:=(Real 64000));assSF146;(x1:=(Real 32000));assSF147;(actl3:=(Real 0));assSF148;(actl2a:=(Real 0))"
definition Pcontrol19 :: proc where
"Pcontrol19 == (actl2:=(Real 0))"
definition Pcontrol20 :: proc where
"Pcontrol20 == Pcontrol15;assSF149;Pcontrol16;assSF150;Pcontrol17;assSF151;Pcontrol18;assSF152;Pcontrol19"
definition Pcontrol21 :: proc where
"Pcontrol21 == (actl2:=(Real 1))"
definition Pcontrol22 :: proc where
"Pcontrol22 == v321:=(Real 45);assSF153;v322:=(Real 40);assSF154;FB3;assSF155;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl3:=(Real 0);assSF156;actl3:=(Real 1);assSF157;a:=C_b;assSF158;done1:=(Real 1))"
definition Pcontrol23 :: proc where
"Pcontrol23 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl3:=(Real 0);assSF159;actl3:=(Real 1);assSF160;a:=C_a;assSF161;done1:=(Real 1))"
definition Pcontrol24 :: proc where
"Pcontrol24 == 
IF ((done1[=](Real 0))) (actl3:=(Real 0);assSF162;actl3:=(Real 1);assSF163;a:=C_A;assSF164;done1:=(Real 1))"
definition Pcontrol25 :: proc where
"Pcontrol25 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl3:=(Real 0);assSF165;actl3:=(Real 1);assSF166;a:=C_b;assSF167;done1:=(Real 1))"
definition Pcontrol26 :: proc where
"Pcontrol26 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl3:=(Real 0);assSF168;actl3:=(Real 1);assSF169;a:=C_a;assSF170;done1:=(Real 1))"
definition Pcontrol27 :: proc where
"Pcontrol27 == 
IF ((done1[=](Real 0))) (actl3:=(Real 0);assSF171;actl3:=(Real 1);assSF172;a:=C_A;assSF173;done1:=(Real 1))"
definition Pcontrol28 :: proc where
"Pcontrol28 == FMA3;assSF174;FB3;assSF175;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl3:=(Real 0);assSF176;actl3:=(Real 1);assSF177;a:=C_b;assSF178;done1:=(Real 1))"
definition Pcontrol29 :: proc where
"Pcontrol29 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl3:=(Real 0);assSF179;actl3:=(Real 1);assSF180;a:=C_a;assSF181;done1:=(Real 1))"
definition Pcontrol30 :: proc where
"Pcontrol30 == 
IF ((done1[=](Real 0))) (actl3:=(Real 0);assSF182;actl3:=(Real 1);assSF183;a:=C_A;assSF184;done1:=(Real 1))"
definition Pcontrol31 :: proc where
"Pcontrol31 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl3:=(Real 0);assSF185;actl3:=(Real 1);assSF186;a:=C_b;assSF187;done1:=(Real 1))"
definition Pcontrol32 :: proc where
"Pcontrol32 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl3:=(Real 0);assSF188;actl3:=(Real 1);assSF189;a:=C_a;assSF190;done1:=(Real 1))"
definition Pcontrol33 :: proc where
"Pcontrol33 == 
IF ((done1[=](Real 0))) (actl3:=(Real 0);assSF191;actl3:=(Real 1);assSF192;a:=C_A;assSF193;done1:=(Real 1))"
definition Pcontrol34 :: proc where
"Pcontrol34 == FB3;assSF194;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl3:=(Real 0);assSF195;actl3:=(Real 1);assSF196;a:=C_b;assSF197;done1:=(Real 1))"
definition Pcontrol35 :: proc where
"Pcontrol35 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl3:=(Real 0);assSF198;actl3:=(Real 1);assSF199;a:=C_a;assSF200;done1:=(Real 1))"
definition Pcontrol36 :: proc where
"Pcontrol36 == 
IF ((done1[=](Real 0))) (actl3:=(Real 0);assSF201;actl3:=(Real 1);assSF202;a:=C_A;assSF203;done1:=(Real 1))"
definition Pcontrol37 :: proc where
"Pcontrol37 == IF ((done1[=](Real 0))[&]E1[=](String ''CONF'')) (Pcontrol22;assSF204;Pcontrol23;assSF205;Pcontrol24)"
definition Pcontrol38 :: proc where
"Pcontrol38 == 
IF ((done1[=](Real 0))[&]mode32[=](Real 1) [&] v321[=](Real 0)) (Pcontrol25;assSF206;Pcontrol26;assSF207;Pcontrol27)"
definition Pcontrol39 :: proc where
"Pcontrol39 == 
IF ((done1[=](Real 0))[&]E1[=](String ''MAA3c'')) (Pcontrol28;assSF208;Pcontrol29;assSF209;Pcontrol30)"
definition Pcontrol40 :: proc where
"Pcontrol40 == 
IF ((done1[=](Real 0))[&]s[>]e32) (Pcontrol31;assSF210;Pcontrol32;assSF211;Pcontrol33)"
definition Pcontrol41 :: proc where
"Pcontrol41 == 
IF ((done1[=](Real 0))) (Pcontrol34;assSF212;Pcontrol35;assSF213;Pcontrol36)"
definition Pcontrol42 :: proc where
"Pcontrol42 == IF ((done1[=](Real 0))[&]s[>]x2) (actl2a:=(Real 0);assSF214;actl3:=(Real 1);assSF215;done1:=(Real 1))"
definition Pcontrol43 :: proc where
"Pcontrol43 == FMA3;assSF216;FB22;assSF217;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2a:=(Real 0);assSF218;actl2a:=(Real 1);assSF219;a:=C_b;assSF220;done1:=(Real 1))"
definition Pcontrol44 :: proc where
"Pcontrol44 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2a:=(Real 0);assSF221;actl2a:=(Real 1);assSF222;a:=C_a;assSF223;done1:=(Real 1))"
definition Pcontrol45 :: proc where
"Pcontrol45 == 
IF ((done1[=](Real 0))) (actl2a:=(Real 0);assSF224;actl2a:=(Real 1);assSF225;a:=C_A;assSF226;done1:=(Real 1))"
definition Pcontrol46 :: proc where
"Pcontrol46 == FMA2;assSF227;FB22;assSF228;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2a:=(Real 0);assSF229;actl2a:=(Real 1);assSF230;a:=C_b;assSF231;done1:=(Real 1))"
definition Pcontrol47 :: proc where
"Pcontrol47 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2a:=(Real 0);assSF232;actl2a:=(Real 1);assSF233;a:=C_a;assSF234;done1:=(Real 1))"
definition Pcontrol48 :: proc where
"Pcontrol48 == 
IF ((done1[=](Real 0))) (actl2a:=(Real 0);assSF235;actl2a:=(Real 1);assSF236;a:=C_A;assSF237;done1:=(Real 1))"
definition Pcontrol49 :: proc where
"Pcontrol49 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2a:=(Real 0);assSF238;actl2a:=(Real 1);assSF239;a:=C_b;assSF240;done1:=(Real 1))"
definition Pcontrol50 :: proc where
"Pcontrol50 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2a:=(Real 0);assSF241;actl2a:=(Real 1);assSF242;a:=C_a;assSF243;done1:=(Real 1))"
definition Pcontrol51 :: proc where
"Pcontrol51 == 
IF ((done1[=](Real 0))) (actl2a:=(Real 0);assSF244;actl2a:=(Real 1);assSF245;a:=C_A;assSF246;done1:=(Real 1))"
definition Pcontrol52 :: proc where
"Pcontrol52 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2a:=(Real 0);assSF247;actl2a:=(Real 1);assSF248;a:=C_b;assSF249;done1:=(Real 1))"
definition Pcontrol53 :: proc where
"Pcontrol53 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2a:=(Real 0);assSF250;actl2a:=(Real 1);assSF251;a:=C_a;assSF252;done1:=(Real 1))"
definition Pcontrol54 :: proc where
"Pcontrol54 == 
IF ((done1[=](Real 0))) (actl2a:=(Real 0);assSF253;actl2a:=(Real 1);assSF254;a:=C_A;assSF255;done1:=(Real 1))"
definition Pcontrol55 :: proc where
"Pcontrol55 == FB22;assSF256;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2a:=(Real 0);assSF257;actl2a:=(Real 1);assSF258;a:=C_b;assSF259;done1:=(Real 1))"
definition Pcontrol56 :: proc where
"Pcontrol56 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2a:=(Real 0);assSF260;actl2a:=(Real 1);assSF261;a:=C_a;assSF262;done1:=(Real 1))"
definition Pcontrol57 :: proc where
"Pcontrol57 == 
IF ((done1[=](Real 0))) (actl2a:=(Real 0);assSF263;actl2a:=(Real 1);assSF264;a:=C_A;assSF265;done1:=(Real 1))"
definition Pcontrol58 :: proc where
"Pcontrol58 == Pcontrol42;assSF266;
IF ((done1[=](Real 0))[&]E1[=](String ''MAA3c'')) (Pcontrol43;assSF267;Pcontrol44;assSF268;Pcontrol45)"
definition Pcontrol59 :: proc where
"Pcontrol59 == 
IF ((done1[=](Real 0))[&]E1[=](String ''MAA2c'')) (Pcontrol46;assSF269;Pcontrol47;assSF270;Pcontrol48)"
definition Pcontrol60 :: proc where
"Pcontrol60 == 
IF ((done1[=](Real 0))[&]s[>]e22) (Pcontrol49;assSF271;Pcontrol50;assSF272;Pcontrol51)"
definition Pcontrol61 :: proc where
"Pcontrol61 == 
IF ((done1[=](Real 0))[&]s[>]e32) (Pcontrol52;assSF273;Pcontrol53;assSF274;Pcontrol54)"
definition Pcontrol62 :: proc where
"Pcontrol62 == 
IF ((done1[=](Real 0))) (Pcontrol55;assSF275;Pcontrol56;assSF276;Pcontrol57)"
definition Pcontrol63 :: proc where
"Pcontrol63 == IF ((done1[=](Real 0))[&]i[=](Real 2) [&] s[>=]x1) (actl2:=(Real 0);assSF277;actl2a:=(Real 1);assSF278;a:=C_b;assSF279;done1:=(Real 1))"
definition Pcontrol64 :: proc where
"Pcontrol64 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2:=(Real 0);assSF280;actl2:=(Real 1);assSF281;a:=C_b;assSF282;done1:=(Real 1))"
definition Pcontrol65 :: proc where
"Pcontrol65 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2:=(Real 0);assSF283;actl2:=(Real 1);assSF284;a:=C_a;assSF285;done1:=(Real 1))"
definition Pcontrol66 :: proc where
"Pcontrol66 == 
IF ((done1[=](Real 0))) (actl2:=(Real 0);assSF286;actl2:=(Real 1);assSF287;a:=C_A;assSF288;done1:=(Real 1))"
definition Pcontrol67 :: proc where
"Pcontrol67 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2:=(Real 0);assSF289;actl2:=(Real 1);assSF290;a:=C_b;assSF291;done1:=(Real 1))"
definition Pcontrol68 :: proc where
"Pcontrol68 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2:=(Real 0);assSF292;actl2:=(Real 1);assSF293;a:=C_a;assSF294;done1:=(Real 1))"
definition Pcontrol69 :: proc where
"Pcontrol69 == 
IF ((done1[=](Real 0))) (actl2:=(Real 0);assSF295;actl2:=(Real 1);assSF296;a:=C_A;assSF297;done1:=(Real 1))"
definition Pcontrol70 :: proc where
"Pcontrol70 == FMA2;assSF298;FB2;assSF299;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2:=(Real 0);assSF300;actl2:=(Real 1);assSF301;a:=C_b;assSF302;done1:=(Real 1))"
definition Pcontrol71 :: proc where
"Pcontrol71 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2:=(Real 0);assSF303;actl2:=(Real 1);assSF304;a:=C_a;assSF305;done1:=(Real 1))"
definition Pcontrol72 :: proc where
"Pcontrol72 == 
IF ((done1[=](Real 0))) (actl2:=(Real 0);assSF306;actl2:=(Real 1);assSF307;a:=C_A;assSF308;done1:=(Real 1))"
definition Pcontrol73 :: proc where
"Pcontrol73 == IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2:=(Real 0);assSF309;actl2:=(Real 1);assSF310;a:=C_b;assSF311;done1:=(Real 1))"
definition Pcontrol74 :: proc where
"Pcontrol74 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2:=(Real 0);assSF312;actl2:=(Real 1);assSF313;a:=C_a;assSF314;done1:=(Real 1))"
definition Pcontrol75 :: proc where
"Pcontrol75 == 
IF ((done1[=](Real 0))) (actl2:=(Real 0);assSF315;actl2:=(Real 1);assSF316;a:=C_A;assSF317;done1:=(Real 1))"
definition Pcontrol76 :: proc where
"Pcontrol76 == FB2;assSF318;IF ((done1[=](Real 0))[&]fv[>=]vr1) (actl2:=(Real 0);assSF319;actl2:=(Real 1);assSF320;a:=C_b;assSF321;done1:=(Real 1))"
definition Pcontrol77 :: proc where
"Pcontrol77 == 
IF ((done1[=](Real 0))[&]fv[>=]vr2) (actl2:=(Real 0);assSF322;actl2:=(Real 1);assSF323;a:=C_a;assSF324;done1:=(Real 1))"
definition Pcontrol78 :: proc where
"Pcontrol78 == 
IF ((done1[=](Real 0))) (actl2:=(Real 0);assSF325;actl2:=(Real 1);assSF326;a:=C_A;assSF327;done1:=(Real 1))"
definition Pcontrol79 :: proc where
"Pcontrol79 == Pcontrol63;assSF328;
IF ((done1[=](Real 0))[&]E1[=](String ''LU'')) (Pcontrol64;assSF329;Pcontrol65;assSF330;Pcontrol66)"
definition Pcontrol80 :: proc where
"Pcontrol80 == 
IF ((done1[=](Real 0))[&]i[=](Real 0) [&] s[>](Real 200)) (Pcontrol67;assSF331;Pcontrol68;assSF332;Pcontrol69)"
definition Pcontrol81 :: proc where
"Pcontrol81 == 
IF ((done1[=](Real 0))[&]E1[=](String ''MAA2c'')) (Pcontrol70;assSF333;Pcontrol71;assSF334;Pcontrol72)"
definition Pcontrol82 :: proc where
"Pcontrol82 == 
IF ((done1[=](Real 0))[&]s[>]e22) (Pcontrol73;assSF335;Pcontrol74;assSF336;Pcontrol75)"
definition Pcontrol83 :: proc where
"Pcontrol83 == 
IF ((done1[=](Real 0))) (Pcontrol76;assSF337;Pcontrol77;assSF338;Pcontrol78)"
definition Pcontrol84 :: proc where
"Pcontrol84 == IF (done1[=](Real 0)) (IF (actl3[=](Real 1)) (Pcontrol37;assSF339;Pcontrol38;assSF340;Pcontrol39;assSF341;Pcontrol40;assSF342;Pcontrol41);assSF343;
IF (actl2a[=](Real 1)) (Pcontrol58;assSF344;Pcontrol59;assSF345;Pcontrol60;assSF346;Pcontrol61;assSF347;Pcontrol62);assSF348;
IF (actl2[=](Real 1)) (Pcontrol79;assSF349;Pcontrol80;assSF350;Pcontrol81;assSF351;Pcontrol82;assSF352;Pcontrol83))"
definition Pcontrol85 :: proc where
"Pcontrol85 == Pcontrol20;assSF353;Pcontrol21;assSF354;done1:=(Real 0)"
definition Pcontrol86 :: proc where
"Pcontrol86 == Pcontrol85;assSF355;(BC_1??E1;assSF356;(Pcontrol84;assSF357;done1:=(Real 0));assSF358;BO_1!!(String ''''))*"
definition Pcontrol87 :: proc where
"Pcontrol87 == IF ((done4[=](Real 0))[&]E4[=](String ''CONFR'')) (actDriver:=(Real 0);assSF359;actDriver:=(Real 1);assSF360;BR_4!!(String ''CONF'');assSF361;done4:=(Real 1))"
definition Pcontrol88 :: proc where
"Pcontrol88 == done4:=(Real 0)"
definition Pcontrol89 :: proc where
"Pcontrol89 == Pcontrol88;assSF362;(BC_4??E4;assSF363;(Pcontrol87;assSF364;done4:=(Real 0));assSF365;BO_4!!(String ''''))*"
definition Pcontrol :: proc where
"Pcontrol == Pcontrol7||Pcontrol11||Pcontrol14||Pcontrol86||Pcontrol89"
end
