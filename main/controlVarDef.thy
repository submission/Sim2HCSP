theory controlVarDef
	imports "assertionDef"
begin

(*Define channel names.*)
definition BC_1 :: cname where
"BC_1 == ''BC_1''"
definition BR_1 :: cname where
"BR_1 == ''BR_1''"
definition BO_1 :: cname where
"BO_1 == ''BO_1''"
definition VO1 :: cname where
"VO1 == ''VO1''"
definition VI1 :: cname where
"VI1 == ''VI1''"
definition vBO1 :: exp where
"vBO1 == SVar ''vBO1''"
definition BC_2 :: cname where
"BC_2 == ''BC_2''"
definition BR_2 :: cname where
"BR_2 == ''BR_2''"
definition BO_2 :: cname where
"BO_2 == ''BO_2''"
definition VO2 :: cname where
"VO2 == ''VO2''"
definition VI2 :: cname where
"VI2 == ''VI2''"
definition vBO2 :: exp where
"vBO2 == SVar ''vBO2''"
definition BC_3 :: cname where
"BC_3 == ''BC_3''"
definition BR_3 :: cname where
"BR_3 == ''BR_3''"
definition BO_3 :: cname where
"BO_3 == ''BO_3''"
definition VO3 :: cname where
"VO3 == ''VO3''"
definition VI3 :: cname where
"VI3 == ''VI3''"
definition vBO3 :: exp where
"vBO3 == SVar ''vBO3''"
definition BC_4 :: cname where
"BC_4 == ''BC_4''"
definition BR_4 :: cname where
"BR_4 == ''BR_4''"
definition BO_4 :: cname where
"BO_4 == ''BO_4''"
definition VO4 :: cname where
"VO4 == ''VO4''"
definition VI4 :: cname where
"VI4 == ''VI4''"
definition vBO4 :: exp where
"vBO4 == SVar ''vBO4''"
definition Ch_control_1 :: cname where
"Ch_control_1 == ''Ch_control_1''"

(*Define event variables assistent.*)
consts eL :: "exp list"
consts nL :: "exp list"
(*Define event variables.*)
definition E1 :: exp where
"E1 == SVar ''E1''"
definition done1 :: exp where
"done1 == RVar ''done1''"
definition E2 :: exp where
"E2 == SVar ''E2''"
definition done2 :: exp where
"done2 == RVar ''done2''"
definition E3 :: exp where
"E3 == SVar ''E3''"
definition done3 :: exp where
"done3 == RVar ''done3''"
definition E4 :: exp where
"E4 == SVar ''E4''"
definition done4 :: exp where
"done4 == RVar ''done4''"
definition E :: exp where
"E == SVar ''E''"
definition num :: exp where
"num == RVar ''num''"
definition EL :: exp where
"EL == List eL"
definition NL :: exp where
"NL == List nL"
(*Define local and sending variables.*)
definition sfTemp1 :: exp where
"sfTemp1 == RVar ''sfTemp1''"
definition s :: exp where
"s == RVar ''s''"
definition v :: exp where
"v == RVar ''v''"
definition a :: exp where
"a == RVar ''a''"
definition CONFR :: exp where
"CONFR == RVar ''CONFR''"
definition MAA2 :: exp where
"MAA2 == RVar ''MAA2''"
definition MAA2c :: exp where
"MAA2c == RVar ''MAA2c''"
definition MAA3 :: exp where
"MAA3 == RVar ''MAA3''"
definition MAA3c :: exp where
"MAA3c == RVar ''MAA3c''"
definition LU :: exp where
"LU == RVar ''LU''"
definition LUA :: exp where
"LUA == RVar ''LUA''"
definition CONF :: exp where
"CONF == RVar ''CONF''"
definition C_b :: exp where
"C_b == RVar ''C_b''"
definition C_A :: exp where
"C_A == RVar ''C_A''"
definition C_a :: exp where
"C_a == RVar ''C_a''"
definition vr2 :: exp where
"vr2 == RVar ''vr2''"
definition vr1 :: exp where
"vr1 == RVar ''vr1''"
definition v332 :: exp where
"v332 == RVar ''v332''"
definition v331 :: exp where
"v331 == RVar ''v331''"
definition v322 :: exp where
"v322 == RVar ''v322''"
definition v321 :: exp where
"v321 == RVar ''v321''"
definition v312 :: exp where
"v312 == RVar ''v312''"
definition v311 :: exp where
"v311 == RVar ''v311''"
definition v232 :: exp where
"v232 == RVar ''v232''"
definition v231 :: exp where
"v231 == RVar ''v231''"
definition v222 :: exp where
"v222 == RVar ''v222''"
definition v221 :: exp where
"v221 == RVar ''v221''"
definition v212 :: exp where
"v212 == RVar ''v212''"
definition v211 :: exp where
"v211 == RVar ''v211''"
definition e33 :: exp where
"e33 == RVar ''e33''"
definition e32 :: exp where
"e32 == RVar ''e32''"
definition e31 :: exp where
"e31 == RVar ''e31''"
definition e23 :: exp where
"e23 == RVar ''e23''"
definition e22 :: exp where
"e22 == RVar ''e22''"
definition e21 :: exp where
"e21 == RVar ''e21''"
definition mode33 :: exp where
"mode33 == RVar ''mode33''"
definition mode32 :: exp where
"mode32 == RVar ''mode32''"
definition mode31 :: exp where
"mode31 == RVar ''mode31''"
definition mode23 :: exp where
"mode23 == RVar ''mode23''"
definition mode22 :: exp where
"mode22 == RVar ''mode22''"
definition mode21 :: exp where
"mode21 == RVar ''mode21''"
definition mode3 :: exp where
"mode3 == RVar ''mode3''"
definition mode2 :: exp where
"mode2 == RVar ''mode2''"
definition i :: exp where
"i == RVar ''i''"
definition fv :: exp where
"fv == RVar ''fv''"
definition x2 :: exp where
"x2 == RVar ''x2''"
definition x1 :: exp where
"x1 == RVar ''x1''"
definition T :: exp where
"T == RVar ''T''"
definition actl3 :: exp where
"actl3 == RVar ''actl3''"
definition actRBC :: exp where
"actRBC == RVar ''actRBC''"
definition actl2a :: exp where
"actl2a == RVar ''actl2a''"
definition actTCC :: exp where
"actTCC == RVar ''actTCC''"
definition actTrain :: exp where
"actTrain == RVar ''actTrain''"
definition actl2 :: exp where
"actl2 == RVar ''actl2''"
definition actDriver :: exp where
"actDriver == RVar ''actDriver''"
(*Define input variables.*)
definition s1 :: exp where
"s1 == RVar ''s1''"
definition s2 :: exp where
"s2 == RVar ''s2''"
definition s3 :: exp where
"s3 == RVar ''s3''"
definition s4 :: exp where
"s4 == RVar ''s4''"
definition v1 :: exp where
"v1 == RVar ''v1''"
definition v2 :: exp where
"v2 == RVar ''v2''"
definition v3 :: exp where
"v3 == RVar ''v3''"
definition v4 :: exp where
"v4 == RVar ''v4''"
(*Define output variables.*)
definition a1 :: exp where
"a1 == RVar ''a1''"
definition a2 :: exp where
"a2 == RVar ''a2''"
definition a3 :: exp where
"a3 == RVar ''a3''"
definition a4 :: exp where
"a4 == RVar ''a4''"
(*Define local variables.*)

end
