theory processDef
	imports "controlPDef"
begin

(*Define continuous processes*)
definition PC1_1 :: proc where
"PC1_1 == plant_v_1:=(Real 0);assertion1;
 plant_s_1:=(Real 0)
"
definition commI1 :: proc where
"commI1 == Ch_plant_v_1_1!!plant_v_1 [[ Ch_plant_s_1_1!!plant_s_1 [[ Ch_control_1_0??control_1_0"
definition PC1_2 :: proc where
"PC1_2 == (<WTrue && WTrue>:WTrue) [[> (commI1)"
definition domain1 :: fform where
"domain1 ==  (plant_and_1[=](Bool False))"
definition PC1_3 :: proc where
"PC1_3 == (<inv1 && domain1>:rg1)
	[[>commI1"
definition domain2 :: fform where
"domain2 ==  (plant_and_1[=](Bool True))"
definition PC1_4 :: proc where
"PC1_4 == (<inv2 && domain2>:rg2)
	[[>commI1"
definition PC1_init :: proc where
"PC1_init == PC1_1;assertion2;PC1_2"
definition PC1_rep :: proc where
"PC1_rep == PC1_3;assertion3;PC1_4"
definition PC1 :: proc where
"PC1 == PC1_init;assertion4;(PC1_rep)*"

(*Define discrete processes*)
(*Define the whole process.*)
definition P :: proc where
"P == PC1||Pcontrol"
end
