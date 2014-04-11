theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts diff :: "exp => exp" 
definition impF :: fform where
"impF == (plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000))"
definition impF1 :: fform where
"impF1 == (plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000)) [&] (control_1_0[=](Real -1))"
definition impF2 :: fform where
"impF2 == (plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 1/2)[*]plant_v_1 [+] (Real 1/32) [+] (Real 2)[*]plant_s_1[<=](Real 128000)) [&] (control_1_0[>=](Real -1) [&] (control_1_0[<=](Real 1)))"
definition aVal :: fform where
"aVal == (control_1_0 [>=] (Real -1)) [&] (control_1_0 [<=] (Real 1)) "

definition assertion1 :: mid where
"assertion1 == (plant_v_1 [=] (Real 0),l[=](Real 0))"
definition assertion2 :: mid where
"assertion2 == ((plant_v_1 [=] (Real 0)) [&] (plant_s_1 [=] (Real 0)),l[=](Real 0))"
definition assertion3 :: mid where
"assertion3 == (impF,WTrue)"
definition assertion4 :: mid where
"assertion4 == ((impF1 [|] impF2) [&] aVal,l[=](Real 0))"

definition rg1 :: fform where
"rg1 == WTrue"
definition rg2 :: fform where
"rg2 == WTrue"

definition inv1 :: fform where 
"inv1 == (plant_v_1[>=](Real 0))[&](plant_v_1[*]plant_v_1 [+] (Real 2)[*]plant_s_1[<=](Real 128000))"
definition inv2 :: fform where
"inv2 == inv1"

end
