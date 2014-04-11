theory varDef
	imports "/home/liang/workspace/s2h/HHLProver/HHL"
begin

(*Define channel names.*)
definition Ch_plant_v_1_1 :: cname where
"Ch_plant_v_1_1 == ''Ch_plant_v_1_1''"
definition Ch_control_1_0 :: cname where
"Ch_control_1_0 == ''Ch_control_1_0''"
definition Ch_plant_s_1_1 :: cname where
"Ch_plant_s_1_1 == ''Ch_plant_s_1_1''"

(*Define receiving variables.*)
definition plant_v_1_1 :: exp where
"plant_v_1_1 == RVar ''plant_v_1_1''"
definition control_1_0 :: exp where
"control_1_0 == RVar ''control_1_0''"
definition plant_s_1_1 :: exp where
"plant_s_1_1 == RVar ''plant_s_1_1''"

(*Define local and sending variables.*)
definition t1 :: exp where
"t1 == RVar ''t1''"
definition temp1 :: exp where
"temp1 == RVar ''temp1''"
definition plant_v_1 :: exp where
"plant_v_1 == RVar ''plant_v_1''"
definition plant_Switch_1 :: exp where
"plant_Switch_1 == RVar ''plant_Switch_1''"
definition plant_co1_1 :: exp where
"plant_co1_1 == RVar ''plant_co1_1''"
definition control_1 :: exp where
"control_1 == RVar ''control_1''"
definition plant_co2_1 :: exp where
"plant_co2_1 == RVar ''plant_co2_1''"
definition plant_and_1 :: exp where
"plant_and_1 == RVar ''plant_and_1''"
definition plant_mul_1 :: exp where
"plant_mul_1 == RVar ''plant_mul_1''"
definition plant_s_1 :: exp where
"plant_s_1 == RVar ''plant_s_1''"

(*Definitions in comments, including extra functions defined by user or used during translation.*)
definition max :: "exp => exp => exp"
where "max(a,b) == if formT(a[<]b) then b else a"
end
