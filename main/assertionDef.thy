theory assertionDef
	imports "varDef"
begin

(*Define consts for processes definition.*)
consts diff :: "exp => exp" 

definition assertion1 :: mid where
"assertion1 == (WTrue,l[=](Real 0))"
definition assertion2 :: mid where
"assertion2 == (WTrue,l[=](Real 0))"
definition assertion3 :: mid where
"assertion3 == (WTrue,l[=](Real 0))"
definition assertion4 :: mid where
"assertion4 == (WTrue,l[=](Real 0))"

definition rg1 :: fform where
"rg1 == (l[=](Real 0))"
definition rg2 :: fform where
"rg2 == (l[=](Real 0))"

definition inv1 :: fform where
"inv1 == WTrue"
definition inv2 :: fform where
"inv2 == WTrue"

end
