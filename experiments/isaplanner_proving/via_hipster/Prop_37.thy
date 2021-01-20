theory Prop_37
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpec) = x xtwoSpec ytwoSpec"

fun elem :: "NatSpecial => NatSpecial ListSpecial => bool" where
"elem y (niltwoSpec) = False"
| "elem y (constwoSpec ztwoSpec xs) = (if x y ztwoSpec then True else elem y xs)"

fun delete :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"delete y (niltwoSpec) = niltwoSpec"
| "delete y (constwoSpec ztwoSpec xs) =
     (if x y ztwoSpec then delete y xs else constwoSpec ztwoSpec (delete y xs))"

hipster x elem delete
end
