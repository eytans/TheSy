theory Prop_68
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

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec z xs) = S (len xs)"

fun delete :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"delete y (niltwoSpec) = niltwoSpec"
| "delete y (constwoSpec ztwoSpec xs) =
     (if x y ztwoSpec then delete y xs else constwoSpec ztwoSpec (delete y xs))"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) z = True"
| "twoSpec (S ztwoSpec) (Z) = False"
| "twoSpec (S ztwoSpec) (S xtwoSpec) = twoSpec ztwoSpec xtwoSpec"

hipster x len delete twoSpec
end
