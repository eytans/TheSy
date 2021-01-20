theory Prop_28
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun y :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"y (niltwoSpec) ytwoSpec = ytwoSpec"
| "y (constwoSpec ztwoSpec xs) ytwoSpec = constwoSpec ztwoSpec (y xs ytwoSpec)"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpectwoSpec) = x xtwoSpec ytwoSpectwoSpec"

fun elem :: "NatSpecial => NatSpecial ListSpecial => bool" where
"elem z (niltwoSpec) = False"
| "elem z (constwoSpec ztwoSpec xs) = (if x z ztwoSpec then True else elem z xs)"

hipster y x elem
end
