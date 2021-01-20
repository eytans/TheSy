theory Prop_14
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun filter :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"filter y (niltwoSpec) = niltwoSpec"
| "filter y (constwoSpec ztwoSpec xs) =
     (if y ztwoSpec then constwoSpec ztwoSpec (filter y xs) else filter y xs)"

hipster x filter
end
