theory Prop_41
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) y = niltwoSpec"
| "take (S z) (niltwoSpec) = niltwoSpec"
| "take (S z) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take z x3)"

fun map :: "('a => 'b) => 'a ListSpecial => 'b ListSpecial" where
"map x (niltwoSpec) = niltwoSpec"
| "map x (constwoSpec z xs) = constwoSpec (x z) (map x xs)"

hipster take map
end
