theory Prop_12
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun map :: "('a => 'b) => 'a ListSpecial => 'b ListSpecial" where
"map x (niltwoSpec) = niltwoSpec"
| "map x (constwoSpec z xs) = constwoSpec (x z) (map x xs)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) y = y"
| "drop (S z) (niltwoSpec) = niltwoSpec"
| "drop (S z) (constwoSpec xtwoSpec x3) = drop z x3"

hipster map drop
end
