theory Prop_36
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun takeWhile :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"takeWhile x (niltwoSpec) = niltwoSpec"
| "takeWhile x (constwoSpec z xs) =
     (if x z then constwoSpec z (takeWhile x xs) else niltwoSpec)"

hipster takeWhile
end
