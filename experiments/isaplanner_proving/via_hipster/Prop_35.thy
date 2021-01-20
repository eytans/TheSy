theory Prop_35
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun dropWhile :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"dropWhile x (niltwoSpec) = niltwoSpec"
| "dropWhile x (constwoSpec z xs) =
     (if x z then dropWhile x xs else constwoSpec z xs)"

hipster dropWhile
end
