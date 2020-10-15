theory Prop_43
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun takeWhile :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"takeWhile y (niltwoSpec) = niltwoSpec"
| "takeWhile y (constwoSpec ztwoSpec xs) =
     (if y ztwoSpec then constwoSpec ztwoSpec (takeWhile y xs) else niltwoSpec)"

fun dropWhile :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"dropWhile y (niltwoSpec) = niltwoSpec"
| "dropWhile y (constwoSpec ztwoSpec xs) =
     (if y ztwoSpec then dropWhile y xs else constwoSpec ztwoSpec xs)"

hipster x takeWhile dropWhile
end
