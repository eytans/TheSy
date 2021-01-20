theory Prop_49
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun butlast :: "'a ListSpecial => 'a ListSpecial" where
"butlast (niltwoSpec) = niltwoSpec"
| "butlast (constwoSpec z (niltwoSpec)) = niltwoSpec"
| "butlast (constwoSpec z (constwoSpec xtwoSpec x3)) =
     constwoSpec z (butlast (constwoSpec xtwoSpec x3))"

fun butlastConcat :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"butlastConcat y (niltwoSpec) = butlast y"
| "butlastConcat y (constwoSpec ztwoSpec xtwoSpec) = x y (butlast (constwoSpec ztwoSpec xtwoSpec))"

hipster x butlast butlastConcat
end
