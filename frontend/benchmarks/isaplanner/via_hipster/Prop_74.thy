theory Prop_74
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) z = niltwoSpec"
| "take (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "take (S ztwoSpec) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take ztwoSpec x3)"

fun rev :: "'a ListSpecial => 'a ListSpecial" where
"rev (niltwoSpec) = niltwoSpec"
| "rev (constwoSpec z xs) = x (rev xs) (constwoSpec z (niltwoSpec))"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec z xs) = S (len xs)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) z = z"
| "drop (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "drop (S ztwoSpec) (constwoSpec xtwoSpec x3) = drop ztwoSpec x3"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) z = Z"
| "twoSpec (S ztwoSpec) (Z) = S ztwoSpec"
| "twoSpec (S ztwoSpec) (S xtwoSpec) = twoSpec ztwoSpec xtwoSpec"

hipster x take rev len drop twoSpec
end
