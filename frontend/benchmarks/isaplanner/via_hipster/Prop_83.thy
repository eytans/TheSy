theory Prop_83
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype ('a, 'b) PairSpecial = PairSpecialtwoSpec "'a" "'b"

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun zip :: "'a ListSpecial => 'b ListSpecial => (('a, 'b) PairSpecial) ListSpecial" where
"zip (niltwoSpec) z = niltwoSpec"
| "zip (constwoSpec ztwoSpec xtwoSpec) (niltwoSpec) = niltwoSpec"
| "zip (constwoSpec ztwoSpec xtwoSpec) (constwoSpec x3 x4) =
     constwoSpec (PairSpecialtwoSpec ztwoSpec x3) (zip xtwoSpec x4)"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) z = niltwoSpec"
| "take (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "take (S ztwoSpec) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take ztwoSpec x3)"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec z xs) = S (len xs)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) z = z"
| "drop (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "drop (S ztwoSpec) (constwoSpec xtwoSpec x3) = drop ztwoSpec x3"

hipster zip x take len drop
end
