theory Prop_85
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

fun rev :: "'a ListSpecial => 'a ListSpecial" where
"rev (niltwoSpec) = niltwoSpec"
| "rev (constwoSpec z xs) = x (rev xs) (constwoSpec z (niltwoSpec))"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec z xs) = S (len xs)"

hipster zip x rev len
end
