theory Prop_82
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype ('a, 'b) PairSpecial = PairSpecialtwoSpec "'a" "'b"

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun zip :: "'a ListSpecial => 'b ListSpecial => (('a, 'b) PairSpecial) ListSpecial" where
"zip (niltwoSpec) y = niltwoSpec"
| "zip (constwoSpec z xtwoSpec) (niltwoSpec) = niltwoSpec"
| "zip (constwoSpec z xtwoSpec) (constwoSpec x3 x4) = constwoSpec (PairSpecialtwoSpec z x3) (zip xtwoSpec x4)"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) y = niltwoSpec"
| "take (S z) (niltwoSpec) = niltwoSpec"
| "take (S z) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take z x3)"

hipster zip take
end
