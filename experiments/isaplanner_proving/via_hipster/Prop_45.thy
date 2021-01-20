theory Prop_45
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype ('a, 'b) PairSpecial = PairSpecialtwoSpec "'a" "'b"

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

fun zip :: "'a ListSpecial => 'b ListSpecial => (('a, 'b) PairSpecial) ListSpecial" where
"zip (niltwoSpec) y = niltwoSpec"
| "zip (constwoSpec z xtwoSpec) (niltwoSpec) = niltwoSpec"
| "zip (constwoSpec z xtwoSpec) (constwoSpec x3 x4) = constwoSpec (PairSpecialtwoSpec z x3) (zip xtwoSpec x4)"

hipster zip
end
