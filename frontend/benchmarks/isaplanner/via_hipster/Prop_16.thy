theory Prop_16
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun last :: "NatSpecial ListSpecial => NatSpecial" where
"last (niltwoSpec) = Z"
| "last (constwoSpec y (niltwoSpec)) = y"
| "last (constwoSpec y (constwoSpec xtwoSpec x3)) = last (constwoSpec xtwoSpec x3)"

hipster last
end
