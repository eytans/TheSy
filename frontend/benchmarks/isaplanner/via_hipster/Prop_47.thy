theory Prop_47
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a TreeSpecial = Leaf | Node "'a TreeSpecial" "'a" "'a TreeSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun mirror :: "'a TreeSpecial => 'a TreeSpecial" where
"mirror (Leaf) = Leaf"
| "mirror (Node l y r) = Node (mirror r) y (mirror l)"

fun max :: "NatSpecial => NatSpecial => NatSpecial" where
"max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S xtwoSpec) = S (max z xtwoSpec)"

fun height :: "'a TreeSpecial => NatSpecial" where
"height (Leaf) = Z"
| "height (Node l y r) = S (max (height l) (height r))"

hipster mirror max height
end
