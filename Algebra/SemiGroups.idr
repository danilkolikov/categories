module SemiGroups

import public Algebra
import public Relation.Equalities

%access public export

natPlusSemiGroup : SemiGroup Nat plus NatEq
natPlusSemiGroup = MkSemiGroup natEqIsEquality (\x, y, z =>  NatRefl $ plusAssociative x y z)

natMultSemiGroup : SemiGroup Nat mult NatEq
natMultSemiGroup = MkSemiGroup natEqIsEquality (\x, y, z => NatRefl $ multAssociative x y z)
