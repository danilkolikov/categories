module Monoids

import public Algebra.SemiGroups

%access public export
%auto_implicits off

natPlusMonoid : RMonoid Nat plus NatEq
natPlusMonoid = MkRMonoid
    natPlusSemiGroup
    0
    (\x => NatRefl $ plusZeroLeftNeutral x)
    (\x => NatRefl $ plusZeroRightNeutral x)

natMultMonoid : RMonoid Nat mult NatEq
natMultMonoid = MkRMonoid
    natMultSemiGroup
    1
    (\x => NatRefl $ multOneLeftNeutral x)
    (\x => NatRefl $ multOneRightNeutral x)
