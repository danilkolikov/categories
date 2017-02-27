module SemiRings

import public Algebra
import public Algebra.Monoids
import public Algebra.Abelian

%access public export

natIsSemiring : SemiRing Nat plus mult NatEq
natIsSemiring = MkSemiRing
    natPlusMonoid
    natPlusAbelian
    natMultMonoid
    (\x, y, z => NatRefl $ multDistributesOverPlusLeft x y z)
    (\x, y, z => NatRefl $ multDistributesOverPlusRight x y z)
