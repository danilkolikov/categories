module Natural

import Setoid
import Algebra
import Relation

%access public export

||| Equivalence relation for natural numbers
public export data NatEqual : Nat -> Nat -> Type where
    NatRefl : {x : Nat} -> {y : Nat} -> (x = y) -> NatEqual x y

||| Proof that custom equalty for natural numbers is equality
natEqIsEquality : IsEquality Nat NatEqual
natEqIsEquality = MkIsEquality
    (MkIsReflexive $ \_ => NatRefl Refl)
    (MkIsSymmetric $ \_, _, (NatRefl left) => NatRefl $ sym left)
    (MkIsTransittive $ \_, _, _, (NatRefl left), (NatRefl center) => NatRefl $ trans left center)

||| Setoid for natural numbers (Example of usage of custom equality)
Natural : Setoid
Natural = MkSetoid Nat NatEqual natEqIsEquality

--- Plus part ---

naturalPlusIsAssociative : IsAssociative Natural plus
naturalPlusIsAssociative = MkIsAssociative $ \x, y, z =>  NatRefl $ plusAssociative x y z

naturalPlusHasNeutral : HasNeutral Natural plus
naturalPlusHasNeutral = MkHasNeutral
    0
    (\x => NatRefl $ plusZeroLeftNeutral x)
    (\x => NatRefl $ plusZeroRightNeutral x)

naturalPlusIsCommutative : IsCommutative Natural plus
naturalPlusIsCommutative = MkIsCommutative $ \x, y => NatRefl $ plusCommutative x y

--- Mult part ---

naturalMultIsAssociative : IsAssociative Natural mult
naturalMultIsAssociative = MkIsAssociative $ \x, y, z => NatRefl $ multAssociative x y z

naturalMultHasNeutral : HasNeutral Natural mult
naturalMultHasNeutral = MkHasNeutral
    1
    (\x => NatRefl $ multOneLeftNeutral x)
    (\x => NatRefl $ multOneRightNeutral x)

naturalMultIsDistributiveOverPlus : IsDistributive Natural plus mult
naturalMultIsDistributiveOverPlus = MkIsDistributive
    (\x, y, z => NatRefl $ multDistributesOverPlusLeft x y z)
    (\x, y, z => NatRefl $ multDistributesOverPlusRight x y z)

--- Algebraic structure ---

naturalIsSemiring : Semiring
naturalIsSemiring = MkSemiring
    Natural
    plus
    mult
    naturalPlusIsAssociative
    naturalPlusHasNeutral
    naturalPlusIsCommutative
    naturalMultIsAssociative
    naturalMultHasNeutral
    naturalMultIsDistributiveOverPlus
