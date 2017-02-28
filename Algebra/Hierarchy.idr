module Hierarchy

import public Algebra

%access public export

monoidIsSemigroup : Monoid' -> Semigroup'
monoidIsSemigroup (MkMonoid' s op assoc _) = MkSemigroup' s op assoc

commutativeMonoidIsMonoid : CommutativeMonoid -> Monoid'
commutativeMonoidIsMonoid (MkCommutativeMonoid s op assoc neutral _) = MkMonoid' s op assoc neutral

groupIsMonoid : Group -> Monoid'
groupIsMonoid (MkGroup s op assoc neutral _) = MkMonoid' s op assoc neutral

abelianGroupIsGroup : AbelianGroup -> Group
abelianGroupIsGroup (MkAbelianGroup s op assoc neutral inverse _) =
    MkGroup s op assoc neutral inverse

abelianGroupIsCommutativeMonoid : AbelianGroup -> CommutativeMonoid
abelianGroupIsCommutativeMonoid (MkAbelianGroup s op assoc neutral _ commut) =
    MkCommutativeMonoid s op assoc neutral commut

semiringIsCommutativeMonoidOverPlus : Semiring -> CommutativeMonoid
semiringIsCommutativeMonoidOverPlus (MkSemiring s plus mult assoc neutral commut _ _ _) =
    MkCommutativeMonoid s plus assoc neutral commut

semiringIsMonoidOverMult : Semiring -> Monoid'
semiringIsMonoidOverMult (MkSemiring s plus mult _ _ _ assoc neutral _) =
    MkMonoid' s mult assoc neutral
