module Algebra

import public Setoid
import public Operation

%access public export

-- Semigroup is already defined
record Semigroup' where
    constructor MkSemigroup'
    setoid : Setoid
    op: Carrier setoid -> Carrier setoid -> Carrier setoid
    isAssociative : IsAssociative setoid op

-- Monoid is already defined
record Monoid' where
    constructor MkMonoid'
    setoid : Setoid
    op: Carrier setoid -> Carrier setoid -> Carrier setoid
    isAssociative : IsAssociative setoid op
    hasNeutral : HasNeutral setoid op

record CommutativeMonoid where
    constructor MkCommutativeMonoid
    setoid : Setoid
    op: Carrier setoid -> Carrier setoid -> Carrier setoid

    isAssociative : IsAssociative setoid op
    hasNeutral : HasNeutral setoid op
    isCommutative : IsCommutative setoid op

record Group where
    constructor MkGroup
    setoid : Setoid
    op: Carrier setoid -> Carrier setoid -> Carrier setoid

    isAssociative : IsAssociative setoid op
    hasNeutral : HasNeutral setoid op
    hasInverse : HasInverse setoid op hasNeutral

record AbelianGroup where
    constructor MkAbelianGroup
    setoid : Setoid
    op: Carrier setoid -> Carrier setoid -> Carrier setoid

    isAssociative : IsAssociative setoid op
    hasNeutral : HasNeutral setoid op
    hasInverse : HasInverse setoid op hasNeutral
    isCommutative : IsCommutative setoid op

record Semiring where
    constructor MkSemiring
    setoid : Setoid
    plus: Carrier setoid -> Carrier setoid -> Carrier setoid
    mult: Carrier setoid -> Carrier setoid -> Carrier setoid

    plusIsAssociative : IsAssociative setoid plus
    plusHasNeutral : HasNeutral setoid plus
    plusIsCommutative : IsCommutative setoid plus

    multIsAssociative : IsAssociative setoid mult
    multHasNeutral : HasNeutral setoid mult

    isDistributive : IsDistributive setoid plus mult
