module Algebra

import Relation

%access public export

record SemiGroup a (op: a -> a -> a) (eq : a -> a -> Type) where
    constructor MkSemiGroup
    getEquality : Equality a eq

    assoc : (x, y, z : a) -> (op x (op y z)) `eq` (op (op x y) z)

||| RecordMonoid (Monoid already exists)
record RMonoid a (op : a -> a -> a) (eq : a -> a -> Type) where
    constructor MkRMonoid
    getSemiGroup : SemiGroup a op eq

    getNeutral : a
    leftNeutral : (x : a) -> (getNeutral `op` x) `eq` x
    rightNeutral : (x: a) -> (x `op` getNeutral) `eq` x

record Group a (op : a -> a -> a) (eq : a -> a -> Type) where
    constructor MkGroup
    getRMonoid : RMonoid a op eq

    inverse : a -> a
    leftInverse : (x : a) -> ((inverse x) `op` x) `eq` (getNeutral getRMonoid)
    rightInverse : (x : a) -> (x `op` (inverse x)) `eq` (getNeutral getRMonoid)

record Abelian a (op : a -> a -> a) (eq : a -> a -> Type) where
    constructor MkAbelian
    getEquality : Equality a eq

    commut : (x, y: a) -> (x `op` y) `eq` (y `op` x)

record AbelianGroup a (op: a -> a -> a) (eq : a -> a -> Type) where
    constructor MkAbelianGroup

    getAbelian : Abelian a op eq
    getGroup : Group a op eq

record SemiRing a (plus : a -> a -> a) (mult : a -> a -> a) (eq : a -> a -> Type) where
    constructor MkSemiRing
    getPlusMonoid : RMonoid a plus eq
    getAbelian : Abelian a plus eq
    getMultMonoid : RMonoid a mult eq

    distributeLeft : (x, y, z: a) -> ((x `plus` y) `mult` z) `eq` ((x `mult` z) `plus` (y `mult` z))
    distributeRight : (x, y, z: a) -> (x `mult` (y `plus` z)) `eq` ((x `mult` y) `plus` (x `mult` z))
