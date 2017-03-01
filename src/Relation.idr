module Relation

%access export

{- Default properties -}

record IsReflexive a (rel: a -> a -> Type) where
    constructor MkIsReflexive
    reflexy : (x: a) -> x `rel` x

record IsAntiReflexive a (rel: a -> a -> Type) where
    constructor MkIsAntiReflexive
    antiReflexy : (x: a) -> Not (x `rel` x)

record IsSymmetric a (rel: a -> a -> Type) where
    constructor MkIsSymmetric
    symmetry : (x, y: a) -> x `rel` y -> y `rel` x

-- Forward declaration
data IsEquality : (a: Type) -> (a -> a -> Type) -> Type

record IsAntiSymmetric
        (a: Type)
        (rel: a -> a -> Type)
        (eq: a -> a -> Type)
        (isEquality : IsEquality a eq)
    where
    constructor MkIsAntiSymmetric
    antiSymmetry : (x, y: a) -> x `rel` y -> y `rel` x -> x `eq` y

record IsTransittive a (rel: a -> a -> Type) where
    constructor MkIsTransittive
    transittivity : (x, y, z: a) -> x `rel` y -> y `rel` z -> x `rel` z

{- Default relation kinds -}

record IsEquality a (rel : a -> a -> Type) where
    constructor MkIsEquality
    isReflexive : IsReflexive a rel
    isSymmetric : IsSymmetric a rel
    isTransittive : IsTransittive a rel

record IsPreOrder a (rel: a -> a -> Type) where
    constructor MkIsPreOrder
    isReflexive : IsReflexive a rel
    isTransittive : IsTransittive a rel

record IsPartialOrder
        (a: Type)
        (rel: a -> a -> Type)
        (eq: a -> a -> Type)
        (isEquality: IsEquality a eq)
    where
    constructor MkIsPartialOrder
    isReflexive : IsReflexive a rel
    isAntgetymmetric : IsAntiSymmetric a rel eq isEquality
    isTransittive : IsTransittive a rel

record IsStrictOrder
        (a: Type)
        (rel: a -> a -> Type)
        (eq: a -> a -> Type)
        (isEquality: IsEquality a eq)
    where
    constructor MkIsStrictOrder
    isAntiReflexive : IsAntiReflexive a rel
    isAntgetymmetric : IsAntiSymmetric a rel eq isEquality
    isTransittive : IsTransittive a rel
