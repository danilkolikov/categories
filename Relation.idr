module Relation

%access export

{- Default properties -}

record Reflexive a (rel: a -> a -> Type) where
    constructor MkReflexive
    reflexy : (x: a) -> x `rel` x

record AntiReflexive a (rel: a -> a -> Type) where
    constructor MkAntiReflexive
    antiReflexy : (x: a) -> Not (x `rel` x)

record Symmetric a (rel: a -> a -> Type) where
    constructor MkSymmetric
    symmetry : (x, y: a) -> x `rel` y -> y `rel` x

-- Forward declaration
data Equality : (a: Type) -> (a -> a -> Type) -> Type

record Antgetymmetric a (rel : a -> a -> Type) (eq : a -> a -> Type) where
    constructor MkAntgetymmetric
    getEquality : Equality a eq
    antgetymmetry : (x, y: a) -> x `rel` y -> y `rel` x -> x `eq` y

record Transittive a (rel: a -> a -> Type) where
    constructor MkTransittive
    transittivity : (x, y, z: a) -> x `rel` y -> y `rel` z -> x `rel` z

{- Default relation kinds -}

record Equality a (rel : a -> a -> Type) where
    constructor MkEquality
    getReflexive : Reflexive a rel
    getSymmetric : Symmetric a rel
    getTransittive : Transittive a rel

record PreOrder a (rel : a -> a -> Type) where
    constructor MkPreOrder
    getReflexive : Reflexive a rel
    getTransittive : Transittive a rel

record PartialOrder a (rel : a -> a -> Type) (eq : a -> a -> Type) where
    constructor MkPartialOrder
    getReflexive : Reflexive a rel
    getAntgetymmetric : Antgetymmetric a rel eq
    getTransittive : Transittive a rel

record StrictOrder a (rel : a -> a -> Type) (eq : a -> a -> Type) where
    constructor MkStrictOrder
    getAntiReflexive : AntiReflexive a rel
    getAntgetymmetric : Antgetymmetric a rel eq
    getTransittive : Transittive a rel
