module Functor

import public Category

%access public export

record CoFunctor
        a (arr : a -> a -> Type) (arrEq : (x, y: a) -> arr x y -> arr x y -> Type)
        b (brr : b -> b -> Type) (brrEq : (x, y: b) -> brr x y -> brr x y -> Type)
    where
    constructor MkCoFunctor
    from : Category a arr arrEq
    to : Category b brr brrEq

    apply : a -> b
    applyArr : (x, y: a) -> x `arr` y -> (apply x) `brr` (apply y)

    preserveId : (x: a) -> brrEq (apply x) (apply x) (applyArr x x (idArr from x)) (idArr to (apply x))
    preserveCompose : (x, y, z: a) -> (f: x `arr` y) -> (g: y `arr` z) ->
        brrEq (apply x) (apply z)
                (applyArr x z (compose from x y z f g))
                (compose to (apply x) (apply y) (apply z) (applyArr x y f) (applyArr y z g))

record ContraFunctor
        a (arr : a -> a -> Type) (arrEq : (x, y: a) -> arr x y -> arr x y -> Type)
        b (brr : b -> b -> Type) (brrEq : (x, y: b) -> brr x y -> brr x y -> Type)
    where
    constructor MkContraFunctor
    from : Category a arr arrEq
    to : Category b brr brrEq

    apply : a -> b
    applyArr : (x, y: a) -> x `arr` y -> (apply y) `brr` (apply x)

    preserveId : (x: a) -> brrEq (apply x) (apply x) (applyArr x x (idArr from x)) (idArr to (apply x))
    inverseCompose : (x, y, z: a) -> (f: x `arr` y) -> (g: y `arr` z) ->
        brrEq (apply z) (apply x)
                (applyArr x z (compose from x y z f g))
                (compose to (apply z) (apply y) (apply x) (applyArr y z g) (applyArr x y f))
