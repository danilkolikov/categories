module Functor

import public Category

%access public export

record CoFunctor (C: Category) (D: Category)
    where
    constructor MkCoFunctor

    apply : Object C -> Object D
    applyArr : (x, y: Object C) -> Arrow C x y -> Arrow D (apply x) (apply y)

    preserveId : (x: Object C) -> ArrowEq D (apply x) (apply x) (applyArr x x (idArr C x)) (idArr D (apply x))
    preserveCompose :
        (x, y, z: Object C) -> (f: Arrow C x y) -> (g: Arrow C y z) ->
        ArrowEq D (apply x) (apply z)
                (applyArr x z (compose C x y z f g))
                (compose D (apply x) (apply y) (apply z) (applyArr x y f) (applyArr y z g))

record ContraFunctor (C: Category) (D: Category)
    where
    constructor MkContraFunctor
    apply : Object C -> Object D
    applyArr : (x, y: Object C) -> Arrow C x y -> Arrow D (apply y) (apply x)

    preserveId : (x: Object C) -> ArrowEq D (apply x) (apply x) (applyArr x x (idArr C x)) (idArr D (apply x))
    inverseCompose :
        (x, y, z: Object C) -> (f: Arrow C x y) -> (g: Arrow C y z) ->
        ArrowEq D (apply z) (apply x)
                (applyArr x z (compose C x y z f g))
                (compose D (apply z) (apply y) (apply x) (applyArr y z g) (applyArr x y f))
