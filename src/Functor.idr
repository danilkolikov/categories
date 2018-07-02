module Functor

import public Category

%access public export

record CoFunctor (c: Category) (d: Category)
    where
    constructor MkCoFunctor

    apply : Object c -> Object d
    applyArr : (x, y: Object c) -> Arrow c x y -> Arrow d (apply x) (apply y)

    preserveId : (x: Object c) -> ArrowEq d (apply x) (apply x) (applyArr x x (idArr c x)) (idArr d (apply x))
    preserveCompose :
        (x, y, z: Object c) -> (f: Arrow c x y) -> (g: Arrow c y z) ->
        ArrowEq d (apply x) (apply z)
                (applyArr x z (compose c x y z f g))
                (compose d (apply x) (apply y) (apply z) (applyArr x y f) (applyArr y z g))

record ContraFunctor (c: Category) (d: Category)
    where
    constructor MkContraFunctor
    apply : Object c -> Object d
    applyArr : (x, y: Object c) -> Arrow c x y -> Arrow d (apply y) (apply x)

    preserveId : (x: Object c) -> ArrowEq d (apply x) (apply x) (applyArr x x (idArr c x)) (idArr d (apply x))
    inverseCompose :
        (x, y, z: Object c) -> (f: Arrow c x y) -> (g: Arrow c y z) ->
        ArrowEq d (apply z) (apply x)
                (applyArr x z (compose c x y z f g))
                (compose d (apply z) (apply y) (apply x) (applyArr y z g) (applyArr x y f))
