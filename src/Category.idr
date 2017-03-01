module Category

import public Relation

%access public export

record Category where
    constructor MkCategory
    Object : Type
    Arrow : Object -> Object -> Type
    ArrowEq : (x, y: Object) -> (f, g: Arrow x y) -> Type

    isEquality : (x, y: Object) -> IsEquality (Arrow x y) (ArrowEq x y)

    compose : (x, y, z: Object) -> (Arrow x y) -> (Arrow y z) -> (Arrow x z)
    assoc :
        (x, y, z, w: Object) ->
        (f : Arrow x y) -> (g : Arrow y z) -> (h : Arrow z w) ->
        ArrowEq x w
                (compose x y w f (compose y z w g h))
                (compose x z w (compose x y z f g) h)

    idArr : (x: Object) -> Arrow x x
    leftId : (x, y : Object) -> (f : Arrow x y) -> ArrowEq x y (compose x x y (idArr x) f) f
    rightId : (x, y : Object) -> (f : Arrow x y) -> ArrowEq x y(compose x y y f (idArr y)) f

dom : (C: Category) -> {x, y: Object C} -> Arrow C x y -> Object C
dom _ {x} _ = x

cod : (C: Category) -> {x, y: Object C} -> Arrow C x y -> Object C
cod _ {y} _ = y
