module Category

import public Relation

%access public export

record Category a (arr : a -> a -> Type) (arrEq : (x, y: a) -> arr x y -> arr x y -> Type) where
    constructor MkCategory
    isEquality : (x, y: a) -> Equality (arr x y) (arrEq x y)

    compose : (x, y, z: a) -> (x `arr` y) -> (y `arr` z) -> (x `arr` z)
    assoc :
        (x, y, z, w: a) ->
        (f : x `arr` y) -> (g : y `arr` z) -> (h : z `arr` w) ->
        arrEq x w
                (compose x y w f (compose y z w g h))
                (compose x z w (compose x y z f g) h)

    idArr : (x: a) -> x `arr` x
    leftId : (x, y : a) -> (f : x `arr` y) -> arrEq x y (compose x x y (idArr x) f) f
    rightId : (x, y : a) -> (f : x `arr` y) -> arrEq x y(compose x y y f (idArr y)) f

dom : Category a arr arrEq -> (x `arr` y) -> a
dom _ {x} _ = x

cod : Category a arr arrEq -> (x `arr` y) -> a
cod _ {y} _ = y
