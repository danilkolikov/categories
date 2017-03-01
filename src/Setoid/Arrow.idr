module Arrow

import public Setoid

%access public export

||| Default equality for arrows. Arrows are equal if their types are equal
data ArrowEquality : {a: Type} -> {arr: a -> a -> Type} -> (x, y: a) -> (f, g: x `arr` y) -> Type where
    ArrowRefl : {a: Type} -> {arr: a -> a -> Type} -> {x, y: a} -> {f, g: x `arr` y} -> ArrowEquality x y f g

||| Proof that default equality of arrows is indeed equality
arrowEqualityIsEquality : {a: Type} -> {arr: a -> a -> Type} -> (x, y: a) -> IsEquality (x `arr` y) (ArrowEquality x y)
arrowEqualityIsEquality _ _ = MkIsEquality
    (MkIsReflexive $ \_ => ArrowRefl)
    (MkIsSymmetric $ \_, _, (ArrowRefl {f} {g}) => ArrowRefl {f=g} {g=f})
    (MkIsTransittive $ \_, _, _, (ArrowRefl {f} {g}), (ArrowRefl {g=h}) => ArrowRefl {f=f} {g=h})

||| Constructor for setoid of arrows between two objects
arrowSetoid : (arr: a -> a -> Type) -> (x, y: a) -> Setoid
arrowSetoid arr x y = MkSetoid
    (x `arr` y)
    (ArrowEquality x y)
    (arrowEqualityIsEquality x y)
