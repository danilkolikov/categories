module Equalities

import public Relation

%access public export

||| Proof that built-in equality is equality
equalIsEquality : {a: Type} -> IsEquality a (=)
equalIsEquality = MkIsEquality
    (MkIsReflexive $ \_ => Refl)
    (MkIsSymmetric $ \_, _ => sym)
    (MkIsTransittive $ \_, _, _ => trans)

||| Default equality for arrows. Arrows are equal if their types are equal
data ArrowEquality : {a: Type} -> {arr: a -> a -> Type} -> (x, y: a) -> (f, g: x `arr` y) -> Type where
    ArrowRefl : {a: Type} -> {arr: a -> a -> Type} -> {x, y: a} -> {f, g: x `arr` y} -> ArrowEquality x y f g

||| Proof that default equality of arrows is indeed equality
arrowEqualityIsEquality : {a: Type} -> {arr: a -> a -> Type} -> (x, y: a) -> IsEquality (x `arr` y) (ArrowEquality x y)
arrowEqualityIsEquality _ _ = MkIsEquality
    (MkIsReflexive $ \_ => ArrowRefl)
    (MkIsSymmetric $ \_, _, (ArrowRefl {f} {g}) => ArrowRefl {f=g} {g=f})
    (MkIsTransittive $ \_, _, _, (ArrowRefl {f} {g}), (ArrowRefl {g=h}) => ArrowRefl {f=f} {g=h})
