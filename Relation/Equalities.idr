module Equalities

import public Relation

%access public export

||| Proof that built-in equality is equality
equalIsEquality : {a: Type} -> Equality a (=)
equalIsEquality = MkEquality
    (MkReflexive $ \_ => Refl)
    (MkSymmetric $ \_, _ => sym)
    (MkTransittive $ \_, _, _ => trans)


||| Default equality for arrows. Arrows are equal if their types are equal
data ArrowEquality : {arr: a -> a -> Type} -> (x, y: a) -> (x `arr` y) -> (x `arr` y) -> Type where
    ArrowRefl : ArrowEquality x y f g

arrowEqualityIsEquality : {arr: a -> a -> Type} -> (x, y: a) -> Equality (x `arr` y) (ArrowEquality x y)
arrowEqualityIsEquality _ _ = MkEquality
    (MkReflexive $ \_ => ArrowRefl)
    (MkSymmetric $ \_, _, (ArrowRefl {f} {g}) => ArrowRefl {f=g} {g=f})
    (MkTransittive $ \_, _, _, (ArrowRefl {f} {g}), (ArrowRefl {g=h}) => ArrowRefl {f=f} {g=h})


||| Equivalence relation for natural numbers
public export data NatEq : Nat -> Nat -> Type where
    NatRefl : {x : Nat} -> {y : Nat} -> (x = y) -> NatEq x y

||| Proof that custom equalty for natural numbers is equality
natEqIsEquality : Equality Nat NatEq
natEqIsEquality = MkEquality
    (MkReflexive $ \_ => NatRefl Refl)
    (MkSymmetric $ \_, _, (NatRefl left) => NatRefl $ sym left)
    (MkTransittive $ \_, _, _, (NatRefl left), (NatRefl center) => NatRefl $ trans left center)
