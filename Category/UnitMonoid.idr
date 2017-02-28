module UnitMonoid

import public Category
import public Algebra
import Relation

%access public export
%auto_implicits off

data UnitArrow : (a : Type) -> () -> () -> Type where
    Arrow : {a: Type} -> (x : a) -> UnitArrow a () ()

getValue : {a: Type} -> UnitArrow a () () -> a
getValue (Arrow x) = x

data UnitEqual : {a: Type} -> (a -> a -> Type) -> (x, y: ()) -> (f, g: UnitArrow a x y) -> Type where
    UnitRefl :  {a: Type} -> {f, g: UnitArrow a () ()} ->
        (eq : a -> a -> Type) -> ((getValue f) `eq` (getValue g)) -> UnitEqual eq () () f g

unitEqualIsEquality : {a: Type} -> {eq: a -> a -> Type}
        -> IsEquality a eq -> (x, y: ()) -> IsEquality (UnitArrow a x y) (UnitEqual eq x y)
unitEqualIsEquality
    (MkIsEquality (MkIsReflexive refl) (MkIsSymmetric symm) (MkIsTransittive transit)) _ _ =
        MkIsEquality
            (MkIsReflexive $
                \(Arrow x) => UnitRefl eq (refl x))
            (MkIsSymmetric $
                \(Arrow x), (Arrow y), (UnitRefl _ prf) => UnitRefl eq (symm x y prf))
            (MkIsTransittive $
                \(Arrow x), (Arrow y), (Arrow z), (UnitRefl _ first), (UnitRefl _ second) =>
                    UnitRefl eq $ transit x y z first second)

monoidIsCategory : Monoid' -> Category
monoidIsCategory (MkMonoid' (MkSetoid a equality eqProof) op (MkIsAssociative assoc) (MkHasNeutral neutral left right)) = MkCategory
        ()
        (UnitArrow a)
        (UnitEqual equality)
        (unitEqualIsEquality eqProof)
        compose
        (\(), (), (), (), (Arrow x), (Arrow y), (Arrow z) => UnitRefl equality $ assoc x y z)
        neutralArrow
        (\(), (), (Arrow x) => UnitRefl equality $ left x)
        (\(), (), (Arrow x) => UnitRefl equality $ right x)
    where
        compose : (f, g, h: ()) -> (UnitArrow a f g) -> (UnitArrow a g h) -> (UnitArrow a f h)
        compose () () () (Arrow x) (Arrow y) = Arrow (x `op` y)

        neutralArrow : (x: ()) -> UnitArrow a x x
        neutralArrow () = Arrow neutral
