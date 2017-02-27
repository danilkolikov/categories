module UnitMonoid

import public Category
import public Algebra
import Relation

%access public export

data UnitArrow : (a : Type) -> () -> () -> Type where
    Arrow : (x : a) -> UnitArrow a () ()

getValue : UnitArrow a () () -> a
getValue (Arrow x) = x

data UnitEqual : (a -> a -> Type) -> (x: ()) -> (y: ()) -> UnitArrow a x y -> UnitArrow a x y -> Type where
    UnitRefl :  (eq : a -> a -> Type) -> ((getValue f) `eq` (getValue g)) -> UnitEqual eq () () f g

unitEqualIsEquality : Equality a eq -> (x, y: ()) -> Equality (UnitArrow a x y) (UnitEqual eq x y)
unitEqualIsEquality
    (MkEquality (MkReflexive refl) (MkSymmetric symm) (MkTransittive transit)) _ _ =
        MkEquality
            (MkReflexive $
                \(Arrow x) => UnitRefl eq (refl x))
            (MkSymmetric $
                \(Arrow x), (Arrow y), (UnitRefl _ prf) => UnitRefl eq (symm x y prf))
            (MkTransittive $
                \(Arrow x), (Arrow y), (Arrow z), (UnitRefl _ first), (UnitRefl _ second) =>
                    UnitRefl eq $ transit x y z first second)

monoid : RMonoid a op eq -> Category () (UnitArrow a) (UnitEqual eq)
monoid (MkRMonoid (MkSemiGroup equal assoc) neutral left right) = MkCategory
        (unitEqualIsEquality equal)
        compose
        (\(), (), (), (), (Arrow x), (Arrow y), (Arrow z) => UnitRefl eq $ assoc x y z)
        neutralArrow
        (\(), (), (Arrow x) => UnitRefl eq $ left x)
        (\(), (), (Arrow x) => UnitRefl eq $ right x)
    where
        compose : (f, g, h: ()) -> (UnitArrow a f g) -> (UnitArrow a g h) -> (UnitArrow a f h)
        compose () () () (Arrow x) (Arrow y) = Arrow (x `op` y)

        neutralArrow : (x: ()) -> UnitArrow a x x
        neutralArrow () = Arrow neutral
