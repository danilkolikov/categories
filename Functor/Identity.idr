module Identity

import public Category
import public Functor
import public Relation

%access public export

identity : Category a arr arrEq -> CoFunctor a arr arrEq a arr arrEq
identity cat with (cat)
    | (MkCategory eq _ _ _ _ _) = MkCoFunctor
        cat
        cat
        id
        (\_, _ => id)
        (\x => let
                    (MkEquality (MkReflexive refl) _ _) = eq x x
                in refl (idArr cat x))
        (\x, y, z, f, g =>
            let
                (MkEquality (MkReflexive refl) _ _) = eq x z
            in refl (compose cat x y z f g))
