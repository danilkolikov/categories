module Identity

import public Category
import public Functor
import public Relation

%access public export

identity : (C: Category)  -> CoFunctor C C
identity (MkCategory _ _ _ eq compose _ idArr _ _) = MkCoFunctor
        id
        (\_, _ => id)
        (\x => let
                    (MkIsEquality (MkIsReflexive refl) _ _) = eq x x
                in refl (idArr x))
        (\x, y, z, f, g =>
            let
                (MkIsEquality (MkIsReflexive refl) _ _) = eq x z
            in refl (compose x y z f g))
