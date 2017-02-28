module PreOrder

import public Category
import public Relation
import public Relation.Equalities

%access public export

preOrderIsCategory : {a: Type} -> {rel: a -> a -> Type} -> IsPreOrder a rel -> Category
preOrderIsCategory (MkIsPreOrder (MkIsReflexive refl) (MkIsTransittive transit)) = MkCategory
    a
    rel
    ArrowEquality
    arrowEqualityIsEquality
    transit
    (\_,_,_,_,_,_,_ => ArrowRefl)
    refl
    (\_,_,_ => ArrowRefl)
    (\_,_,_ => ArrowRefl)
