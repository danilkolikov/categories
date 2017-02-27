module PreOrder

import public Category
import public Relation
import public Relation.Equalities

preorder : PreOrder a rel -> Category a rel ArrowEquality
preorder (MkPreOrder (MkReflexive refl) (MkTransittive transit))= MkCategory
    arrowEqualityIsEquality
    transit
    (\_,_,_,_,_,_,_ => ArrowRefl)
    refl
    (\_,_,_ => ArrowRefl)
    (\_,_,_ => ArrowRefl)
