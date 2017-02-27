module Discrete

import public Category
import public Relation
import public Relation.Equalities

%access export

discrete : Equality a eq -> Category a eq ArrowEquality
discrete (MkEquality (MkReflexive refl) (MkSymmetric symm) (MkTransittive transit)) = MkCategory
    arrowEqualityIsEquality
    transit
    (\_, _, _, _, _, _, _ => ArrowRefl)
    refl
    (\_, _, _ => ArrowRefl)
    (\_, _, _ => ArrowRefl)
