module UnitMonoids

import public Category.UnitMonoid
import public Algebra.Hierarchy
import public Setoid.Natural

import Utils

%access public export

naturalPlusMonoidCat : Category
naturalPlusMonoidCat =
    naturalIsSemiring & semiringIsCommutativeMonoidOverPlus >>> commutativeMonoidIsMonoid >>> monoidIsCategory

naturalMultMonoidCat : Category
naturalMultMonoidCat = naturalIsSemiring & semiringIsMonoidOverMult >>> monoidIsCategory
