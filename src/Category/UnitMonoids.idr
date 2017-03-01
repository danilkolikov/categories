module UnitMonoids

import public Category.UnitMonoid
import public Algebra.Hierarchy
import public Setoid.Natural

import Util.Operators

%access public export

naturalPlusMonoidCat : Category
naturalPlusMonoidCat =
    naturalIsSemiring & semiringIsCommutativeMonoidOverPlus >>> commutativeMonoidIsMonoid >>> monoidIsCategory

naturalMultMonoidCat : Category
naturalMultMonoidCat = naturalIsSemiring & semiringIsMonoidOverMult >>> monoidIsCategory
