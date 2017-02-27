module UnitMonoids

import public Category.UnitMonoid
import public Algebra.Monoids

%access public export

natPlusMonoidCat : Category () (UnitArrow Nat) (UnitEqual NatEq)
natPlusMonoidCat = monoid natPlusMonoid

natMultMonoidCat : Category () (UnitArrow Nat) (UnitEqual NatEq)
natMultMonoidCat = monoid natMultMonoid
