module Abelian

import public Algebra
import public Relation.Equalities

%access public export

natPlusAbelian : Abelian Nat plus NatEq
natPlusAbelian = MkAbelian natEqIsEquality (\x, y => NatRefl $ plusCommutative x y)

natMultAbelian : Abelian Nat mult NatEq
natMultAbelian = MkAbelian natEqIsEquality (\x, y => NatRefl $ multCommutative x y)
