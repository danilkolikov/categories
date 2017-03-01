module Hierarchy

import public Relation

%access public export

equalityIsPreOrder : {a: Type} -> {rel: a -> a -> Type} -> IsEquality a rel -> IsPreOrder a rel
equalityIsPreOrder (MkIsEquality refl _ trans) = MkIsPreOrder refl trans
