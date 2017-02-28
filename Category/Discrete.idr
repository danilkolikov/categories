module Discrete

import public Relation
import public Relation.Hierarchy
import public Category
import public Category.Order

import Utils

%access public export

equalityIsCategory : {a: Type} -> {eq: a -> a -> Type} -> IsEquality a eq -> Category
equalityIsCategory =  equalityIsPreOrder >>> preOrderIsCategory

discreteCategory : (a: Type) -> Category
discreteCategory a = equalIsEquality {a=a} & equalityIsCategory
