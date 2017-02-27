module Identities

import public Functor.Identity
import public Relation.Equalities
import public Category.Discretes

%access public export

identityOne : CoFunctor () (=) ArrowEquality () (=) ArrowEquality
identityOne = identity one
