module Identities

import public Functor.Identity
import public Category.Discretes

%access public export

identityOne : CoFunctor one one
identityOne = identity one
