module Identities

import public Functor.Identity
import public Category.Discretes

%access public export

identityOne : CoFunctor Discretes.one Discretes.one
identityOne = identity Discretes.one
