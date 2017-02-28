module Discretes

import public Category.Discrete
import Relation.Equalities

%access public export

one : Category
one = discreteCategory ()

two : Category
two = discreteCategory Bool
