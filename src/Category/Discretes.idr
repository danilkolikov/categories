module Discretes

import public Category.Discrete

%access public export

one : Category
one = discreteCategory ()

two : Category
two = discreteCategory Bool
