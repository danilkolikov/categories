module Discretes

import public Category.Discrete

%access public export

discreteCat : Category a (=) ArrowEquality
discreteCat = discrete equalIsEquality

one : Category () (=) ArrowEquality
one = discrete equalIsEquality

two : Category Bool (=) ArrowEquality
two = discrete equalIsEquality
