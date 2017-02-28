module Setoid

import public Relation

%access public export

record Setoid where
    constructor MkSetoid
    Carrier : Type
    Equal : Carrier -> Carrier -> Type
    getEquality : IsEquality Carrier Equal
