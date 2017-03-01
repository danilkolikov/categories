module Operation

import public Setoid

%access public export
%auto_implicits off

record IsAssociative (s : Setoid) (op : Carrier s -> Carrier s -> Carrier s) where
    constructor MkIsAssociative
    assoc : (x, y, z: Carrier s) -> Equal s (x `op` (y `op` z)) ((x `op` y) `op` z)

record HasNeutral (s: Setoid) (op: Carrier s -> Carrier s -> Carrier s) where
    constructor MkHasNeutral
    getNeutral : Carrier s
    leftNeutral : (x: Carrier s) -> Equal s (getNeutral `op` x) x
    rightNeutral : (x: Carrier s) -> Equal s (x `op` getNeutral) x

record HasInverse
                    (s: Setoid)
                    (op: Carrier s -> Carrier s -> Carrier s)
                    (hasNeutral : HasNeutral s op)
    where
    constructor MkHasInverse

    inverse : Carrier s -> Carrier s
    leftInverse : (x: Carrier s) -> Equal s ((inverse x) `op` x) $ getNeutral hasNeutral
    rightInverse : (x: Carrier s) -> Equal s (x `op` (inverse x)) $ getNeutral hasNeutral

record IsCommutative (s: Setoid) (op: Carrier s -> Carrier s -> Carrier s) where
    constructor MkIsCommutative
    commut : (x, y: Carrier s) -> Equal s (x `op` y) (y `op` x)

record IsDistributive
        (s: Setoid)
        (plus: Carrier s -> Carrier s -> Carrier s)
        (mult: Carrier s -> Carrier s -> Carrier s)
    where
    constructor MkIsDistributive
    distributeLeft : (x, y, z: Carrier s) ->
        Equal s ((x `plus` y) `mult` z) ((x `mult` z) `plus` (y `mult` z))
    distributeRight : (x, y, z: Carrier s) ->
        Equal s (x `mult` (y `plus` z)) ((x `mult` y) `plus` (x `mult` z))
