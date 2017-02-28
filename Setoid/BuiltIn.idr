module BuiltIn

import public Setoid

%access public export

||| Proof that built-in equality is equality
equalIsEquality : {a: Type} -> IsEquality a (=)
equalIsEquality = MkIsEquality
    (MkIsReflexive $ \_ => Refl)
    (MkIsSymmetric $ \_, _ => sym)
    (MkIsTransittive $ \_, _, _ => trans)

||| Constructor of setoids which use built-in equality
builtInSetoid : (a: Type) -> Setoid
builtInSetoid a = MkSetoid
    a
    (=)
    equalIsEquality

builtInNatural : Setoid
builtInNatural = builtInSetoid Nat

builtInInteger : Setoid
builtInInteger = builtInSetoid Int
