module Set

import public Category
import public Setoid.SetoidFunction

%access public export

||| Category of all Setoids where objects are Setoids and morphisms are (extensional) functions between Setoids
Setoid : Category
Setoid = MkCategory
    Setoid
    SetoidFunction
    SetoidFunctionEquality
    setoidFunctionEqualityIsEquality

    setFunCompose
    setFunComposeIsAssociative

    setFunIdentity
    setFunIdentityIsLeftIdentity
    setFunIdentityIsRightIdentity
