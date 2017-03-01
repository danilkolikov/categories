module SetoidFunction

import public Data.Morphisms
import public Setoid

%access public export

||| Extensional Function between two Setoids
record SetoidFunction (A: Setoid) (B: Setoid) where
    constructor MkSetoidFunction
    ||| Application of function
    apply : Carrier A -> Carrier B
    ||| Proof that if x == y  in A that f(x) == f(y) in B
    congruence : (x, y: Carrier A) -> Equal A x y -> Equal B (apply x) (apply y)

||| Composition of setoid functions is setoid function
setFunCompose : (A, B, C: Setoid) -> SetoidFunction A B -> SetoidFunction B C -> SetoidFunction A C
setFunCompose _ _ _ (MkSetoidFunction f congF) (MkSetoidFunction g congG) = MkSetoidFunction
    (g . f)
    (\x, y, equal => congG (f x) (f y) $ congF x y equal)

||| Identity setoid function
setFunIdentity : (A: Setoid) -> SetoidFunction A A
setFunIdentity _ = MkSetoidFunction
    id
    (\x, y, equal => equal)

||| SetoidFunction equality - two functions are equal if they are equal for any argument
data SetoidFunctionEquality : (A, B: Setoid) -> (f, g: SetoidFunction A B) -> Type where
    SetoidFunctionRefl : {A, B: Setoid}
                    -> {f, g: SetoidFunction A B}
                    -> ((x: Carrier A) -> Equal B (apply f x) (apply g x))
                    -> SetoidFunctionEquality A B f g

||| Proof that defined equality of setoid functions is indeed equality
setoidFunctionEqualityIsEquality : (A, B: Setoid) -> IsEquality (SetoidFunction A B) (SetoidFunctionEquality A B)
setoidFunctionEqualityIsEquality
    A
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive reflB) (MkIsSymmetric symB) (MkIsTransittive transB)))
    = MkIsEquality
        (MkIsReflexive $ \f => SetoidFunctionRefl $ \x => reflB $ apply f x)
        (MkIsSymmetric $ \f, g, (SetoidFunctionRefl prf)
            => SetoidFunctionRefl $ \x => symB (apply f x) (apply g x) (prf x))
        (MkIsTransittive $ \f, g, h, (SetoidFunctionRefl left), (SetoidFunctionRefl right)
            => SetoidFunctionRefl $ \x => transB (apply f x) (apply g x) (apply h x) (left x) (right x))

||| Constructor for setoid of functions between two setoids
SetoidFunctionSetoid : (A, B: Setoid) -> Setoid
SetoidFunctionSetoid A B = MkSetoid
    (SetoidFunction A B)
    (SetoidFunctionEquality A B)
    (setoidFunctionEqualityIsEquality A B)

-- Proofs --

||| Proof that composition of SetoidFunctions is application of corresponding functions
setFunCompositionIsApplication : (A, B, C: Setoid)
    -> (f: SetoidFunction A B)
    -> (g: SetoidFunction B C)
    -> (x: Carrier A)
    -> Equal C (apply (setFunCompose A B C f g) x) (apply g $ apply f x)
setFunCompositionIsApplication
    _ _ (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    (MkSetoidFunction f _)
    (MkSetoidFunction g _)
    x = refl $ g $ f x

||| Proof that composition of SetoidFunctions is associative
setFunComposeIsAssociative : (A, B, C, D: Setoid) ->
    (f: SetoidFunction A B) -> (g: SetoidFunction B C) -> (h: SetoidFunction C D) ->
    SetoidFunctionEquality A D
        (setFunCompose A B D f (setFunCompose B C D g h))
        (setFunCompose A C D (setFunCompose A B C f g) h)
setFunComposeIsAssociative
    A B C D@(MkSetoid _ _ (MkIsEquality _ (MkIsSymmetric sym) (MkIsTransittive trans)))
    F G H = SetoidFunctionRefl $ \x => let
            -- step_1 : (G . F)(x) = g(f(x))
            step_1 = setFunCompositionIsApplication A B C F G x
            -- step_2 : H ((G . F)(x)) = h(g(f(x)))
            step_2 = congruence H (apply (setFunCompose A B C F G) $ x) (apply G (apply F x)) step_1
            -- step_3 :  (H . (G . F)) (x) = H ((G . F)(x)
            step_3 = setFunCompositionIsApplication A C D (setFunCompose A B C F G) H x
            -- step_4 : (H . (G . F)) (x) = h(g(f(x)))
            step_4 = trans
                (apply (setFunCompose A C D (setFunCompose A B C F G) H) x)
                (apply H $ apply (setFunCompose A B C F G) x)
                (apply H $ apply G $ apply F x)
                step_3 step_2
            -- step_5 : (H . G) (f(x)) = h(g(f(x)))
            step_5 = setFunCompositionIsApplication B C D G H (apply F x)
            -- step_6 : ((H . G) . F) (x) = (H . G) (f(x))
            step_6 = setFunCompositionIsApplication A B D F (setFunCompose B C D G H) x
            -- step_7 : ((H . G) . F) (x) = h(g(f(x)))
            step_7 = trans
                (apply (setFunCompose A B D F (setFunCompose B C D G H)) x)
                (apply (setFunCompose B C D G H) (apply F x))
                (apply H $ apply G $ apply F x)
                step_6 step_5
            -- qed : ((H . G) . F)(x) = (H . (G . F))(x)
            qed = trans
                (apply (setFunCompose A B D F (setFunCompose B C D G H)) x)
                (apply H $ apply G $ apply F x)
                (apply (setFunCompose A C D (setFunCompose A B C F G) H) x)
                step_7 $ sym
                    (apply (setFunCompose A C D (setFunCompose A B C F G) H) x)
                    (apply H $ apply G $ apply F x)
                    step_4
        in qed

||| Proof that identityFun is left identity for composition
setFunIdentityIsLeftIdentity : (A, B: Setoid) -> (f : SetoidFunction A B)
    -> SetoidFunctionEquality A B (setFunCompose A A B (setFunIdentity A) f) f
setFunIdentityIsLeftIdentity
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    B
    (MkSetoidFunction _ cong) =
        SetoidFunctionRefl $ \x => cong x x (refl x)

||| Proof that identityFun is right identity for composition
setFunIdentityIsRightIdentity : (A, B: Setoid) -> (f : SetoidFunction A B)
    -> SetoidFunctionEquality A B (setFunCompose A B B f (setFunIdentity B)) f
setFunIdentityIsRightIdentity
    A
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    (MkSetoidFunction apply _) =
        SetoidFunctionRefl $ \x => refl (apply x)
