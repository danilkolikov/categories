module SetoidFunction

import public Data.Morphisms
import public Setoid

%access public export

||| Extensional Function between two Setoids
record SetoidFunction (a: Setoid) (b: Setoid) where
    constructor MkSetoidFunction
    ||| Application of function
    apply : Carrier a -> Carrier b
    ||| Proof that if x == y  in a that f(x) == f(y) in b
    congruence : (x, y: Carrier a) -> Equal a x y -> Equal b (apply x) (apply y)

||| Composition of setoid functions is setoid function
setFunCompose : (a, b, c: Setoid) -> SetoidFunction a b -> SetoidFunction b c -> SetoidFunction a c
setFunCompose _ _ _ (MkSetoidFunction f congF) (MkSetoidFunction g congG) = MkSetoidFunction
    (g . f)
    (\x, y, equal => congG (f x) (f y) $ congF x y equal)

||| Identity setoid function
setFunIdentity : (a: Setoid) -> SetoidFunction a a
setFunIdentity _ = MkSetoidFunction
    id
    (\x, y, equal => equal)

||| SetoidFunction equality - two functions are equal if they are equal for any argument
data SetoidFunctionEquality : (a, b: Setoid) -> (f, g: SetoidFunction a b) -> Type where
    SetoidFunctionRefl : {a, b: Setoid}
                    -> {f, g: SetoidFunction a b}
                    -> ((x: Carrier a) -> Equal b (apply f x) (apply g x))
                    -> SetoidFunctionEquality a b f g

||| Proof that defined equality of setoid functions is indeed equality
setoidFunctionEqualityIsEquality : (a, b: Setoid) -> IsEquality (SetoidFunction a b) (SetoidFunctionEquality a b)
setoidFunctionEqualityIsEquality
    a
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive reflB) (MkIsSymmetric symB) (MkIsTransittive transB)))
    = MkIsEquality
        (MkIsReflexive $ \f => SetoidFunctionRefl $ \x => reflB $ apply f x)
        (MkIsSymmetric $ \f, g, (SetoidFunctionRefl prf)
            => SetoidFunctionRefl $ \x => symB (apply f x) (apply g x) (prf x))
        (MkIsTransittive $ \f, g, h, (SetoidFunctionRefl left), (SetoidFunctionRefl right)
            => SetoidFunctionRefl $ \x => transB (apply f x) (apply g x) (apply h x) (left x) (right x))

||| Constructor for setoid of functions between two setoids
SetoidFunctionSetoid : (a, b: Setoid) -> Setoid
SetoidFunctionSetoid a b = MkSetoid
    (SetoidFunction a b)
    (SetoidFunctionEquality a b)
    (setoidFunctionEqualityIsEquality a b)

-- Proofs --

||| Proof that composition of SetoidFunctions is application of corresponding functions
setFunCompositionIsApplication : (a, b, c: Setoid)
    -> (f: SetoidFunction a b)
    -> (g: SetoidFunction b c)
    -> (x: Carrier a)
    -> Equal c (apply (setFunCompose a b c f g) x) (apply g $ apply f x)
setFunCompositionIsApplication
    _ _ (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    (MkSetoidFunction f _)
    (MkSetoidFunction g _)
    x = refl $ g $ f x

||| Proof that composition of SetoidFunctions is associative
setFunComposeIsAssociative : (a, b, c, d: Setoid) ->
    (f: SetoidFunction a b) -> (g: SetoidFunction b c) -> (h: SetoidFunction c d) ->
    SetoidFunctionEquality a d
        (setFunCompose a b d f (setFunCompose b c d g h))
        (setFunCompose a c d (setFunCompose a b c f g) h)
setFunComposeIsAssociative
    a b c d@(MkSetoid _ _ (MkIsEquality _ (MkIsSymmetric sym) (MkIsTransittive trans)))
    f g h = SetoidFunctionRefl $ \x => let
            -- step_1 : (g . f)(x) = g(f(x))
            step_1 = setFunCompositionIsApplication a b c f g x
            -- step_2 : h ((g . f)(x)) = h(g(f(x)))
            step_2 = congruence h (apply (setFunCompose a b c f g) $ x) (apply g (apply f x)) step_1
            -- step_3 :  (h . (g . f)) (x) = h ((g . f)(x)
            step_3 = setFunCompositionIsApplication a c d (setFunCompose a b c f g) h x
            -- step_4 : (h . (g . f)) (x) = h(g(f(x)))
            step_4 = trans
                (apply (setFunCompose a c d (setFunCompose a b c f g) h) x)
                (apply h $ apply (setFunCompose a b c f g) x)
                (apply h $ apply g $ apply f x)
                step_3 step_2
            -- step_5 : (h . g) (f(x)) = h(g(f(x)))
            step_5 = setFunCompositionIsApplication b c d g h (apply f x)
            -- step_6 : ((h . g) . f) (x) = (h . g) (f(x))
            step_6 = setFunCompositionIsApplication a b d f (setFunCompose b c d g h) x
            -- step_7 : ((h . g) . f) (x) = h(g(f(x)))
            step_7 = trans
                (apply (setFunCompose a b d f (setFunCompose b c d g h)) x)
                (apply (setFunCompose b c d g h) (apply f x))
                (apply h $ apply g $ apply f x)
                step_6 step_5
            -- qed : ((h . g) . f)(x) = (h . (g . f))(x)
            qed = trans
                (apply (setFunCompose a b d f (setFunCompose b c d g h)) x)
                (apply h $ apply g $ apply f x)
                (apply (setFunCompose a c d (setFunCompose a b c f g) h) x)
                step_7 $ sym
                    (apply (setFunCompose a c d (setFunCompose a b c f g) h) x)
                    (apply h $ apply g $ apply f x)
                    step_4
        in qed

||| Proof that identityFun is left identity for composition
setFunIdentityIsLeftIdentity : (a, b: Setoid) -> (f : SetoidFunction a b)
    -> SetoidFunctionEquality a b (setFunCompose a a b (setFunIdentity a) f) f
setFunIdentityIsLeftIdentity
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    b
    (MkSetoidFunction _ cong) =
        SetoidFunctionRefl $ \x => cong x x (refl x)

||| Proof that identityFun is right identity for composition
setFunIdentityIsRightIdentity : (a, b: Setoid) -> (f : SetoidFunction a b)
    -> SetoidFunctionEquality a b (setFunCompose a b b f (setFunIdentity b)) f
setFunIdentityIsRightIdentity
    a
    (MkSetoid _ _ (MkIsEquality (MkIsReflexive refl) _ _))
    (MkSetoidFunction apply _) =
        SetoidFunctionRefl $ \x => refl (apply x)
