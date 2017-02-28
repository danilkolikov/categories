module Utils

%access public export

infixr 1 >>>
infixr 1 &

||| Inverse function composition
(>>>) : {a, b, c: Type} -> (a -> b) -> (b -> c) -> (a -> c)
f >>> g = g . f

||| Inverse function application
(&) : {a, b: Type} -> a -> (a -> b) -> b
x & f = f x
