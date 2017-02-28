module Utils

%access public export

infixr 1 >>>
infixr 1 &

||| Inverse composition function
(>>>) : {a, b, c: Type} -> (a -> b) -> (b -> c) -> (a -> c)
f >>> g = g . f

||| Invers function application
(&) : {a, b: Type} -> a -> (a -> b) -> b
x & f = f x
