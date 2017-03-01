# Category Theory & Algebra

Attempt to formalize category theory and algebra using Idris language
Contains definition of

- Algebraic structures - Semigroup, Monoid, Semiring, ...
- Setoids - Natural numbers, built-in setoids, extensional functions
- Properties of relations and operations
- Category - Discrete, Monoids, PreOrder, Setoids
- Functor (Co- and Contra-variant)
- Some examples

## Installation & Usage

To install `categories` package, you should:

1. Clone repository to folder
2. Run `idris --install categories.ipkg`

To use proofs and types from `categories` in files import them as default modules and start Idris with command
```
idris -p categories %FILE_NAME%
```
To use modules from  `categories` in REPL, import them using `:module` command
