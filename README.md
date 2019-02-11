# Musings on category theory

Nothing special, just trying to make sense of various papers and ideas involving
Category Theory.

## Compiling to Categories

Experimenting with compiling STLC to Closed Cartesian Categories.
See Conal Elliott's ICFP'17 paper
[Compiling to Categories](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf).

Source: https://github.com/snowleopard/cats/blob/master/src/CCC.hs.

An example `ghci` session:
```haskell
λ> k = Lam $ Lam $ Var (S Z)
λ> :t k
k :: Expr c (a1 -> a2 -> a1)
λ> :t compile k
compile k :: CCC c (a1 -> a2 -> a1)
λ> pretty (compile k)
"curry (curry (snd . fst))"
```
