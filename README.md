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

## Matrix category

Experimenting with an inductive matrix data type that forms a category.

Source: https://github.com/snowleopard/cats/blob/master/src/Matrix.hs.

An example `ghci` session:
```haskell
λ> m = (singleton 1 ||| singleton 2) &&& (singleton 3 ||| singleton (4 :: Int))
λ> dump m
[1,2]
[3,4]
λ> dump (transpose m)
[1,3]
[2,4]
λ> dump (m . transpose m)
[5,11]
[11,25]
λ> dump ((m . transpose m) ||| id)
[5,11,1,0]
[11,25,0,1]
λ> dump $ functionN (\x y -> bool 0 (1 :: Int) (x || y))
[0,1]
[1,1]
λ> dump $ functionN (\x y -> x && y)
[False,False]
[False,True]
```
