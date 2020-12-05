{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses, GADTs, LambdaCase, ScopedTypeVariables #-}
module Tree where

import Control.Category
import Prelude hiding (id, (.), fst, snd, curry, uncurry, last)
import Data.Monoid (Sum (..))

-- | "Categorical binary trees" storing elements 'e' in the leafs and cached
-- measures 'm' in every internal node. This construction is inspired by finger
-- trees but generalises the idea from monoidal to categorical measures. We use
-- unbalanced trees here only for the sake of simplicity.
data Tree e m a b where
    Nil :: Tree e m a a
    Tip :: e a b -> Tree e m a b
    Bin :: m a b -> Tree e m a x -> Tree e m x b -> Tree e m a b

class Category m => Measured e m where
    measure :: e a b -> m a b

measureTree :: Measured e m => Tree e m a b -> m a b
measureTree = \case
    Nil       -> id
    Tip e     -> measure e
    Bin m _ _ -> m

empty :: Tree e m a a
empty = Nil

singleton :: e a b -> Tree e m a b
singleton = Tip

append :: Measured e m => Tree e m a x -> Tree e m x b -> Tree e m a b
append x y = Bin (measureTree x >>> measureTree y) x y

instance Measured e m => Category (Tree e m) where
    id  = empty
    (.) = flip append

data First e a b where
    NoFirst :: First e a a
    First   :: e a x -> First e a b

instance Category (First e) where
    id = NoFirst

    x . NoFirst = x
    _ . First e = First e

first :: Tree e m a b -> First e a b
first = \case
    Nil       -> NoFirst
    Tip e     -> First e
    Bin _ l r -> first l >>> first r

data ViewL e m a b where
    NoneL :: ViewL e m a a
    SomeL :: e a x -> Tree e m x b -> ViewL e m a b

viewL :: Measured e m => Tree e m a b -> ViewL e m a b
viewL = \case
    Nil -> NoneL
    Tip e -> SomeL e Nil
    Bin _ l r -> case viewL l of
        NoneL -> viewL r
        SomeL e t -> SomeL e (t >>> r)

data Last e a b where
    NoLast :: Last e a a
    Last   :: e x b -> Last e a b

instance Category (Last e) where
    id = NoLast

    NoLast . x = x
    Last e . _ = Last e

last :: Tree e m a b -> Last e a b
last = \case
    Nil       -> NoLast
    Tip e     -> Last e
    Bin _ l r -> last l >>> last r

data ViewR e m a b where
    NoneR :: ViewR e m a a
    SomeR :: Tree e m a x -> e x b -> ViewR e m a b

viewR :: Measured e m => Tree e m a b -> ViewR e m a b
viewR = \case
    Nil -> NoneR
    Tip e -> SomeR Nil e
    Bin _ l r -> case viewR r of
        NoneR -> viewR l
        SomeR t e -> SomeR (l >>> t) e

data Split e m a b where
    Split :: Tree e m a x -> Tree e m x b -> Split e m a b

split :: forall e m a b. Measured e m => (forall x. m a x -> Bool) -> Tree e m a b -> Split e m a b
split p x = go id x
  where
    go :: m a x -> Tree e m x y -> Split e m x y
    go m x = case x of
        Nil       -> Split Nil Nil
        Tip e     -> if p (m >>> measure e) then Split Nil x else Split x Nil
        Bin _ l r -> let ml = m >>> measureTree l in
                     if p ml
                       then case go m  l of Split x y -> Split x (y >>> r)
                       else case go ml r of Split x y -> Split (l >>> x) y

---------------------- Type-aligned arrays: S-expressions ----------------------

data Zero
data Succ a

data Token a b where
    Atom    :: String -> Token a a
    Opening :: Token a (Succ a)
    Closing :: Token (Succ a) a

type Count = One (Sum Int)

instance Measured Token Count where
    measure _ = One (Sum 1)

-- Exprpessions of type 'forall a. Expr a a' are balanced
type Expr a b = Tree Token Count a b

data Some e where
    Some :: First e x y -> Some e

get :: Expr a b -> Int -> Some Token
get expr index = case split (\(One (Sum m)) -> m > index) expr of
    Split _l r -> Some (first r)

update :: Expr a b -> Int -> (forall x y. Token x y -> Expr x y) -> Expr a b
update expr index f = case split (\(One (Sum m)) -> m > index) expr of
    Split l r -> case viewL r of
        NoneL     -> l
        SomeL e t -> l >>> f e >>> t

atom :: String -> Expr a a
atom = singleton . Atom

opening :: Expr a (Succ a)
opening = singleton Opening

closing :: Expr (Succ a) a
closing = singleton Closing

exampleAtoms :: [String] -> Expr a a
exampleAtoms ss = opening >>> contents >>> closing
  where
    contents = foldr (append . atom) empty ss

exampleBalanced :: Expr a a
exampleBalanced = opening >>> closing

exampleUnbalanced :: Expr (Succ (Succ a)) (Succ a)
exampleUnbalanced = closing >>> closing >>> opening

-- Given a string, try to split it into a prefix and a suffix so that the prefix
-- starts with an opening bracket and is balanced. The outer pair of brackets of
-- the prefix is removed.
breakBalanced :: String -> Maybe (String, String)
breakBalanced [] = Nothing
breakBalanced (c : s)
    | c /= '('  = Nothing
    | otherwise = go 1 [] s
        where
          go :: Int -> String -> String -> Maybe (String, String)
          go 0 prefix suffix  = Just (reverse (tail prefix), suffix) -- safe
          go _ _      []      = Nothing
          go b prefix (c : s) =
                let newBalance | c == '('  = b + 1
                               | c == ')'  = b - 1
                               | otherwise = b
                in go newBalance (c : prefix) s

parseBalanced :: String -> Maybe (Expr a a)
parseBalanced [] = Just empty
parseBalanced s@(c : _)
    | c == ')'  = Nothing
    | c == '('  = do
        (prefix, suffix) <- breakBalanced s
        prefix <- parseBalanced prefix
        suffix <- parseBalanced suffix
        return $ opening >>> prefix >>> closing >>> suffix
    | otherwise = let (prefix, suffix) = break (`elem` "()") s in
                  (atom prefix >>>) <$> parseBalanced suffix

shiftToken :: Token a b -> Token (Succ a) (Succ b)
shiftToken (Atom s) = Atom s
shiftToken Opening  = Opening
shiftToken Closing  = Closing

shiftExpr :: Expr a b -> Expr (Succ a) (Succ b)
shiftExpr Nil         = Nil
shiftExpr (Tip e)     = Tip (shiftToken e)
shiftExpr (Bin _ x y) = append (shiftExpr x) (shiftExpr y)

updateS :: Expr a b -> Int -> (forall x y. Token x y -> Expr x (Succ y)) -> Maybe (Expr a (Succ b))
updateS expr index f = case split (\(One (Sum m)) -> m > index) expr of
    Split l r -> case viewL r of
        NoneL     -> Nothing
        SomeL e t -> Just $ l >>> f e >>> shiftExpr t

----------------------- Wrapping a monoid into a category ----------------------

newtype One m a b = One { getOne :: m }

instance Monoid m => Category (One m) where
    id = One mempty
    One x . One y = One (x <> y)

-------------------------------- Bicyclic monoid -------------------------------

data Bicyclic = Bicyclic Int Int

instance Semigroup Bicyclic where
    Bicyclic c1 o1 <> Bicyclic c2 o2 = let matched = min o1 c2 in
        Bicyclic (c1 + c2 - matched) (o1 + o2 - matched)

instance Monoid Bicyclic where
    mempty = Bicyclic 0 0

-- TODO: Add example from the paper
-- "Reflection without Remorse" by Atze van der Ploeg and Oleg Kiselyov.
