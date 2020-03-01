{-# LANGUAGE DefaultSignatures, GADTs, LambdaCase, ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes, TypeApplications, TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
module Matrix where

-- Experimenting with an inductive matrix data type that forms a category.
--
-- This experiment is heavily inspired by the LAoP matrix manipulation library
-- by Armando Santos (http://hackage.haskell.org/package/laop) that defines the
-- following data type:
--
-- data Matrix e c r where
--     Empty :: Matrix e Void Void
--     One   :: e -> Matrix e () ()
--     Join  :: Matrix e a r -> Matrix e b r -> Matrix e (Either a b) r
--     Fork  :: Matrix e c a -> Matrix e c b -> Matrix e c (Either a b)
--
-- By making the data type a bit more complex we get a lawful Category instance.
--------------------------------------------------------------------------------
import Control.Category
import Data.Bool
import Data.Functor.Contravariant
import Data.Kind
import Data.Void
import Prelude hiding (id, (.), fst, snd, curry, uncurry)

import qualified Data.List as List
import qualified Prelude

--------------------------------- Construction ---------------------------------
data Matrix e a b where
    Identity :: Matrix e a a
    Zero     :: Matrix e a b
    Lift     :: (e -> e -> e) -> Matrix e a b -> Matrix e a b -> Matrix e a b
    Join     :: Matrix e a c -> Matrix e b c -> Matrix e (Either a b) c
    Fork     :: Matrix e a b -> Matrix e a c -> Matrix e a (Either b c)

empty :: Matrix e Void Void
empty = Identity

emap :: (e -> e) -> Matrix e a b -> Matrix e a b
emap f = Lift (const f) Zero

scale :: Num e => e -> Matrix e a b -> Matrix e a b
scale e = emap (e*)

one :: Num e => e -> Matrix e () ()
one e = scale e Identity

constant :: e -> Matrix e a b
constant e = emap (const e) Zero

-- Better switch to using a custom type class Field without the signum nonsense
instance Num e => Num (Matrix e a b) where
    fromInteger = constant . fromInteger
    (+)         = Lift (+)
    (-)         = Lift (-)
    (*)         = Lift (*)
    abs         = emap abs
    negate      = emap negate
    signum      = error "No sensible definition"

instance Num e => Category (Matrix e) where
    id = Identity

    Identity   . x          = x
    x          . Identity   = x
    Zero       . _          = Zero
    _          . Zero       = Zero
    Lift f x y . z          = Lift f (x . z) (y . z)
    x          . Lift f y z = Lift f (x . y) (x . z)
    Join w x   . Fork y z   = (w . y) + (x . z)
    Fork x y   . z          = Fork (x . z) (y . z)
    x          . Join y z   = Join (x . y) (x . z)

-- Adapted from https://hackage.haskell.org/package/categories
class Category k => Cartesian k where
    type Product k :: Type -> Type -> Type
    fst   :: Product k a b `k` a
    snd   :: Product k a b `k` b
    (&&&) :: (a `k` b) -> (a `k` c) -> a `k` Product k b c

instance Cartesian (->) where
    type Product (->) = (,)
    fst = Prelude.fst
    snd = Prelude.snd
    (f &&& g) a = (f a, g a)

instance Num e => Cartesian (Matrix e) where
    type Product (Matrix e) = Either
    fst   = Join Identity Zero
    snd   = Join Zero Identity
    (&&&) = Fork

-- A standard construction for any Cartesian category.
bimapProduct :: Cartesian k => k a c -> k b d -> Product k a b `k` Product k c d
bimapProduct f g = (f . fst) &&& (g . snd)

class Category k => CoCartesian k where
    type Sum k :: Type -> Type -> Type
    inl   :: a `k` Sum k a b
    inr   :: b `k` Sum k a b
    (|||) :: k a c -> k b c -> Sum k a b `k` c

-- A standard construction for any CoCartesian category.
bimapSum :: CoCartesian k => k a c -> k b d -> Sum k a b `k` Sum k c d
bimapSum f g = (inl . f) ||| (inr . g)

-- For free!
(-|-) :: Num e => Matrix e a b -> Matrix e c d -> Matrix e (Either a c) (Either b d)
(-|-) = bimapSum

infixl 5 -|-

instance CoCartesian (->) where
    type Sum (->) = Either
    inl = Left
    inr = Right
    (f ||| _) (Left  a) = f a
    (_ ||| g) (Right a) = g a

instance Num e => CoCartesian (Matrix e) where
    type Sum (Matrix e) = Either
    inl = Fork Identity Zero
    inr = Fork Zero Identity
    (|||) = Join

class (Cartesian k, CoCartesian k) => Distributive k where
    distribute :: Product k a (Sum k b c) `k` Sum k (Product k a b) (Product k a c)

instance Distributive (->) where
    distribute (a, Left  b) = Left  (a, b)
    distribute (a, Right c) = Right (a, c)

instance Num e => Distributive (Matrix e) where
    distribute = Fork (id -|- fst) (id -|- snd)

transpose :: Matrix e a b -> Matrix e b a
transpose m = case m of
    Identity   -> Identity
    Zero       -> Zero
    Lift f x y -> Lift f (transpose x) (transpose y)
    Join x y   -> Fork (transpose x) (transpose y)
    Fork x y   -> Join (transpose x) (transpose y)

select :: Num e => Matrix e a (Either b c) -> Matrix e b c -> Matrix e a c
select x y = Join y id . x

class Construct a where
    row :: Num e => Vector e a -> Matrix e a ()

    linearMap :: (Construct b, Num e) => LinearMap e a b -> Matrix e a b

instance Construct Void where
    linearMap = const Zero
    row = const Zero

instance Construct () where
    row v = one (at v ())

    linearMap m = column (m 1)

instance (Construct a, Construct b) => Construct (Either a b) where
    row v = row (Left >$< v) ||| row (Right >$< v)

    linearMap m = linearMap (m . padRight) ||| linearMap (m . padLeft)

column :: (Construct a, Num e) => Vector e a -> Matrix e () a
column = transpose . row

function :: (Construct a, Construct b, Enumerable a, Num e) => (a -> b -> e) -> Matrix e a b
function f = linearMap $ \v -> Vector $ \b -> dot v $ Vector $ \a -> f a b

----------------------------------- Semantics ----------------------------------
newtype Vector e a = Vector { at :: a -> e }

instance Contravariant (Vector e) where
    contramap f (Vector g) = Vector (g . f)

instance Num e => Num (Vector e a) where
    fromInteger = Vector . const . fromInteger

    (+)    = liftV2 (+)
    (-)    = liftV2 (-)
    (*)    = liftV2 (*)
    abs    = liftV1 abs
    negate = liftV1 negate
    signum = error "No sensible definition"

liftV1 :: (e -> e) -> Vector e a -> Vector e a
liftV1 f x = Vector (\a -> f (at x a))

liftV2 :: (e -> e -> e) -> Vector e a -> Vector e a -> Vector e a
liftV2 f x y = Vector (\a -> f (at x a) (at y a))

-- Semantics of Matrix e a b
type LinearMap e a b = Vector e a -> Vector e b

semantics :: Num e => Matrix e a b -> LinearMap e a b
semantics m = case m of
    Identity   -> id
    Zero       -> const 0
    Lift f x y -> \v -> liftV2 f (semantics x v) (semantics y v)
    Join x y   -> \v -> semantics x (Left >$< v) + semantics y (Right >$< v)
    Fork x y   -> \v -> Vector $ either (at (semantics x v)) (at (semantics y v))

padLeft :: Num e => Vector e b -> Vector e (Either a b)
padLeft v = Vector $ \case Left _  -> 0
                           Right b -> at v b

padRight :: Num e => Vector e a -> Vector e (Either a b)
padRight v = Vector $ \case Left a  -> at v a
                            Right _ -> 0

dot :: (Num e, Enumerable a) => Vector e a -> Vector e a -> e
dot x y = sum [ at x a * at y a | a <- enumerate ]

-------------------------------- Deconstruction --------------------------------
class Enumerable a where
    enumerate :: [a]
    default enumerate :: Enum a => [a]
    enumerate = enumFrom (toEnum 0)

instance Enumerable Void where
    enumerate = []

-- 1, 2, 3...
instance Enumerable ()
instance Enumerable Bool
instance Enumerable Ordering

instance (Enumerable a, Enumerable b) => Enumerable (Either a b) where
    enumerate = (Left <$> enumerate) ++ (Right <$> enumerate)

instance (Enumerable a, Enumerable b) => Enumerable (a, b) where
    enumerate = [ (a, b) | a <- enumerate, b <- enumerate ]

basis :: (Enumerable a, Eq a, Num e) => [Vector e a]
basis = [ Vector (bool 0 1 . (==a)) | a <- enumerate ]

toLists :: (Enumerable a, Enumerable b, Eq a, Num e) => Matrix e a b -> [[e]]
toLists m = List.transpose
    [ [ at r i | i <- enumerate ] | c <- basis, let r = semantics m c ]

dump :: (Enumerable a, Enumerable b, Eq a, Num e, Show e) => Matrix e a b -> IO ()
dump = mapM_ print . toLists

------------------------------- Normalised types -------------------------------
class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

instance Profunctor (->) where
    dimap f g h = g . h . f

class Construct (Norm a) => ConstructNorm a where
    type Norm a
    toNorm :: a -> Norm a
    fromNorm :: Norm a -> a

instance ConstructNorm () where
    type Norm () = ()
    toNorm = Prelude.id
    fromNorm = Prelude.id

instance (ConstructNorm a, ConstructNorm b) => ConstructNorm (Either a b) where
    type Norm (Either a b) = Either (Norm a) (Norm b)
    toNorm = either (Left . toNorm) (Right . toNorm)
    fromNorm = either (Left . fromNorm) (Right . fromNorm)

-- Instance for other data types can be obtained mechanically using Generics
instance ConstructNorm Bool where
    type Norm Bool = Either () ()
    toNorm = bool (Left ()) (Right ())
    fromNorm = either (const False) (const True)

rowN :: (ConstructNorm a, Num e) => Vector e a -> Matrix e (Norm a) ()
rowN = row . contramap fromNorm

linearMapN :: (ConstructNorm a, ConstructNorm b, Num e)
           => LinearMap e a b -> Matrix e (Norm a) (Norm b)
linearMapN = linearMap . dimap (contramap toNorm) (contramap fromNorm)

columnN :: (ConstructNorm a, Num e) => Vector e a -> Matrix e () (Norm a)
columnN = transpose . rowN

functionN :: (ConstructNorm a, ConstructNorm b, Enumerable a, Num e)
          => (a -> b -> e) -> Matrix e (Norm a) (Norm b)
functionN f = linearMapN $ \v -> Vector $ \b -> dot v $ Vector $ \a -> f a b