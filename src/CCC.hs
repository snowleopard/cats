{-# LANGUAGE GADTs #-}
module CCC where

-- Experimenting with compiling STLC to Closed Cartesian Categories.
-- See Conal Elliott's ICFP'17 paper "Compiling to Categories":
-- http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf
--
-- See also: "The categorical abstract machine" by Cousineau et al. (1987):
-- https://core.ac.uk/download/pdf/82453178.pdf

------------------------- Simply typed lambda-calculus -------------------------

-- | An expression of type @a@ in a typing context @c@.
--
-- Typing contexts are represented simply by tuples:
-- * ()     is the empty context.
-- * (c, a) is a context @c@ extended with a variable of type @a@.
data Expr c a where
    Var :: Index c a -> Expr c a
    Lit :: Int -> Expr () Int
    Lam :: Expr (c, a) b -> Expr c (a -> b)
    App :: Expr c (a -> b) -> Expr c a -> Expr c b
    Let :: Expr c a -> Expr (c, a) b -> Expr c b

-- | Index of a variable of type @a@ in a context @c@. The zero index 'Z'
-- corresponds to the variable occuring as the last element of the context.
-- Otherwise, we skip ('S') the last element and index into the rest of the
-- context.
data Index c a where
    Z ::              Index (c, a) a
    S :: Index c a -> Index (c, b) a

------------------------------ Example expressions -----------------------------

-- | The identity function.
exId :: Expr () (a -> a)
exId = Lam (Var Z)

-- | Constant @1@.
ex1 :: Expr () Int
ex1 = Lit 1

-- | Also constant @1@, but expressed as the application of the identity
-- function 'exId' to the constant 'ex1'.
exAppId1 :: Expr () Int
exAppId1 = App exId ex1

-- | The constant function, demonstrating variable indexing.
exConst :: Expr () (a -> b -> a)
exConst = Lam $ Lam $ Var (S Z)

-- | An open expression with functions @f :: b -> c@ and @g :: a -> b@ in the
-- context that computes their composition @f . g :: a -> c@.
exCompose :: Expr (((), a -> b), b -> c) (a -> c)
exCompose = Lam (App f (App g x))
  where
    x = Var Z
    f = Var (S Z)
    g = Var (S (S Z))

-------------------------- Closed Cartesian Categories -------------------------

-- | Expressions written in the language of Closed Cartesian Categories.
data CCC a b where
    -- Category
    Id    :: CCC a a
    (:.:) :: CCC b c -> CCC a b -> CCC a c
    -- Cartesian Category
    (:*:) :: CCC a b -> CCC a c -> CCC a (b, c)
    Fst   :: CCC (a, b) a
    Snd   :: CCC (a, b) b
    -- Terminal object
    Unit  :: CCC a ()
    Const :: Show a => a -> CCC () a -- Show needed for pretty-printing
    -- Closed Cartesian Category
    Apply   :: CCC (a -> b, a) b
    Curry   :: CCC (a, b) c -> CCC a (b -> c)
    Uncurry :: CCC a (b -> c) -> CCC (a, b) c

data UntypedCCC where
    U :: CCC a b -> UntypedCCC

instance Show UntypedCCC where
    showsPrec p (U ccc) = case ccc of
        Id        -> showString "id"
        f :.: g   -> showParen (p > 9) $ showsPrec 9 (U f)
                                       . showString " . "
                                       . showsPrec 9 (U g)
        f :*: g   -> showParen (p > 3) $ showsPrec 3 (U f)
                                       . showString " * "
                                       . showsPrec 3 (U g)
        Fst       -> showString "fst"
        Snd       -> showString "snd"
        Unit      -> showString "()"
        Const i   -> shows i
        Apply     -> showString "apply"
        Curry f   -> showParen (p >= 11) $ showString "curry "
                                         . showsPrec 11 (U f)
        Uncurry f -> showParen (p >= 11) $ showString "uncurry "
                                         . showsPrec 11 (U f)

-- | Pretty-print a 'CCC' expression.
pretty :: CCC a b -> String
pretty = show . U

----------------------------- Compiling STLC to CCC ----------------------------

-- | Compile a simply typed lambda calculus expression 'Expr' into 'CCC'.
compile :: Expr c a -> CCC c a
compile e = case e of
    Var Z     -> Snd
    Var (S v) -> compile (Var v) :.: Fst
    Lit i     -> Const i
    Lam e     -> Curry (compile e)
    App e1 e2 -> Apply :.: (compile e1 :*: compile e2)
    Let e1 e2 -> compile e2 :.: (Id :*: compile e1)
