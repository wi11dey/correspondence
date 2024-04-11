{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingFunctor #-}

import Data.Coerce
import Data.Void
import Data.Proxy
import Control.Monad

class Lattice t (l :: * → *) where
  fromTruth :: t → l a
  (∧) :: l a → l a → l a
  (∨) :: l a → l a → l a

class Lattice t l ⇒ ComplementedLattice t l where
  complement :: l a → l a

data PrefixComplement

(¬) :: CompletementedLattice t l ⇒ PrefixComplement → l → l

instance ComplementedLattice t l ⇒ ComplementedLattice t (PrefixComplement → l)

-- (Logic :: (* → *) → * → *) creates a metalanguage as a function of the underlying latice and quantifiers
data Logic l q =
  Connective (l (Logic l q))
  Proposition Relation |
  Quantified q
  deriving (Eq, Functor)

true = Truth True
false = Truth False

class (Eq e, Show v) ⇒ Variable q v where
  zeroVar :: v
  nextVar :: v → v

class (Eq e, Show e) ⇒ Element q e

instance Variable q v ⇒ Element q v

instance (Num e) ⇒ Element FirstOrder v

instance Element (HigherOrder n) (Set (n - 1) a)

type family Set (n :: Nat) a where
  Set 0 = ()
  Set 1 = [a]
  Set n = [Set (n - 1) a]

newtype Constant = Constant String
  deriving Eq

instance IsLabel (c :: Symbol) Constant where
  fromLabel = Constant $ symbolVal (Proxy :: Proxy c)

instance Show Constant where
  show = ('#':) . quote . coerce
    where
      quote c
        | isIdentifier c = c
        | otherwise = '"':(c ++ "\"")

      isIdentifier _ = False
      isIdentifier ('_':rest) = all isIdentifierChar rest
      isIdentifier (start:rest)
        | isLower start = all isIdentifierChar rest

      isIdentifierChar _ = False
      isIdentifierChar '_' = True
      isIdentifierChar '\'' = True
      isIdentifierChar c
        | isAlpha c = True
        | isDigit c = True

instance Element FirstOrder Constant

newtype Variable1 = Variable1 Int

instance Variable FirstOrder Variable1 where
  zeroVar = coerce 0
  nextVar = coerce . succ . coerce

data Element (n :: Nat) =
  Variable Int |
  Constant String

class Variable v ⇒ Quantifier v q where
  type Element q
  newVar :: v
  nextVar :: v → v

type ZerothOrder = Void

data FirstOrder =
  Ɐ :: Formula (Element 1) f ⇒ (Element 1 → f) → FirstOrder
  Ǝ :: Formula (Element 1) f ⇒ (Element 1 → f) → FirstOrder

data HigherOrder (n :: Nat) where
  Lift1 :: (1 <= n) ⇒ FirstOrder → HigherOrder n
  Lift :: (m <= n) ⇒ HigherOrder m → HigherOrder n
  Ɐ' :: Formula (Element n) f ⇒ (Element n → f) → HigherOrder n
  Ǝ' :: Formula (Element n) f ⇒ (Element n → f) → HigherOrder n

class Liftable a b where
  lift :: a → b

-- An first-order sentence is also an nth-order sentence whenever 1 ≤ n
instance (1 <= n) ⇒ Liftable FirstOrder (HigherOrder n) where
  lift = Lift1

-- An mth-order sentence is also an nth-order sentence whenever m ≤ n
instance (m <= n) ⇒ Liftable (HigherOrder m) (HigherOrder n) where
  lift = Lift

type Order (n :: Nat) = Formula n f ⇒ (Argument n → f) → HigherOrder n

type family HigherOrderLogic t (n :: Nat) where
  HigherOrderLogic 0 = Logic t Void
  HigherOrderLogic 1 = Logic t FirstOrder
  HigherOrderLogic n = Logic t (HigherOrder n)

class Functor s ⇒ Sentence q s where
  quantified :: s → Logic t q

instance (Sentence q s, Liftable q p) ⇒ Sentence p s where
  quantified sentence = fmap lift (quantified sentence :: Logic t q)

instance Sentence q (Logic t q) where
  quantified = id

instance Functor q ⇒ Sentence q q where
  quantified = Quantified

class (Sentence q s, Functor f) ⇒ Formula s f where
  free :: f → s
  increment :: f → f

instance Sentence q s ⇒ Formula s s where
  free = const id

  increment (a `And` b) = And `on` increment
  increment (a `Or` b) = Or `on` increment
  increment (Not a) = Not $ increment a
  increment (Ɐ formula) = Ɐ $ increment formula
  increment (Ǝ formula) = Ǝ $ increment formula
  increment = id

  fmap = id

instance (Sentence q s, Formula s f) ⇒ Formula (q → f) where
  free formula =
    free
    $ increment
    $ formula
    $ Variable
    $ Symbol 0

  increment formula (Variable (Symbol i)) =
    formula
    $ Variable
    $ Symbol
    $ succ i
  increment = id

  fmap = fix ((.) .)

class Variable v where
  anyVar :: v
  nextVar :: v

data Prefix = Prefix

(¬) :: Sentence q s ⇒ () → s → s
(¬) = const $ Not . quantified

instance Sentence q s ⇒ Sentence q (() → s) where
  quantified = fix (. ($ ()))

(∧) :: Sentence q s ⇒ s → s → s

names :: [String] → [String]
names = join bfs where
  bfs letters q = q ++ bfs letters ((++) <$> letters <*> q)

instance Show (Element 0) where
  show = const "_"

name :: [Char] → Int → String
name = (!!) . names . map return

instance Show (Element 1) where show (Variable i) = name ['𝘢'..'𝘻'] i
instance Show (Element 2) where show (Variable i) = name ['𝗮'..'𝘇'] i
instance Show (Element 3) where show (Variable i) = name ['𝙖'..'𝙯'] i
instance Show (Element 4) where show (Variable i) = name ['𝘈'..'𝘡'] i
instance Show (Element 5) where show (Variable i) = name ['𝘈'..'𝘡'] i

subscript :: Int → String
subscript =
  (. show)
  $ map
  $ (['₀'..'₉'] !!)
  . subtract (fromEnum '0')
  . fromEnum

instance Show (Element n) where
  show (Constant s) = s
  show (Variable i) =
    (!! i)
    $ map (++ subscript order)
    $ names
    $ map return ['A'..'Z']
    where order = natValue (Proxy :: Proxy n)
