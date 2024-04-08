{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingFunctor #-}

import Data.Void

data Logic t q =
  Truth t |
  And (Logic t q) (Logic t q) |
  Or (Logic t q) (Logic t q) |
  Not (Logic t q) |
  Implies (Logic t q) (Logic t q) |
  Proposition (Relation t) |
  Quantified q
  deriving (Eq, Functor)

true = Truth True
false = Truth False

class Variable v ⇒ Quantifier v q where
  type Element q
  newVar :: v
  nextVar :: v → v

data FirstOrder =
  Ɐ :: Formula 1 f ⇒ (Element → f) → FirstOrder
  Ǝ :: Formula 1 f ⇒ (Element → f) → FirstOrder

data HigherOrder (n :: Nat) where
  Lift1 :: (1 <= n) ⇒ FirstOrder → HigherOrder n
  Lift :: (m <= n) ⇒ HigherOrder m → HigherOrder n
  Ɐ' :: Formula n f ⇒ (Argument n → f) → HigherOrder n
  Ǝ' :: Formula n f ⇒ (Argument n → f) → HigherOrder n

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

instance (Liftable q p, Sentence q s) ⇒ Sentence p s where
  quantified sentence = fmap lift (quantified sentence :: Logic t q)

instance (Sentence (HigherOrder m) s, m <= n) ⇒ Sentence (HigherOrder n) s where
  quantified sentence = fmap Lift (quantified sentence :: Logic t (HigherOrder m))

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
