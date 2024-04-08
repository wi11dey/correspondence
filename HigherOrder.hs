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
  Ɐ' :: Formula n f ⇒ (Argument n → f) → HigherOrder n
  Ǝ' :: Formula n f ⇒ (Argument n → f) → HigherOrder n

type Order (n :: Nat) = Formula n f ⇒ (Argument n → f) → HigherOrder n

type family HigherOrderLogic t (n :: Nat) where
  HigherOrderLogic 0 = Logic t Void
  HigherOrderLogic 1 = Logic t FirstOrder
  HigherOrderLogic n = Logic t (HigherOrder n)

class Functor s ⇒ Sentence q s where
  quantified :: s → Logic t q

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
