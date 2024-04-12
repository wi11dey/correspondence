{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}

import Control.Monad
import Control.Monad.Wrapper
import Data.Function
import Data.Coerce
import GHC.TypeLits

data Relation = Relation {
  name :: String,
  fixity :: Fixity,
  precedence :: Int,
  associativity :: Associativity,
  arguments :: [Element]
  }

instance Ord Relation where
  compare = compare . name

data Associativity = LeftAssociative | RightAssociative | NonAssociative

data Fixity = Prefix | Infix | Postfix

class Show r ⇒ RelationType r
  chain :: Wrapper Sentence Relation → r

instance RelationType Relation where
  chain = flip coerce \relation@(Relation { arguments }) →
    relation { arguments = reverse arguments }

instance RelationType Sentence where
  chain = Proposition . (chain :: _ → Relation)

instance (Argument a, RelationType r) ⇒ RelationType (a → r) where
  chain current arg = chain do
    relation@(Relation { previousArguments }) ← current
    element ← wrap arg
    return relation { arguments = element:previousArguments }

relation :: RelationType r ⇒ String → r
relation name = chain $ return $ Relation {
  name,
  fixity = Prefix,
  precedence = 10,
  associativity = LeftAssociative,
  arguments = []
  }

class Argument a where
  wrap :: a → Wrapper Sentence Element

instance Argument Element where
  wrap = return

-- e.g. a < b < c
instance Argument Relation where
  wrap relation@(Relation { arguments }) = Wrapper \next →
    Proposition relation ∧ next (last arguments)

-- e.g. a + b + c = 2
instance Argument (Arity 1) where
  wrap f = Wrapper \next →
    Ǝ\a → f a ∧ next a

type family Arity (arity :: Nat) where
  Arity 0 = Sentence
  Arity arity = Argument a ⇒ a → Arity (arity - 1)

unwrap :: Wrapper Sentence Sentence → Sentence
unwrap = flip coerce (const true)

(≡) :: Arity 2
(≡) = ((unwrap . liftM Proposition) .)
  . (liftM2 Equals `on` wrap)

data Element =
  Variable Symbol |
  Constant String

(>) = relation ">" :: Arity 2
(+) = infixFunction "+" LeftAssociative 3

prefixRelation :: String → Arity 1
prefixRelation name = withElement \element → Relation {
  name,
  fixity = Prefix,
  precedence = 0,
  associativity = LeftAssociative,
  arguments = [element]
  }
infixRelation :: String → Associativity → Int → Arity 2
infixFunction :: String → Associativity → Int → Arity 3
postfixRelation :: String → Arity 1

data Sentence =
  Bool Bool |
  And Sentence Sentence |
  Or Sentence Sentence |
  Not Sentence |
  Implies Sentence Sentence |
  Proposition Relation |
  ∀f. Formula f ⇒ Ɐ (Element → f) |
  ∀f. Formula f ⇒ Ǝ (Element → f)

deMorgan :: Sentence → Sentence
deMorgan (Not (a `And` b)) = (Not a) `Or` (Not b)
deMorgan (Not (a `Or` b)) = (Not a) `And` (Not b)
deMorgan (Not (Ɐ formula)) = Ǝ $ formulaMap $ deMorgan . Not
deMorgan (Not (Ǝ formula)) = Ǝ $ formulaMap $ deMorgan . Not
deMorgan (Bool True `And` a) = a
deMorgan (a `And` Bool True) = a
deMorgan (Bool True `And` a) = a
deMorgan = id

instance Eq Sentence where
  (Bool a) == (Bool b) = a == b
  (a `And` b) == (c `And` d) =
    a == c && c == d ||
    a == d && b == c
  (a `Or` b) == (c `Or` d) =
    a == c && c == d ||
    a == d && b == c
  (Not a) == (Not b) = a == b
  (Proposition a) == (Proposition b) = a == b
  (Ɐ a) == (Ǝ b)

(∧) = And
Bool True ∧ a = a
a ∧ Bool True = a
Bool False ∧ _ = false
_ ∧ Bool False = false

(∨) = Or
Bool True ∨ _ = true
_ ∨ Bool True = true
Bool False ∨ a = a
a ∨ Bool False = a

-- TODO make binary operator so can be used as "prefix" operator in a section
(¬) = Not
(¬) (Bool b) = Prelude.not b
not = (¬)

(⟹) = Implies

newtype Symbol = Symbol Int

class Formula f where
  free :: f → Sentence
  increment :: f → f
  -- TODO can this be made a functor?
  formulaMap :: (Sentence → Sentence) → f → f

instance Formula Sentence where
  free = id

  increment (a `And` b) = And `on` increment
  increment (a `Or` b) = Or `on` increment
  increment (Not a) = Not $ increment a
  increment (Ɐ formula) = Ɐ $ increment formula
  increment (Ǝ formula) = Ǝ $ increment formula
  increment = id

  formulaMap = id

instance Formula f ⇒ Formula (Element → f) where
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

  formulaMap = fix ((.) .)

instance Formula f ⇒ Eq f where
  (==) = (==) `on` free

forAll = Ɐ
exists = Ǝ

true = Bool True
false = Bool False

instance Show Quantifier where
  show quantifier =
    take 1
    $ show
    $ quantifier
    $ const true

instance Show s ⇒ Show (Element → s)

letters = ['a'..'z']

names :: [String]
names = bfs $ map (:[]) letters where
  bfs q = q ++ bfs ((:) <$> letters <*> q)

instance Show Symbol where
  show (Symbol i) = names !! i

-- Sentences in head position will always automatically be popped if possible
(¢) :: Sentence → Element → Sentence -- Application (play on $)

infixl 0 ¢

ifThenElse condition thenBody elseResult = condition ⟹ thenBody ∧ ¬condition ⟹ elseBody

class Axiom a where
  sentence :: a → Sentence

class Axiom a ⇒ Assumption (name :: Symbol) a where
  assume :: String → Sentence → a

instance (KnownSymbol name, Assumption name a) ⇒ IsLabel name (Sentence → a) where
  fromLabel = assume @name (symbolVal (Proxy :: Proxy name))

newtype UniqueImage = UniqueImage Sentence

class Axiom UniqueImage where
  sentence = coerce

uniqueƎ :: (Element → Sentence) → Sentence
uniqueƎ formula = Ǝ\a → Ɐ\b → formula b ⟹ b ≡ a

uniqueImage :: Arity n → UniqueImage
uniqueImage relation =
  UniqueImage relation.name
  case natVal (Proxy :: Proxy n) of
    0 → true
    1 → true
    2 → Ɐ\a → uniqueƎ\b → relation a ≡ b
    _ → Ɐ\a → uniqueImage $ relation a

peano =
  [
    uniqueImage succ,
    #"every natural number has a successor"
      $ Ɐ\a → Ǝ\b → succ a ≡ b,
    #"zero is not the successor of any natural number"
      $ Ɐ\a → 0 ≠ succ a,
    #"two natural numbers are equal if their successors are equal"
      $ Ɐ\a b → succ a ≡ succ b ⟹ a ≡ b,
    #"zero is the identity element of addition for natural numbers"
      $ Ɐ\a → a + 0 ≡ a,
    #"the inductive definition of addition for natural numbers"
      $ Ɐ\a b → a + succ b ≡ succ $ a + b,
    #"zero is the annihilator element of multiplication for natural numbers"
      $ Ɐ\a → a * 0 ≡ 0
  ]

class Theorem (name :: Symbol) where
  theory :: Axiom a ⇒ [a]
  show = Sentence
  proof = Proof a Sentence

instance Theorem "√2 is irrational" where
  theory = rationals

  show = ¬Ǝ\x → rational x ∧ x^2 ≡ 2
  proof = do
    x ← supposeForContradiction $ #"√2 is rational"
      $ Ǝ\x → rational x ∧ x^2 ≡ 2

    (a, b) ← have (Ǝ\a b → x ≡ a/b ∧ whole a ∧ whole b ∧ b ≠ 0) do
      because @"rationality implies there exists a whole numerator and non-zero denominator"

    withoutLossOfGeneralityAssume $ reduced a b

    have (odd a ∧ odd b) do
      asdf

    from (x^2 ≡ 2 ∧ x ≡ a/b) $ have (2 ≡ a^2/b^2) do
      asdf

    have (2*b^2 ≡ a^2) do
      have (2*b^2 ≡ a^2/b^2*b^2) `by` bothSides (*b^2)
      from (b ≠ 0) $ have (b^2 ≠ 0) `by` bothSides (^2)
      have (2*b^2 ≡ a^2) $ because @"cancellation of nonzero denominator"

    contradiction

thm = show @"some result" [peano]
  (Ɐ\x → Ǝ formula) do
    have (Ǝ\x → a) `by` substitute @"every natural number has a successor"
    have (Ǝ\x → a) `by` substitute $ Ǝ\x → a

(*) = infixFunction "*" LeftAssociative 3

divides dividend divisor = Ǝ\a → a*dividend ≡ divisor
