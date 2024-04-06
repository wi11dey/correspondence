{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE BlockArguments #-}

import Control.Monad
import Control.Monad.Wrapped
import Data.Function
import Data.Sequence

data Relation = Relation
  {
    name :: String,
    fixity :: Fixity,
    precedence :: Natural,
    associativity :: Associativity,
    elements :: Seq Element
  } |
  Equals Element Element -- Equality is the only primitive notion.

seed = Relation
  {
    name = "",
    fixity = Prefix,
    precedence = 0,
    associativity = LeftAssociative,
    elements = empty
  }

data Associativity = LeftAssociative | RightAssociative | NonAssociative

data Fixity = Prefix | Infix | Postfix

class Show r ⇒ RelationType r
  chain :: (Relation → Sentence) → r

instance RelationType (Sentence) where
  chain = ($ seed)

instance (Argument a, RelationType r) ⇒ RelationType (a → r) where
  chain next arg = chain $ \last → unwrap do
    el ← arg
    return $ next $ last { elements = elements last |> el }

relation :: RelationType r ⇒ String → r
relation name = chain $ \end → end { name }

class Argument a where
  wrap :: a → Wrapped Sentence Element

instance Argument Element where
  wrap = return

instance Argument (Arity 1) where
  wrap f = Wrapped $ \suffix →
    Ǝ $ \a → f a ∧ suffix a

type family Arity (arity :: Nat) where
  Arity 0 = Sentence
  Arity arity = Argument a ⇒ a → Arity (arity - 1)

unwrap :: Wrapped Sentence Sentence → Sentence
unwrap = flip coerce (const true)

(≡) :: Arity 2
(≡) = ((unwrap . liftM Proposition) .)
  . (liftM2 Equals `on` wrap)

newtype Symbol = Symbol Int

data Element =
  Variable Symbol |
  Constant String

(>) = relation ">" :: Arity 2
(+) = infixFunction "+" LeftAssociative 3

prefixRelation :: String → Arity 1
prefixRelation name = withElement $ \element → Relation
  {
    name,
    fixity = Prefix,
    precedence = 0,
    associativity = LeftAssociative,
    elements = [element]
  }
infixRelation :: String → Associativity → Int → Arity 2
infixFunction :: String → Associativity → Int → Arity 3
postfixRelation :: String → Arity 1

data Sentence =
  Bool Bool |
  And Sentence Sentence |
  Or Sentence Sentence |
  Not Sentence |
  Proposition Relation |
  Quantified Quantified |
  deriving Eq

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

(¬) = Not
(¬) (Bool b) = Prelude.not b
not = (¬)

data Quantified =
  Ɐ (Element → Sentence) |
  Ǝ (Element → Sentence)
  deriving (Eq, Show)

type Quantifier = (Element → Sentence) → Quantified

deconstruct :: Quantified → (Quantifier, Element → Sentence)
deconstruct (Ɐ lambda) = (Ɐ, lambda)
deconstruct (Ǝ lambda) = (Ǝ, lambda)

withFree :: (Element → Sentence) → Sentence
withFree f =
  deconflict
  $ f
  $ Variable
  $ Symbol 0
  where
    deconflict :: Sentence → Sentence
    deconflict (deconstruct → (quantifier, lambda)) =
      Quantified
      $ quantifier
      $ (deconflict .)
      $ incArg
      $ lambda
    deconflict (And a b) = And `on` deconflict
    deconflict (Or a b) = Or `on` deconflict
    deconflict (Not a) = Not $ deconflict a
    deconflict a = a

    incArg :: (Element → Sentence) → Element → Sentence
    incArg lambda c@(Constant _) = lambda c
    incArg lambda (Variable (Symbol i)) =
      lambda
      $ Variable
      $ Symbol
      $ i + 1

instance Eq (Element → Sentence) where
  a == b = (==) `on` withFree a

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

(*) = infixFunction "*" LeftAssociative 3

divides dividend divisor = Ǝ $ \a → a * dividend ≡ divisor
