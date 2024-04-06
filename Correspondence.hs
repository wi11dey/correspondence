{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

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

data Associativity = LeftAssociative | RightAssociative | NonAssociative

data Fixity = Prefix | Infix | Postfix

class Show r ⇒ RelationType r
  buildRelation :: (Relation → Sentence) → r

instance RelationType (Sentence) where
  buildRelation next = next $ Relation
    {
      name = "",
      fixity = Prefix,
      precedence = 0,
      associativity = LeftAssociative,
      elements = empty
    }

instance (Argument a, RelationType r) ⇒ RelationType (a → r) where
  buildRelation next arg = buildRelation $ \old →
    withElement arg $ \element →
      next $ old { elements = elements old |> element }

relation :: RelationType r ⇒ String → r
relation name = buildRelation $ \relation →
  relation { name }

class Argument a where
  withElement :: a → (Element → Sentence) → Sentence

instance Argument Element where
  withElement element cont = cont element

instance Argument (Arity 1) where
  withElement f cont = Ǝ $ \a → f a ∧ cont a

type family Arity (arity :: Nat) where
  Arity 0 = Sentence
  Arity arity = Argument a ⇒ a → Arity (arity - 1)

withElement2 :: (Argument a, Argument b) => (Element -> Element -> Sentence) -> a -> b -> Sentence

(≡) :: Arity 2
a ≡ b = withElement2 

newtype Symbol = Symbol Int

data Element =
  Variable Symbol |
  Constant String

(>) = relation ">" :: Arity 2
(+) = infixFunction "+" LeftAssociative 3

prefixRelation :: String → Arity 1
prefixRelation name arg = withElement arg $ \element → Relation
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
(∨) = Or
(¬) = Not
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
    deconflict (And a b) = And (deconflict a) (deconflict b)
    deconflict (Or a b) = Or (deconflict a) (deconflict b)
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
  a == b = withFree a == withFree b

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
