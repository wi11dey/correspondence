{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}

import Data.Sequence

(≡) = (==)

data Relation = Relation
  {
    symbol :: String,
    fixity :: Fixity,
    precedence :: Natural,
    associativity :: Associativity,
    terms :: Seq Term
  } |
  Equals Term Term

data Associativity = LeftAssociative | RightAssociative | NonAssociative

data Fixity = Prefix | Infix | Postfix

class Show r ⇒ RelationType r
  buildRelation :: (Relation → Sentence) → r

instance RelationType (Sentence) where
  buildRelation next = next $ Relation
    {
      symbol = "",
      fixity = Prefix,
      precedence = 0,
      associativity = LeftAssociative,
      terms = empty
    }

instance (Argument a, RelationType r) ⇒ RelationType (a → r) where
  buildRelation next arg = buildRelation $ \old →
    withTerm arg $ \term →
      next $ old { terms = terms old |> term }

relation :: RelationType r ⇒ String → r
relation symbol = buildRelation $ \relation →
  relation { symbol }

class Argument a where
  withTerm :: a → (Term → Sentence) → Sentence

instance Argument Term where
  withTerm term cont = cont term

instance Argument (Arity 1) where
  withTerm f = Ǝ $ \a → f a ∧ cont a

type family Arity (arity :: Nat) where
  Arity 0 = Sentence
  Arity arity = Argument a ⇒ a → Arity (arity - 1)

data Term =
  Variable String |
  Constant String

(>) = relation ">" :: Arity 2
(+) = infixFunction "+" LeftAssociative 3

prefixRelation :: String → Arity 1
prefixRelation symbol arg = withTerm arg $ \term → Relation
  {
    symbol,
    fixity = Prefix,
    precedence = 0,
    associativity = LeftAssociative,
    terms = [term]
  }
infixRelation :: String → Associativity → Natural → Arity 2
infixFunction :: String → Associativity → Natural → Arity 3
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

data Quantified =
  Ɐ (Term → Sentence) |
  Ǝ (Term → Sentence)
  deriving Show

forAll = Ɐ
exists = Ǝ

true = Bool True
false = Bool False

instance Show ((Variable → Sentence) → Quantified) where
  show quantifier =
    take 1
    $ show
    $ quantifier
    $ const true

(*) = infixFunction "*" LeftAssociative 3

divides dividend divisor = Ǝ $ \a → a * dividend ≡ divisor

instance Show s ⇒ Show (Term → s)

letters = ['a'..'z']

names :: [String]
names = bfs $ map (:[]) letters where
  bfs q = q ++ bfs ((:) <$> letters <*> q)
