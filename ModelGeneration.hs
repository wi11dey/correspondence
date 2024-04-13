{-# LANGUAGE LambdaCase #-}

type Multimap k v = Map k (Set v)

data Generated =
  Explicit Constant |
  Infinite

data Model a = Model {
  universe :: [Generated],
  relations :: Multimap Relation [Generated]
  }

models :: Axiom FirstOrder a ⇒ [a] → [Model]
models theory =
  Model {
    universe =
      map Explicit
      $ foldMap constants theory,
    relations = Map.empty
  }
  where
    nextModels start = 
      do
        axiom ← theory
        case quantified $ sentence $ axiom of
          Ɐ formula → _
          Ǝ formula → _

-- A theory is defined by its generators (axioms and axiom schemata)
type Theory q = ∀a. Axiom q a ⇒ [a]

instance Theorem "generate models for first-order theory" where
  statement = Ɐ\theory → (suchThat theory :: Theory FirstOrder) ⟹ Ǝ\models → (Ɐ\model → model ∈ models) ⟹ model ⊨ theory
  proof = do
    theory ← have Ǝ\theory → suchThat theory :: Theory FirstOrder
    a

main = proof @"generate models for first-order theory" ¢


-- These don't work:

type family Runnable (* → Constraint) :: Type
type instance Runnable 

something :: Assumption "law of the excluded middle" a ⇒ a → ()

type family Runnable a where
  

class Runnable a where
  run :: RunnableType r ⇒ Proof a → r

instance Runnable (Proof a) s

-- Explicitly make an overlapping instance without {-# OVERLAPPING #-} so that trying to run a non-constructive proof fails to type-check:
instance Assumption "law of the excluded middle" a ⇒ Specializable (Proof a) s where
  ¢ = undefined

