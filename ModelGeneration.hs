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
-- theory is defined by its generators (axioms and axiom schemata)
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
