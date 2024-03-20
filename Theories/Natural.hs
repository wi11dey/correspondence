{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PartialTypeSignatures #-}

newtype ℕ = ℕ Theory

succ = relation :: ℕ → Relation

instance Theory ℕ where
  axioms =
    [ succ
    , axiom mdo
        x ← ℕ
        0 ≠ succ x
    , axiom mdo
        x ← ℕ
        y ← ℕ
        given (succ x = succ y)
        x = y
    ]
