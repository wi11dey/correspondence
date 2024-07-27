data TM t a = {
  δ :: Matrix t,
  decoder :: Int → a
  }

accepts machine input = Ǝ\t → machine

type Is a = (a → b) → b

suchThat :: a → Is b
suchThat element next = (cast :: Maybe b)

instance _⇒ Theorem "complexity class P" where
  statement = Ɐ\decisionProblem → decisionProblem ∈ "P" ⇔ Ɐ\input → Ǝ\machine → (suchThat machine :: Is (TM Bool Bool)) ⟹ machine `accepts` input ⇔ decisionProblem ¢ input
