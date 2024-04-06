{-# LANGUAGE UnicodeSyntax #-}

module Control.Monad.Wrapped where
import Control.Monad
import Data.Function

newtype Wrapped b a = Wrapped ((a → b) → b)

instance Functor (Wrapped b) where
    fmap = liftM

instance Applicative (Wrapped b) where
    pure  = Wrapped . (&)
    (<*>) = ap

instance Monad (Wrapped b) where
  (Wrapped wrapper) >>= f = Wrapped
    $ wrapper . flip (coerce . f)
