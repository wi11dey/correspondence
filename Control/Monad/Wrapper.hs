{-# LANGUAGE UnicodeSyntax #-}

module Control.Monad.Wrapper where
import Control.Monad
import Data.Coerce
import Data.Function

newtype Wrapper b a = Wrapper ((a → b) → b)

instance Functor (Wrapper b) where
    fmap = liftM

instance Applicative (Wrapper b) where
    pure = Wrapper . (&)
    (<*>) = ap

instance Monad (Wrapper b) where
  (Wrapper wrapper) >>= f = Wrapper
    $ wrapper . flip (coerce . f)
