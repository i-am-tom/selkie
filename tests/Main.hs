{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Data.Kind (Type)
import GHC.Generics ((:*:) (..), Generic, Generically (..))
import Selkie.Optics
import Selkie.Annotation
import Data.Functor.Identity (Identity)

type User :: Type
data User = User { _name :: String, _age :: Int, _likesDogs :: Bool }
  deriving stock (Eq, Generic, Ord, Show)
  deriving Annotate via Generically User

lens :: Lens' User _
lens = field @"_name"


main :: IO ()
main = sequence_
  [
  ]