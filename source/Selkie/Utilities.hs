{-# LANGUAGE TypeFamilies #-}

module Selkie.Utilities where

import Data.Kind (Type)
import GHC.TypeLits (ErrorMessage, TypeError)

type Step :: Type
type Step = () -> Either () ()

type Or :: Maybe k -> ErrorMessage -> k
type family Or xs e where
  'Nothing `Or` e = TypeError e
  'Just xs `Or` _ = xs

type (<|>) :: Maybe k -> Maybe k -> Maybe k
type family xs <|> ys where
  'Just xs <|> 'Nothing = 'Just xs
  'Nothing <|>       ys =       ys

type Prepend :: k -> Maybe [k] -> Maybe [k]
type family Prepend x xs where
  Prepend x  'Nothing  = 'Nothing
  Prepend x ('Just xs) = 'Just (x ': xs)
