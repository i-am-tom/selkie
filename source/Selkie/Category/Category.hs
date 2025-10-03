{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Category.Category where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)

type Trivial :: t -> Constraint
class Trivial x
instance Trivial x

type Category :: (t -> Constraint) -> (t -> t -> Type) -> Constraint
class c ~ Obj k => Category c (k :: t -> t -> Type) | k -> c where
  type Obj k :: t -> Constraint
  type Obj k = Trivial

  (.) :: (c x, c y, c z) => k y z -> k x y -> k x z
  id :: (c x) => k x x

infixr 9 .

type Category' :: (t -> t -> Type) -> Constraint
type Category' k = Category (Obj k) k

instance Category Trivial (->) where
  type Obj (->) = Trivial

  (.) :: (y -> z) -> (x -> y) -> (x -> z)
  f . g = \x -> f (g x)

  id :: x -> x
  id = \x -> x

instance Category Functor (:~>) where
  type Obj (:~>) = Functor

  (.) :: (Functor y, Functor z) => y :~> z -> x :~> y -> x :~> z
  NT f . NT g = NT \x -> f (g x)

  id :: Functor x => x :~> x
  id = NT \x -> x