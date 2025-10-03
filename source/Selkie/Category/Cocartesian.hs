{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Category.Cocartesian where

import Control.Natural ((:~>) (..))
import GHC.Generics ((:+:) (..))
import Data.Kind (Constraint, Type)
import Selkie.Category.Category (Category (..), Trivial)

type Cocartesian :: (t -> t -> t) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Category c k, b ~ Sum k, forall x y. (c x, c y) => c (b x y))
    => Cocartesian b c (k :: t -> t -> Type) | k -> c b where
  type Sum k :: t -> t -> t

  (▽) :: (c x, c y, c z) => k x z -> k y z -> k (b x y) z
  inl :: (c x, c y) => k x (b x y)
  inr :: (c x, c y) => k y (b x y)

infixr 3 ▽

type Cocartesian' :: (t -> t -> Type) -> Constraint
type Cocartesian' k = Cocartesian (Sum k) (Obj k) k

instance Cocartesian Either Trivial (->) where
  type Sum (->) = Either

  (▽) :: (x -> z) -> (y -> z) -> Either x y -> z
  f ▽ g = \case
    Left  x -> f x
    Right y -> g y

  inl :: x -> Either x y
  inl = \x -> Left x

  inr :: y -> Either x y
  inr = \y -> Right y

instance Cocartesian (:+:) Functor (:~>) where
  type Sum (:~>) = (:+:)

  (▽) :: (Functor x, Functor y) => x :~> z -> y :~> z -> x :+: y :~> z
  NT f ▽ NT g = NT \case
    L1 x -> f x
    R1 y -> g y

  inl :: (Functor x, Functor y) => x :~> x :+: y
  inl = NT \x -> L1 x

  inr :: (Functor x, Functor y) => y :~> x :+: y
  inr = NT \y -> R1 y