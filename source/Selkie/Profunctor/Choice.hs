{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Profunctor.Choice where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:+:) (..))
import Data.Profunctor (Forget (..))
import Prelude hiding ((.))
import Selkie.Category (Category (..), Cocartesian (..), Trivial)
import Selkie.Profunctor.Profunctor (Profunctor (..), Forget1 (..))

type Choice :: (t -> t -> t) -> (t -> Constraint) -> (t -> t -> Type) -> (t -> t -> Type) -> Constraint
class (Cocartesian b c k, Profunctor c k p) => Choice b c k p | p -> k, k -> b c where
  left :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  right :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Choice' :: (t -> t -> Type) -> Constraint
class Choice (Sum (Arrow p)) (Obj (Arrow p)) (Arrow p) p => Choice' p
instance Choice (Sum (Arrow p)) (Obj (Arrow p)) (Arrow p) p => Choice' p

instance Choice Either Trivial (->) (->) where
  left :: (x -> y) -> (Either x z -> Either y z)
  left f = either (Left . f) Right

  right :: (x -> y) -> (Either z x -> Either z y)
  right f = either Left (Right . f)

instance Monoid r => Choice Either Trivial (->) (Forget r) where
  left :: Forget r x y -> Forget r (Either x z) (Either y z)
  left (Forget f) = Forget \case
    Left  x -> f x
    Right _ -> mempty

  right :: Forget r x y -> Forget r (Either z x) (Either z y)
  right (Forget f) = Forget \case
    Left  _ -> mempty
    Right y -> f y

instance Choice (:+:) Functor (:~>) (:~>) where
  left :: (Functor x, Functor y, Functor z) => (x :~> y) -> ((x :+: z) :~> (y :+: z))
  left (NT f) = NT \case
    L1 x -> L1 (f x)
    R1 y -> R1  y

  right :: (Functor x, Functor y, Functor z) => (x :~> y) -> ((z :+: x) :~> (z :+: y))
  right (NT f) = NT \case
    L1 x -> L1  x
    R1 y -> R1 (f y)

instance Monoid r => Choice (:+:) Functor (:~>) (Forget1 r) where
  left :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (x :+: z) (y :+: z)
  left (Forget1 f) = Forget1 \case
    L1 x -> f x
    R1 _ -> mempty

  right :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (z :+: x) (z :+: y)
  right (Forget1 f) = Forget1 \case
    L1 _ -> mempty
    R1 y -> f y