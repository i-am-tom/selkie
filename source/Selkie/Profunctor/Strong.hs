{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Profunctor.Strong where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import Data.Profunctor (Forget (..))
import GHC.Generics ((:*:) (..))
import Selkie.Category (Category (..), Cartesian (..), Trivial)
import Selkie.Profunctor.Profunctor (Profunctor (..), Forget1 (..))
import Prelude hiding ((.))

type Strong :: (t -> t -> t) -> (t -> Constraint) -> (t -> t -> Type) -> (t -> t -> Type) -> Constraint
class (Cartesian b c k, Profunctor c k p) => Strong b c k p | p -> k, k -> b c where
  first :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  second :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Strong' :: (t -> t -> Type) -> Constraint
class Strong (Product (Arrow p)) (Obj (Arrow p)) (Arrow p) p => Strong' p
instance Strong (Product (Arrow p)) (Obj (Arrow p)) (Arrow p) p => Strong' p

instance Strong (,) Trivial (->) (->) where
  first :: (x -> y) -> ((x, z) -> (y, z))
  first f = \(x, z) -> (f x, z)

  second :: (x -> y) -> ((z, x) -> (z, y))
  second f = \(z, x) -> (z, f x)

instance Strong (,) Trivial (->) (Forget r) where
  first :: Forget r x y -> Forget r (x, z) (y, z)
  first (Forget f) = Forget \(x, _) -> f x

  second :: Forget r x y -> Forget r (z, x) (z, y)
  second (Forget f) = Forget \(_, y) -> f y

instance Strong (:*:) Functor (:~>) (:~>) where
  first :: (Functor x, Functor y, Functor z) => (x :~> y) -> ((x :*: z) :~> (y :*: z))
  first (NT f) = NT \(x :*: z) -> f x :*: z

  second :: (Functor x, Functor y, Functor z) => (x :~> y) -> ((z :*: x) :~> (z :*: y))
  second (NT f) = NT \(z :*: x) -> z :*: f x

instance Strong (:*:) Functor (:~>) (Forget1 r) where
  first :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (x :*: z) (y :*: z)
  first (Forget1 f) = Forget1 \(x :*: _) -> f x

  second :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (z :*: x) (z :*: y)
  second (Forget1 f) = Forget1 \(_ :*: x) -> f x