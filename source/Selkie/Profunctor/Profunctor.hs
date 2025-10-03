{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Profunctor.Profunctor where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import Data.Profunctor (Forget (..))
import Prelude hiding ((.), id)
import Selkie.Category (Category (..), Trivial)

type Profunctor :: (t -> Constraint) -> (t -> t -> Type) -> (t -> t -> Type) -> Constraint
class (Arrow p ~ k, Category c k) => Profunctor c k (p :: t -> t -> Type) | p -> k, k -> c where
  type Arrow p :: t -> t -> Type

  dimap :: (c x, c y, c z, c w) => k x y -> k z w -> p y z -> p x w
  dimap f g = lmap f . rmap g

  lmap :: (c x, c y, c z) => k x y -> p y z -> p x z
  lmap f = dimap f id

  rmap :: (c y, c z, c w) => k z w -> p y z -> p y w
  rmap g = dimap id g

  {-# MINIMAL dimap | (lmap, rmap) #-}

type Profunctor' :: (t -> t -> Type) -> Constraint
class Profunctor (Obj (Arrow p)) (Arrow p) p => Profunctor' p
instance Profunctor (Obj (Arrow p)) (Arrow p) p => Profunctor' p

instance Profunctor Trivial (->) (->) where
  type Arrow (->) = (->)

  dimap :: (x -> y) -> (z -> w) -> (y -> z) -> (x -> w)
  dimap pre post f = post . f . pre

  lmap :: (x -> y) -> (y -> z) -> (x -> z)
  lmap pre f = f . pre

  rmap :: (z -> w) -> (y -> z) -> (y -> w)
  rmap post f = post . f

instance Profunctor Trivial (->) (Forget r) where
  type Arrow (Forget r) = (->)

  dimap :: (x -> y) -> (z -> w) -> Forget r y z -> Forget r x w
  dimap pre _ (Forget f) = Forget (f . pre)

  lmap :: (x -> y) -> Forget r y z -> Forget r x z
  lmap pre (Forget f) = Forget (f . pre)

  rmap :: (z -> w) -> Forget r y z -> Forget r y w
  rmap _ (Forget f) = Forget f

instance Profunctor Functor (:~>) (:~>) where
  type Arrow (:~>) = (:~>)

  dimap :: (Functor x, Functor y, Functor z, Functor w) => (x :~> y) -> (z :~> w) -> (y :~> z) -> (x :~> w)
  dimap pre post f = post . f . pre

  lmap :: (Functor x, Functor y, Functor z) => (x :~> y) -> (y :~> z) -> (x :~> z)
  lmap pre f = f . pre

  rmap :: (Functor y, Functor z, Functor w) => (z :~> w) -> (y :~> z) -> (y :~> w)
  rmap post f = post . f

type Forget1 :: Type -> (t -> Type) -> (t -> Type) -> Type
newtype Forget1 r f g = Forget1 (forall x. f x -> r)

instance Profunctor Functor (:~>) (Forget1 r) where
  type Arrow (Forget1 r) = (:~>)

  dimap :: (Functor x, Functor y, Functor z, Functor w) => (x :~> y) -> (z :~> w) -> Forget1 r y z -> Forget1 r x w
  dimap (NT pre) _ (Forget1 f) = Forget1 (f . pre)

  lmap :: (Functor x, Functor y, Functor z) => (x :~> y) -> Forget1 r y z -> Forget1 r x z
  lmap (NT pre) (Forget1 f) = Forget1 (f . pre)

  rmap :: (Functor y, Functor z, Functor w) => (z :~> w) -> Forget1 r y z -> Forget1 r y w
  rmap _ (Forget1 f) = Forget1 f