{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Profunctor where

import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:) (..), (:+:) (..))
import Prelude hiding ((.), id)
import Selkie.Category

type Profunctor :: (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Category c k, k ~ Arrow p) => Profunctor k c (p :: t -> t -> Type) | p -> k c where
  type Arrow p :: t -> t -> Type

  dimap :: (c x, c y, c z, c w) => k x y -> k z w -> p y z -> p x w

  default dimap :: (p ~ k, c x, c y, c z, c w) => k x y -> k z w -> p y z -> p x w
  dimap pre post f = post . f . pre

type Profunctor' :: (t -> t -> Type) -> Constraint
type Profunctor' p = Profunctor (Arrow p) (Obj (Arrow p)) p

type Strong :: (t -> t -> t) -> (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Profunctor k c p, Cartesian c b k) => Strong b k c p | p -> b k c where
  first :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  second :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Strong' :: (t -> t -> Type) -> Constraint
type Strong' p = Strong (Product (Arrow p)) (Arrow p) (Obj (Arrow p)) p

type Choice :: (t -> t -> t) -> (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Profunctor k c p, Cocartesian c b k) => Choice b k c p | p -> b k c where
  left :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  right :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Choice' :: (t -> t -> Type) -> Constraint
type Choice' p = Choice (Coproduct (Arrow p)) (Arrow p) (Obj (Arrow p)) p

---

instance Profunctor (->) Trivial (->) where
  type Arrow (->) = (->)

instance Strong (,) (->) Trivial (->) where
  first f (x, z) = (f x, z)
  second f (z, y) = (z, f y)

instance Choice Either (->) Trivial (->) where
  left f = \case
    Left x -> Left (f x)
    Right y -> Right y

  right f = \case
    Left x -> Left x
    Right y -> Right (f y)

---

instance Profunctor (~>) Functor (~>) where
  type Arrow (~>) = (~>)

instance Strong (:*:) (~>) Functor (~>) where
  first (NT f) = NT \(x :*: z) -> f x :*: z
  second (NT f) = NT \(z :*: y) -> z :*: f y

instance Choice (:+:) (~>) Functor (~>) where
  left (NT f) = NT \case
    L1 x -> L1 (f x)
    R1 y -> R1 y

  right (NT f) = NT \case
    L1 x -> L1 x
    R1 y -> R1 (f y)