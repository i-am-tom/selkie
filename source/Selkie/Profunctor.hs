{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Profunctor where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import Data.Profunctor (Forget (..))
import GHC.Generics ((:*:) (..), (:+:) (..))
import Prelude hiding ((.), id)
import Selkie.Category (Category ((.)), Cartesian, Cocartesian, Trivial)
import Selkie.Category qualified as Category
import Data.Monoid (Monoid(mempty))

type Profunctor :: (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Category c k, k ~ Arrow p) => Profunctor k c (p :: t -> t -> Type) | p -> k c where
  type Arrow p :: t -> t -> Type

  dimap :: (c x, c y, c z, c w) => k x y -> k z w -> p y z -> p x w

type Profunctor' :: (t -> t -> Type) -> Constraint
type Profunctor' p = Profunctor (Arrow p) (Obj (Arrow p)) p

type Obj :: (t -> t -> Type) -> t -> Constraint
type Obj p = Category.Obj (Arrow p)

type Strong :: (t -> t -> t) -> (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Profunctor k c p, Cartesian c b k, forall x y. (c x, c y) => c (b x y))
    => Strong b k c p | p -> b k c where
  first :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  second :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Strong' :: (t -> t -> Type) -> Constraint
type Strong' p = Strong (Category.Product (Arrow p)) (Arrow p) (Obj (Arrow p)) p

type Choice :: (t -> t -> t) -> (t -> t -> Type) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Profunctor k c p, Cocartesian c b k, forall x y. (c x, c y) => c (b x y))
    => Choice b k c p | p -> b k c where
  left :: (c x, c y, c z) => p x y -> p (b x z) (b y z)
  right :: (c x, c y, c z) => p x y -> p (b z x) (b z y)

type Choice' :: (t -> t -> Type) -> Constraint
type Choice' p = Choice (Category.Coproduct (Arrow p)) (Arrow p) (Obj (Arrow p)) p

---

instance Profunctor (->) Trivial (->) where
  type Arrow (->) = (->)

  dimap :: (Trivial x, Trivial y, Trivial z, Trivial w) => (x -> y) -> (z -> w) -> (y -> z) -> x -> w
  dimap pre post f = post . f . pre


instance Strong (,) (->) Trivial (->) where
  first :: (Trivial x, Trivial y, Trivial z) => (x -> y) -> (x, z) -> (y, z)
  first f (x, z) = (f x, z)

  second :: (Trivial x, Trivial y, Trivial z) => (x -> y) -> (z, x) -> (z, y)
  second f (z, y) = (z, f y)

instance Choice Either (->) Trivial (->) where
  left :: (Trivial x, Trivial y, Trivial z) => (x -> y) -> Either x z -> Either y z
  left f = \case
    Left x -> Left (f x)
    Right y -> Right y

  right :: (Trivial x, Trivial y, Trivial z) => (x -> y) -> Either z x -> Either z y
  right f = \case
    Left x -> Left x
    Right y -> Right (f y)

---

instance Profunctor (:~>) Functor (:~>) where
  type Arrow (:~>) = (:~>)

  dimap :: (Functor x, Functor y, Functor z, Functor w) => x :~> y -> z :~> w -> y :~> z -> x :~> w
  dimap pre post f = post . f . pre

instance Strong (:*:) (:~>) Functor (:~>) where
  first :: (Functor x, Functor y, Functor z) => x :~> y -> (x :*: z) :~> (y :*: z)
  first (NT f) = NT \(x :*: z) -> f x :*: z

  second :: (Functor x, Functor y, Functor z) => (x :~> y) -> (z :*: x) :~> (z :*: y)
  second (NT f) = NT \(z :*: y) -> z :*: f y

instance Choice (:+:) (:~>) Functor (:~>) where
  left :: (Functor x, Functor y, Functor z) => (x :~> y) -> (x :+: z) :~> (y :+: z)
  left (NT f) = NT \case
    L1 x -> L1 (f x)
    R1 y -> R1 y

  right :: (Functor x, Functor y, Functor z) => (x :~> y) -> (z :+: x) :~> (z :+: y)
  right (NT f) = NT \case
    L1 x -> L1 x
    R1 y -> R1 (f y)

---

instance Profunctor (->) Trivial (Forget r) where
  type Arrow (Forget r) = (->)

  dimap :: (Trivial x, Trivial y, Trivial z, Trivial w) => (x -> y) -> (z -> w) -> Forget r y z -> Forget r x w
  dimap pre _ (Forget f) = Forget (f . pre)

instance Strong (,) (->) Trivial (Forget r) where
  first :: (Trivial x, Trivial y, Trivial z) => Forget r x y -> Forget r (x, z) (y, z)
  first (Forget f) = Forget \(x, _) -> f x

  second :: (Trivial x, Trivial y, Trivial z) => Forget r x y -> Forget r (z, x) (z, y)
  second (Forget f) = Forget \(_, x) -> f x

instance Monoid r => Choice Either (->) Trivial (Forget r) where
  left :: (Monoid r, Trivial x, Trivial y, Trivial z) => Forget r x y -> Forget r (Either x z) (Either y z)
  left (Forget f) = Forget \case
    Left  x -> f x
    Right _ -> mempty

  right :: (Monoid r, Trivial x, Trivial y, Trivial z) => Forget r x y -> Forget r (Either z x) (Either z y)
  right (Forget f) = Forget \case
    Left  _ -> mempty
    Right y -> f y

---

type Forget1 :: Type -> (Type -> Type) -> (Type -> Type) -> Type
newtype Forget1 r f g = Forget1 (forall x. f x -> r)

instance Profunctor (:~>) Functor (Forget1 r) where
  type Arrow (Forget1 r) = (:~>)

  dimap :: (Functor x, Functor y, Functor z, Functor w) => x :~> y -> z :~> w -> Forget1 r y z -> Forget1 r x w
  dimap (NT pre) _ (Forget1 f) = Forget1 (f . pre)

instance Strong (:*:) (:~>) Functor (Forget1 r) where
  first :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (x :*: z) (y :*: z)
  first (Forget1 f) = Forget1 \(x :*: _) -> f x

  second :: (Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (z :*: x) (z :*: y)
  second (Forget1 f) = Forget1 \(_ :*: y) -> f y

instance Monoid r => Choice (:+:) (:~>) Functor (Forget1 r) where
  left :: (Monoid r, Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (x :+: z) (y :+: z)
  left (Forget1 f) = Forget1 \case
    L1 x -> f x
    R1 _ -> mempty

  right :: (Monoid r, Functor x, Functor y, Functor z) => Forget1 r x y -> Forget1 r (z :+: x) (z :+: y)
  right (Forget1 f) = Forget1 \case
    L1 _ -> mempty
    R1 y -> f y