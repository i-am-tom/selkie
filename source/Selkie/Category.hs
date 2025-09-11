{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Category where

import Data.Kind (Constraint, Type)
import GHC.Generics ((:+:) (..), (:*:) (..))
import Prelude hiding ((.), id)

type Category :: (t -> Constraint) -> (t -> t -> Type) -> Constraint
class Obj k ~ c => Category c k | k -> c where
  type Obj k :: t -> Constraint

  id :: (c x) => k x x
  (.) :: (c x, c y, c z) => k y z -> k x y -> k x z

type Category' :: (t -> t -> Type) -> Constraint
type Category' k = Category (Obj k) k

type Cartesian :: (t -> Constraint) -> (t -> t -> t) -> (t -> t -> Type) -> Constraint
class (Category c k, forall x y. (c x, c y) => c (p x y), Product k ~ p)
    => Cartesian c p k | k -> c p where
  type Product k :: t -> t -> t

  (△) :: (c x, c y, c z) => k x y -> k x z -> k x (p y z)
  exl :: (c x, c y) => k (p x y) x
  exr :: (c x, c y) => k (p x y) y

type Cartesian' :: (t -> t -> Type) -> Constraint
type Cartesian' k = Cartesian (Obj k) (Product k) k

type Cocartesian :: (t -> Constraint) -> (t -> t -> t) -> (t -> t -> Type) -> Constraint
class (Category c k, forall x y. (c x, c y) => c (s x y), Coproduct k ~ s)
    => Cocartesian c s k | k -> c s where
  type Coproduct k :: t -> t -> t

  (▽) :: (c x, c y, c z) => k x z -> k y z -> k (s x y) z
  inl :: (c x, c y) => k x (s x y)
  inr :: (c x, c y) => k y (s x y)

type Cocartesian' :: (t -> t -> Type) -> Constraint
type Cocartesian' k = Cocartesian (Obj k) (Coproduct k) k

---

class Trivial x
instance Trivial x

instance Category Trivial (->) where
  type Obj (->) = Trivial

  id = \x -> x
  f . g = \x -> f (g x)

instance Cartesian Trivial (,) (->) where
  type Product (->) = (,)

  f △ g = \x -> (f x, g x)
  exl = fst
  exr = snd

instance Cocartesian Trivial (Either) (->) where
  type Coproduct (->) = Either

  f ▽ g = either f g
  inl = Left
  inr = Right

---

type (~>) :: (t -> Type) -> (t -> Type) -> Type
newtype f ~> g = NT (forall x. f x -> g x)

instance f ~ g => Semigroup (f ~> g) where
  NT f <> NT g = NT (f . g)

instance f ~ g => Monoid (f ~> g) where
  mempty = NT id

instance Category Functor (~>) where
  type Obj (~>) = Functor

  NT f . NT g = NT \x -> f (g x)
  id = NT id

instance Cartesian Functor (:*:) (~>) where
  type Product (~>) = (:*:)

  NT f △ NT g = NT \x -> f x :*: g x
  exl = NT \(x :*: _) -> x
  exr = NT \(_ :*: y) -> y

instance Cocartesian Functor (:+:) (~>) where
  type Coproduct (~>) = (:+:)

  NT f ▽ NT g = NT \case
    L1 x -> f x
    R1 y -> g y

  inl = NT \x -> L1 x
  inr = NT \x -> R1 x
