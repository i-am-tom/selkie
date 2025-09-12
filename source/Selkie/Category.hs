{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Category where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:+:) (..), (:*:) (..), U1 (..), Generic (..), K1 (..), R)
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

type Terminal :: (t -> Constraint) -> t -> (t -> t -> Type) -> Constraint
class (Category c k, c u) => Terminal c u k | k -> c u where
  type Unit k :: t

  unit :: (c x) => k x u

type Terminal' :: (t -> t -> Type) -> Constraint
type Terminal' k = Terminal (Obj k) (Unit k) k

---

class Trivial x
instance Trivial x

instance Category Trivial (->) where
  type Obj (->) = Trivial

  id :: Trivial x => x -> x
  id = \x -> x

  (.) :: (Trivial x, Trivial y, Trivial z) => (y -> z) -> (x -> y) -> x -> z
  f . g = \x -> f (g x)

instance Cartesian Trivial (,) (->) where
  type Product (->) = (,)

  (△) :: (Trivial x, Trivial y, Trivial z) => (x -> y) -> (x -> z) -> x -> (y, z)
  f △ g = \x -> (f x, g x)

  exl :: (Trivial x, Trivial y) => (x, y) -> x
  exl = fst

  exr :: (Trivial x, Trivial y) => (x, y) -> y
  exr = snd

instance Cocartesian Trivial (Either) (->) where
  type Coproduct (->) = Either

  (▽) :: (Trivial x, Trivial y, Trivial z) => (x -> z) -> (y -> z) -> Either x y -> z
  f ▽ g = either f g

  inl :: (Trivial x, Trivial y) => x -> Either x y
  inl = Left

  inr :: (Trivial x, Trivial y) => y -> Either x y
  inr = Right

instance Terminal Trivial () (->) where
  type Unit (->) = ()

  unit :: Trivial x => x -> ()
  unit = \_ -> ()

---

instance Category Functor (:~>) where
  type Obj (:~>) = Functor

  (.) :: (Functor x, Functor y, Functor z) => y :~> z -> x :~> y -> x :~> z
  NT f . NT g = NT \x -> f (g x)

  id :: Functor x => x :~> x
  id = NT id

instance Cartesian Functor (:*:) (:~>) where
  type Product (:~>) = (:*:)

  (△) :: (Functor x, Functor y, Functor z) => (x :~> y) -> (x :~> z) -> x :~> (y :*: z)
  NT f △ NT g = NT \x -> f x :*: g x

  exl :: (Functor x, Functor y) => (x :*: y) :~> x
  exl = NT \(x :*: _) -> x

  exr :: (Functor x, Functor y) => (x :*: y) :~> y
  exr = NT \(_ :*: y) -> y

instance Cocartesian Functor (:+:) (:~>) where
  type Coproduct (:~>) = (:+:)

  (▽) :: (Functor x, Functor y, Functor z) => (x :~> z) -> (y :~> z) -> (x :+: y) :~> z
  NT f ▽ NT g = NT \case
    L1 x -> f x
    R1 y -> g y

  inl :: (Functor x, Functor y) => x :~> (x :+: y)
  inl = NT \x -> L1 x

  inr :: (Functor x, Functor y) => y :~> (x :+: y)
  inr = NT \x -> R1 x

instance Terminal Functor U1 (:~>) where
  type Unit (:~>) = ()

  unit :: Functor x => x :~> U1
  unit = NT \_ -> U1