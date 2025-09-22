{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Category.Class where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:+:) (..), (:*:) (..), U1 (..), V1)
import Prelude hiding ((.), id)
import Data.Void qualified as Void

type Category :: (t -> Constraint) -> (t -> t -> Type) -> Constraint
class Obj k ~ c => Category c (k :: t -> t -> Type) | k -> c where
  type Obj k :: t -> Constraint

  id :: (c x) => k x x
  (.) :: (c x, c y, c z) => k y z -> k x y -> k x z

type Category' :: (t -> t -> Type) -> Constraint
class Category (Obj k) k => Category' k
instance Category (Obj k) k => Category' k

type Cartesian :: (t -> Constraint) -> (t -> t -> t) -> (t -> t -> Type) -> Constraint
class (Category c k, forall x y. (c x, c y) => c (b x y), Product k ~ b)
    => Cartesian c b (k :: t -> t -> Type) | k -> c b where
  type Product k :: t -> t -> t

  (△) :: (c x, c y, c z) => k x y -> k x z -> k x (b y z)

  exl :: (c x, c y) => k (b x y) x
  exr :: (c x, c y) => k (b x y) y

type Cartesian' :: (t -> t -> Type) -> Constraint
class Cartesian (Obj k) (Product k) k => Cartesian' k
instance Cartesian (Obj k) (Product k) k => Cartesian' k

type Cocartesian :: (t -> Constraint) -> (t -> t -> t) -> (t -> t -> Type) -> Constraint
class (Category c k, forall x y. (c x, c y) => c (b x y), Coproduct k ~ b)
    => Cocartesian c b (k :: t -> t -> Type) | k -> c b where
  type Coproduct k :: t -> t -> t

  (▽) :: (c x, c y, c z) => k x z -> k y z -> k (b x y) z

  inl :: (c x, c y) => k x (b x y)
  inr :: (c x, c y) => k y (b x y)

type Cocartesian' :: (t -> t -> Type) -> Constraint
class Cocartesian (Obj k) (Coproduct k) k => Cocartesian' k
instance Cocartesian (Obj k) (Coproduct k) k => Cocartesian' k

type Initial :: (t -> Constraint) -> t -> (t -> t -> Type) -> Constraint
class (Category c k, c i) => Initial c i (k :: t -> t -> Type) | k -> c i where
  type Void k :: t

  initial :: (c x) => k i x

type Initial' :: (t -> t -> Type) -> Constraint
class Initial (Obj k) (Void k) k => Initial' k
instance Initial (Obj k) (Void k) k => Initial' k

type Terminal :: (t -> Constraint) -> t -> (t -> t -> Type) -> Constraint
class (Category c k, c u) => Terminal c u (k :: t -> t -> Type) | k -> c u where
  type Unit k :: t

  terminal :: (c x) => k x u

type Terminal' :: (t -> t -> Type) -> Constraint
class Terminal (Obj k) (Unit k) k => Terminal' k
instance Terminal (Obj k) (Unit k) k => Terminal' k

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

instance Initial Trivial Void.Void (->) where
  type Void (->) = Void.Void

  initial :: Trivial x => Void.Void -> x
  initial = \case

instance Terminal Trivial () (->) where
  type Unit (->) = ()

  terminal :: Trivial x => x -> ()
  terminal = \_ -> ()

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
  type Unit (:~>) = U1

  terminal :: Functor x => x :~> U1
  terminal = NT \_ -> U1

instance Initial Functor V1 (:~>) where
  type Void (:~>) = V1

  initial :: Functor x => V1 :~> x
  initial = NT \case