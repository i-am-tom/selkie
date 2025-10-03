{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Category.Cartesian where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:) (..))
import Selkie.Category.Category (Category (..), Trivial)

type Cartesian :: (t -> t -> t) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Category c k, b ~ Product k, forall x y. (c x, c y) => c (b x y))
    => Cartesian b c (k :: t -> t -> Type) | k -> c b where
  type Product k :: t -> t -> t

  (△) :: (c x, c y, c z) => k x y -> k x z -> k x (b y z)
  exl :: (c x, c y) => k (b x y) x
  exr :: (c x, c y) => k (b x y) y

infixr 3 △

type Cartesian' :: (t -> t -> Type) -> Constraint
type Cartesian' k = Cartesian (Product k) (Obj k) k

instance Cartesian (,) Trivial (->) where
  type Product (->) = (,)

  (△) :: (x -> y) -> (x -> z) -> x -> (y, z)
  f △ g = \x -> (f x, g x)

  exl :: (x, y) -> x
  exl = \(x, _) -> x

  exr :: (x, y) -> y
  exr = \(_, y) -> y

instance Cartesian (:*:) Functor (:~>) where
  type Product (:~>) = (:*:)

  (△) :: (Functor y, Functor z) => x :~> y -> x :~> z -> x :~> (y :*: z)
  NT f △ NT g = NT \x -> f x :*: g x

  exl :: (Functor x, Functor y) => (x :*: y) :~> x
  exl = NT \(x :*: _) -> x

  exr :: (Functor x, Functor y) => (x :*: y) :~> y
  exr = NT \(_ :*: y) -> y