{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Generic where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import Data.Profunctor (Forget (..))
import GHC.Generics (Generic (..), K1 (..), Rec0)
import Selkie.Annotation (AnnC (..), GAnnC (..), Ann, GAnn, ForgetA (..), GForgetA (..))
import Selkie.Profunctor (Profunctor', Forget1 (..), )

type OK :: Type -> Constraint
class (Generic x, Ann x ~ GAnn (Rep x)) => OK x
instance (Generic x, Ann x ~ GAnn (Rep x)) => OK x

type Represented :: (Type -> Type -> Type) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (Profunctor' p, Profunctor' p', p' ~ Representation p) => Represented p p' | p -> p' where
  type Representation p :: (Type -> Type) -> (Type -> Type) -> Type
  generically :: (OK x, OK y) => p' (Rep x) (Rep y) -> p x y
  ungenerically :: p x y -> p' (Rec0 x) (Rec0 y)

type Represented' :: (Type -> Type -> Type) -> Constraint
type Represented' p = Represented p (Representation p)

instance Represented (->) (:~>) where
  type Representation (->) = (:~>)

  generically :: (OK x, OK y) => (Rep x :~> Rep y) -> (x -> y)
  generically (NT f) = to . f . from

  ungenerically :: (x -> y) -> (Rec0 x :~> Rec0 y)
  ungenerically f = NT (K1 . f . unK1)

instance Represented (Forget r) (Forget1 r) where
  type Representation (Forget r) = Forget1 r

  generically :: (OK x, OK y) => Forget1 r (Rep x) (Rep y) -> Forget r x y
  generically (Forget1 f) = Forget (f . from)

  ungenerically :: Forget r x y -> Forget1 r (Rec0 x) (Rec0 y)
  ungenerically (Forget f) = Forget1 (f . unK1)

instance Represented (AnnC w) (GAnnC w) where
  type Representation (AnnC w) = GAnnC w

  generically :: (OK x, OK y) => GAnnC w (Rep x) (Rep y) -> AnnC w x y
  generically (GAnnC f) = AnnC f

  ungenerically :: AnnC w x y -> GAnnC w (Rec0 x) (Rec0 y)
  ungenerically (AnnC f) = GAnnC f

instance Represented (ForgetA r w) (GForgetA r w) where
  type Representation (ForgetA r w) = GForgetA r w

  generically :: (OK x, OK y) => GForgetA r w (Rep x) (Rep y) -> ForgetA r w x y
  generically (GForgetA f) = ForgetA f

  ungenerically :: ForgetA r w x y -> GForgetA r w (Rec0 x) (Rec0 y)
  ungenerically (ForgetA f) = GForgetA f