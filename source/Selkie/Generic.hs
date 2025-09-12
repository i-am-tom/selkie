{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Generic where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import Data.Profunctor (Forget (..))
import GHC.Generics ((:+:), (:*:), Generic (..), Rec0, K1 (..), M1 (..), U1)
import Prelude hiding ((.))
import Selkie.Category (Category ((.)), Terminal)
import Selkie.Profunctor (Profunctor, Profunctor', Strong, Choice, Forget1 (..))

type RepK :: Type
type RepK = Type -> Type

---

type Lift :: (Type -> RepK -> Constraint) -> (RepK -> RepK -> Type) -> (Type -> Type -> Type) -> Constraint
class (Profunctor' p, Profunctor' p', Constrained p ~ c, Lifted p ~ p')
    => Lift c p' p | p -> p' c where
  type Constrained p :: Type -> RepK -> Constraint
  type Lifted p :: RepK -> RepK -> Type

  generically :: (c x (Rep x), c y (Rep y)) => p' (Rep x) (Rep y) -> p x y
  ungenerically :: p x y -> p' (Rec0 x) (Rec0 y)

type Lift' :: (Type -> Type -> Type) -> Constraint
type Lift' p = Lift (Constrained p) (Lifted p) p

type Constrained' :: (Type -> Type -> Type) -> Type -> Constraint
type Constrained' p s = Constrained p s (Rep s)

class (Generic x, Rep x ~ y) => IsRepresentedBy x y
instance (Generic x, Rep x ~ y) => IsRepresentedBy x y

instance Lift IsRepresentedBy (:~>) (->) where
  type Constrained (->) = IsRepresentedBy
  type Lifted (->) = (:~>)

  generically :: (IsRepresentedBy x (Rep x), IsRepresentedBy y (Rep y)) => Rep x :~> Rep y -> x -> y
  generically (NT f) = \x -> to (f (from x))

  ungenerically :: (x -> y) -> Rec0 x :~> Rec0 y
  ungenerically f = NT \(K1 x) -> K1 (f x)

instance Lift IsRepresentedBy (Forget1 r) (Forget r) where
  type Constrained (Forget r) = IsRepresentedBy
  type Lifted (Forget r) = Forget1 r

  generically :: (IsRepresentedBy x (Rep x), IsRepresentedBy y (Rep y)) => Forget1 r (Rep x) (Rep y) -> Forget r x y
  generically (Forget1 f) = Forget \x -> f (from x)

  ungenerically :: Forget r x y -> Forget1 r (Rec0 x) (Rec0 y)
  ungenerically (Forget f) = Forget1 \(K1 x) -> f x