{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Profunctor.Generic where

import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:), (:+:), Generic (..), M1 (..), K1 (..), U1 (..), Rec0)
import Control.Natural ((:~>) (..))
import Selkie.Category.Class (Terminal (..))
import Selkie.Category.Generic (CategoryG, CartesianG, CocartesianG)
import Selkie.Profunctor.Class (Profunctor (..), Strong, Choice, ObjC, Forget1 (..))

type ProfunctorG :: ((Type -> Type) -> (Type -> Type) -> Type) -> ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (CategoryG c k, Profunctor k c p, Terminal c U1 k, forall i m x. c x => c (M1 i m x))
    => ProfunctorG k c p | p -> k c, k -> c where
  meta :: (c x, c y) => p x y -> p (M1 i m x) (M1 i m y)
  rec0 :: (Generic x, c (Rec0 x), c (Rep x)) => p (Rep x) (Rep x) -> p (Rec0 x) (Rec0 x)
  unit :: p (Rec0 ()) (Rec0 ()) -> p U1 U1

instance ProfunctorG (:~>) Functor (:~>) where
  meta :: (Functor x, Functor y) => (x :~> y) -> M1 i m x :~> M1 i m y
  meta = dimap (NT unM1) (NT M1)

  rec0 :: (Generic x, Functor (Rec0 x), Functor (Rep x)) => (Rep x :~> Rep x) -> Rec0 x :~> Rec0 x
  rec0 (NT f) = NT (K1 . to . f . from . unK1)

  unit :: Rec0 () :~> Rec0 () -> U1 :~> U1
  unit _ = NT id

instance ProfunctorG (:~>) Functor (Forget1 r) where
  meta :: (Functor x, Functor y) => Forget1 r x y -> Forget1 r (M1 i m x) (M1 i m y)
  meta (Forget1 k) = Forget1 \(M1 x) -> k x

  rec0 :: (Generic x, Functor (Rec0 x), Functor (Rep x)) => Forget1 r (Rep x) (Rep x) -> Forget1 r (Rec0 x) (Rec0 x)
  rec0 (Forget1 k) = Forget1 \(K1 x) -> k (from x)

  unit :: Forget1 r (Rec0 ()) (Rec0 ()) -> Forget1 r U1 U1
  unit (Forget1 k) = Forget1 \U1 -> k (K1 ())

type ProfunctorG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class ProfunctorG (Arrow p) (ObjC p) p => ProfunctorG' p
instance ProfunctorG (Arrow p) (ObjC p) p => ProfunctorG' p

type StrongG :: ((Type -> Type) -> (Type -> Type) -> Type) -> ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (CartesianG c k, ProfunctorG k c p, Strong (:*:) k c p) => StrongG k c p | p -> k c

instance (CartesianG c k, ProfunctorG k c p, Strong (:*:) k c p) => StrongG k c p

type StrongG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class StrongG (Arrow p) (ObjC p) p => StrongG' p
instance StrongG (Arrow p) (ObjC p) p => StrongG' p

type ChoiceG :: ((Type -> Type) -> (Type -> Type) -> Type) -> ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (CocartesianG c k, ProfunctorG k c p, Choice (:+:) k c p) => ChoiceG k c p | p -> k c

instance (CocartesianG c k, ProfunctorG k c p, Choice (:+:) k c p) => ChoiceG k c p

type ChoiceG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class ChoiceG (Arrow p) (ObjC p) p => ChoiceG' p
instance ChoiceG (Arrow p) (ObjC p) p => ChoiceG' p
