{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Category.Generic where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:) (..), (:+:) (..), U1 (..), V1)
import Selkie.Category.Class (Category (..), Cartesian (..), Cocartesian (..), Terminal (..), Initial (..))

type CategoryG :: ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (Category c k, Terminal c U1 k, Initial c V1 k) => CategoryG c k | k -> c where

instance CategoryG Functor (:~>) where

type CategoryG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class CategoryG (Obj k) k => CategoryG' k
instance CategoryG (Obj k) k => CategoryG' k

type CartesianG :: ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class Cartesian c (:*:) k => CartesianG c k | k -> c

instance Cartesian c (:*:) k => CartesianG c k

type CartesianG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class CartesianG (Obj k) k => CartesianG' k
instance CartesianG (Obj k) k => CartesianG' k

type CocartesianG :: ((Type -> Type) -> Constraint) -> ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class Cocartesian c (:+:) k => CocartesianG c k | k -> c

instance Cocartesian c (:+:) k => CocartesianG c k

type CocartesianG' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class CocartesianG (Obj k) k => CocartesianG' k
instance CocartesianG (Obj k) k => CocartesianG' k