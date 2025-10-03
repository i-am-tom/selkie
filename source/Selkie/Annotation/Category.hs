{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Annotation.Category where

import Data.Kind (Type)
import GHC.Generics ((:*:) (..), (:+:))
import Selkie.Annotation.Types (Annotate (..), GAnnotate (..))
import Selkie.Category (Category (..), Cartesian (..), Cocartesian (..))
import Prelude hiding ((.))

type AnnC :: Type -> Type -> Type -> Type
newtype AnnC w x y = AnnC { annC :: Ann x w -> Ann y w }

instance Category Annotate (AnnC w) where
  type Obj (AnnC w) = Annotate

  (.) :: (Annotate x, Annotate y, Annotate z) => AnnC w y z -> AnnC w x y -> AnnC w x z
  AnnC f . AnnC g = AnnC (f . g)

  id :: (Annotate x) => AnnC w x x
  id = AnnC \x -> x

instance Cartesian (,) Annotate (AnnC w) where
  type Product (AnnC w) = (,)
  
  (△) :: (Annotate x, Annotate y, Annotate z) => AnnC w x y -> AnnC w x z -> AnnC w x (y, z)
  AnnC f △ AnnC g = AnnC \x -> f x :*: g x
  
  exl :: (Annotate x, Annotate y) => AnnC w (x, y) x
  exl = AnnC \(x :*: _) -> x
  
  exr :: (Annotate x, Annotate y) => AnnC w (x, y) y
  exr = AnnC \(_ :*: y) -> y

instance Monoid w => Cocartesian Either Annotate (AnnC w) where
  type Sum (AnnC w) = Either
  
  (▽) :: (Annotate x, Annotate y, Annotate z) => AnnC w x z -> AnnC w y z -> AnnC w (Either x y) z
  AnnC f ▽ AnnC g = AnnC \(x :*: y) -> f x <> g y

  inl :: (Annotate x, Annotate y) => AnnC w x (Either x y)
  inl = AnnC \x -> x :*: mempty
  
  inr :: (Annotate x, Annotate y) => AnnC w y (Either x y)
  inr = AnnC \y -> mempty :*: y

type GAnnC :: Type -> (Type -> Type) -> (Type -> Type) -> Type
newtype GAnnC w x y = GAnnC { gannC :: GAnn x w -> GAnn y w }

instance Category GAnnotate (GAnnC w) where
  type Obj (GAnnC w) = GAnnotate
  
  (.) :: (GAnnotate x, GAnnotate y, GAnnotate z) => GAnnC w y z -> GAnnC w x y -> GAnnC w x z
  GAnnC f . GAnnC g = GAnnC (f . g)

  id :: (GAnnotate x) => GAnnC w x x
  id = GAnnC \x -> x

instance Cartesian (:*:) GAnnotate (GAnnC w) where
  type Product (GAnnC w) = (:*:)
  
  (△) :: (GAnnotate x, GAnnotate y, GAnnotate z) => GAnnC w x y -> GAnnC w x z -> GAnnC w x (y :*: z)
  GAnnC f △ GAnnC g = GAnnC \x -> f x :*: g x
  
  exl :: (GAnnotate x, GAnnotate y) => GAnnC w (x :*: y) x
  exl = GAnnC \(x :*: _) -> x
  
  exr :: (GAnnotate x, GAnnotate y) => GAnnC w (x :*: y) y
  exr = GAnnC \(_ :*: y) -> y

instance Monoid w => Cocartesian (:+:) GAnnotate (GAnnC w) where
  type Sum (GAnnC w) = (:+:)
  
  (▽) :: (GAnnotate x, GAnnotate y, GAnnotate z) => GAnnC w x z -> GAnnC w y z -> GAnnC w (x :+: y) z
  GAnnC f ▽ GAnnC g = GAnnC \(x :*: y) -> f x <> g y
  
  inl :: (GAnnotate x, GAnnotate y) => GAnnC w x (x :+: y)
  inl = GAnnC \x -> x :*: mempty
  
  inr :: (GAnnotate x, GAnnotate y) => GAnnC w y (x :+: y)
  inr = GAnnC \y -> mempty :*: y