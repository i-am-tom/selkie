{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Annotation.Profunctor where

import Data.Kind (Type)
import GHC.Generics ((:*:) (..), (:+:) (..))
import Prelude hiding ((.))
import Selkie.Annotation.Category (AnnC (..), GAnnC (..))
import Selkie.Annotation.Types (Annotate (..), GAnnotate (..))
import Selkie.Category (Category (..))
import Selkie.Profunctor (Profunctor (..), Strong (..), Choice (..))

instance Profunctor Annotate (AnnC w) (AnnC w) where
  type Arrow (AnnC w) = AnnC w

  dimap :: (Annotate a, Annotate b, Annotate c, Annotate d) => AnnC w a b -> AnnC w c d -> AnnC w b c -> AnnC w a d
  dimap pre post f = post . f . pre

  lmap :: (Annotate a, Annotate b, Annotate c) => AnnC w a b -> AnnC w b c -> AnnC w a c
  lmap pre f = f . pre

  rmap :: (Annotate b, Annotate c, Annotate d) => AnnC w c d -> AnnC w b c -> AnnC w b d
  rmap post f = post . f

instance Strong (,) Annotate (AnnC w) (AnnC w) where
  first :: (Annotate x, Annotate y) => AnnC w x y -> AnnC w (x, z) (y, z)
  first (AnnC f) = AnnC \(x :*: z) -> f x :*: z

  second :: (Annotate x, Annotate y) => AnnC w x y -> AnnC w (z, x) (z, y)
  second (AnnC f) = AnnC \(z :*: x) -> z :*: f x

instance Monoid w => Choice Either Annotate (AnnC w) (AnnC w) where
  left :: (Annotate x, Annotate y) => AnnC w x y -> AnnC w (Either x z) (Either y z)
  left (AnnC f) = AnnC \(x :*: y) -> f x :*: y

  right :: (Annotate x, Annotate y) => AnnC w x y -> AnnC w (Either z x) (Either z y)
  right (AnnC f) = AnnC \(z :*: x) -> z :*: f x

instance Profunctor GAnnotate (GAnnC w) (GAnnC w) where
  type Arrow (GAnnC w) = GAnnC w

  dimap :: (GAnnotate a, GAnnotate b, GAnnotate c, GAnnotate d) => GAnnC w a b -> GAnnC w c d -> GAnnC w b c -> GAnnC w a d
  dimap pre post f = post . f . pre

  lmap :: (GAnnotate a, GAnnotate b, GAnnotate c) => GAnnC w a b -> GAnnC w b c -> GAnnC w a c
  lmap pre f = f . pre

  rmap :: (GAnnotate b, GAnnotate c, GAnnotate d) => GAnnC w c d -> GAnnC w b c -> GAnnC w b d
  rmap post f = post . f

instance Strong (:*:) GAnnotate (GAnnC w) (GAnnC w) where
  first :: (GAnnotate x, GAnnotate y) => GAnnC w x y -> GAnnC w (x :*: z) (y :*: z)
  first (GAnnC f) = GAnnC \(x :*: z) -> f x :*: z

  second :: (GAnnotate x, GAnnotate y) => GAnnC w x y -> GAnnC w (z :*: x) (z :*: y)
  second (GAnnC f) = GAnnC \(z :*: x) -> z :*: f x

instance Monoid w => Choice (:+:) GAnnotate (GAnnC w) (GAnnC w) where
  left :: (GAnnotate x, GAnnotate y) => GAnnC w x y -> GAnnC w (x :+: z) (y :+: z)
  left (GAnnC f) = GAnnC \(x :*: y) -> f x :*: y

  right :: (GAnnotate x, GAnnotate y) => GAnnC w x y -> GAnnC w (z :+: x) (z :+: y)
  right (GAnnC f) = GAnnC \(z :*: x) -> z :*: f x

type ForgetA :: Type -> Type -> Type -> Type -> Type
newtype ForgetA r w a b = ForgetA { runForgetA :: Ann a w -> r }

---

instance Profunctor Annotate (AnnC w) (ForgetA r w) where
  type Arrow (ForgetA r w) = AnnC w

  dimap :: (Annotate a, Annotate b, Annotate c, Annotate d) => AnnC w a b -> AnnC w c d -> ForgetA r w b c -> ForgetA r w a d
  dimap (AnnC pre) _ (ForgetA f) = ForgetA \x -> f (pre x)

  lmap :: (Annotate a, Annotate b, Annotate c) => AnnC w a b -> ForgetA r w b c -> ForgetA r w a c
  lmap (AnnC pre) (ForgetA f) = ForgetA \x -> f (pre x)

  rmap :: (Annotate b, Annotate c, Annotate d) => AnnC w c d -> ForgetA r w b c -> ForgetA r w b d
  rmap _ (ForgetA f) = ForgetA f

instance Strong (,) Annotate (AnnC w) (ForgetA r w) where
  first :: (Annotate x, Annotate y) => ForgetA r w x y -> ForgetA r w (x, z) (y, z)
  first (ForgetA f) = ForgetA \(x :*: _) -> f x

  second :: (Annotate x, Annotate y) => ForgetA r w x y -> ForgetA r w (z, x) (z, y)
  second (ForgetA f) = ForgetA \(_ :*: y) -> f y

instance Monoid w => Choice Either Annotate (AnnC w) (ForgetA r w) where
  left :: (Annotate x, Annotate y) => ForgetA r w x y -> ForgetA r w (Either x z) (Either y z)
  left (ForgetA f) = ForgetA \(x :*: _) -> f x

  right :: (Annotate x, Annotate y) => ForgetA r w x y -> ForgetA r w (Either z x) (Either z y)
  right (ForgetA f) = ForgetA \(_ :*: y) -> f y

---

type GForgetA :: Type -> Type -> (Type -> Type) -> (Type -> Type) -> Type
newtype GForgetA r w a b = GForgetA { runGForgetA :: GAnn a w -> r }

instance Profunctor GAnnotate (GAnnC w) (GForgetA r w) where
  type Arrow (GForgetA r w) = GAnnC w

  dimap :: (GAnnotate a, GAnnotate b, GAnnotate c, GAnnotate d) => GAnnC w a b -> GAnnC w c d -> GForgetA r w b c -> GForgetA r w a d
  dimap (GAnnC pre) _ (GForgetA f) = GForgetA \x -> f (pre x)

  lmap :: (GAnnotate a, GAnnotate b, GAnnotate c) => GAnnC w a b -> GForgetA r w b c -> GForgetA r w a c
  lmap (GAnnC pre) (GForgetA f) = GForgetA \x -> f (pre x)

  rmap :: (GAnnotate b, GAnnotate c, GAnnotate d) => GAnnC w c d -> GForgetA r w b c -> GForgetA r w b d
  rmap _ (GForgetA f) = GForgetA f

instance Strong (:*:) GAnnotate (GAnnC w) (GForgetA r w) where
  first :: (GAnnotate x, GAnnotate y) => GForgetA r w x y -> GForgetA r w (x :*: z) (y :*: z)
  first (GForgetA f) = GForgetA \(x :*: _) -> f x

  second :: (GAnnotate x, GAnnotate y) => GForgetA r w x y -> GForgetA r w (z :*: x) (z :*: y)
  second (GForgetA f) = GForgetA \(_ :*: y) -> f y

instance Monoid w => Choice (:+:) GAnnotate (GAnnC w) (GForgetA r w) where
  left :: (GAnnotate x, GAnnotate y) => GForgetA r w x y -> GForgetA r w (x :+: z) (y :+: z)
  left (GForgetA f) = GForgetA \(x :*: _) -> f x

  right :: (GAnnotate x, GAnnotate y) => GForgetA r w x y -> GForgetA r w (z :+: x) (z :+: y)
  right (GForgetA f) = GForgetA \(_ :*: y) -> f y