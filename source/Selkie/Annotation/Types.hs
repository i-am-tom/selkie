{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Annotation.Types where

import Data.Functor.Identity (Identity (..))
import Data.Foldable (fold)
import Data.Kind (Constraint, Type)
import GHC.Generics ((:+:) (..), (:*:) (..), Generic (..), Generically (..), M1 (..), K1 (..), Rec0)
import Selkie.Generic (RepK)

type Annotate :: (Type -> Type) -> Type -> Constraint
class (Annotated x ~ a, Foldable a, forall w. (Monoid w) => Monoid (a w))
    => Annotate a x | x -> a where
  type Annotated x :: Type -> Type

  attach :: Monoid w => w -> a w -> a w
  change :: Monoid w => x -> x -> a w -> w

type Annotate' :: Type -> Constraint
class Annotate (Annotated x) x => Annotate' x
instance Annotate (Annotated x) x => Annotate' x

type Atomic :: Type -> Type
newtype Atomic x = Atomic x
  deriving stock (Eq)

instance Eq x => Annotate Identity (Atomic x) where
  type Annotated (Atomic x) = Identity

  attach :: Monoid w => w -> Identity w -> Identity w
  attach w (Identity ws) = Identity (w <> ws)

  change :: Monoid w => Atomic x -> Atomic x -> Identity w -> w
  change x y (Identity ws) = if x == y then mempty else ws

---

type GAnnotate :: (Type -> Type) -> (Type -> Type) -> Constraint
class (GAnnotated rep ~ a, Foldable a, forall w. (Monoid w) => Monoid (a w))
    => GAnnotate a rep | rep -> a where
  type GAnnotated rep :: Type -> Type

  gattach :: Monoid w => w -> a w -> a w
  gchange :: Monoid w => rep v -> rep v -> a w -> w

type GAnnotate' :: RepK -> Constraint
class GAnnotate (GAnnotated rep) rep => GAnnotate' rep
instance GAnnotate (GAnnotated rep) rep => GAnnotate' rep

instance (GAnnotate a x, forall w. Monoid w => Monoid (a w))
    => GAnnotate a (M1 i m x) where
  type GAnnotated (M1 i m x) = GAnnotated x

  gattach :: Monoid w => w -> a w -> a w
  gattach = gattach @_ @x

  gchange :: Monoid w => M1 i m x v -> M1 i m x v -> a w -> w
  gchange (M1 x) (M1 y) = gchange x y

instance (GAnnotate l x, GAnnotate r y) => GAnnotate (l :*: r) (x :+: y) where
  type GAnnotated (x :+: y) = GAnnotated x :*: GAnnotated y

  gattach :: Monoid w => w -> (l :*: r) w -> (l :*: r) w
  gattach w (xs :*: ys) = gattach @_ @x w xs :*: gattach @_ @y w ys

  gchange :: Monoid w => (x :+: y) v -> (x :+: y) v -> (:*:) l r w -> w
  gchange xs ys (l :*: r) = case (xs, ys) of
    (L1 x, L1 y) -> gchange x y l
    (R1 x, R1 y) -> gchange x y r
    ____________ -> fold (l :*: r)

instance (GAnnotate l x, GAnnotate r y) => GAnnotate (l :*: r) (x :*: y) where
  type GAnnotated (x :*: y) = GAnnotated x :*: GAnnotated y

  gattach :: Monoid w => w -> (l :*: r) w -> (l :*: r) w
  gattach w (l :*: r) = gattach @_ @x w l :*: gattach @_ @y w r

  gchange :: Monoid w => (x :*: y) v -> (x :*: y) v -> (:*:) l r w -> w
  gchange (x :*: y) (x' :*: y') (l :*: r) = gchange x x' l <> gchange y y' r

instance Annotate a x => GAnnotate a (Rec0 x) where
  type GAnnotated (Rec0 x) = Annotated x

  gattach :: Monoid w => w -> a w -> a w
  gattach = attach @_ @x

  gchange :: Monoid w => Rec0 x v -> Rec0 x v -> a w -> w
  gchange (K1 x) (K1 y) = change x y

instance (Generic s, GAnnotate a (Rep s), Foldable a)
    => Annotate a (Generically s) where
  type Annotated (Generically s) = GAnnotated (Rep s)

  attach :: Monoid w => w -> a w -> a w
  attach = gattach @_ @(Rep s)

  change :: Monoid w => Generically s -> Generically s -> a w -> w
  change (Generically x) (Generically y) = gchange (from x) (from y)

deriving via Generically (x, y)
  instance (Annotate a x, Annotate b y)
    => Annotate (a :*: b) (x, y)

deriving via Generically (Either x y)
  instance (Annotate a x, Annotate b y)
    => Annotate (a :*: b) (Either x y)