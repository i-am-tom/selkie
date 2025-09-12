{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Optics.Field where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics hiding (Meta)
import GHC.TypeLits (Symbol)
import Selkie.Generic (Constrained', Lift (..), Lift', RepK)
import Selkie.Optics.Internal (Field, HasMeta (..), HasMeta', Optic', Step)
import Selkie.Profunctor (Profunctor (..), Strong (..), Obj)

type StrongG :: (RepK -> RepK -> Type) -> Constraint
type StrongG p = Strong (:*:) (Arrow p) (Obj p) p

type GHasField :: [Step] -> (RepK -> RepK -> Type) -> RepK -> Type -> Constraint
class (HasMeta' p, StrongG p) => GHasField path p rep a | path rep -> a where
  gfield :: Optic' p rep (Rec0 a)

instance (GHasField path p rep a, Obj p rep) => GHasField path p (M1 i m rep) a where
  gfield :: (GHasField path p rep a, Obj p rep) => p (Rec0 a) (Rec0 a) -> p (M1 i m rep) (M1 i m rep)
  gfield = meta . gfield @path

instance (GHasField path p l a, Obj p l, Obj p r) => GHasField ('Left ': path) p (l :*: r) a where
  gfield :: (GHasField path p l a, Obj p l, Obj p r) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gfield = first . gfield @path

instance (GHasField path p r a, Obj p l, Obj p r) => GHasField ('Right ': path) p (l :*: r) a where
  gfield :: (GHasField path p r a, Obj p l, Obj p r) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gfield = second . gfield @path

instance (HasMeta' p, StrongG p) => GHasField '[] p (Rec0 a) a where
  gfield :: p (Rec0 a) (Rec0 a) -> p (Rec0 a) (Rec0 a)
  gfield = id

type GHasField' :: Symbol -> (Type -> Type -> Type) -> Type -> Type -> Constraint
type GHasField' x p s a = GHasField (Field x (Rep s)) (Lifted p) (Rep s) a

type HasField :: Symbol -> (Type -> Type -> Type) -> Type -> Type -> Constraint
class HasField x p s a | x s -> a where
  field :: (Obj p s, Obj p a) => Optic' p s a

instance (Lift' p, Constrained' p s, GHasField' x p s a) => HasField x p s a where
  field :: (Lift' p, Constrained' p s, GHasField' x p s a, Obj p s, Obj p a) => p a a -> p s s
  field = generically . gfield @(Field x (Rep s)) . ungenerically
