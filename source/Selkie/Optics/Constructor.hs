{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Optics.Constructor where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics hiding (Constructor, Meta)
import GHC.TypeLits (Symbol)
import Selkie.Generic (Constrained', Lift (..), Lift', RepK)
import Selkie.Optics.Internal (Constructor, HasMeta (..), HasMeta', Optic', Step)
import Selkie.Profunctor (Profunctor (..), Choice (..), Obj)

type ChoiceG :: (RepK -> RepK -> Type) -> Constraint
type ChoiceG p = Choice (:*:) (Arrow p) (Obj p) p

type GHasConstructor :: [Step] -> (RepK -> RepK -> Type) -> RepK -> Type -> Constraint
class (HasMeta' p, ChoiceG p) => GHasConstructor path p rep a | path rep -> a where
  gconstructor :: Optic' p rep (Rec0 a)

instance (GHasConstructor path p rep a, Obj p rep) => GHasConstructor path p (M1 i m rep) a where
  gconstructor :: (GHasConstructor path p rep a, Obj p rep) => p (Rec0 a) (Rec0 a) -> p (M1 i m rep) (M1 i m rep)
  gconstructor = meta . gconstructor @path

instance (GHasConstructor path p l a, Obj p l, Obj p r) => GHasConstructor ('Left ': path) p (l :*: r) a where
  gconstructor :: (GHasConstructor path p l a, Obj p l, Obj p r) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gconstructor = left . gconstructor @path

instance (GHasConstructor path p r a, Obj p l, Obj p r) => GHasConstructor ('Right ': path) p (l :*: r) a where
  gconstructor :: (GHasConstructor path p r a, Obj p l, Obj p r) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gconstructor = right . gconstructor @path

instance (HasMeta' p, ChoiceG p) => GHasConstructor '[] p (Rec0 a) a where
  gconstructor :: p (Rec0 a) (Rec0 a) -> p (Rec0 a) (Rec0 a)
  gconstructor = id

type GHasConstructor' :: Symbol -> (Type -> Type -> Type) -> Type -> Type -> Constraint
type GHasConstructor' x p s a = GHasConstructor (Constructor x (Rep s)) (Lifted p) (Rep s) a

type HasConstructor :: Symbol -> (Type -> Type -> Type) -> Type -> Type -> Constraint
class HasConstructor x p s a | x s -> a where
  constructor :: (Obj p s, Obj p a) => Optic' p s a

instance (Lift' p, Constrained' p s, GHasConstructor' x p s a) => HasConstructor x p s a where
  constructor :: (Lift' p, Constrained' p s, GHasConstructor' x p s a, Obj p s, Obj p a) => p a a -> p s s
  constructor = generically . gconstructor @(Constructor x (Rep s)) . ungenerically
