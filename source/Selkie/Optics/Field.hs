{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedRecordUpdate #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Optics.Field where

import Data.Kind (Constraint, Type)
import GHC.Generics
import GHC.TypeLits (Symbol)
import Selkie.Utilities (Step, Or, type (<|>), Prepend)
import Selkie.Profunctor.Class (Strong (..))
import Selkie.Profunctor (ProfunctorG (..),StrongG')
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Selkie.Optics.Types (Lens', GWalk)

type HasField :: Symbol -> Type -> Type -> Constraint
class HasField x s a | x s -> a where
  field :: Lens' s a

instance GHasField (Field x (Rep s)) (Rep s) a => HasField x s a where
  field :: Lens' s a
  field = rec0 . gfield @(Field x (Rep s))

instance {-# OVERLAPPING #-} TypeError ('Text "He have no empty fields!") => HasField "" s s where
  field :: Lens' s s
  field = undefined

---

type GHasField :: [Step] -> (Type -> Type) -> Type -> Constraint
class GHasField path s a | path s -> a where
  gfield :: forall p. (StrongG' p, GWalk p s) => p (Rec0 a) (Rec0 a) -> p s s

instance GHasField path s a => GHasField path (M1 i m s) a where
  gfield :: (StrongG' p, GWalk p (M1 i m s)) => p (Rec0 a) (Rec0 a) -> p (M1 i m s) (M1 i m s)
  gfield = meta . gfield @path

instance GHasField path l a => GHasField ('Left ': path) (l :*: r) a where
  gfield :: (StrongG' p, GWalk p (l :*: r)) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gfield = first . gfield @path

instance GHasField path r a => GHasField ('Right ': path) (l :*: r) a where
  gfield :: (StrongG' p, GWalk p (l :*: r)) => p (Rec0 a) (Rec0 a) -> p (l :*: r) (l :*: r)
  gfield = second . gfield @path

instance a ~ b => GHasField '[] (Rec0 a) b where
  gfield :: (StrongG' p, GWalk p (Rec0 a)) => p (Rec0 a) (Rec0 a) -> p (Rec0 a) (Rec0 a)
  gfield = id

---

type Field :: Symbol -> (Type -> Type) -> [Step]
type Field x rep = Field_ x rep `Or` (ShowType x ':<>: 'Text " not found")

type Field_ :: Symbol -> (Type -> Type) -> Maybe [Step]
type family Field_ x rep where
  Field_ x (D1 m rs) = Field_ x rs
  Field_ x (C1 m rs) = Field_ x rs
  Field_ x (l :*: r) = Prepend 'Left (Field_ x l) <|> Prepend 'Right (Field_ x r)
  Field_ x (l :+: r) = TypeError ('Text "Sum types are not supported")

  Field_ x (S1 ('MetaSel ('Just x) _ _ _) _) = 'Just '[]
  Field_ x (S1 __________________________ _) = 'Nothing

  Field_ x U1 = TypeError ('Text "Unit types are not supported")
  Field_ x V1 = TypeError ('Text "Void types are not supported")