{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Optics.Constructor where

import Data.Kind (Constraint, Type)
import GHC.Generics hiding (Constructor)
import GHC.TypeLits (Symbol)
import Selkie.Utilities (Step, Or, type (<|>), Prepend)
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Selkie.Generic (Represented (..), OK)
import Selkie.Optics.Helpers (Prism', GPrismLike (..), GIsoLike (..))

type HasConstructor :: Symbol -> Type -> Type -> Constraint
class HasConstructor x s a | x s -> a where
  constructor :: OK s => Prism' s a

instance GHasConstructor (Constructor x (Rep s)) (Rep s) a => HasConstructor x s a where
  constructor :: OK s => Prism' s a
  constructor = generically . gconstructor @(Constructor x (Rep s)) . ungenerically

instance {-# OVERLAPPING #-} TypeError ('Text "No empty fields!") => HasConstructor "" s s where
  constructor :: OK s => Prism' s s
  constructor = undefined

---

type GHasConstructor :: [Step] -> (Type -> Type) -> Type -> Constraint
class GHasConstructor path s a | path s -> a where
  gconstructor :: forall p. GPrismLike p => p (Rec0 a) (Rec0 a) -> p s s

instance GHasConstructor path s a => GHasConstructor path (M1 i m s) a where
  gconstructor :: (GPrismLike p) => p (Rec0 a) (Rec0 a) -> p (M1 i m s) (M1 i m s)
  gconstructor = meta . gconstructor @path

instance GHasConstructor path l a => GHasConstructor ('Left ': path) (l :+: r) a where
  gconstructor :: (GPrismLike p) => p (Rec0 a) (Rec0 a) -> p (l :+: r) (l :+: r)
  gconstructor = left . gconstructor @path

instance GHasConstructor path r a => GHasConstructor ('Right ': path) (l :+: r) a where
  gconstructor :: (GPrismLike p) => p (Rec0 a) (Rec0 a) -> p (l :+: r) (l :+: r)
  gconstructor = right . gconstructor @path

instance a ~ b => GHasConstructor '[] (Rec0 a) b where
  gconstructor :: (GPrismLike p) => p (Rec0 a) (Rec0 a) -> p (Rec0 a) (Rec0 a)
  gconstructor = id

instance GHasConstructor '[] U1 () where
  gconstructor :: (GPrismLike p) => p (Rec0 ()) (Rec0 ()) -> p U1 U1
  gconstructor = unit

---

type Constructor :: Symbol -> (Type -> Type) -> [Step]
type Constructor x rep = Constructor_ x rep `Or` (ShowType x ':<>: 'Text " not found")

type Constructor_ :: Symbol -> (Type -> Type) -> Maybe [Step]
type family Constructor_ x rep where
  Constructor_ x (D1 m rs) = Constructor_ x rs
  Constructor_ x (l :+: r) = Prepend 'Left (Constructor_ x l) <|> Prepend 'Right (Constructor_ x r)
  Constructor_ x (l :*: r) = TypeError ('Text "Product types are not supported")

  Constructor_ x (C1 ('MetaCons x _ _) _) = 'Just '[]
  Constructor_ x (C1 _________________ _) = 'Nothing
  Constructor_ x (S1 _________________ _) = TypeError ('Text "How did this happen?")

  Constructor_ x U1 = TypeError ('Text "Unit types are not supported")
  Constructor_ x V1 = TypeError ('Text "Void types are not supported")