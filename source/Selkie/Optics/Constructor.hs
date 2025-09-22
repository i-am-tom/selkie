{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedRecordUpdate #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Optics.Constructor where

import Data.Kind (Constraint, Type)
import GHC.Generics hiding (Constructor)
import GHC.TypeLits (Symbol)
import Selkie.Utilities (Step, Or, type (<|>), Prepend)
import Selkie.Profunctor.Class (Choice (..))
import Selkie.Profunctor (ProfunctorG (..),ChoiceG')
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Selkie.Optics.Types (Prism', GWalk)

type HasConstructor :: Symbol -> Type -> Type -> Constraint
class HasConstructor x s a | x s -> a where
  constructor :: Prism' s a

instance GHasConstructor (Constructor x (Rep s)) (Rep s) a => HasConstructor x s a where
  constructor :: Prism' s a
  constructor = rec0 . gconstructor @(Constructor x (Rep s))

instance {-# OVERLAPPING #-} TypeError ('Text "He have no empty constructors!") => HasConstructor "" s s where
  constructor :: Prism' s s
  constructor = undefined

---

type GHasConstructor :: [Step] -> (Type -> Type) -> Type -> Constraint
class GHasConstructor path s a | path s -> a where
  gconstructor :: forall p. (ChoiceG' p, GWalk p s) => p (Rec0 a) (Rec0 a) -> p s s

instance GHasConstructor path s a => GHasConstructor path (M1 i m s) a where
  gconstructor :: (ChoiceG' p, GWalk p (M1 i m s)) => p (Rec0 a) (Rec0 a) -> p (M1 i m s) (M1 i m s)
  gconstructor = meta . gconstructor @path

instance GHasConstructor path l a => GHasConstructor ('Left ': path) (l :+: r) a where
  gconstructor :: (ChoiceG' p, GWalk p (l :+: r)) => p (Rec0 a) (Rec0 a) -> p (l :+: r) (l :+: r)
  gconstructor = left . gconstructor @path

instance GHasConstructor path r a => GHasConstructor ('Right ': path) (l :+: r) a where
  gconstructor :: (ChoiceG' p, GWalk p (l :+: r)) => p (Rec0 a) (Rec0 a) -> p (l :+: r) (l :+: r)
  gconstructor = right . gconstructor @path

instance GHasConstructor '[] (Rec0 a) a where
  gconstructor :: (ChoiceG' p, GWalk p (Rec0 a)) => p (Rec0 a) (Rec0 a) -> p (Rec0 a) (Rec0 a)
  gconstructor = id

instance GHasConstructor '[] U1 () where
  gconstructor :: (ChoiceG' p, GWalk p U1) => p (Rec0 ()) (Rec0 ()) -> p U1 U1
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