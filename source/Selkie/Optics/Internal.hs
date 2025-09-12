{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Optics.Internal where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:), (:+:), U1, V1, C1, D1, S1, Meta (..), M1 (..))
import GHC.TypeLits (ErrorMessage (..), Symbol, TypeError)
import Selkie.Profunctor (Profunctor, Arrow, Obj)

type Optic :: (t -> t -> Type) -> t -> t -> t -> t -> Type
type Optic p s t a b = p a b -> p s t

type Optic' :: (t -> t -> Type) -> t -> t -> Type
type Optic' p s a = Optic p s s a a

type RepK :: Type
type RepK = Type -> Type

type HasMeta :: (RepK -> RepK -> Type) -> (RepK -> Constraint) -> (RepK -> RepK -> Type) -> Constraint
class (Profunctor k c p, forall i m x. c x => c (M1 i m x)) => HasMeta k c p | p -> k c where
  meta :: (c x, c y) => Optic p (M1 i m x) (M1 i m y) x y

instance HasMeta (:~>) Functor (:~>) where
  meta :: (Functor x, Functor y) => x :~> y -> M1 i m x :~> M1 i m y
  meta (NT f) = NT \(M1 x) -> M1 (f x)

type HasMeta' :: (RepK -> RepK -> Type) -> Constraint
type HasMeta' p = HasMeta (Arrow p) (Obj p) p

---

type Step :: Type
type Step = () -> Either () ()

type Or :: Maybe k -> ErrorMessage -> k
type family Or xs e where
  Or  'Nothing  e = TypeError e
  Or ('Just xs) _ = xs

type (<|>) :: Maybe k -> Maybe k -> Maybe k
type family xs <|> ys where
  'Just xs <|> 'Nothing = 'Just xs
  'Nothing <|> 'Just ys = 'Just ys

type Prepend :: k -> Maybe [k] -> Maybe [k]
type family Prepend x xs where
  Prepend x  'Nothing  = 'Nothing
  Prepend x ('Just xs) = 'Just (x ': xs)

---

type Field :: Symbol -> (Type -> Type) -> [Step]
type Field x rep = Field_ x rep `Or` (ShowType x ':<>: 'Text " not found")

type Field_ :: Symbol -> (Type -> Type) -> Maybe [Step]
type family Field_ x rep where
  Field_ x (D1 m rs) = Field_ x rs
  Field_ x (C1 m rs) = Field_ x rs
  Field_ x (l :*: r) = Prepend 'Left (Field_ x l) <|> Prepend 'Right (Field_ x r)

  Field_ x (S1 ('MetaSel ('Just x) _ _ _) _) = 'Just '[]
  Field_ x (S1 __________________________ _) = 'Nothing

  Field_ x (l :+: r) = TypeError ('Text "Sum types are not supported")
  Field_ x U1 = TypeError ('Text "Unit types are not supported")
  Field_ x V1 = TypeError ('Text "Void types are not supported")

---

type Constructor :: Symbol -> (Type -> Type) -> [Step]
type Constructor x rep = Constructor_ x rep `Or` (ShowType x ':<>: 'Text " not found")

type Constructor_ :: Symbol -> (Type -> Type) -> Maybe [Step]
type family Constructor_ x rep where
  Constructor_ x (D1 m rs) = Constructor_ x rs
  Constructor_ x (l :+: r) = Prepend 'Left (Constructor_ x l) <|> Prepend 'Right (Constructor_ x r)

  Constructor_ x (C1 ('MetaCons x _ _) _) = 'Just '[]
  Constructor_ x (C1 _________________ _) = 'Nothing
  Constructor_ x (S1 _________________ _) = TypeError ('Text "How did this happen?")

  Constructor_ x (l :*: r) = TypeError ('Text "Product types are not supported")
  Constructor_ x U1 = TypeError ('Text "Unit types are not supported")
  Constructor_ x V1 = TypeError ('Text "Void types are not supported")