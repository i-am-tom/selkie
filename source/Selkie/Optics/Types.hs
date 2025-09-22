{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Selkie.Optics.Types where

import Data.Kind (Constraint, Type)
import GHC.Generics
import Selkie.Profunctor (ChoiceG', ObjC, StrongG')

type Walk :: ((Type -> Type) -> (Type -> Type) -> Type) -> Type -> Constraint
class (Generic s, ObjC p (Rec0 s), ObjC p (Rep s), GWalk p (Rep s)) => Walk p s
instance (Generic s, ObjC p (Rec0 s), ObjC p (Rep s), GWalk p (Rep s)) => Walk p s

type GWalk :: ((Type -> Type) -> (Type -> Type) -> Type) -> (Type -> Type) -> Constraint
type family GWalk p xs where
  GWalk p (M1 i m xs) = (ObjC p xs, GWalk p xs)
  GWalk p (ls :+: rs) = (ObjC p ls, ObjC p rs, GWalk p ls, GWalk p rs)
  GWalk p (ls :*: rs) = (ObjC p ls, ObjC p rs, GWalk p ls, GWalk p rs)
  GWalk p (K1 R leaf) = ()
  GWalk p  U1         = ()
  GWalk p  V1         = ()

type Optic :: ((Type -> Type) -> (Type -> Type) -> Type) -> Type -> Type -> Type -> Type -> Type
type Optic p s t a b = p (Rec0 a) (Rec0 b) -> p (Rec0 s) (Rec0 t)

type Optic' :: ((Type -> Type) -> (Type -> Type) -> Type) -> Type -> Type -> Type
type Optic' p s a = Optic p s s a a

type Lens :: Type -> Type -> Type -> Type -> Type
type Lens s t a b = forall p. (StrongG' p, Walk p s, Walk p t) => Optic p s t a b

type Lens' :: Type -> Type -> Type
type Lens' s a = Lens s s a a

type Prism :: Type -> Type -> Type -> Type -> Type
type Prism s t a b = forall p. (ChoiceG' p, Walk p s, Walk p t) => Optic p s t a b

type Prism' :: Type -> Type -> Type
type Prism' s a = Prism s s a a

type Traversal :: Type -> Type -> Type -> Type -> Type
type Traversal s t a b = forall p. (ChoiceG' p, StrongG' p, Walk p s, Walk p t) => Optic p s t a b

type Traversal' :: Type -> Type -> Type
type Traversal' s a = Traversal s s a a