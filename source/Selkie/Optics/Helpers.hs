{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Optics.Helpers where

import Control.Natural ((:~>) (..))
import Data.Kind (Constraint, Type)
import GHC.Generics ((:*:) (..), (:+:) (..), K1 (..), M1 (..), Rec0, U1 (..))
import Selkie.Annotation (GAnnC (..), GForgetA (..))
import Selkie.Generic (Represented', Representation)
import Selkie.Profunctor (Profunctor', Strong', Choice', Forget1 (..))

type Optic :: (t -> t -> Type) -> t -> t -> t -> t -> Type
type Optic p s t a b = p a b -> p s t

type Optic' :: (t -> t -> Type) -> t -> t -> Type
type Optic' p s a = p a a -> p s s

---

type GIsoLike :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class Profunctor' p => GIsoLike p where
  meta :: Optic p (M1 i m x) (M1 i m y) x y
  unit :: Optic p U1 U1 (Rec0 ()) (Rec0 ())

instance GIsoLike (:~>) where
  meta :: Optic (:~>) (M1 i m x) (M1 i m y) x y
  meta (NT f) = NT \(M1 x) -> M1 (f x)

  unit :: Optic (:~>) U1 U1 (Rec0 ()) (Rec0 ())
  unit (NT _) = NT id

instance GIsoLike (GAnnC w) where
  meta :: Optic (GAnnC w) (M1 i m x) (M1 i m y) x y
  meta (GAnnC f) = GAnnC f

  unit :: Optic (GAnnC w) U1 U1 (Rec0 ()) (Rec0 ())
  unit (GAnnC f) = GAnnC f

instance GIsoLike (GForgetA r w) where
  meta :: Optic (GForgetA r w) (M1 i m x) (M1 i m y) x y
  meta (GForgetA f) = GForgetA f

  unit :: Optic (GForgetA r w) U1 U1 (Rec0 ()) (Rec0 ())
  unit (GForgetA f) = GForgetA f

instance GIsoLike (Forget1 r) where
  meta :: Optic (Forget1 r) (M1 i m x) (M1 i m y) x y
  meta (Forget1 f) = Forget1 \(M1 x) -> f x

  unit :: Optic (Forget1 r) U1 U1 (Rec0 ()) (Rec0 ())
  unit (Forget1 f) = Forget1 \_ -> f (K1 ())

type IsoLike :: (Type -> Type -> Type) -> Constraint
class (Represented' p, GIsoLike (Representation p)) => IsoLike p
instance (Represented' p, GIsoLike (Representation p)) => IsoLike p

type Iso :: Type -> Type -> Type -> Type -> Type
type Iso s t a b = forall p. IsoLike p => Optic p s t a b

type Iso' :: Type -> Type -> Type
type Iso' s a = Iso s s a a

---

type GLensLike :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (Strong' p, GIsoLike p) => GLensLike p where
  first :: Optic p (x :*: z) (y :*: z) x y
  second :: Optic p (z :*: x) (z :*: y) x y

instance GLensLike (:~>) where
  first :: Optic (:~>) (x :*: z) (y :*: z) x y
  first (NT f) = NT \(x :*: z) -> f x :*: z

  second :: Optic (:~>) (z :*: x) (z :*: y) x y
  second (NT f) = NT \(z :*: x) -> z :*: f x

instance GLensLike (GAnnC w) where
  first :: Optic (GAnnC w) (x :*: z) (y :*: z) x y
  first (GAnnC f) = GAnnC \(x :*: z) -> f x :*: z

  second :: Optic (GAnnC w) (z :*: x) (z :*: y) x y
  second (GAnnC f) = GAnnC \(z :*: x) -> z :*: f x

instance GLensLike (GForgetA r w) where
  first :: Optic (GForgetA r w) (x :*: z) (y :*: z) x y
  first (GForgetA f) = GForgetA \(x :*: _) -> f x

  second :: Optic (GForgetA r w) (z :*: x) (z :*: y) x y
  second (GForgetA f) = GForgetA \(_ :*: y) -> f y

instance GLensLike (Forget1 r) where
  first :: Optic (Forget1 r) (x :*: z) (y :*: z) x y
  first (Forget1 f) = Forget1 \(x :*: _) -> f x

  second :: Optic (Forget1 r) (z :*: x) (z :*: y) x y
  second (Forget1 f) = Forget1 \(_ :*: x) -> f x

type LensLike :: (Type -> Type -> Type) -> Constraint
class (Represented' p, GLensLike (Representation p)) => LensLike p
instance (Represented' p, GLensLike (Representation p)) => LensLike p

type Lens :: Type -> Type -> Type -> Type -> Type
type Lens s t a b = forall p. LensLike p => Optic p s t a b

type Lens' :: Type -> Type -> Type
type Lens' s a = Lens s s a a

---

type GPrismLike :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (Choice' p, GIsoLike p) => GPrismLike p where
  left :: Optic p (x :+: z) (y :+: z) x y
  right :: p x y -> p (z :+: x) (z :+: y)

instance GPrismLike (:~>) where
  left :: Optic (:~>) (x :+: z) (y :+: z) x y
  left (NT f) = NT \case
    L1 x -> L1 (f x)
    R1 y -> R1  y

  right :: Optic (:~>) (z :+: x) (z :+: y) x y
  right (NT f) = NT \case
    L1 x -> L1  x
    R1 y -> R1 (f y)

instance Monoid w => GPrismLike (GAnnC w) where
  left :: Optic (GAnnC w) (x :+: z) (y :+: z) x y
  left (GAnnC f) = GAnnC \(x :*: y) -> f x :*: y

  right :: Optic (GAnnC w) (z :+: x) (z :+: y) x y
  right (GAnnC f) = GAnnC \(x :*: y) -> x :*: f y

instance Monoid w => GPrismLike (GForgetA r w) where
  left :: Optic (GForgetA r w) (x :+: z) (y :+: z) x y
  left (GForgetA f) = GForgetA \(x :*: _) -> f x

  right :: Optic (GForgetA r w) (z :+: x) (z :+: y) x y
  right (GForgetA f) = GForgetA \(_ :*: y) -> f y

instance Monoid r => GPrismLike (Forget1 r) where
  left :: Optic (Forget1 r) (x :+: z) (y :+: z) x y
  left (Forget1 f) = Forget1 \case
    L1 x -> f x
    R1 _ -> mempty

  right :: Optic (Forget1 r) (z :+: x) (z :+: y) x y
  right (Forget1 f) = Forget1 \case
    L1 _ -> mempty
    R1 x -> f x

type PrismLike :: (Type -> Type -> Type) -> Constraint
class (Represented' p, GPrismLike (Representation p)) => PrismLike p
instance (Represented' p, GPrismLike (Representation p)) => PrismLike p

type Prism :: Type -> Type -> Type -> Type -> Type
type Prism s t a b = forall p. PrismLike p => Optic p s t a b

type Prism' :: Type -> Type -> Type
type Prism' s a = Prism s s a a

---

type GTraversalLike :: ((Type -> Type) -> (Type -> Type) -> Type) -> Constraint
class (GLensLike p, GPrismLike p) => GTraversalLike p
instance (GLensLike p, GPrismLike p) => GTraversalLike p

type TraversalLike :: (Type -> Type -> Type) -> Constraint
class (LensLike p, PrismLike p) => TraversalLike p
instance (LensLike p, PrismLike p) => TraversalLike p

type Traversal :: Type -> Type -> Type -> Type -> Type
type Traversal s t a b = forall p. TraversalLike p => Optic p s t a b

type Traversal' :: Type -> Type -> Type
type Traversal' s a = Traversal s s a a