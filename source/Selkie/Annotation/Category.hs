{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeFamilies #-}

module Selkie.Annotation.Category where

import Data.Kind (Type)
import GHC.Generics ((:*:) (..), (:+:) (..))
import Selkie.Annotation.Types (Annotate (..), Annotate', GAnnotated (..), GAnnotate')
import Selkie.Category (Category (..), Cartesian (..), Cocartesian (..))
import Selkie.Generic (RepK)
import Prelude hiding (id, (.))

type Ann :: Type -> Type -> Type
newtype Ann a b = Ann (forall w. (Monoid w) => Annotated a w -> Annotated b w)

instance Category Annotate' Ann where
  type Obj Ann = Annotate'

  id :: Annotate' x => Ann x x
  id = Ann id

  (.) :: (Annotate' x, Annotate' y, Annotate' z) => Ann y z -> Ann x y -> Ann x z
  Ann f . Ann g = Ann (f . g)

instance Cartesian Annotate' (,) Ann where
  type Product Ann = (,)

  (△) :: (Annotate' x, Annotate' y, Annotate' z) => Ann x y -> Ann x z -> Ann x (y, z)
  Ann f △ Ann g = Ann \x -> f x :*: g x

  exl :: (Annotate' x, Annotate' y) => Ann (x, y) x
  exl = Ann \(x :*: _) -> x

  exr :: (Annotate' x, Annotate' y) => Ann (x, y) y
  exr = Ann \(_ :*: y) -> y

instance Cocartesian Annotate' (,) Ann where
  type Coproduct Ann = (,)

  (▽) :: (Annotate' x, Annotate' y, Annotate' z) => Ann x z -> Ann y z -> Ann (x, y) z
  Ann f ▽ Ann g = Ann \(x :*: y) -> f x <> g y

  inl :: (Annotate' x, Annotate' y) => Ann x (x, y)
  inl = Ann \x -> x :*: mempty

  inr :: (Annotate' x, Annotate' y) => Ann y (x, y)
  inr = Ann \y -> mempty :*: y

---

type GAnn :: RepK -> RepK -> Type
newtype GAnn f g = GAnn (forall w. (Monoid w) => GAnnotated f w -> GAnnotated g w)

instance Category GAnnotate' GAnn where
  type Obj GAnn = GAnnotate'

  id :: GAnnotate' rep => GAnn rep rep
  id = GAnn id

  (.) :: (GAnnotate' f, GAnnotate' g, GAnnotate' h) => GAnn g h -> GAnn f g -> GAnn f h
  GAnn f . GAnn g = GAnn (f . g)

instance Cartesian GAnnotate' (:*:) GAnn where
  type Product GAnn = (:*:)

  (△) :: (GAnnotate' f, GAnnotate' g, GAnnotate' h) => GAnn f g -> GAnn f h -> GAnn f (g :*: h)
  GAnn f △ GAnn g = GAnn \x -> f x :*: g x

  exl :: (GAnnotate' f, GAnnotate' g) => GAnn (f :*: g) f
  exl = GAnn \(x :*: _) -> x

  exr :: (GAnnotate' f, GAnnotate' g) => GAnn (f :*: g) g
  exr = GAnn \(_ :*: y) -> y

instance Cocartesian GAnnotate' (:*:) GAnn where
  type Coproduct GAnn = (:*:)

  (▽) :: (GAnnotate' f, GAnnotate' g, GAnnotate' h) => GAnn f h -> GAnn g h -> GAnn (f :*: g) h
  GAnn f ▽ GAnn g = GAnn \(x :*: y) -> f x <> g y

  inl :: (GAnnotate' f, GAnnotate' g) => GAnn f (f :*: g)
  inl = GAnn \x -> x :*: mempty

  inr :: (GAnnotate' f, GAnnotate' g) => GAnn g (f :*: g)
  inr = GAnn \x -> mempty :*: x