{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Selkie.Annotation.Types where

import Data.Functor.Identity (Identity (..))
import Data.Kind (Type, Constraint)
import GHC.Generics (Generic (..), Generically (..))
import GHC.Generics qualified as G
import Prelude hiding ((.), id)

-- We can't have the QC directly because we want a type family in the head. We
-- can't use an MPTC because it breaks deriving. So, hacks.
class (forall x. Monoid x => Monoid (t x)) => Monoid1 t
instance (forall x. Monoid x => Monoid (t x)) => Monoid1 t

-- No QC because we can't have type families in the head, so it has to be a
-- MPTC, which means deriving is ugly.
type Annotate :: Type -> Constraint
class (Foldable (Ann x), Monoid1 (Ann x)) => Annotate x where
  type Ann x :: Type -> Type

  attach :: Monoid w => w -> Ann x w -> Ann x w

instance (Generic x, Foldable (GAnn (Rep x)), GAnnotate (Rep x))
    => Annotate (Generically x) where
  type Ann (Generically x) = GAnn (Rep x)

  attach :: Monoid w => w -> Ann (Generically x) w -> Ann (Generically x) w
  attach = gattach @(Rep x)

deriving via Generically (x, y) instance (Annotate x, Annotate y) => Annotate (x, y)
deriving via Generically (Either x y) instance (Annotate x, Annotate y) => Annotate (Either x y)
deriving via Generically () instance Annotate ()

type Atomic :: Type -> Type
newtype Atomic x = Atomic x
  deriving stock (Eq, Ord, Show)

instance Annotate (Atomic x) where
  type Ann (Atomic x) = Identity

  attach :: Monoid w => w -> Ann (Atomic x) w -> Ann (Atomic x) w
  attach w (Identity ws) = Identity (w <> ws)

deriving via Atomic [x] instance Annotate [x]
deriving via Atomic Int instance Annotate Int
deriving via Atomic Bool instance Annotate Bool

---

type GAnnotate :: (Type -> Type) -> Constraint
class (Foldable (GAnn rep), Monoid1 (GAnn rep)) => GAnnotate rep where
  type GAnn rep :: Type -> Type

  gattach :: Monoid w => w -> GAnn rep w -> GAnn rep w

instance GAnnotate x => GAnnotate (G.M1 i m x) where
  type GAnn (G.M1 i m x) = GAnn x

  gattach :: Monoid w => w -> GAnn x w -> GAnn x w
  gattach = gattach @x

instance (GAnnotate l, GAnnotate r) => GAnnotate (l G.:*: r) where
  type GAnn (l G.:*: r) = GAnn l G.:*: GAnn r

  gattach :: Monoid w => w -> (GAnn l G.:*: GAnn r) w -> (GAnn l G.:*: GAnn r) w
  gattach w (l G.:*: r) = gattach @l w l G.:*: gattach @r w r

instance (GAnnotate l, GAnnotate r) => GAnnotate (l G.:+: r) where
  type GAnn (l G.:+: r) = GAnn l G.:*: GAnn r

  gattach :: Monoid w => w -> (GAnn l G.:*: GAnn r) w -> (GAnn l G.:*: GAnn r) w
  gattach w (a G.:*: b) = gattach @l w a G.:*: gattach @r w b

instance GAnnotate G.U1 where
  type GAnn G.U1 = Identity

  gattach :: Monoid w => w -> Identity w -> Identity w
  gattach w (Identity ws) = Identity (w <> ws)

instance Annotate x => GAnnotate (G.Rec0 x) where
  type GAnn (G.Rec0 x) = Ann x

  gattach :: Monoid w => w -> Ann x w -> Ann x w
  gattach = attach @x
