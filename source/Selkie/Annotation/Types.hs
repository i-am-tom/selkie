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
class (Monoid1 (Ann x)) => Annotate x where
  type Ann x :: Type -> Type

  active :: Monoid w => x -> Ann x w -> w
  attach :: Monoid w => w -> Ann x w -> Ann x w

instance (Generic x, GAnnotate (Rep x))
    => Annotate (Generically x) where
  type Ann (Generically x) = GAnn (Rep x)

  active :: Monoid w => Generically x -> Ann (Generically x) w -> w
  active (Generically x) = gactive (from x)

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

  active :: Monoid w => Atomic x -> Ann (Atomic x) w -> w
  active _ (Identity ws) = ws

  attach :: Monoid w => w -> Ann (Atomic x) w -> Ann (Atomic x) w
  attach w (Identity ws) = Identity (w <> ws)

deriving via Atomic [x] instance Annotate [x]
deriving via Atomic Int instance Annotate Int
deriving via Atomic Bool instance Annotate Bool

---

type GAnnotate :: (Type -> Type) -> Constraint
class Monoid1 (GAnn rep) => GAnnotate rep where
  type GAnn rep :: Type -> Type

  gactive :: Monoid w => rep v -> GAnn rep w -> w
  gattach :: Monoid w => w -> GAnn rep w -> GAnn rep w

instance GAnnotate x => GAnnotate (G.M1 i m x) where
  type GAnn (G.M1 i m x) = GAnn x

  gactive :: Monoid w => G.M1 i m x v -> GAnn x w -> w
  gactive (G.M1 x) = gactive x

  gattach :: Monoid w => w -> GAnn x w -> GAnn x w
  gattach = gattach @x

instance (GAnnotate l, GAnnotate r) => GAnnotate (l G.:*: r) where
  type GAnn (l G.:*: r) = GAnn l G.:*: GAnn r

  gactive :: Monoid w => (l G.:*: r) v -> (GAnn l G.:*: GAnn r) w -> w
  gactive (l G.:*: r) (a G.:*: b) = gactive l a <> gactive r b

  gattach :: Monoid w => w -> (GAnn l G.:*: GAnn r) w -> (GAnn l G.:*: GAnn r) w
  gattach w (l G.:*: r) = gattach @l w l G.:*: gattach @r w r

instance (GAnnotate l, GAnnotate r) => GAnnotate (l G.:+: r) where
  type GAnn (l G.:+: r) = GAnn l G.:*: GAnn r

  gactive :: Monoid w => (l G.:+: r) v -> (GAnn l G.:*: GAnn r) w -> w
  gactive (G.L1 l) (a G.:*: _) = gactive l a
  gactive (G.R1 r) (_ G.:*: b) = gactive r b

  gattach :: Monoid w => w -> (GAnn l G.:*: GAnn r) w -> (GAnn l G.:*: GAnn r) w
  gattach w (a G.:*: b) = gattach @l w a G.:*: gattach @r w b

instance GAnnotate G.U1 where
  type GAnn G.U1 = Identity

  gactive :: Monoid w => G.U1 v -> Identity w -> w
  gactive _ (Identity ws) = ws

  gattach :: Monoid w => w -> Identity w -> Identity w
  gattach w (Identity ws) = Identity (w <> ws)

instance Annotate x => GAnnotate (G.Rec0 x) where
  type GAnn (G.Rec0 x) = Ann x

  gactive :: Monoid w => G.Rec0 x v -> Ann x w -> w
  gactive (G.K1 x) = active x

  gattach :: Monoid w => w -> Ann x w -> Ann x w
  gattach = attach @x
