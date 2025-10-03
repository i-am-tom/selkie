{-# LANGUAGE BlockArguments #-}

module Selkie.Optics
  ( module M

  , (^.)
  , (%~)
  , (.~)

  , (^.@)
  , (.~@)
  ) where

import Selkie.Optics.Constructor as M
import Selkie.Optics.Field as M
import Selkie.Optics.Helpers as M

import Selkie.Annotation (Annotate (..), AnnC (..), ForgetA (..))
import Data.Profunctor (Forget (..))

(^.) :: Optic (Forget a) s t a b -> s -> a
(^.) l = runForget (l (Forget id))

(%~) :: Optic (->) s t a b -> (a -> b) -> (s -> t)
(%~) = id

(.~) :: Optic (->) s t a b -> b -> (s -> t)
(.~) l b = l %~ \_ -> b

(^.@) :: (Annotate a, Monoid w) => Optic' (ForgetA (Ann a w) w) s a -> Ann s w -> Ann a w
(^.@) l = runForgetA (l (ForgetA id))

(.~@) :: forall w s a. (Annotate a, Monoid w) => Optic' (AnnC w) s a -> w -> (Ann s w -> Ann s w)
(.~@) l w = annC (l (AnnC (attach @a w)))