{-# LANGUAGE BlockArguments #-}

module Selkie.Optics
  ( module M

  , (^.)
  , (^?)
  , (%~)
  , (.~)

  , (^.@)
  , (.~@)
  ) where

import Selkie.Optics.Constructor as M
import Selkie.Optics.Field as M
import Selkie.Optics.Helpers as M

import Data.Monoid (Last (..))
import Selkie.Annotation (Annotate (..), AnnC (..), ForgetA (..))
import Data.Profunctor (Forget (..))

(^.) :: s -> Optic (Forget a) s t a b -> a
(^.) s l = runForget (l (Forget id)) s

(^?) :: s -> Optic (Forget (Last a)) s t a b -> Maybe a
(^?) s l = getLast (runForget (l (Forget pure)) s)

(%~) :: Optic (->) s t a b -> (a -> b) -> (s -> t)
(%~) = id

(.~) :: Optic (->) s t a b -> b -> (s -> t)
(.~) l b = l %~ \_ -> b

(^.@) :: (Annotate a, Monoid w) => Ann s w -> Optic' (ForgetA (Ann a w) w) s a -> Ann a w
(^.@) s l = runForgetA (l (ForgetA id)) s

(.~@) :: forall w s a. (Annotate a, Monoid w) => Optic' (AnnC w) s a -> w -> (Ann s w -> Ann s w)
(.~@) l w = annC (l (AnnC (attach @a w)))