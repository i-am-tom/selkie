{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FunctionalDependencies #-}

module Selkie.Monad.State where

import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (StateT, evalStateT, get, modify, state)
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Kind (Type, Constraint)
import Data.Monoid (Ap (..))
import Prelude hiding (read)

import Selkie.Annotation.Types (Ann, Annotate(..))
import Selkie.Optics (Traversal', (.~@), (^.@), (%~), (^?))

type MonadObservableState :: Type -> (Type -> Type) -> Constraint
class Monad m => MonadObservableState s m | m -> s where
  read :: Annotate a => Traversal' s a -> m (Maybe a)
  listen :: Annotate a => Traversal' s a -> (a -> m ()) -> m ()
  update :: Annotate a => Traversal' s a -> (a -> a) -> m ()

type Annotated :: Type -> Type -> Type
data Annotated w x = Annotated { value :: x, annotation :: Ann x w }

type ObservableStateT :: Type -> (Type -> Type) -> Type -> Type
newtype ObservableStateT s m x = ObservableStateT (StateT (Annotated (ObservableStateT s m ()) s) m x)
  deriving newtype (Functor, Applicative, Monad, MonadIO)
  deriving (Semigroup, Monoid) via (Ap (ObservableStateT s m) x)

runObservableStateT :: (Monad m, Annotate s) => ObservableStateT s m x -> s -> m x
runObservableStateT (ObservableStateT xs) s = evalStateT xs (Annotated s mempty)

instance Monad m => MonadObservableState s (ObservableStateT s m) where
  read :: Annotate a => Traversal' s a -> ObservableStateT s m (Maybe a)
  read l = fmap ((^? l) . value) (ObservableStateT get)

  listen :: Annotate a => Traversal' s a -> (a -> ObservableStateT s m ()) -> ObservableStateT s m ()
  listen l k = ObservableStateT do
    modify \(Annotated x ann) ->
      Annotated x $ ann & l .~@ do
        read l >>= \case
          Just x' -> k x'
          Nothing -> mempty

  update :: forall a. Annotate a => Traversal' s a -> (a -> a) -> ObservableStateT s m ()
  update l f = join do
    ObservableStateT do
      state \(Annotated x ann) ->
        ( fold (ann ^.@ l)
        , Annotated (x & l %~ f) ann
        )