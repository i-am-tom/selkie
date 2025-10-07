{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Kind (Type)
import GHC.Generics (Generic, Generically (..))
import Selkie.Annotation (Annotate)
import Selkie.Category (Category (id))
import Selkie.Optics (HasConstructor (..), HasField (..), Traversal')
import Selkie.Monad.State (MonadObservableState (..), runObservableStateT)
import Prelude hiding (id, read)

type State :: Type
data State
  = State
      { page :: Page
      , user :: User
      }
  deriving stock (Eq, Generic, Ord, Show)
  deriving Annotate via (Generically State)

type Page :: Type
data Page = Home | About
  deriving stock (Eq, Generic, Ord, Show)
  deriving Annotate via (Generically Page)

type User :: Type
data User
  = Authenticated Profile
  | Guest
  deriving stock (Eq, Generic, Ord, Show)
  deriving Annotate via (Generically User)

type Profile :: Type
data Profile
  = Profile
      { username :: String
      , likesDogs :: Bool
      }
  deriving stock (Eq, Generic, Ord, Show)
  deriving Annotate via (Generically Profile)

-- $> main
--
-- Name changed to Tom
-- No longer likes dogs
-- User logged out
main :: IO ()
main = runObservableStateT example (State Home Guest)

example :: (MonadObservableState State m, MonadIO m) => m ()
example = do
  let username :: Traversal' State String
      username = field @"user" . constructor @"Authenticated" . field @"username"
  
  let dogLiking :: Traversal' State Bool
      dogLiking = field @"user" . constructor @"Authenticated" . field @"likesDogs"

  listen username \name ->
    liftIO (putStrLn ("Name changed to " ++ name))
  
  listen dogLiking \case
    True -> liftIO (putStrLn "No longer likes dogs")
    False -> liftIO (putStrLn "Now likes dogs")

  listen (field @"user" . constructor @"Guest") \() ->
    liftIO (putStrLn ("User logged out"))
  
  update (field @"user") \_ -> Authenticated (Profile "Tom" True)
  update (field @"user") \_ -> Guest

  update dogLiking \x -> not x