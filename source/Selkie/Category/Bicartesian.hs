module Selkie.Category.Bicartesian where

import Data.Kind (Constraint, Type)
import Selkie.Category.Category (Category (..))
import Selkie.Category.Cartesian (Cartesian (..))
import Selkie.Category.Cocartesian (Cocartesian (..))

type Bicartesian :: (t -> t -> t) -> (t -> t -> t) -> (t -> Constraint) -> (t -> t -> Type) -> Constraint
class (Cartesian p c k, Cocartesian s c k) => Bicartesian p s c k
instance (Cartesian p c k, Cocartesian s c k) => Bicartesian p s c k

type Bicartesian' :: (t -> t -> Type) -> Constraint
type Bicartesian' k = Bicartesian (Product k) (Sum k) (Obj k) k
