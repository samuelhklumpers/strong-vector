{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines a fixed-size vector datatype,
-- and includes the instances and tools to allow for user-friendly manipulation.
module Vectors (
    --module Vectors,
    module VectorsBase
    , module VectorsLens
    , module VectorsSparse)
    where

import VectorsBase
import VectorsLens
import VectorsSparse

