{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Vectors
module Vectors (
    --module Vectors,
    module VectorsBase
    , module VectorsLens
    , module VectorsSparse)
    -- Publicly re-export the contents of the base modules
    where

import VectorsBase
import VectorsLens
import VectorsSparse

