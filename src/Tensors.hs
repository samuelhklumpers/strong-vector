{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines a fixed-size tensor datatype,
-- and includes the instances and tools to allow for user-friendly manipulation.
module Tensors (
    --module Vectors,
    module TensorsBase
    , module TensorsSparse)
    where

import TensorsBase
import TensorsSparse

