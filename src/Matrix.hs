-- | Matrices
module Matrix where

import Naturals
import VectorsBase


-- | @subMatrix n m x@ returns the submatrix obtained by deleting the @n@th row and @m@th column, provided @x@ is non-empty
subMatrix :: Fin ('S n) -> Fin ('S m) -> Vec ('S n) (Vec ('S m) a) -> Vec n (Vec m a)
subMatrix f g v = delete g <$> delete f v

-- | Return the determinant of a square matrix
det :: forall a n. Num a => Vec n (Vec n a) -> a
det VN               = 0
det (VC (VC x _) VN) = x
det v@(VC _ w)       = sum $ cof <$> enumerate v
    where
    -- j-th cofactor
    cof (j, VC x _) = sign j * x * minor (toFZ $ size w) j v

    sign :: Fin m -> a
    sign FZ = 1
    sign (FS FZ) = -1
    sign (FS (FS f)) = sign f

-- | Return the minor of a non-empty square matrix
minor :: Num a => Fin ('S n) -> Fin ('S n) -> Vec ('S n) (Vec ('S n) a) -> a
minor i j v = det (subMatrix i j v)


