{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances #-} -- only used for show instances
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Database where
import Vectors hiding ((++))
import NaturalsBase
import SingBase
import Tensors
import Naturals (toFin, sizeList, (-|))
import NaturalsFams
import Data.Type.Bool
import qualified Data.Type.Equality as T


data C = CA | CB | CC | CD | CE | CF | CG 
       | CH | CI | CJ | CK | CL | CM | CN 
       | CO | CP | CQ | CR | CS | CT | CU 
       | CV | CW | CX | CY | CZ 
       deriving (Eq, Show)

data Character c where
    SCA :: Character 'CA
    SCB :: Character 'CB
    SCC :: Character 'CC
    SCD :: Character 'CD
    SCE :: Character 'CE
    SCF :: Character 'CF
    SCG :: Character 'CG
    SCH :: Character 'CH
    SCI :: Character 'CI
    SCJ :: Character 'CJ
    SCK :: Character 'CK
    SCL :: Character 'CL
    SCM :: Character 'CM
    SCN :: Character 'CN
    SCO :: Character 'CO
    SCP :: Character 'CP
    SCQ :: Character 'CQ
    SCR :: Character 'CR
    SCS :: Character 'CS
    SCT :: Character 'CT
    SCU :: Character 'CU
    SCV :: Character 'CV
    SCW :: Character 'CW
    SCX :: Character 'CX
    SCY :: Character 'CY
    SCZ :: Character 'CZ


instance Show (Character c) where
    show SCA = "a"
    show SCB = "b"
    show SCC = "c"
    show SCD = "d"
    show SCE = "e"
    show SCF = "f"
    show SCG = "g"
    show SCH = "h"
    show SCI = "i"
    show SCJ = "j"
    show SCK = "k"
    show SCL = "l"
    show SCM = "m"
    show SCN = "n"
    show SCO = "o"
    show SCP = "p"
    show SCQ = "q"
    show SCR = "r"
    show SCS = "s"
    show SCT = "t"
    show SCU = "u"
    show SCV = "v"
    show SCW = "w"
    show SCX = "x"
    show SCY = "y"
    show SCZ = "z"

type STRING = TList Character

data Table c r = Table (List c) (Tensor (Length c ': r ': '[]) String) deriving (Show)

instance Show (List h) where
  show _                   = ""

instance Show (STRING s) where
    show XNil                    = ""
    show (XCons c cs)            = show c ++ show cs

data Header :: [C] -> N -> * where
  Header ::  Nat a -> Header n a deriving (Show)

class Member string xs t head where
  select' :: STRING s -> List xs -> t

-- Is true if the string equals the first element in the list
type family Head string ss where
  Head s (Header s' _ ': _) = s T.== s'
  Head s _                  = 'False

-- Return the index of the string in the list
type family Lookup string ss :: N where
  Lookup s (Header s' t ': tail) = If (s T.== s') t (Lookup s tail)

select :: forall s ss. Member s ss (Nat (Lookup s ss)) (Head s ss) => STRING s -> List ss -> Nat (Lookup s ss)
select = select' @s @ss @(Nat (Lookup s ss)) @(Head s ss)

instance Member s (Header s t ': tail) (Nat t) 'True where
  select' _ (XCons (Header x) _) = x
instance Member s tail t (Head s tail) => Member s (Header s' t' ': tail) t 'False where
  select' string (XCons _ xs) = select' @s @tail @t @(Head s tail) string xs

-- | Insert a row into a table
insertRow :: Vec (Length c) String -> Table c r ->  Table c ('S r)
insertRow ss (Table h (TC xs)) = Table h (TC (fmap (uncurry addToFront) (merge ss xs)))
  where merge :: Vec n String -> Vec n (Tensor ix String) -> Vec n (String, Tensor ix String)
        merge VN VN               = VN
        merge (VC v vs) (VC y ys) = VC (v,y) (merge vs ys)
        addToFront :: a -> Tensor (m ': '[]) a -> Tensor ('S m ': '[]) a
        addToFront s (TC VN)        = TC (VC (TZ s) VN)
        addToFront s (TC (VC t ts)) = TC (VC (TZ s) (VC t ts))

-- | Insert a new column into a table. 
-- Given the name of the header and the values of all rows in that column
insertColumn :: STRING x -> Tensor (r ': '[]) String -> Table c r ->  Table (Header x (Length c) ': c) r
insertColumn _ ts (Table h (TC xs)) = Table newHeaders (TC (VC ts xs))
    where newHeaders          = XCons (Header (sizeList h)) h

-- | Creates an empty table
emptyTable :: Table '[] 'Z
emptyTable = Table XNil (enshape VN (XCons NZ $ XCons NZ XNil))

-- | Select a column from a table by giving the index
selectByIndex :: (((n + m) - m) ~ n, Length c ~ 'S (n + m)) =>
  Nat m -> Table c r -> Tensor '[r] String
selectByIndex n (Table _ r) = getCol r $ toFin ((-|) (sizeT r) n) n
  where getCol :: Tensor (n ': r ': '[]) String -> Fin n -> Tensor (r ': '[]) String
        getCol ((TC (VC c _)))  FZ            = c
        getCol ((TC (VC _ (VC c cs)))) (FS s) = getCol (TC (VC c cs)) s
        sizeT :: Tensor (S n ': r ': '[]) a -> Nat n
        sizeT ((TC (VC _ VN)))        = NZ
        sizeT ((TC (VC _ (VC t ts)))) = NS (sizeT (TC (VC t ts)))


-- | Select a column from a table by giving the name of the column
selectFromTable :: (Member s c (Nat (Lookup s c)) (Head s c),
 Length c ~ 'S (n + Lookup s c),
 ((n + Lookup s c) - Lookup s c) ~ n) =>
  STRING s -> Table c r -> Tensor '[r] String
selectFromTable colName t@(Table c _) = selectByIndex (select colName c) t
