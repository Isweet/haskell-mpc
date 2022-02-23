module Lib where

import Prelude
import Data.Bits
import Data.Word
import Data.Int
import Data.Proxy
import Data.Type.Equality
import Control.Monad.IO.Class

type Party = String

unzipWith ∷ (a → (b, c)) → [a] → ([b], [c])
unzipWith f = unzip . map f

-----------------
-- MPC Classes --
-----------------

-------------------------------
--- Encryption / Decryption ---
-------------------------------

---- Encrypt type `s` according to protocol `p` using effects `c`
class EncDec p s c | p → c where
  enc   ∷ (Monad m, c m) ⇒ s → m [p s]
  dec   ∷ (Monad m, c m) ⇒ [p s] → m s
  embed ∷ (Monad m, c m) ⇒ s → m (p s)

-----------------------------------
--- Addition / Group Operations ---
-----------------------------------

---- Additive Identity (0)
class (EncDec p s c) ⇒ MPCAddId p s c where
  addId ∷ (Monad m, c m) ⇒ m (p s)

---- Additive Inverse (-a)
class (EncDec p s c) ⇒ MPCAddInv p s c where
  addInv ∷ (Monad m, c m) ⇒ p s → m (p s)

---- Addition (a + b)
class (EncDec p s c) ⇒ MPCAdd p s c where
  add ∷ (Monad m, c m) ⇒ p s → p s → m (p s)

---- Group Operations
class (MPCAddId p s c, MPCAddInv p s c, MPCAdd p s c) ⇒ MPCGroup p s c

-----------------------------------------------
--- Multiplication / Ring, Field Operations ---
-----------------------------------------------

---- Multiplicative Identity (1)
class (EncDec p s c) ⇒ MPCMulId p s c where
  mulId ∷ (Monad m, c m) ⇒ m (p s)

---- Multiplicative Inverse (1/a)
class (EncDec p s c) ⇒ MPCMulInv p s c where
  mulInv ∷ (Monad m, c m) ⇒ p s → m (p s)

---- Multiplication (a * b)
class (EncDec p s c) ⇒ MPCMul p s c where
  mul ∷ (Monad m, c m) ⇒ p s → p s → m (p s)

---- Ring Operations
class (MPCGroup p s c, MPCMulId  p s c, MPCMul p s c) ⇒ MPCRing  p s c

---- Field Operations
class (MPCRing  p s c, MPCMulInv p s c)             ⇒ MPCField p s c

------------------
--- Conversion ---
------------------

---- Convert from a to b (a ⊑ b)
class (EncDec p a c, EncDec p b c) ⇒ MPCConv p a b c where
  conv ∷ (Monad m, c m) ⇒ p a → m (p b)

---- Reflexivity (a ⊑ a)
instance (EncDec p s c) ⇒ MPCConv p s s c where
  conv = return

---- INS: TODO: Conversion should be a partial order. How?
---- INS: TODO: Conversion should be a lattice. How?

--------------------------
--- Derived Operations ---
--------------------------

---- Subtraction (a - b)
sub ∷ (Monad m, MPCAddInv p s c, MPCAdd p s c, c m) ⇒ p s → p s → m (p s)
sub a b = do
  c ← addInv b -- c = -b
  add a c      -- a + c = a + (-b) = a - b

---- Conditionals (g ? a : b)
cond ∷ (Monad m, MPCConv p Bool s c, MPCRing p s c, c m) ⇒ p Bool → p s → p s → m (p s)
cond g a b = do
  c   ← conv g
  one ← mulId
  d   ← mul c a   -- d = c * a
  e   ← sub one c -- e = 1 - c
  f   ← mul e b   -- f = e * b = (1 - c) * b
  add d f         -- d + f = (c * a) + ((1 - c) * b)

-------------------------------
--- Derived Encrypted Types ---
-------------------------------

---- INS: TODO: Should also support (Either a b). How?

data Value p a where
  ValBase ∷ p a → Value p a
  ValProd ∷ (Value p a, Value p b) → Value p (a, b)

---- Base
instance (EncDec p a c) ⇒ EncDec (Value p) a c where
  enc a = do
    as ← enc a
    return $ map ValBase as
  dec xs = do
    let as = map (\ (ValBase x) → x) xs
    dec as
  embed a = do
    a ← embed a
    return $ ValBase a

---- INS: TODO: Operations

---- Products
instance (EncDec (Value p) a c, EncDec (Value p) b c) ⇒ EncDec (Value p) (a, b) c where
  enc (a, b) = do
    as  ← enc a
    bs  ← enc b
    return $ zipWith (curry ValProd) as bs
  dec xs = do
    let (as, bs) = unzipWith (\ (ValProd x) → x) xs
    a ← dec as
    b ← dec bs
    return (a, b)
  embed (a, b) = do
    a ← embed a
    b ← embed b
    return $ ValProd (a, b)

---- INS: TODO: Operations

-----------
--- GMW ---
-----------

---------------
---- Types ----
---------------

type GMWBoolShare = Bool

type GMWWord8Share = Word8

data GMWWord a where
  GMWWord8 ∷ GMWWord8Share → GMWWord Word8

data GMW a where
  GMWBool ∷ GMWBoolShare → GMW Bool

-----------------------
---- Booleans (ℤ2) ----
-----------------------

class (MonadIO m) ⇒ MonadGMW m
instance (MonadIO m) ⇒ MonadGMW m

instance EncDec GMW Bool MonadGMW where
  enc b           = return $ [GMWBool b]
  dec [GMWBool b] = return b
  embed b         = return $ GMWBool b

instance MPCAddId GMW Bool MonadGMW where
  addId = embed False

instance MPCAddInv GMW Bool MonadGMW where
  addInv (GMWBool b) = return $ GMWBool $ complement b

instance MPCAdd GMW Bool MonadGMW where
  add (GMWBool b1) (GMWBool b2) = return $ GMWBool $ b1 `xor` b2

instance MPCMulId GMW Bool MonadGMW where
  mulId = embed True

instance MPCMulInv GMW Bool MonadGMW where
  mulInv _ = return $ GMWBool $ True

instance MPCMul GMW Bool MonadGMW where
  mul (GMWBool b1) (GMWBool b2) = return $ GMWBool $ b1 .&. b2

instance MPCGroup GMW Bool MonadGMW
instance MPCRing  GMW Bool MonadGMW
instance MPCField GMW Bool MonadGMW

--------------------------------------
---- Naturals (ℤ8, ℤ16, ℤ32, ℤ64) ----
--------------------------------------

---- INS: TODO

------------------
---- Examples ----
------------------

basic ∷ ∀ p c m . (Monad m, MPCRing p Bool c, c m) ⇒ Proxy p → m Bool
basic _ = do
  x ← enc @p True
  y ← enc False
  b ← enc True
  z ← cond (head b) (head x) (head y)
  r ← add z (head x)
  dec [r]
