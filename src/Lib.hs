module Lib where

import Prelude
import Data.Bits
import Data.Word
import Data.Int
import Data.Proxy
import Data.Type.Equality
import Control.Monad.IO.Class

-----------------
-- MPC Classes --
-----------------

---- INS: TODO: What's the right thing to do about the monadic effects?

-------------------------------
--- Encryption / Decryption ---
-------------------------------

---- Encrypt type `s` according to protocol `p`
class EncDec p s where
  enc   ∷ (Monad m) ⇒ s → m [p s]
  dec   ∷ (Monad m) ⇒ [p s] → m s
  embed ∷ (Monad m) ⇒ s → m (p s)

-----------------------------------
--- Addition / Group Operations ---
-----------------------------------

---- Additive Identity (0)
class (EncDec p s) ⇒ MPCAddId p s where
  addId ∷ (Monad m) ⇒ m (p s)

---- Additive Inverse (-a)
class (EncDec p s) ⇒ MPCAddInv p s where
  addInv ∷ (Monad m) ⇒ p s → m (p s)

---- Addition (a + b)
class (EncDec p s) ⇒ MPCAdd p s where
  add ∷ (Monad m) ⇒ p s → p s → m (p s)

---- Group Operations
class (MPCAddId p s, MPCAddInv p s, MPCAdd p s) ⇒ MPCGroup p s

-----------------------------------------------
--- Multiplication / Ring, Field Operations ---
-----------------------------------------------

---- Multiplicative Identity (1)
class (EncDec p s) ⇒ MPCMulId p s where
  mulId ∷ (Monad m) ⇒ m (p s)

---- Multiplicative Inverse (1/a)
class (EncDec p s) ⇒ MPCMulInv p s where
  mulInv ∷ (Monad m) ⇒ p s → m (p s)

---- Multiplication (a * b)
class (EncDec p s) ⇒ MPCMul p s where
  mul ∷ (Monad m) ⇒ p s → p s → m (p s)

---- Ring Operations
class (MPCGroup p s, MPCMulId  p s, MPCMul p s) ⇒ MPCRing  p s

---- Field Operations
class (MPCRing  p s, MPCMulInv p s)             ⇒ MPCField p s

------------------
--- Conversion ---
------------------

---- Convert from a to b (a ⊑ b)
class (EncDec p a, EncDec p b) ⇒ MPCConv p a b where
  conv ∷ (Monad m) ⇒ p a → m (p b)

---- Reflexivity (a ⊑ a)
instance (EncDec p s) ⇒ MPCConv p s s where
  conv = return

---- INS: TODO: Conversion should be a partial order. How?
---- INS: TODO: Conversion should be a lattice. How?

--------------------------
--- Derived Operations ---
--------------------------

---- Subtraction (a - b)
sub ∷ (Monad m, MPCAddInv p s, MPCAdd p s) ⇒ p s → p s → m (p s)
sub a b = do
  c ← addInv b -- c = -b
  add a c      -- a + c = a + (-b) = a - b

---- Conditionals (g ? a : b)
cond ∷ (Monad m, MPCConv p Bool s, MPCRing p s) ⇒ p Bool → p s → p s → m (p s)
cond g a b = do
  c   ← conv g
  one ← mulId
  d   ← mul c a   -- d = c * a
  e   ← sub one c -- e = 1 - c
  f   ← mul e b   -- f = e * b = (1 - c) * b
  add d f         -- d + f = (c * b) + ((1 - c) * b)

-------------------------------
--- Derived Encrypted Types ---
-------------------------------

---- INS: TODO: Should also support (Either a b). How?

data Value p a where
  ValBase ∷ p a → Value p a
  ValProd ∷ (Value p a, Value p b) → Value p (a, b)

---- Base
instance (EncDec p a) ⇒ EncDec (Value p) a where
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
instance (EncDec p a, EncDec p b) ⇒ EncDec (Value p) (a, b) where
  enc (a, b) = do
    as  ← enc a
    bs  ← enc b
    return $ map ValProd $ zip (map ValBase as) (map ValBase bs)
  dec xs = do
    let (as, bs) = unzip $ map (\ (ValProd x) → x) xs
    a ← dec as
    b ← dec bs
    return (a, b)
  embed (a, b) = do
    a ← embed a
    b ← embed b
    return $ ValProd ((ValBase a), (ValBase b))

---- INS: TODO: Operations

-----------
--- Yao ---
-----------

---------------
---- Types ----
---------------

type YaoBoolShare = Bool

type YaoWord8Share = Word8

data YaoWord a where
  YaoWord8 ∷ YaoWord8Share → YaoWord Word8

data Yao a where
  YaoBool ∷ YaoBoolShare → Yao Bool

-----------------------
---- Booleans (ℤ2) ----
-----------------------

instance EncDec Yao Bool where
  enc b             = return $ [YaoBool b]
  dec [(YaoBool b)] = return b
  embed b           = return $ YaoBool b

instance MPCAddId Yao Bool where
  addId = embed False

instance MPCAddInv Yao Bool where
  addInv (YaoBool b) = return $ YaoBool $ complement b

instance MPCAdd Yao Bool where
  add (YaoBool b1) (YaoBool b2) = return $ YaoBool $ b1 `xor` b2

instance MPCMulId Yao Bool where
  mulId = embed True

instance MPCMulInv Yao Bool where
  mulInv _ = return $ YaoBool $ True

instance MPCMul Yao Bool where
  mul (YaoBool b1) (YaoBool b2) = return $ YaoBool $ b1 .&. b2

instance MPCGroup Yao Bool
instance MPCRing  Yao Bool
instance MPCField Yao Bool

--------------------------------------
---- Naturals (ℤ8, ℤ16, ℤ32, ℤ64) ----
--------------------------------------

---- INS: TODO

------------------
---- Examples ----
------------------

basic ∷ Monad m ⇒ m Bool
basic = do
  x ← enc @Yao True
  y ← enc False
  b ← enc True
  z ← cond (head b) (head x) (head y)
  r ← add z (head x)
  dec [r]
