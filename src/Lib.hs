module Lib where

import Prelude
import Data.Bits
import Data.Word
import Data.Int
import Data.Proxy
import Data.Type.Equality
import Control.Monad.IO.Class
import Data.Set
import Data.Map

type Party = String

-----------------
-- MPC Classes --
-----------------

---- INS: TODO: What's the right thing to do about the monadic effects?

class Monad m ⇒ MonadMPC m where
  everyone ∷ m (Set Party)
  me       ∷ m Party

-------------------------------
--- Encryption / Decryption ---
-------------------------------

---- Encrypt type `s` according to protocol `p`
class EncDec p s where
  enc   ∷ (MonadMPC m) ⇒ s → m (Map Party (p s))
  dec   ∷ (MonadMPC m) ⇒ (Map Party (p s)) → m s
  embed ∷ (MonadMPC m) ⇒ s → m (p s)

-----------------------------------
--- Addition / Group Operations ---
-----------------------------------

---- Additive Identity (0)
class (EncDec p s) ⇒ MPCAddId p s where
  addId ∷ m (p s)

---- Additive Inverse (-a)
class (EncDec p s) ⇒ MPCAddInv p s where
  addInv ∷ (MonadMPC m) ⇒ p s → m (p s)

---- Addition (a + b)
class (EncDec p s) ⇒ MPCAdd p s where
  add ∷ (MonadMPC m) ⇒ p s → p s → m (p s)

---- Group Operations
class (MPCAddId p s, MPCAddInv p s, MPCAdd p s) ⇒ MPCGroup p s

-----------------------------------------------
--- Multiplication / Ring, Field Operations ---
-----------------------------------------------

---- Multiplicative Identity (1)
class (EncDec p s) ⇒ MPCMulId p s where
  mulId ∷ (MonadMPC m) ⇒ m (p s)

---- Multiplicative Inverse (1/a)
class (EncDec p s) ⇒ MPCMulInv p s where
  mulInv ∷ (MonadMPC m) ⇒ p s → m (p s)

---- Multiplication (a * b)
class (EncDec p s) ⇒ MPCMul p s where
  mul ∷ (MonadMPC m) ⇒ p s → p s → m (p s)

---- Ring Operations
class (MPCGroup p s, MPCMulId  p s, MPCMul p s) ⇒ MPCRing  p s

---- Field Operations
class (MPCRing  p s, MPCMulInv p s)             ⇒ MPCField p s

------------------
--- Conversion ---
------------------

---- Convert from a to b (a ⊑ b)
class (EncDec p a, EncDec p b) ⇒ MPCConv p a b where
  conv ∷ (MonadMPC m) ⇒ p a → m (p b)

---- Reflexivity (a ⊑ a)
instance (EncDec p s) ⇒ MPCConv p s s where
  conv = return

---- INS: TODO: Conversion should be a partial order. How?
---- INS: TODO: Conversion should be a lattice. How?

--------------------------
--- Derived Operations ---
--------------------------

---- Subtraction (a - b)
sub ∷ (MonadMPC m, MPCAddInv p s, MPCAdd p s) ⇒ p s → p s → m (p s)
sub a b = do
  c ← addInv b -- c = -b
  add a c      -- a + c = a + (-b) = a - b

---- Conditionals (g ? a : b)
cond ∷ (MonadMPC m, MPCConv p Bool s, MPCRing p s) ⇒ p Bool → p s → p s → m (p s)
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

instance EncDec GMW Bool where
  enc b             = return $ [GMWBool b]
  dec [(GMWBool b)] = return b
  embed b           = return $ GMWBool b

instance MPCAddId GMW Bool where
  addId = embed False

instance MPCAddInv GMW Bool where
  addInv (GMWBool b) = return $ GMWBool $ complement b

instance MPCAdd GMW Bool where
  add (GMWBool b1) (GMWBool b2) = return $ GMWBool $ b1 `xor` b2

instance MPCMulId GMW Bool where
  mulId = embed True

instance MPCMulInv GMW Bool where
  mulInv _ = return $ GMWBool $ True

instance MPCMul GMW Bool where
  mul (GMWBool b1) (GMWBool b2) = return $ GMWBool $ b1 .&. b2

instance MPCGroup GMW Bool
instance MPCRing  GMW Bool
instance MPCField GMW Bool

--------------------------------------
---- Naturals (ℤ8, ℤ16, ℤ32, ℤ64) ----
--------------------------------------

---- INS: TODO

------------------
---- Examples ----
------------------

basic ∷ MonadMPC m ⇒ m Bool
basic = do
  x ← enc @GMW True
  y ← enc False
  b ← enc True
  z ← cond (head b) (head x) (head y)
  r ← add z (head x)
  dec [r]
