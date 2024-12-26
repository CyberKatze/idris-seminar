module Main
import Data.Vect

data N = Z | S N 

data Even : N -> Type
data Odd  : N -> Type

data Even : N -> Type where
  ZIsEven : Even Z
  SOddIsEven : Odd n -> Even (S n)

data Odd : N -> Type where
  SEvenIsOdd : Even n -> Odd (S n)

zeroIsEven : Even Z
zeroIsEven = ZIsEven

threeIsOdd : Odd (S (S (S Z)))

safeDiv : (num : Nat) -> (d : Nat) -> {auto ok : GT d Z}-> Nat  
safeDiv n d  = div n d  

-- This works automatically because Idris can prove 0 < 5  
example : Nat  
example = safeDiv 12 5
-- This fails because Idris can't prove 0 < 0
-- example2 : Nat
-- example2 = safeDiv 12 0

-- Idris2: Practical dependent types with erasure  
index' : (i : Fin n) -> Vect n a -> a  
index' FZ     (x :: xs) = x  
index' (FS k) (x :: xs) = index' k xs  
