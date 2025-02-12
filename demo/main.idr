module Main
import Data.Vect
import Regex
import Data.List
import RegexParser
import Lang

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

safeDiv : (num : Nat) -> (d : Nat) -> {auto 0 ok : GT d Z}-> Nat  
safeDiv n d = ?hole

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


-- Regular expression

main : IO ()
main = do
  putStrLn "is regexA matching 'a'? using boolean match?" 
  printLn $ parseRegexString "a*b|c"  
  -- print $ B.match regexA "a"
  let res = parseRegexString "ab*"  
  case res of
      Left err => putStrLn $ "Error: " ++ err
      Right reg => do
        print $ match reg (unpack "abbbbc")







vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vzipWith f [] ys = []
vzipWith f (x :: xs) ys = ?vzipWit_1
