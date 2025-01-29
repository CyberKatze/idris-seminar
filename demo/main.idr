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


-- Regular expression


regexB : Regex
regexB = Chr 'b'

proofSingleChar : C.Match (Chr 'b') ['b']
proofSingleChar = MChr 'b' 

length_append : (xs : Vect n a) -> (ys : Vect m a) -> length (xs ++ ys) = (length xs) + (length ys)
length_append [] ys = Refl
length_append (x :: xs) ys = let rec = Main.length_append xs ys in rewrite rec in Refl 

proofConcat: C.Match (Concat (Chr 'a') (Chr 'b')) ['a', 'b']
proofConcat = ?h1 


regexABStar : Regex
regexABStar = Concat (Chr 'a') (Star (Chr 'b'))


proofAltLeft : C.Match (Alt (Chr 'a') (Chr 'b')) ['a'] 
proofAltLeft  = MAltL (MChr 'a')


main : IO ()
main = do
  putStrLn "is regexA matching 'a'? using boolean match?" 
  printLn $ parseRegexString "a*b|c"  
  -- print $ B.match regexA "a"
  let res = parseRegexString "ab*"  
  case res of
      Left err => putStrLn $ "Error: " ++ err
      Right reg => do
        print $ match reg "abbbb"

regexABStarC : Regex
regexABStarC = Concat (Star (Concat (Chr 'a') (Chr 'b'))) (Chr 'c')
is_match = match regexABStarC "ababw"
