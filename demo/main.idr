module Main
import Data.Vect
import Regex
import Data.List
import RegexParser

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
regexA : Regex
regexA = Star (Chr 'a')


proofSingleChar : C.Match (Chr 'b') "b"
proofSingleChar = C.MChr 'b'

proofConcat: C.Match (Concat (Chr 'a') (Chr 'b')) "ab"
proofConcat = C.MConcat (C.MChr 'a') (C.MChr 'b')

-- ab*
regexABStar : Regex
regexABStar = Concat (Chr 'a') (Star (Chr 'b'))

proofAltLeft : C.Match (Alt (Chr 'a') (Chr 'b')) "a"
proofAltLeft  = C.MAltL (C.MChr 'a')

proofRegexABStar : C.Match Main.regexABStar "ab"
proofRegexABStar = C.MConcat (C.MChr 'a') (C.MStarCons (C.MChr 'b') C.MStarEmpty)

proofRegexABStar2 : C.Match Main.regexABStar "abb"
proofRegexABStar2 = C.MConcat (C.MChr 'a') (C.MStarCons (C.MChr 'b') (C.MStarCons (C.MChr 'b') C.MStarEmpty))

main : IO ()
main = do
  putStrLn "is regexA matching 'a'? using boolean match?" 
  printLn $ parseRegexString "a*b|c"  
  -- print $ B.match regexA "a"

x = matches regexA "aaa"

-- As a record  
record Person where  
  constructor MkPerson  
  name : String  
  age : Int  
  email : String

pers1 : Person
pers1 = MkPerson "Alice" 25 "Joe"
