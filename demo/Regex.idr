module Regex

import Data.List
import Data.String

public export
data Regex =
    Empty
  | Chr Char
  | Concat Regex Regex
  | Alt Regex Regex
  | Star Regex



-- Helper function for string splits  
splits : String -> List (String, String)  
splits str =   
  let chars = unpack str in  
  zip (map pack (inits chars)) (map pack (tails chars))  

-- Covering annotation ensures termination checking  
export
covering  
matches : Regex -> String -> List String  
matches Empty str =   
  if str == ""   
    then [""]   
    else []  
matches (Chr c) str =   
  case unpack str of  
    [] => []  
    (x :: xs) => if x == c   
                   then [pack [c]]  
                   else []  
matches (Concat r1 r2) str =   
  [m1 ++ m2 |   
    (s1, s2) <- splits str,  
    m1 <- matches r1 s1,  
    m2 <- matches r2 s2]  
matches (Alt r1 r2) str =   
  matches r1 str ++ matches r2 str  
matches (Star r) str =   
  "" :: -- empty match  
  [m1 ++ m2 |   
    (s1, s2) <- splits str,  
    s1 /= "",  -- ensure progress  
    m1 <- matches r s1,  
    m2 <- matches (Star r) s2]  

-- Main match function  
public export  
match : Regex -> String -> Bool  
match r s = not (null (matches r s))  
namespace C
  public export
  data Match: Regex -> String -> Type where
    -- Match for Empty regex
    Mempty : Match Empty ""
    -- Match for a single character
    MChr : ( c2 : Char ) -> {auto prf: c1 = c2} -> Match (Chr c1) (pack [c2])
    -- Match for concatenation
    MConcat : (m1 : Match r1 s1) -> (m2 : Match r2 s2) -> Match (Concat r1 r2) (s1 ++ s2)
    -- Match for alternation
    MAltL : (m : Match r1 s) -> Match (Alt r1 r2) s
    MAltR : (m : Match r2 s) -> Match (Alt r1 r2) s

    MStarEmpty : Match (Star r) ""

    MStarCons: (m1 : Match r s1) -> (m2 : Match (Star r) s2) -> Match (Star r) (s1 ++ s2)

