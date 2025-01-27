module Regex

import Data.List
import Data.String
import Data.Vect

public export
data Regex : Type where
  Null: Regex
  Empty: Regex  
  Chr : Char -> Regex
  Concat: Regex -> Regex -> Regex
  Alt:  Regex -> Regex -> Regex
  Star :  Regex -> Regex

-- First, implement Show for Regex  

public export  
Show Regex where  
  show Null = "∅"  -- null set
  show Empty = "ε"  -- epsilon for empty string  
  show (Chr c) = pack [c] 
  show (Concat r1 r2) = show r1 ++ show r2  
  show (Alt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"  
  show (Star r) = case r of
    Chr _ => show r ++ "*"
    Empty => show r
    Null => "ε" 
    _ => "(" ++ show r ++ ")*"


-- Helper function for string splits  
splits : String -> List (String, String)  
splits str =   
  let chars = unpack str in  
  zip (map pack (inits chars)) (map pack (tails chars))  

-- Covering annotation ensures termination checking  
export
covering  
matches : Regex -> String -> List String  
matches Null str = []
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
match r str = elem str (matches r str)

namespace C
  public export
  data Match: {n : Nat} -> Regex -> Vect n Char -> Type where
    -- Match for Empty regex
    Mempty : Match Empty [] 
    -- Match for a single character (Chr 'a') "a"
    MChr : ( c2 : Char ) -> {auto prf: c1 = c2} -> Match (Chr c1) ([c2])
    -- Match for concatenation
    -- MConcat : {v1: Vect n1 Char}-> {v2: Vect n2 Char} -> {prf: n2 + n1 = n} ->(m1 : Match r1 v1) -> (m2 : Match r2 v2) -> Match (Concat r1 r2) (v1 ++ v2)
    MConcat : (n1 : Nat) ->
              {v1: Vect n1 Char} -> 
              {v2: Vect n2 Char} ->
                  Match r1 v1 ->  
                  Match r2 v2 ->  
                  Match (Concat r1 r2) (v1 ++ v2)  
    -- Match for alternation
    MAltL : (m : Match r1 v) -> Match (Alt r1 r2) v
    MAltR : (m : Match r2 v) -> Match (Alt r1 r2) v

    MStarEmpty : Match (Star r) [] 
    MStarCons: (m1 : Match r v1) -> (m2 : Match (Star r) v2) -> Match (Star r) (v1 ++ v2)
