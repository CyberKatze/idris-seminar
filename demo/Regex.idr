module Regex

import Data.List
import Data.String
import Data.Vect
import Lang
import Data.List.Quantifiers

public export
data Regex: (a: Type) -> Type where
  Empty: Regex a
  Epsilon: Regex a
  Chr : a -> Regex a
  Concat: Regex a -> Regex a -> Regex a
  Alt:  Regex a -> Regex a -> Regex a
  Star :  Regex a -> Regex a

lang : {a: Type } -> Regex a -> Lang a
lang Empty = empty
lang Epsilon = eps
lang (Chr c) = tok c
lang (Concat x y) = langConcat (lang x) (lang y)
lang (Alt x y) = union (lang x) (lang y)
lang (Star x) = langStar (lang x)

covering
simplify : Regex a -> Regex a
simplify (Concat Empty _) = Empty  
simplify (Concat _ Empty) = Empty  
simplify (Concat Epsilon r ) = r  
simplify (Concat r Epsilon ) = r  
simplify (Alt Empty r) = r  
simplify (Alt r Empty) = r  
simplify r =  r  

simplifyCorrect : (r : Regex a) -> (s : List a) ->  lang r s -> lang (simplify r) s   
simplifyCorrect Empty s l = l 
simplifyCorrect Epsilon s l = l 
simplifyCorrect (Chr x) s l = l 
simplifyCorrect (Star x) s l = l 
simplifyCorrect (Concat Empty y) s (((x, z) ** (w, (v, t)))) = v
simplifyCorrect (Concat Epsilon Empty) s (((x, y) ** (z, (w, v)))) = v 
simplifyCorrect (Concat Epsilon Epsilon) s (((x, y) ** (z, (w, v)))) = 
  let prf_1 = cong (++ y) w 
      prf_2 = trans (trans z prf_1) v 
      in prf_2 
simplifyCorrect (Concat Epsilon (Chr x)) s (((y, z) ** (w, (v, t)))) = 
  let prf_1 = cong (++ z) v  
      prf_2 = trans (trans w prf_1) t
      in prf_2 
simplifyCorrect (Concat Epsilon (Concat x y)) s (((z, w) ** (v, (t, u)))) = 
  let prf_1 = cong (++ w) t 
      prf_2 = (trans v prf_1) 
      in rewrite prf_2 in u 
simplifyCorrect (Concat Epsilon (Alt x y)) s (((z, w) ** (v, (t, u)))) = 
  let prf_1 = cong (++ w) t
      prf_2 = trans v prf_1
      in rewrite prf_2 in u 
simplifyCorrect (Concat Epsilon (Star x)) s (((y, z) ** (w, (v, t)))) = 
  let prf_1 = cong (++ z) v
      prf_2 = trans w prf_1
      in rewrite prf_2 in t 
simplifyCorrect (Concat (Chr x) Empty) s (((y, z) ** (w, (v, t)))) = t 
simplifyCorrect (Concat (Chr x) Epsilon) s (((y, z) ** (w, (v, t)))) = 
let prf_1 = cong (y ++) t
    prf_2 = trans w prf_1
    prf_3 = appendNilRightNeutral y
    prf_4 = trans (trans prf_2 prf_3) v
  in prf_4
simplifyCorrect (Concat (Chr x) (Chr y)) s l = l 
simplifyCorrect (Concat (Chr x) (Concat y z)) s l = l 
simplifyCorrect (Concat (Chr x) (Alt y z)) s l = l 
simplifyCorrect (Concat (Chr x) (Star y)) s l = l 
simplifyCorrect (Concat (Concat x z) Empty) s (((y, w) ** (v, (t, u)))) = u 
simplifyCorrect (Concat (Concat x z) Epsilon) s (((y, w) ** (v, (t, u)))) = 
  let prf_1 = cong (y ++) u
      prf_2 = trans v prf_1
      prf_3 = appendNilRightNeutral y 
      prf_4 = trans prf_2 prf_3 
  in rewrite prf_4 in t 
simplifyCorrect (Concat (Concat x z) (Chr y)) s l = l 
simplifyCorrect (Concat (Concat x z) (Concat y w)) s l = l 
simplifyCorrect (Concat (Concat x z) (Alt y w)) s l = l 
simplifyCorrect (Concat (Concat x z) (Star y)) s l = l 
simplifyCorrect (Concat (Alt x z) Empty) s (((y, w) ** (v, (t, u)))) = u 
simplifyCorrect (Concat (Alt x z) Epsilon) s (((y, w) ** (v, (t, u)))) = 
  let prf_1 = cong (y ++) u
      prf_2 = appendNilRightNeutral y
      prf_3 = trans (trans v prf_1) prf_2
  in rewrite prf_3 in t 
simplifyCorrect (Concat (Alt x z) (Chr y)) s l = l 
simplifyCorrect (Concat (Alt x z) (Concat y w)) s l = l 
simplifyCorrect (Concat (Alt x z) (Alt y w)) s l = l 
simplifyCorrect (Concat (Alt x z) (Star y)) s l = l 
simplifyCorrect (Concat (Star x) Empty) s (((y, z) ** (w, (v, t)))) = t 
simplifyCorrect (Concat (Star x) Epsilon) s (((y, z) ** (w, (v, t)))) = 
  let prf_1 = cong (y ++ ) t
      prf_2 = appendNilRightNeutral y
      prf_3 = trans (trans w prf_1) prf_2
  in rewrite prf_3 in v
simplifyCorrect (Concat (Star x) (Chr y)) s l = l 
simplifyCorrect (Concat (Star x) (Concat y z)) s l = l 
simplifyCorrect (Concat (Star x) (Alt y z)) s l = l 
simplifyCorrect (Concat (Star x) (Star y)) s l = l 
simplifyCorrect (Alt Empty y) s Left x impossible
simplifyCorrect (Alt Empty y) s (Right x) = x  
simplifyCorrect (Alt Epsilon Empty) s l = either id absurd l --also we could use case split and impossible
simplifyCorrect (Alt Epsilon Epsilon) s l = l 
simplifyCorrect (Alt Epsilon (Chr x)) s l = l 
simplifyCorrect (Alt Epsilon (Concat x y)) s l = l 
simplifyCorrect (Alt Epsilon (Alt x y)) s l = l 
simplifyCorrect (Alt Epsilon (Star x)) s l = l 
simplifyCorrect (Alt (Chr x) Empty) s l = either id absurd l
simplifyCorrect (Alt (Chr x) Epsilon) s l = l 
simplifyCorrect (Alt (Chr x) (Chr y)) s l = l 
simplifyCorrect (Alt (Chr x) (Concat y z)) s l = l 
simplifyCorrect (Alt (Chr x) (Alt y z)) s l = l 
simplifyCorrect (Alt (Chr x) (Star y)) s l = l 
simplifyCorrect (Alt (Concat x z) Empty) s l = either id absurd l 
simplifyCorrect (Alt (Concat x z) Epsilon) s l = l 
simplifyCorrect (Alt (Concat x z) (Chr y)) s l = l 
simplifyCorrect (Alt (Concat x z) (Concat y w)) s l = l 
simplifyCorrect (Alt (Concat x z) (Alt y w)) s l = l 
simplifyCorrect (Alt (Concat x z) (Star y)) s l = l 
simplifyCorrect (Alt (Alt x z) Empty) s l = either id absurd l 
simplifyCorrect (Alt (Alt x z) Epsilon) s l = l 
simplifyCorrect (Alt (Alt x z) (Chr y)) s l = l 
simplifyCorrect (Alt (Alt x z) (Concat y w)) s l = l 
simplifyCorrect (Alt (Alt x z) (Alt y w)) s l = l 
simplifyCorrect (Alt (Alt x z) (Star y)) s l = l 
simplifyCorrect (Alt (Star x) Empty) s l = either id absurd l 
simplifyCorrect (Alt (Star x) Epsilon) s l = l 
simplifyCorrect (Alt (Star x) (Chr y)) s l = l 
simplifyCorrect (Alt (Star x) (Concat y z)) s l = l 
simplifyCorrect (Alt (Star x) (Alt y z)) s l = l 
simplifyCorrect (Alt (Star x) (Star y)) s l = l 


public export  
Show (Regex Char) where  
  show Empty = "∅"  -- null set
  show Epsilon = "ε"  -- epsilon for empty string  
  show (Chr c) = pack [c]
  show (Concat r1 r2) = show r1 ++ show r2  
  show (Alt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"  
  show (Star r) = case r of
    Chr _ => show r ++ "*"
    Empty => "ε" 
    Epsilon => "ε" 
    _ => "(" ++ show r ++ ")*"


-- Helper function for string splits  
splits : List Char -> List (List Char, List Char)  
splits chars =  zip (inits chars) (tails chars)  


-- Covering annotation ensures termination checking  
export
covering  
matches : Regex Char -> List Char -> List (List Char)  
matches Empty str = []
matches Epsilon str =   
  case str of  
    [] => [[]]   
    _ =>  []  
matches (Chr c) str =   
  case str of  
    [] => []  
    (x :: xs) => if x == c   
                   then [[c]]  
                   else []  
matches (Concat r1 r2) str =   
  [m1 ++ m2 |   
    (s1, s2) <- splits str,  
    m1 <- matches r1 s1,  
    m2 <- matches r2 s2]  
matches (Alt r1 r2) str =   
  matches r1 str ++ matches r2 str  
matches (Star r) str =   
  [] :: -- empty match  
  [m1 ++ m2 |   
    (s1, s2) <- splits str,  
    s1 /= [],  -- ensure progress  
    m1 <- matches r s1,  
    m2 <- matches (Star r) s2]  

-- Main match function  
public export
match : Regex Char -> List Char -> Bool  
match r str = elem str (matches r str)


-- namespace C
--   public export
--   data Match: {n : Nat} -> Regex Char -> Vect n Char -> Type where
--     -- Match for Empty regex
--     Mempty : Match Empty [] 
--     -- Match for a single character (Chr 'a') "a"
--     MChr : ( c2 : Char ) -> {auto prf: c1 = c2} -> Match (Chr c1) ([c2])
--     -- Match for concatenation
--     -- MConcat : {v1: Vect n1 Char}-> {v2: Vect n2 Char} -> {prf: n2 + n1 = n} ->(m1 : Match r1 v1) -> (m2 : Match r2 v2) -> Match (Concat r1 r2) (v1 ++ v2)
--     MConcat : (n1 : Nat) ->
--               {v1: Vect n1 Char} -> 
--               {v2: Vect n2 Char} ->
--                   Match r1 v1 ->  
--                   Match r2 v2 ->  Match (Concat r1 r2) (v1 ++ v2)  
--     -- Match for alternation
--     MAltL : (m : Match r1 v) -> Match (Alt r1 r2) v
--     MAltR : (m : Match r2 v) -> Match (Alt r1 r2) v
--
--     MStarEmpty : Match (Star r) [] 
--     MStarCons: (m1 : Match r v1) -> (m2 : Match (Star r) v2) -> Match (Star r) (v1 ++ v2)
