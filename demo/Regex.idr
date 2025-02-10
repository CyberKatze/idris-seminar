module Regex

import Data.List
import Data.String
import Data.Vect
import Lang
import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality 
import Decidable.Equality.Core
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
simplify (Concat Empty r) = Empty  
simplify (Concat r Empty) = Empty  
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
splits [] = [([],[])]
splits (x :: xs) = ([], x :: xs) :: (map (\(ys, zs) => (x :: ys, zs)) (splits xs))

mapElem : {a, b : Type} ->
(f : a -> b) ->
(x : a) ->
(xs : List a) ->
Elem x xs ->
Elem (f x) (map f xs)
mapElem f x [] prf = absurd prf
mapElem f x (x::xs) Here = Here
mapElem f x (y::ys) (There prf) = There (mapElem f x ys prf)

splitRightNil : (t : List Char) -> Elem (t, []) (splits t)
splitRightNil [] = Here
splitRightNil (x :: xs) = ?eeef



splitElem : {s : List Char} ->
(z, w : List Char) ->
(p : s = z ++ w) ->
Elem (z, w) (splits s)
splitElem {s = ([] ++ _)} [] [] Refl = Here 
splitElem {s = ([] ++ _)} [] (x :: xs) Refl = Here 
splitElem {s = ((_ :: _) ++ [])} (x :: xs) [] Refl =  splitRightNil _ 
splitElem {s = s} (x :: xs) (y :: ys) prf = ?herere_3 

-- lemmma
inAppLeft : {xs, ys : List a}-> Elem x xs -> Elem x (xs ++ ys)
inAppLeft prf {xs = []} = absurd prf
inAppLeft Here {xs = (x :: xs)} = Here
inAppLeft (There z) {xs = (y :: xs)} = There (inAppLeft z)

inAppRight : {xs, ys : List a}-> Elem x ys -> Elem x (xs ++ ys)
inAppRight prf {xs = []} = prf
inAppRight prf {xs = (x :: xs)} = There (inAppRight prf)

elemSplit : {xs, ys : List a} -> Elem x (xs ++ ys) -> Either (Elem x xs) (Elem x ys)
elemSplit prf {xs = []} = Right prf 
elemSplit Here {xs = (x :: xs)} = Left Here
elemSplit (There y) {xs = (x :: xs)} = case elemSplit y {xs}  of
                                                      (Left z) => Left (There z)
                                                      (Right z) => Right z

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
    ([x]) => case decEq x c of
                   Yes _ => [[c]]  
                   No _ => []  
    (x1 :: x2 :: xs) => []  
matches (Concat r1 r2) str =   
  concatMap (\(s1, s2) =>  
    concatMap (\m1 =>  
      map (\m2 => m1 ++ m2) (matches r2 s2)  
    ) (matches r1 s1)  
  ) (splits str)
matches (Alt r1 r2) str =   
  matches r1 str ++ matches r2 str  
matches (Star r) str =   
  [] :: -- empty match  
  [m1 ++ m2 |   
    (s1, s2) <- splits str,  
    s1 /= [],  -- ensure progress  
    m1 <- matches r s1,  
    m2 <- matches (Star r) s2]  

decEqRefl : (x : Char) -> decEq x x = Yes Refl


--leammas

-- Completeness of the matches function
matchesCompletness : (r : Regex Char) -> (s : List Char) -> lang r s -> Elem s (matches r s)
matchesCompletness Empty s l impossible
matchesCompletness Epsilon s l = rewrite l in Here
matchesCompletness (Chr x) s l = rewrite l in rewrite decEqRefl x in Here
matchesCompletness (Concat x y) s (((z, w) ** (v, (t, u)))) = ?hf_3
matchesCompletness (Alt x y) s (Left z) = let rec = matchesCompletness x s z in inAppLeft rec
matchesCompletness (Alt x y) s (Right z) = let rec = matchesCompletness y s z in inAppRight rec
matchesCompletness (Star x) s l = ?hf_5


-- Soundness of the matches function
matchesSoundness : (r : Regex Char) -> (s : List Char) -> Elem s (matches r s) -> lang r s
matchesSoundness Empty s prf = absurd prf
matchesSoundness Epsilon s prf = case s of 
                                      [] => Refl
                                      (x :: xs) => absurd prf 
matchesSoundness (Chr x) s prf = case s of
                                      [] => absurd prf
                                      ([y]) => case decEq y x of
                                                        (Yes z) => rewrite z in Refl
                                                        (No contra) => absurd (contra _)
                                      (x1 :: x2 :: xs) => absurd prf 
matchesSoundness (Concat x y) s prf = ?ffg_5
matchesSoundness (Alt x y) s prf = case elemSplit prf of
                                                  (Left z) => Left (matchesSoundness x s z)
                                                  (Right z) => Right (matchesSoundness y s z)
matchesSoundness (Star x) s prf = ?ffg_7
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
