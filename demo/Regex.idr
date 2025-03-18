module Regex

import Data.List
import Data.Bool
import Data.String
import Data.Vect
import Lang
import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality
import Decidable.Equality.Core
import Prelude
improt
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
simplify (Concat Epsilon r ) = r
simplify (Concat r Empty) = Empty
simplify (Concat r Epsilon ) = r
simplify (Alt Empty r) = r
simplify (Alt r Empty) = r
simplify r =  r

covering
simplifyCorrect : (r : Regex a) -> (s : List a) ->  lang r s -> lang (simplify r) s
simplifyCorrect (Concat Empty r) s (((x, z) ** (w, (v, t)))) = v
simplifyCorrect (Concat Epsilon r) s (((x, y) ** (z, (w, v)))) =
  let prf_1 = cong (++ y) w
      prf_2 = trans z prf_1
      in  rewrite prf_2 in v
simplifyCorrect (Concat (Chr x) Empty) s (((y, z) ** (w, (v, t)))) = t
simplifyCorrect (Concat (Concat x z) Empty) s (((y, w) ** (v, (t, u)))) = u
simplifyCorrect (Concat (Alt x z) Empty) s (((y, w) ** (v, (t, u)))) = u
simplifyCorrect (Concat (Star x) Empty) s (((y, z) ** (w, (v, t)))) = t
simplifyCorrect (Concat (Chr x) Epsilon) s (((y, z) ** (w, (v, t)))) =
  let prf_1 = cong (y ++) t
      prf_2 = trans w prf_1
      prf_3 = appendNilRightNeutral y
      prf_4 = trans (trans prf_2 prf_3) v
      in prf_4
simplifyCorrect (Concat (Concat x z) Epsilon) s (((y, w) ** (v, (t, u)))) =
  let prf_1 = cong (y ++) u
      prf_2 = trans v prf_1
      prf_3 = appendNilRightNeutral y
      prf_4 = trans prf_2 prf_3
  in rewrite prf_4 in t
simplifyCorrect (Concat (Alt x z) Epsilon) s (((y, w) ** (v, (t, u)))) =
  let prf_1 = cong (y ++) u
      prf_2 = appendNilRightNeutral y
      prf_3 = trans (trans v prf_1) prf_2
  in rewrite prf_3 in t
simplifyCorrect (Concat (Star x) Epsilon) s (((y, z) ** (w, (v, t)))) =
  let prf_1 = cong (y ++ ) t
      prf_2 = appendNilRightNeutral y
      prf_3 = trans (trans w prf_1) prf_2
  in rewrite prf_3 in v
simplifyCorrect (Alt Empty r) s l = either absurd id l
simplifyCorrect (Alt Epsilon Empty) s l = either id absurd l
simplifyCorrect (Alt (Chr x) Empty) s l = either id absurd l
simplifyCorrect (Alt (Concat x z) Empty) s l = either id absurd l
simplifyCorrect (Alt (Alt x z) Empty) s l = either id absurd l
simplifyCorrect (Alt (Star x) Empty) s l = either id absurd l
simplifyCorrect Empty s l = l
simplifyCorrect Epsilon s l = l
simplifyCorrect (Chr x) s l = l
simplifyCorrect (Concat (Chr x) (Chr y)) s l = l
simplifyCorrect (Concat (Chr x) (Concat y z)) s l = l
simplifyCorrect (Concat (Chr x) (Alt y z)) s l = l
simplifyCorrect (Concat (Chr x) (Star y)) s l = l
simplifyCorrect (Concat (Concat x z) (Chr y)) s l = l
simplifyCorrect (Concat (Concat x z) (Concat y w)) s l = l
simplifyCorrect (Concat (Concat x z) (Alt y w)) s l = l
simplifyCorrect (Concat (Concat x z) (Star y)) s l = l
simplifyCorrect (Concat (Alt x z) (Chr y)) s l = l
simplifyCorrect (Concat (Alt x z) (Concat y w)) s l = l
simplifyCorrect (Concat (Alt x z) (Alt y w)) s l = l
simplifyCorrect (Concat (Alt x z) (Star y)) s l = l
simplifyCorrect (Concat (Star x) (Chr y)) s l = l
simplifyCorrect (Concat (Star x) (Concat y z)) s l = l
simplifyCorrect (Concat (Star x) (Alt y z)) s l = l
simplifyCorrect (Concat (Star x) (Star y)) s l = l
simplifyCorrect (Alt Epsilon Epsilon) s l = l
simplifyCorrect (Alt Epsilon (Chr x)) s l = l
simplifyCorrect (Alt Epsilon (Concat x y)) s l = l
simplifyCorrect (Alt Epsilon (Alt x y)) s l = l
simplifyCorrect (Alt Epsilon (Star x)) s l = l
simplifyCorrect (Alt (Chr x) Epsilon) s l = l
simplifyCorrect (Alt (Chr x) (Chr y)) s l = l
simplifyCorrect (Alt (Chr x) (Concat y z)) s l = l
simplifyCorrect (Alt (Chr x) (Alt y z)) s l = l
simplifyCorrect (Alt (Chr x) (Star y)) s l = l
simplifyCorrect (Alt (Concat x z) Epsilon) s l = l
simplifyCorrect (Alt (Concat x z) (Chr y)) s l = l
simplifyCorrect (Alt (Concat x z) (Concat y w)) s l = l
simplifyCorrect (Alt (Concat x z) (Alt y w)) s l = l
simplifyCorrect (Alt (Concat x z) (Star y)) s l = l
simplifyCorrect (Alt (Alt x z) Epsilon) s l = l
simplifyCorrect (Alt (Alt x z) (Chr y)) s l = l
simplifyCorrect (Alt (Alt x z) (Concat y w)) s l = l
simplifyCorrect (Alt (Alt x z) (Alt y w)) s l = l
simplifyCorrect (Alt (Alt x z) (Star y)) s l = l
simplifyCorrect (Alt (Star x) Epsilon) s l = l
simplifyCorrect (Alt (Star x) (Chr y)) s l = l
simplifyCorrect (Alt (Star x) (Concat y z)) s l = l
simplifyCorrect (Alt (Star x) (Alt y z)) s l = l
simplifyCorrect (Alt (Star x) (Star y)) s l = l
simplifyCorrect (Star x) s l = l


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
mutual
  splits : List Char -> List (List Char, List Char)
  splits [] = [([],[])]
  splits (x :: xs) = ([], x :: xs) :: appendFirst x (splits xs)

  appendFirst : (a : Char) -> List (List Char, List Char) -> List (List Char, List Char)
  appendFirst a [] = []
  appendFirst a ((x, y) :: xs) = (a:: x, y) :: appendFirst a xs

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


splitLemma : {xs, ws : List Char} -> (x : Char) ->
             Elem (xs, ws) (splits (xs ++ ws)) ->
             Elem (x :: xs, ws) (appendFirst x (splits (xs ++ ws)))
splitLemma x prf = ?dfdfd

splitElem : {s : List Char} ->
(z, w : List Char) ->
(p : s = z ++ w) ->
Elem (z, w) (splits s)
splitElem [] [] prf  =  rewrite prf in Here
splitElem [] (w :: ws) prf  =  rewrite prf in Here
splitElem (x :: xs) w prf  = rewrite prf in  let rec = splitLemma x (splitElem xs w Refl) in  (There rec)

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
mutual
  matchConcatList : (r1 : Regex Char) -> (r2 : Regex Char) -> (s : List (List Char, List Char)) -> Bool
  matchConcatList r1 r2 [] = False
  matchConcatList r1 r2 ((s1, s2) :: xs) = (match r1 s1 && (match r2 s2)) || (matchConcatList r1 r2 xs)
  -- Covering annotation ensures termination checking
  export
  covering
  match : Regex Char -> List Char -> Bool
  match Empty str = False
  match Epsilon [] = True
  match Epsilon _ = False
  match (Chr c) [] = False
  match (Chr c) [x] = x == c
  match (Chr c) (x1 :: x2 :: xs) = False
  match (Concat r1 r2) str =
    matchConcatList r1 r2 (splits str)
  match (Alt r1 r2) str =
    match r1 str || match r2 str
  match (Star r) [] =  True
  match (Star r) (x::xs) =
    matchConcatList r (Star r) (appendFirst x (splits xs))

exampleRegex : Regex Char
exampleRegex = Star (Concat (Chr 'a') (Chr 'b'))

decEqRefl : (x : Char) -> decEq x x = Yes Refl
%unsafe
singletonEq :{x, y : Char} ->  Prelude.Basics.(::) x [] = y :: [] -> x == y = True
singletonEq Refl = believe_me Refl
singletonEqRev :{x, y : Char} -> x == y = True -> Prelude.Basics.(::) x [] = y :: []

--leammas

splitsMatch: {s : List (List Char , List Char) }-> Elem (s1, s2) s -> match r1 s1 && match r2 s2 = True -> matchConcatList r1 r2 s = True
splitsMatch {s= [] } prf prf2 impossible
splitsMatch {s= ((s1, s2) :: xs) } Here prf2 = rewrite prf2 in Refl
splitsMatch {s= ((ns1, ns2) :: xs) } (There y) prf2 = let rec = splitsMatch y prf2
                                                          temp = trans (cong ((match r1 ns1 && match r2 ns2) ||) rec) (orTrueTrue _ ) in rewrite sym temp in Refl


-- Completeness of the match function
matchCompletness : (r : Regex Char) -> (s : List Char) -> lang r s -> match r s = True
matchCompletness Empty s l  = absurd l
matchCompletness Epsilon s prf = rewrite prf in Refl
matchCompletness (Chr x) [] l = ?ddfdf
matchCompletness (Chr x) ([y]) prf = rewrite singletonEq prf in ?ddfeeer
matchCompletness (Chr x) (x1 :: x2 :: xs) l impossible
matchCompletness (Alt x y) s (Left z) = let rec = matchCompletness x s z in rewrite rec in Refl
matchCompletness (Alt x y) s (Right z) = let rec = matchCompletness y s z in rewrite rec in rewrite orTrueTrue (match x s) in Refl
matchCompletness (Concat x y) s (((pre, suf) ** (v, (t, u)))) =
  let rec1 = matchCompletness x pre t
      rec2 = matchCompletness y suf u
      temp = trans (cong (&& (match y suf)) rec1 ) rec2
      in ?heee
      --lem = sym (splitsMatch (splitElem z w v) temp) in rewrite lem
      --in Refl
matchCompletness (Star r) s (([] ** (y, z))) =  rewrite y in Refl
matchCompletness (Star r) [] (xs ** (z, ws)) = Refl
matchCompletness (Star r) (y :: ys) (((x::xs) ** (z, w::ws))) =
  let rec = matchCompletness (Star r) (foldr (++) [] xs) (xs ** (Refl, ws) )
      rec1 = matchCompletness r x w
      There (splitPrf) = splitElem x (foldr (++) [] xs) z
      temp = trans (cong (&& (match (Star r) (foldr (++) [] xs))) rec1) rec
      spp = splitsMatch splitPrf temp
      in spp
matchCompletness (Star r) (y :: ys) (([] ** (z, ws))) = absurd z
matchCompletness (Star r) (y :: ys) (((x :: xs) ** (z, []))) impossible
matchCompletness (Star r) (y :: ys) ((xs ** (z, ws))) impossible



matchSoundness : (r : Regex Char) -> (s : List Char) -> (match r s) = True -> lang r s
matchSoundness Empty s prf = absurd prf
matchSoundness Epsilon s prf = case s of
                                      [] => Refl
                                      (x :: xs) => absurd prf
matchSoundness (Chr x) s prf = case s of
                                      [] => absurd prf
                                      ([y]) => singletonEqRev prf
                                      (x1 :: x2 :: xs) => absurd prf
matchSoundness (Alt x y) s prf = case decEq (match x s) True of
                                      (Yes z) => let rec = matchSoundness x s z  in Left rec
                                      (No contra_x) => case decEq (match y s) True of
                                                          (Yes z) => let rec = matchSoundness y s z in Right rec
                                                          (No contra_y) => let mx = notTrueIsFalse contra_x
                                                                               my = notTrueIsFalse contra_y
                                                                               temp = sym (trans (cong (|| match y s) mx) my)
                                                                              in absurd (trans temp prf)
matchSoundness (Concat x y) s prf = ?ffg_5
matchSoundness (Star x) s prf = ?ffg_7
-- Main match function

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
