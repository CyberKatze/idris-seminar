module Lang

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.So
import Decidable.Equality

%default total

Lang : Type -> Type
Lang a = List a -> Type

-- Empty language: no strings
empty : Lang a
empty _ = Void

-- Universal language: all strings
univ : Lang a
univ _ = Unit 

-- Single-token language
tok : a -> Lang a
tok c w = w = [c]

singleA : Lang Char
singleA = tok 'a'

singleB : Lang Char
singleB = tok 'b'

union: Lang a -> Lang a -> Lang a
union l1 l2 w = Either (l1 w) (l2 w)

aUnionB : Lang Char
aUnionB = union singleA singleB

intersection: Lang a -> Lang a -> Lang a
intersection l1 l2 w = Pair (l1 w) (l2 w)

interAandB : Lang Char
interAandB = intersection aUnionB singleB

proofA : interAandB ['b']
proofA = (Right Refl,  Refl)

exists : {a, b : Type} -> (p: (Pair a b) -> Type) -> Type 
exists {a} {b} p =  DPair (a, b) p 


langConcat: {a: Type} -> Lang a -> Lang a -> Lang a  
langConcat l1 l2 w = exists (\ (w1 , w2) => Pair (w = w1 ++ w2) (Pair (l1 w1) (l2 w2)))

-- "ab"
concatAandB : langConcat Lang.singleA Lang.singleB ['a', 'b']
concatAandB  = MkDPair (['a'], ['b']) (Refl , Refl, Refl) 


