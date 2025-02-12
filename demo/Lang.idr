module Lang

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.So
import Decidable.Equality
import Data.Vect

%default total
public export
Lang : (a: Type) -> Type
Lang a = List a -> Type

-- Empty language: no strings
public export
empty : Lang a
empty _ = Void



-- Universal language: all strings
public export
univ : Lang a
univ _ = Unit 

-- Language contain empty string
public export
eps : Lang a
eps w = w = []

-- Single-token language
public export
tok : a -> Lang a
tok c w = w = [c]

-- Scalar multiplication
-- not sure when this is useful
public export
(:.:) : Type -> Lang a -> Lang a
(:.:) s l w = Pair s (l w)

-- A ⊎ B
public export
union: Lang a -> Lang a -> Lang a
union l1 l2 w = Either (l1 w) (l2 w)

-- A ∩ B
public export
intersection: Lang a -> Lang a -> Lang a
intersection l1 l2 w = Pair (l1 w) (l2 w)

-- ∃ x. p x, idris couldn't resolve missing type
public export
exists : {a, b : Type} -> (p: (Pair a b) -> Type) -> Type 
exists {a} {b} p =  DPair (a, b) p 

public export
langConcat: {a: Type} -> Lang a -> Lang a -> Lang a  
langConcat l1 l2 w = exists (\ (w1 , w2) => Pair (w = w1 ++ w2) (Pair (l1 w1) (l2 w2)))

public export
concat: {a: Type} -> List (List a )-> List a
concat = foldr (++) []

public export
langStar: {a: Type} -> Lang a -> Lang a
langStar l w  = DPair _ (\ws => Pair (w = concat ws ) (All l ws))


------------------------
-- Examples:
------------------------
singleA : Lang Char
singleA = tok 'a'

singleB : Lang Char
singleB = tok 'b'

aUnionB : Lang Char
aUnionB = union singleA singleB

interAandB : Lang Char
interAandB = intersection aUnionB singleB

proof_b_eq_inter_AandB : interAandB ['b']
proof_b_eq_inter_AandB = (Right Refl,  Refl)

-- "ab"
proof_concatAandB : langConcat Lang.singleA Lang.singleB ['a', 'b']
proof_concatAandB  = ((['a'], ['b']) ** (Refl , Refl, Refl) )

proof_starA : langStar Lang.singleA ['a', 'a', 'a']
proof_starA = ([['a'], ['a'], ['a']] ** (Refl, [Refl, Refl, Refl]))

------------------------

------------------------
-- Decomposition of language
------------------------
-- Nullables
v : { b: Type } -> ( List a -> b ) -> b
v f = f []


-- Derivative
derive :{a,b: Type} -> (List a -> b) -> List a -> (List a -> b)
derive f u = f . ( u ++ )

delta : {a,b: Type} -> (List a -> b) -> a -> (List a -> b)
delta f c = derive f [c]


------------------------
-- monoid homomorphism 
-- Domain: List under concatenation (List, ++ , [])
-- Codomain: endofunctions under composition (A -> A, . , id)
proof_derive:{v, u : List a} -> derive f (u ++ v) = derive (derive f u) v
proof_derive {u = []} = Refl
proof_derive {u = (x :: xs)} = let prf = proof_derive {f = derive f [x]} {u = xs} in prf 

proof_derive_is_fold_delta : (u: List a ) -> derive f u = foldl Lang.delta f u
proof_derive_is_fold_delta [] = Refl
proof_derive_is_fold_delta (x :: xs) = let rec =  proof_derive_is_fold_delta {f = derive f [x]} xs in rewrite rec in Refl

delta_empty : delta Lang.empty a = Lang.empty
delta_empty = Refl

delta_univ : delta Lang.univ a = Lang.univ
delta_univ = Refl

record Iso (A : Type) (B : Type) where  
  constructor MkIso  
  to     : A -> B  
  from   : B -> A  

  -- Proofs that these functions are inverses  
  toFrom : (a : A) -> from (to a) = a  
  fromTo : (b : B) -> to (from b) = b


exIso : {a: Type} -> (p: a -> Type) -> (q: a -> Type) -> Type
exIso p q =  {w : a} -> Iso (p w) (q w)


-- delta_one :  exIso (Lang.delta Lang.one x ) Lang.empty 
-- delta_one = MkIso absurd absurd ?hhhh ?hh1

export
v_concat : Iso (Lang.v (Lang.langConcat l1 l2)) (Pair (v l1) (v l2))
v_concat = MkIso (\ ?hgggh => (?jjj, ?hhh ) ) ?hh2 ?hh3 ?hh4


delta_concat : Lang.delta (Lang.langConcat l1 l2) c = ?rr
delta_concat =  ?ggg
