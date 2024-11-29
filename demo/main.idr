module Main

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
threeIsOdd = SEvenIsOdd (SOddIsEven (SEvenIsOdd ZIsEven))


reverse' : List a -> List a
reverse' [] = []
reverse' (x::xs) = reverse' xs ++ [x]

onePlusOne: 1+1=2
onePlusOne = Refl 

plus_commutes_zero : (m :Nat) -> m = m + 0
plus_commutes_zero Z = Refl
plus_commutes_zero (S k) = 
  let rec = plus_commutes_zero k in
      rewrite sym rec in Refl

plus_commutes_S : (k : Nat) -> (m : Nat) -> S (m + k) =  m + (S k)
plus_commutes_S k Z = Refl
plus_commutes_S k (S m) = 
    let rec = plus_commutes_S k m in
    rewrite rec in Refl 

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_zero m
plus_commutes (S k) m = let rec = plus_commutes k m in
                            rewrite rec in plus_commutes_S k m



