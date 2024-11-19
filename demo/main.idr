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

