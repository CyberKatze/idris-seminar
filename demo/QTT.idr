import Data.Vect
data Vector: (1 n :Nat) ->  Type -> Type where
  Nil : Vector Z a
  (::) : {1 n: Nat} -> a -> Vector n a -> Vector (S n) a

b: Vector 3 Nat
b = 3:: 2 :: 1:: Nil

Head : Vector (S n) a -> a
Head (x :: xs) = x

double :(1 n : Integer) -> Integer 
double n =  n 

rep : Nat -> a -> List a
rep 0 x = []
rep (S k) x = x :: rep k x

data Comp : List ty -> Type where
  Empty: Comp []
  Run: (n : Nat) -> (x: ty) -> Comp xs -> Comp (rep n x ++ xs)

data Singelton : x -> Type where
  Val: (x: a) -> Singelton x

uncompress : Comp xs -> Singelton xs 
uncompress Empty = Val [] 
uncompress (Run n x comp) = let Val ys = uncompress comp in Val ((rep n x) ++ ys) 

fromSingelton : Singelton {x} xs -> x 
fromSingelton (Val xs) = xs 

sample : Comp (rep 1 3 ++ rep 2 2 ++ []) 
sample = Run 1 3 (Run 2 2 Empty)
