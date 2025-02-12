module Test
import Data.Vect

vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vzipWith f [] ys = ?vzipWit_0
vzipWith f (x :: xs) ys = ?vzipWit_1
