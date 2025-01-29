module Test
import Data.Vect

plus' : Nat -> Nat -> Nat
plus' Z y = y
plus' (S k) y = S (plus' k y)


plusReducesL : (n : Nat) -> plus' Z n = n
plusReducesL n = Refl


plusReducesR : (n: Nat) -> plus' n Z = n
plusReducesR 0 = Refl 
plusReducesR (S k) = 
  let rec = plusReducesR k in 
  rewrite rec in Refl


vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) ->
(xs = ys) -> n = m
vect_eq_length  v1 _ Refl = Refl

leibnizEq : { A: Type } -> (a : A) -> (b : A) -> Type
leibnizEq a b = (P : (_ -> Type)) -> P a -> P b

reflex : {a : Type} -> leibnizEq a a
reflex = \a => (\a => a )

data FileState = Opened | Closed


data File : FileState -> Type where
  MkFile : (fileName : String) -> File st

openFile : (1 f : File Closed) -> File Opened
openFile (MkFile name) = MkFile name 

closeFile : (1 f : File Opened) -> File Closed
closeFile (MkFile name) = MkFile name

deleteFile : (1 f : File Closed) -> IO ()
deleteFile (MkFile name) = putStrLn "File deleted."

newFile : (1 p : (1 f : File Closed) -> IO ()) -> IO ()
newFile p = p (MkFile "example.txt")

fileProg : IO ()
fileProg = do
    newFile $ \f =>
      let f = openFile f 
          f = closeFile f in 
          deleteFile f
    putStrLn "File program done."
