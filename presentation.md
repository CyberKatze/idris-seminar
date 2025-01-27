---
title: Idris2
author: Zahra Khodabakhshian
---

## Contents

- Background
- Idris2 features
- Problem specification

<!-- end_slide -->
## Background
Idris 1 first introduced by Edwin Brady in 2009.


<!-- end_slide -->
## Equality in idris

### Propositional

```haskell
data (=) : a -> b -> Type where
Refl : x = x

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

```

<!-- end_slide -->

### Heterogeneous Equality
```haskell
vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) ->
(xs = ys) -> n = m
vect_eq_length  v1 _ Refl = Refl

```

<!-- end_slide -->

### Leibniz Equality

```haskell
leibnizEq : { A: Type } -> (a : A) -> (b : A) -> Type
leibnizEq a b = (P : (_ -> Type)) -> P a -> P b
```

<!-- end_slide -->
## Multiplicities
- Quantitative Type Theory

```latex
0: The variable is used only at compile time and erased at runtime
1: The variable must be used exactly once at runtime (linear)
ω: The variable can be used any number of times (unrestricted)
```

<!-- end_slide -->
### Erasure

<!-- end_slide -->
### Linearity

```haskell
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
fileProg =
  newFile $ \f =>
    let f = openFile f 
        f = closeFile f in 
        deleteFile f

```
