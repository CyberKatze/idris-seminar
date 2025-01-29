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
<!-- new_lines: 1 -->
Idris was one of the first languages to bring dependent types into the practical world of programming.


<!-- end_slide -->
## Equality in idris

### Propositional

```haskell
data (=) : a -> b -> Type where
Refl : x = x
```
```haskell
plus' : Nat -> Nat -> Nat
plus' Z y = y
plus' (S k) y = S (plus' k y)
```
```haskell
plusReducesL : (n : Nat) -> plus' Z n = n
plusReducesL n = Refl
```
```haskell
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

## Multiplicities
- Quantitative Type Theory

```latex
0: The variable is used only at compile time and erased at runtime
1: The variable must be used exactly once at runtime (linear)
ω: The variable can be used any number of times (unrestricted)
```

<!-- end_slide -->
### Erasure
 it allows us to be precise about which values are relevant at run time!!!

 Idris 1 :
 ```haskell
vlen : Vect n a -> Nat
vlen {n} xs = n

 ```
Idris 1 infers whether n is needed at runtime.
 
 <!-- incremental_lists: false -->
Problem: The programmer has no explicit control or indication of whether n is retained at runtime or erased.
<!-- new_lines: 1 -->
Idris 2 :
```haskell
vlen : {n : Nat} -> Vect n a -> Nat
vlen xs = n

```
The type now explicitly states that n is a compile-time implicit argument that will be passed as part of the function call.
<!-- end_slide -->
in Idris 2, names bound in types are also available in the definition without explicitly rebinding them.)

This also means that when you call vlen, you need the length available

```haskell
sumLengths : Vect m a -> Vect n a —> Nat
sumLengths xs ys = vlen xs + vlen ys
```

```haskell
vlen.idr:7:20--7:28:While processing right hand side of Main.sumLengths at vlen.idr:7:1--10:1:
m is not accessible in this context
```
<!-- end_slide -->
by replacing the right hand side of sumLengths with a hole…

```haskell
sumLengths : Vect m a -> Vect n a -> Nat
sumLengths xs ys = ?sumLengths_rhs
```
then checking the hole’s type 

```haskell
Main> :t sumLengths_rhs
 0 n : Nat
 0 a : Type
 0 m : Nat
   ys : Vect n a
   xs : Vect m a
-------------------------------------
sumLengths_rhs : Nat
```
we need to give bindings for m and n with unrestricted multiplicity

```haskell
sumLengths : {m, n : _} -> Vect m a -> Vect n a —> Nat
sumLengths xs ys = vlen xs + vlen xs
```
<!-- end_slide -->

One final note on erasure:
```haskell
badNot : (0 x : Bool) -> Bool
badNot False = True
badNot True = False
```
This is rejected with the error:
```haskell
badnot.idr:2:1--3:1:Attempt to match on erased argument False in
Main.badNot
```
The following, however, is fine.
```haskell
data SBool : Bool -> Type where
     SFalse : SBool False
     STrue  : SBool True
```
```haskell
sNot : (0 x : Bool) -> SBool x -> Bool
sNot False SFalse = True
sNot True  STrue  = False
```
<!-- end_slide -->
### Linearity
<!-- column_layout: [8,10] -->

<!-- column: 0 -->

```haskell
data FileState = Opened | Closed
```
```haskell
data File : FileState -> Type where
  MkFile : (fileName : String) -> File st
```
```haskell
openFile : (1 f : File Closed) -> File Opened
openFile (MkFile name) = MkFile name 
```
<!-- column: 1-->


```haskell
closeFile : (1 f : File Opened) -> File Closed
closeFile (MkFile name) = MkFile name
```
```haskell
deleteFile : (1 f : File Closed) -> IO ()
deleteFile (MkFile name) = putStrLn "File deleted."
```
```haskell
newFile : (1 p : (1 f : File Closed) -> IO ()) -> IO ()
newFile p = p (MkFile "example.txt")
```
<!-- reset_layout -->
```haskell
fileProg : IO ()
fileProg =
  newFile $ \f =>
    let f = openFile f 
        f = closeFile f in 
        deleteFile f

```
