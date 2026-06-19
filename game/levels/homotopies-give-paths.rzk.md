---
hints:
- text: 'Function extensionality, `funext X A f g`, is the proof that `htpy-eq` is an equivalence. The inverse map you want is its retraction.'
- text: 'If you are stuck, start with the shape `first (first (funext ? ? ? ?))` and fill in the four arguments.'
- text: 'The four arguments are `X A f g`: `first (first (funext X A f g))`.'
id: homotopies-give-paths
inventory:
- 'funext : FunExt | the function extensionality axiom (htpy-eq is an equivalence)'
statement: '((x : X) → f x = g x) → (f = g)'
title: Homotopies give paths
---

Function extensionality is the axiom that `htpy-eq` is an equivalence: a homotopy and a path of functions carry the same information. `funext X A f g` is that equivalence. Read off its inverse to turn a homotopy back into a path. Because the term uses the axiom, the definition is marked `uses (funext)`.

```rzk prelude
#lang rzk-1
#def ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) → (a = x) → U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
#def htpy-eq (X : U) (A : X → U) (f g : (x : X) → A x) (p : f = g)
  : (x : X) → f x = g x
  := ind-path ((x : X) → A x) f (\ g0 p0 → (x : X) → f x = g0 x) (\ x → refl) g p
#def homotopy (A B : U) (f g : A → B)
  : U
  := (a : A) → f a = g a
#def identity (A : U)
  : A → A
  := \ a → a
#def comp (A B C : U) (g : B → C) (f : A → B)
  : A → C
  := \ a → g (f a)
#def product (A B : U)
  : U
  := Σ (_ : A) , B
#def has-retraction (A B : U) (f : A → B)
  : U
  := Σ (r : B → A) , homotopy A A (comp A B A r f) (identity A)
#def has-section (A B : U) (f : A → B)
  : U
  := Σ (s : B → A) , homotopy B B (comp B A B f s) (identity B)
#def is-equiv (A B : U) (f : A → B)
  : U
  := product (has-retraction A B f) (has-section A B f)
#def FunExt
  : U
  := (X : U) → (A : X → U) → (f : (x : X) → A x) → (g : (x : X) → A x)
   → is-equiv (f = g) ((x : X) → f x = g x) (htpy-eq X A f g)
#assume funext : FunExt
```

```rzk template
#def eq-htpy uses (funext) (X : U) (A : X → U) (f : (x : X) → A x) (g : (x : X) → A x)
  : ((x : X) → f x = g x) → (f = g)
  := ?
```

```rzk solution
#def eq-htpy uses (funext) (X : U) (A : X → U) (f : (x : X) → A x) (g : (x : X) → A x)
  : ((x : X) → f x = g x) → (f = g)
  := first (first (funext X A f g))
```

## Conclusion

This is `eq-htpy`, the inverse of `htpy-eq` supplied by the axiom: `first (first (funext X A f g))` is the retraction map. Homotopic functions are equal. The Yoneda round-trips, later, are paths built this way.
