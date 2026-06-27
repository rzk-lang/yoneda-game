---
hints:
- text: 'A path `e : s = t` between pairs, pushed through the projection `first`, gives a path between first components. That pushing-through is `ap`.'
- text: 'Apply `ap` with the function `\ z → first z`: `ap (Σ (a : A) , B a) A s t (\ z → first z) e`.'
id: path-on-first-components
inventory:
- name: ap
  type: '(A B : U) (x y : A) (f : A → B) (p : x = y) → f x = f y'
  synopsis: 'apply a function to a path'
statement: 'first s = first t'
title: A path on first components
---

Two pairs are identified by a path `e : s = t`. Their first components are then identified too. Apply `ap` with the first projection to turn the path of pairs into a path `first s = first t`.

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
#def ap
  ( A B : U) ( x y : A) ( f : A → B) ( p : x = y)
  : f x = f y
  := ind-path A x (\ y' p' → f x = f y') refl y p
```

```rzk template
#def first-path-Σ (A : U) (B : A → U) (s t : Σ (a : A) , B a) (e : s = t)
  : first s = first t
  := ?
```

```rzk solution
#def first-path-Σ (A : U) (B : A → U) (s t : Σ (a : A) , B a) (e : s = t)
  : first s = first t
  := ap (Σ (a : A) , B a) A s t (\ z → first z) e
```

## Conclusion

This is `first-path-Σ`, the action of `first` on a path of pairs. It is `ap` applied to the projection `\ z → first z`. The matching statement for second components needs transport, which we leave to the library.
