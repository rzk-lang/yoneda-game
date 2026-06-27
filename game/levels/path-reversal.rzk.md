---
forbidden:
- idJ
hints:
- text: 'Induct on `p` with `ind-path`. As the endpoint varies, you want a path back to `x`.'
- text: 'The motive sends an endpoint `b` and a path `x = b` to `b = x`. At `refl` that is `x = x`, so the base case is `refl`. Build it with `ind-path A x (\ b q → b = x) refl y p`.'
id: path-reversal
inventory:
- name: ind-path
  type: '(A : U) (a : A) (C : (b : A) → a = b → U) (d : C a refl) (x : A) (p : a = x) → C x p'
  synopsis: 'path induction'
statement: y = x
title: Path reversal
---

A path runs from `x` to `y`. Reverse it to get a path from `y` to `x`. By path induction it is enough to reverse `refl`, and the reverse of the trivial path is trivial.

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
```

```rzk template
#def rev (A : U) (x y : A) (p : x = y)
  : y = x
  := ?
```

```rzk solution
#def rev (A : U) (x y : A) (p : x = y)
  : y = x
  := ind-path A x (\ y' p' → y' = x) refl y p
```

## Conclusion

Reversal turns `x = y` into `y = x`. Every path is invertible, which is why identifications behave like isomorphisms.
