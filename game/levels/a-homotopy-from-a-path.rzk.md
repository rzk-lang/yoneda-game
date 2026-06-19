---
hints:
- text: 'A path `p : f = g` between functions: induct on `p`. The motive, for a function `g0` and a path `f = g0`, is the homotopy `(x : X) → f x = g0 x`.'
- text: 'At `refl` the homotopy is `\ x → refl`. Build it: `ind-path ((x : X) → A x) f (\ g0 p0 → (x : X) → f x = g0 x) (\ x → refl) g p`.'
id: a-homotopy-from-a-path
inventory:
- 'ind-path : (A : U) (a : A) (C : (b : A) → a = b → U) (d : C a refl) (x : A) (p : a = x) → C x p | path induction'
statement: '(x : X) → f x = g x'
title: A homotopy from a path
---

A path between functions `p : f = g` yields a homotopy: at each point `x`, a path `f x = g x`. Build it by path induction. When `p` is `refl`, the homotopy is `refl` everywhere.

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
#def htpy-eq (X : U) (A : X → U) (f : (x : X) → A x) (g : (x : X) → A x) (p : f = g)
  : (x : X) → f x = g x
  := ?
```

```rzk solution
#def htpy-eq (X : U) (A : X → U) (f : (x : X) → A x) (g : (x : X) → A x) (p : f = g)
  : (x : X) → f x = g x
  := ind-path ((x : X) → A x) f (\ g0 p0 → (x : X) → f x = g0 x) (\ x → refl) g p
```

## Conclusion

This is `htpy-eq`, sending a path of functions to the pointwise homotopy. Function extensionality will say this map is an equivalence.
