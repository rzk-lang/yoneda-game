---
hints:
- text: 'Use `ind-path` to reduce to the case where the path is `refl`. You supply a motive: for an endpoint and a path to it, what are you proving?'
- text: 'The motive sends an endpoint `b` and a path `x = b` to the goal `f x = f b`. At `refl` that is `f x = f x`, so the base case is `refl`. Build it with `ind-path A x (\ b q → f x = f b) refl y p`.'
id: functions-act-on-paths
inventory:
- 'ind-path : (A : U) (a : A) (C : (b : A) → a = b → U) (d : C a refl) (x : A) (p : a = x) → C x p | path induction'
statement: f x = f y
title: Functions act on paths
---

A function `f : A → B` does to paths what it did to morphisms: it carries them along. Given `p : x = y`, applying `f` gives a path `f x = f y`. Build it by path induction, reducing to the case where `p` is `refl` and both ends are `f x`.

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
#def ap (A B : U) (x y : A) (f : A → B) (p : x = y)
  : f x = f y
  := ?
```

```rzk solution
#def ap (A B : U) (x y : A) (f : A → B) (p : x = y)
  : f x = f y
  := ind-path A x (\ y' p' → f x = f y') refl y p
```

## Conclusion

This is `ap`, the action of a function on a path. When `p` is `refl`, so is its image, which is exactly the base case path induction asks for.
