---
hints:
- text: 'Both `x` and `y` are a contraction path away from the center. Route a path from `x` to the center to `y`.'
- text: '`homotopy-contraction A is-contr-A x : center = x`, so its reversal is `x = center`. Concatenate with `homotopy-contraction A is-contr-A y : center = y`: `concat A x (center-contraction A is-contr-A) y (rev A (center-contraction A is-contr-A) x (homotopy-contraction A is-contr-A x)) (homotopy-contraction A is-contr-A y)`.'
id: any-two-points-equal
inventory:
- 'center-contraction   : (A : U) (is-contr-A : is-contr A) → A | the center of a contractible type'
- 'homotopy-contraction : (A : U) (is-contr-A : is-contr A) (z : A) → center-contraction A is-contr-A = z | the path from the center to any point'
- 'rev    : (A : U) (x y : A) (p : x = y) → y = x | reverse a path'
- 'concat : (A : U) (x y z : A) (p : x = y) (q : y = z) → x = z | concatenate two paths'
statement: x = y
title: Any two points are equal
---

If a type is contractible, any two of its points are equal. Both `x` and `y` are a path away from the center, so route a path from `x` to the center and on to `y`.

```rzk prelude
#lang rzk-1
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
#def ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) → (a = x) → U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
#def rev
  ( A : U) ( x y : A) ( p : x = y)
  : y = x
  := ind-path A x (\ y' p' → y' = x) refl y p
#def concat
  ( A : U) ( x y z : A) ( p : x = y) ( q : y = z)
  : x = z
  := ind-path A y (\ z' q' → x = z') p z q
#def center-contraction (A : U) (is-contr-A : is-contr A)
  : A
  := first is-contr-A
#def homotopy-contraction (A : U) (is-contr-A : is-contr A)
  : (z : A) → (center-contraction A is-contr-A) = z
  := second is-contr-A
```

```rzk template
#def eq-is-contr (A : U) (is-contr-A : is-contr A) (x y : A)
  : x = y
  := ?
```

```rzk solution
#def eq-is-contr (A : U) (is-contr-A : is-contr A) (x y : A)
  : x = y
  := concat A x (center-contraction A is-contr-A) y
       (rev A (center-contraction A is-contr-A) x (homotopy-contraction A is-contr-A x))
       (homotopy-contraction A is-contr-A y)
```

## Conclusion

Reverse one contraction path and concatenate it with the other: `x` to the center to `y`. Contractibility collapses every point into one.
