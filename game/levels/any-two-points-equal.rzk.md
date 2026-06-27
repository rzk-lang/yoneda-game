---
forbidden:
- idJ
hints:
- text: 'Both `x` and `y` are reached by a contraction path from the center, so the two paths share their domain. That is exactly what `zag-zig-concat` joins.'
- text: '`homotopy-contraction A is-contr-A x : center = x` and `homotopy-contraction A is-contr-A y : center = y` share the center. Join them: `zag-zig-concat A x (center-contraction A is-contr-A) y (homotopy-contraction A is-contr-A x) (homotopy-contraction A is-contr-A y)`.'
id: any-two-points-equal
inventory:
- name: center-contraction
  type: '(A : U) (is-contr-A : is-contr A) → A'
  synopsis: 'the center of a contractible type'
- name: homotopy-contraction
  type: '(A : U) (is-contr-A : is-contr A) (z : A) → center-contraction A is-contr-A = z'
  synopsis: 'the path from the center to any point'
- name: zag-zig-concat
  type: '(A : U) (x y z : A) (p : y = x) (q : y = z) → x = z'
  synopsis: 'join two paths that share a domain'
statement: x = y
title: Any two points are equal
---

If a type is contractible, any two of its points are equal. Both `x` and `y` are reached by a contraction path from the center, so the two paths share their domain. Join them with `zag-zig-concat`.

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
#def zag-zig-concat
  ( A : U) ( x y z : A) ( p : y = x) ( q : y = z)
  : x = z
  := concat A x y z (rev A y x p) q
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
  := zag-zig-concat A x (center-contraction A is-contr-A) y
       (homotopy-contraction A is-contr-A x) (homotopy-contraction A is-contr-A y)
```

## Conclusion

The two contraction paths share the center as their domain, so `zag-zig-concat` joins them into a path `x = y`. Contractibility collapses every point into one.
