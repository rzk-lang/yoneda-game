---
forbidden:
- idJ
hints:
- text: 'You are given `v : hom A a b` and must produce a transformation. Introduce the object and arrow it acts on: `\ v z f → ?`, with `f : hom A z a`.'
- text: 'Compose `f : z → a` with `v : a → b` to get an arrow `z → b`: `comp-is-segal A is-segal-A z a b f v`.'
id: the-inverse-by-composition
inventory:
- name: comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z'
  synopsis: 'the chosen composite'
statement: 'hom A a b → ((z : A) → hom A z a → hom A z b)'
title: The inverse by composition
---

The inverse goes the other way: from a single arrow `v : a → b` it must rebuild a whole fiberwise transformation. There is one natural way to do it. Given an object `z` and an arrow `f : z → a`, compose `f` with `v` to land in `hom A z b`. This is where the Segal structure earns its place: the composite exists because `A` is a pre-∞-category. Build it.

(The `#def` name `contra-yon` is the geodesic's `Contra-yon`: the contravariant Yoneda inverse.)

```rzk prelude
#lang rzk-1
#def Δ¹
  : 2 → TOPE
  := \ t → TOP
#def Δ²
  : ( 2 × 2) → TOPE
  := \ (t , s) → s ≤ t
#def hom (A : U) (x y : A)
  : U
  := (t : Δ¹) → A [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ]
#def hom2 (A : U) (x y z : A)
  ( f : hom A x y) (g : hom A y z) (h : hom A x z)
  : U
  := ((t , s) : Δ²) → A [ s ≡ 0₂ ↦ f t , t ≡ 1₂ ↦ g s , s ≡ t ↦ h s ]
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
#def is-segal (A : U)
  : U
  := (x : A) → (y : A) → (z : A) → (f : hom A x y) → (g : hom A y z)
   → is-contr (Σ (h : hom A x z) , hom2 A x y z f g h)
#def comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x y z : A)
  ( f : hom A x y) ( g : hom A y z)
  : hom A x z
  := first (first (is-segal-A x y z f g))
```

```rzk template
#def contra-yon
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := ?
```

```rzk solution
#def contra-yon
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := \ v z f → comp-is-segal A is-segal-A z a b f v
```

## Conclusion

This map only exists for a pre-∞-category, since it needs composites. Evaluation needs no such structure. The lemma claims these two maps are mutually inverse, and the rest of the section proves the two round-trips.
