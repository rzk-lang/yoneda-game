---
hints:
- text: 'Unfold the two maps: evaluating the rebuilt transformation at the identity gives the composite of the identity at `a` with `v`. That is exactly what the left unit law `id-comp-is-segal` simplifies.'
- text: 'Apply the left unit law to `v`: `id-comp-is-segal A is-segal-A a b v`.'
id: the-easy-round-trip
inventory:
- name: id-comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y : A) (f : hom A x y) → comp-is-segal A is-segal-A x x y (id-hom A x) f = f'
  synopsis: 'the left unit law'
statement: 'contra-evid A a b (contra-yon A is-segal-A a b v) = v'
title: The easy round-trip
---

One of the two round-trips is immediate. Start with an arrow `v`, rebuild the transformation with `contra-yon`, then evaluate at the identity with `contra-evid`. Unfolding the two maps, the result is the composite of the identity at `a` with `v`. The left unit law says that composite is `v` again. Apply it. The left unit law is the mirror of the right unit law you proved earlier, and it is provided here ready to use. Build it.

(The `#def` name `contra-evid-yon` is the geodesic's `Contra-evid-yon`.)

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
#def id-hom (A : U) (x : A)
  : hom A x x
  := \ t → x
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
#def witness-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x y z : A)
  ( f : hom A x y) ( g : hom A y z)
  : hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
  := second (first (is-segal-A x y z f g))
#def ind-path
  ( A : U) ( a : A) ( C : (x : A) → (a = x) → U) ( d : C a refl)
  ( x : A) ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
#def ap
  ( A B : U) ( x y : A) ( f : A → B) ( p : x = y)
  : f x = f y
  := ind-path A x (\ y' p' → f x = f y') refl y p
#def first-path-Σ
  ( A : U) ( B : A → U) ( s t : Σ (a : A) , B a) ( e : s = t)
  : first s = first t
  := ap (Σ (a : A) , B a) A s t (\ z → first z) e
#def center-contraction (A : U) (is-contr-A : is-contr A)
  : A
  := first is-contr-A
#def homotopy-contraction (A : U) (is-contr-A : is-contr A)
  : (z : A) → (center-contraction A is-contr-A) = z
  := second is-contr-A
#def uniqueness-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x y z : A)
  ( f : hom A x y) ( g : hom A y z) ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : (comp-is-segal A is-segal-A x y z f g) = h
  := first-path-Σ (hom A x z) (hom2 A x y z f g)
       (comp-is-segal A is-segal-A x y z f g , witness-comp-is-segal A is-segal-A x y z f g)
       (h , alpha)
       (homotopy-contraction (Σ (k : hom A x z) , hom2 A x y z f g k) (is-segal-A x y z f g) (h , alpha))
#def id-comp-witness (A : U) (x y : A) (f : hom A x y)
  : hom2 A x x y (id-hom A x) f f
  := \ (t , s) → f s
#def id-comp-is-segal (A : U) (is-segal-A : is-segal A) (x y : A) (f : hom A x y)
  : (comp-is-segal A is-segal-A x x y (id-hom A x) f) = f
  := uniqueness-comp-is-segal A is-segal-A x x y (id-hom A x) f f (id-comp-witness A x y f)
#def contra-evid (A : U) (a b : A)
  : ((z : A) → hom A z a → hom A z b) → hom A a b
  := \ ϕ → ϕ a (id-hom A a)
#def contra-yon (A : U) (is-segal-A : is-segal A) (a b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := \ v z f → comp-is-segal A is-segal-A z a b f v
```

```rzk template
#def contra-evid-yon
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( v : hom A a b)
  : contra-evid A a b (contra-yon A is-segal-A a b v) = v
  := ?
```

```rzk solution
#def contra-evid-yon
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( v : hom A a b)
  : contra-evid A a b (contra-yon A is-segal-A a b v) = v
  := id-comp-is-segal A is-segal-A a b v
```

## Conclusion

This is the section homotopy of the equivalence, and it falls straight out of the left unit law. The other round-trip is harder: rebuilding from the identity-value and then comparing to the original transformation takes naturality and function extensionality.
