---
forbidden:
- idJ
hints:
- text: 'This is the mirror of the right unit law. The composite `id ∘ f` is a witnessed composite, and the left-unit triangle `id-comp-witness` witnesses that its hypotenuse is `f`. Uniqueness does the rest.'
- text: 'Apply `uniqueness-comp-is-segal` to the unit triangle: `uniqueness-comp-is-segal A is-segal-A x x y (id-hom A x) f f (id-comp-witness A x y f)`.'
  when-goal: '= f'
id: left-unit-law
inventory:
- name: uniqueness-comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) (h : hom A x z) (alpha : hom2 A x y z f g h) → comp-is-segal A is-segal-A x y z f g = h'
  synopsis: 'any witnessed composite equals the chosen one'
- name: id-comp-witness
  type: '(A : U) (x y : A) (f : hom A x y) → hom2 A x x y (id-hom A x) f f'
  synopsis: 'the left-unit triangle'
- name: id-hom
  type: '(A : U) (x : A) → hom A x x'
  synopsis: 'the identity arrow'
statement: comp-is-segal A is-segal-A x x y (id-hom A x) f = f
title: The left unit law
---

Now the mirror image: composing the identity at `x` with `f : x → y` on the left also returns `f`. The witness is the left-unit triangle, given in the prelude as `id-comp-witness`, whose left edge is the identity and whose hypotenuse is `f`. So `f` is a witnessed composite of the identity and `f`, and uniqueness identifies it with the chosen composite. The `#def` name `id-comp-is-segal` is the faithful sHoTT name. Build it.

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
```

```rzk template
#def id-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( f : hom A x y)
  : (comp-is-segal A is-segal-A x x y (id-hom A x) f) = f
  := ?
```

```rzk solution
#def id-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( f : hom A x y)
  : (comp-is-segal A is-segal-A x x y (id-hom A x) f) = f
  := uniqueness-comp-is-segal A is-segal-A x x y (id-hom A x) f f (id-comp-witness A x y f)
```

## Conclusion

Both unit laws come from the same source: a hand-built unit triangle, fed to uniqueness of composites. The left unit law is the one that later closes the easy round-trip of the Yoneda equivalence, where evaluating a representable transformation at the identity and composing back returns the original.
