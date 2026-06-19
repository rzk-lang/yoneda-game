---
hints:
- text: 'You already have uniqueness of composites. The composite `f ∘ id` is *some* witnessed composite, and the right-unit triangle `comp-id-witness` witnesses that its hypotenuse is `f`. Uniqueness turns that witness into the equality.'
- text: 'Apply `uniqueness-comp-is-segal` to the unit triangle: `uniqueness-comp-is-segal A is-segal-A x y y f (id-hom A y) f (comp-id-witness A x y f)`.'
  when-goal: '= f'
id: right-unit-law
inventory:
- 'uniqueness-comp-is-segal : (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) (h : hom A x z) (alpha : hom2 A x y z f g h) → comp-is-segal A is-segal-A x y z f g = h | any witnessed composite equals the chosen one'
- 'comp-id-witness          : (A : U) (x y : A) (f : hom A x y) → hom2 A x y y f (id-hom A y) f | the right-unit triangle'
- 'id-hom                   : (A : U) (x : A) → hom A x x | the identity arrow'
statement: comp-is-segal A is-segal-A x y y f (id-hom A y) = f
title: The right unit law
---

Composing `f : x → y` with the identity at `y` returns `f`. The right-unit triangle from the morphisms section is the witness: it is the degenerate triangle whose right edge is the identity and whose hypotenuse is `f` itself. Here it is given in the prelude as `comp-id-witness`, its faithful sHoTT name. So `f` is a witnessed composite of `f` and the identity, and uniqueness identifies it with the chosen one. The `#def` name `comp-id-is-segal` is the faithful sHoTT name. Build it.

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
#def comp-id-witness (A : U) (x y : A) (f : hom A x y)
  : hom2 A x y y f (id-hom A y) f
  := \ (t , s) → f t
```

```rzk template
#def comp-id-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( f : hom A x y)
  : (comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  := ?
```

```rzk solution
#def comp-id-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( f : hom A x y)
  : (comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  := uniqueness-comp-is-segal A is-segal-A x y y f (id-hom A y) f (comp-id-witness A x y f)
```

## Conclusion

The right unit law is one line off uniqueness, once you have the witnessing triangle. The same triangle you built by hand in the morphisms section now pays off as the witness `comp-id-witness`. This law returns later to simplify the naturality square on the path to Yoneda.
