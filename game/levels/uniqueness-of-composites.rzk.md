---
hints:
- text: 'The space of fillers `Σ (k : hom A x z) , hom2 A x y z f g k` is contractible, and its center is the chosen composite paired with its witness. Your own `(h , alpha)` is another point of that same space, so the contraction connects the two. The equality you want is the path on first components.'
- text: 'Feed the contraction to `first-path-Σ`. The contraction is `homotopy-contraction (Σ (k : hom A x z) , hom2 A x y z f g k) (is-segal-A x y z f g) (h , alpha)`; its first-component path is exactly the goal.'
  when-goal: '= h'
id: uniqueness-of-composites
inventory:
- 'first-path-Σ         : (A : U) (B : A → U) (s t : Σ (a : A) , B a) (e : s = t) → first s = first t | the path induced on first components'
- 'homotopy-contraction : (A : U) (is-contr-A : is-contr A) (z : A) → center-contraction A is-contr-A = z | the path from the center to any point'
- 'comp-is-segal        : (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z | the chosen composite'
- 'witness-comp-is-segal: (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g) | the triangle witnessing the chosen composite'
statement: comp-is-segal A is-segal-A x y z f g = h
title: Uniqueness of composites
---

In a Segal type the type of fillers over a composable pair, pairs `(k , alpha)` of an arrow `k` and a triangle `alpha` witnessing it, is contractible. Contractibility means more than existence: every point equals the center. So any arrow `h` that you can witness with a triangle `alpha` is forced to equal the chosen composite. The witness pairs `h` with `alpha` into a point of the contractible space, the contraction joins that point to the center, and the path on first components is the equality of arrows. The `#def` name `uniqueness-comp-is-segal` is the faithful sHoTT name. Build it.

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
```

```rzk template
#def uniqueness-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( z : A)
  ( f : hom A x y) ( g : hom A y z) ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : (comp-is-segal A is-segal-A x y z f g) = h
  := ?
```

```rzk solution
#def uniqueness-comp-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x : A) ( y : A) ( z : A)
  ( f : hom A x y) ( g : hom A y z) ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : (comp-is-segal A is-segal-A x y z f g) = h
  := first-path-Σ (hom A x z) (hom2 A x y z f g)
       (comp-is-segal A is-segal-A x y z f g , witness-comp-is-segal A is-segal-A x y z f g)
       (h , alpha)
       (homotopy-contraction (Σ (k : hom A x z) , hom2 A x y z f g k) (is-segal-A x y z f g) (h , alpha))
```

## Conclusion

Uniqueness is contractibility, read on the nose. The chosen composite is the center of the space of fillers, and any other witnessed arrow is connected to it by the contraction. This single lemma drives both unit laws next, and returns later to simplify the naturality square on the way to Yoneda.
