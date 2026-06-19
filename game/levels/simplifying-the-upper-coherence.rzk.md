---
hints:
- text: 'Both the right unit law and `id-coherence` start from the same arrow, the composite of `ϕ x (v ∘ f)` with the identity. `zag-zig-concat` joins two paths out of a shared source.'
- text: 'The shared source is `comp-is-segal A is-segal-A x b b (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b)`, with endpoints `ϕ x (comp-is-segal A is-segal-A x y a f v)` and the diagonal. You pass `hom A x b` as the explicit type argument.'
- text: 'The two paths are the right unit law and the upper coherence: `comp-id-is-segal A is-segal-A x b (ϕ x (comp-is-segal A is-segal-A x y a f v))` and `id-coherence A is-segal-A a b x y f v ϕ`.'
  when-goal: '= (diagonal'
id: simplifying-the-upper-coherence
inventory:
- 'zag-zig-concat : (A : U) (x y z : A) (p : y = x) (q : y = z) → x = z | join two paths that share a source'
- 'comp-id-is-segal : (A : U) (is-segal-A : is-segal A) (x y : A) (f : hom A x y) → comp-is-segal A is-segal-A x y y f (id-hom A y) = f | the right unit law'
- 'id-coherence : (A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → comp-is-segal A is-segal-A x b b (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b) = diagonal … | the upper coherence (given)'
- 'diagonal : (A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → hom A x b | the diagonal of the transformed square'
- 'comp-is-segal : (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z | the chosen composite'
- 'id-hom : (A : U) (x : A) → hom A x x | the identity arrow'
- 'hom : (A : U) (x y : A) → U | the type of arrows, passed as an explicit type argument'
statement: 'ϕ x (comp-is-segal A is-segal-A x y a f v) = diagonal A is-segal-A a b x y f v ϕ'
title: Simplifying the upper coherence
---

The square's upper half gives a second relation. Its witness and coherence are supplied in the prelude as `id-witness` and `id-coherence`, the mirror images of the two you just built. The coherence `id-coherence` says the composite of `ϕ x (v ∘ f)` with the identity equals the diagonal. But composing with the identity changes nothing, by the right unit law you proved earlier. Cancel it. Both that unit law and `id-coherence` start from the same identity composite, so `zag-zig-concat` joins them. The `#def` name `simplified-id-coherence` abbreviates `simplified-coherence-witness-id-transformation-id-codomain-square`. Build it.

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
#def comp-id-is-segal
  ( A : U) ( is-segal-A : is-segal A) ( x y : A) ( f : hom A x y)
  : (comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  := uniqueness-comp-is-segal A is-segal-A x y y f (id-hom A y) f (comp-id-witness A x y f)
#def codomain-square
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  : ( t : Δ¹) → (s : Δ¹) → A
  := \ t s →
       recOR
       ( s ≤ t ↦ (witness-comp-is-segal A is-segal-A x y a f v) (t , s)
       , t ≤ s ↦ (comp-id-witness A x a (comp-is-segal A is-segal-A x y a f v)) (s , t))
#def square-transformation
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  := \ t → ϕ (f t) (\ s → codomain-square A is-segal-A a b x y f v t s)
#def diagonal
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom A x b
  := \ t → square-transformation A is-segal-A a b x y f v ϕ t t
#def id-witness
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom2 A x b b
    (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b)
    (diagonal A is-segal-A a b x y f v ϕ)
  := \ (t , s) → square-transformation A is-segal-A a b x y f v ϕ s t
#def id-coherence
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (comp-is-segal A is-segal-A x b b (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b))
    = (diagonal A is-segal-A a b x y f v ϕ)
  := uniqueness-comp-is-segal A is-segal-A x b b
       (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b)
       (diagonal A is-segal-A a b x y f v ϕ)
       (id-witness A is-segal-A a b x y f v ϕ)
```

```rzk template
#def simplified-id-coherence
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (ϕ x (comp-is-segal A is-segal-A x y a f v))
    = (diagonal A is-segal-A a b x y f v ϕ)
  := ?
```

```rzk solution
#def simplified-id-coherence
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (ϕ x (comp-is-segal A is-segal-A x y a f v))
    = (diagonal A is-segal-A a b x y f v ϕ)
  := zag-zig-concat (hom A x b)
       (ϕ x (comp-is-segal A is-segal-A x y a f v))
       (comp-is-segal A is-segal-A x b b (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b))
       (diagonal A is-segal-A a b x y f v ϕ)
       (comp-id-is-segal A is-segal-A x b (ϕ x (comp-is-segal A is-segal-A x y a f v)))
       (id-coherence A is-segal-A a b x y f v ϕ)
```

## Conclusion

Both halves now read as equalities through the diagonal: the left composite equals it, and so does the value of `ϕ` on the composite. One concatenation away from naturality.
