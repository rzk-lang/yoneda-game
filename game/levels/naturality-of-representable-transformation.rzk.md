---
forbidden:
- idJ
hints:
- text: 'Both sides equal the diagonal: `comp-coherence` gives the left side, `simplified-id-coherence` gives the right. `zig-zag-concat` joins two paths into a shared target.'
- text: 'The shape is `zig-zag-concat (hom A x b) (comp-is-segal A is-segal-A x y b f (ϕ y v)) (diagonal A is-segal-A a b x y f v ϕ) (ϕ x (comp-is-segal A is-segal-A x y a f v)) ? ?`.'
- text: 'The two paths are the coherences: `comp-coherence A is-segal-A a b x y f v ϕ` and `simplified-id-coherence A is-segal-A a b x y f v ϕ`.'
  when-goal: '= (ϕ x'
id: naturality-of-representable-transformation
inventory:
- name: zig-zag-concat
  type: '(A : U) (x y z : A) (p : x = y) (q : z = y) → x = z'
  synopsis: 'join two paths that share a target'
- name: comp-coherence
  type: '(A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → comp-is-segal A is-segal-A x y b f (ϕ y v) = diagonal …'
  synopsis: 'the lower coherence'
- name: simplified-id-coherence
  type: '(A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → ϕ x (comp-is-segal A is-segal-A x y a f v) = diagonal …'
  synopsis: 'the simplified upper coherence'
- name: diagonal
  type: '(A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → hom A x b'
  synopsis: 'the diagonal of the transformed square'
- name: comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z'
  synopsis: 'the chosen composite'
- name: hom
  type: '(A : U) (x y : A) → U'
  synopsis: 'the type of arrows, passed as an explicit type argument'
statement: 'comp-is-segal A is-segal-A x y b f (ϕ y v) = ϕ x (comp-is-segal A is-segal-A x y a f v)'
title: Naturality is automatic
---

Everything is in place. `comp-coherence` says the composite of `f` and `ϕ y v` equals the diagonal. `simplified-id-coherence` says the value of `ϕ` on the composite of `f` and `v` equals the same diagonal. Two arrows equal to a common third are equal to each other. Join the two equalities through the diagonal with `zig-zag-concat`, and naturality falls out: `ϕ` carries the composite to the composite, with no naturality hypothesis assumed. Build it.

(The `#def` name `naturality` abbreviates the geodesic's `Naturality-contravariant-fiberwise-representable-transformation`.)

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
#def zig-zag-concat
  ( A : U) ( x y z : A) ( p : x = y) ( q : z = y)
  : x = z
  := concat A x y z p (rev A z y q)
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
  : ( t : Δ¹) → (s : Δ¹) → A [ t ≡ 0₂ ↦ comp-is-segal A is-segal-A x y a f v s
                             , t ≡ 1₂ ↦ v s
                             , s ≡ 0₂ ↦ f t
                             , s ≡ 1₂ ↦ a ]
  := \ t s →
       recOR
       ( s ≤ t ↦ (witness-comp-is-segal A is-segal-A x y a f v) (t , s)
       , t ≤ s ↦ (comp-id-witness A x a (comp-is-segal A is-segal-A x y a f v)) (s , t))
#def square-transformation
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b [ t ≡ 0₂ ↦ ϕ x (comp-is-segal A is-segal-A x y a f v)
                              , t ≡ 1₂ ↦ ϕ y v ]
  := \ t → ϕ (f t) (\ s → codomain-square A is-segal-A a b x y f v t s)
#def diagonal
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom A x b
  := \ t → square-transformation A is-segal-A a b x y f v ϕ t t
#def comp-witness
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom2 A x y b f (ϕ y v) (diagonal A is-segal-A a b x y f v ϕ)
  := \ (t , s) → square-transformation A is-segal-A a b x y f v ϕ t s
#def comp-coherence
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (comp-is-segal A is-segal-A x y b f (ϕ y v)) = (diagonal A is-segal-A a b x y f v ϕ)
  := uniqueness-comp-is-segal A is-segal-A x y b f (ϕ y v)
       (diagonal A is-segal-A a b x y f v ϕ)
       (comp-witness A is-segal-A a b x y f v ϕ)
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
#def simplified-id-coherence
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (ϕ x (comp-is-segal A is-segal-A x y a f v)) = (diagonal A is-segal-A a b x y f v ϕ)
  := zag-zig-concat (hom A x b)
       (ϕ x (comp-is-segal A is-segal-A x y a f v))
       (comp-is-segal A is-segal-A x b b (ϕ x (comp-is-segal A is-segal-A x y a f v)) (id-hom A b))
       (diagonal A is-segal-A a b x y f v ϕ)
       (comp-id-is-segal A is-segal-A x b (ϕ x (comp-is-segal A is-segal-A x y a f v)))
       (id-coherence A is-segal-A a b x y f v ϕ)
```

```rzk template
#def naturality
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (comp-is-segal A is-segal-A x y b f (ϕ y v))
    = (ϕ x (comp-is-segal A is-segal-A x y a f v))
  := ?
```

```rzk solution
#def naturality
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (comp-is-segal A is-segal-A x y b f (ϕ y v))
    = (ϕ x (comp-is-segal A is-segal-A x y a f v))
  := zig-zag-concat (hom A x b)
       (comp-is-segal A is-segal-A x y b f (ϕ y v))
       (diagonal A is-segal-A a b x y f v ϕ)
       (ϕ x (comp-is-segal A is-segal-A x y a f v))
       (comp-coherence A is-segal-A a b x y f v ϕ)
       (simplified-id-coherence A is-segal-A a b x y f v ϕ)
```

## Conclusion

Every fiberwise transformation between representable functors is automatically natural. The proof was geometric: a square built from a composition witness and a unit triangle, transported by `ϕ`, then read back as two composition relations and glued by uniqueness, the unit law, and path concatenation. This is the technical heart of the contravariant Yoneda lemma.
