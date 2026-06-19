---
hints:
- text: 'This is a `concat` of two paths in `hom A x b`, through the midpoint `ϕ x (comp-is-segal A is-segal-A x a a f (id-hom A a))`. The first path is naturality; the second transports the right unit law through `ϕ x`.'
- text: 'The first path is naturality applied to `f` and the identity: `naturality A is-segal-A a b x a f (id-hom A a) ϕ`.'
- text: 'The second path applies `ϕ x` to the right unit law with `ap`: `ap (hom A x a) (hom A x b) (comp-is-segal A is-segal-A x a a f (id-hom A a)) f (ϕ x) (comp-id-is-segal A is-segal-A x a f)`.'
  when-goal: '= ϕ x f'
id: the-pointwise-round-trip
inventory:
- name: naturality
  type: '(A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) (ϕ : (z : A) → hom A z a → hom A z b) → comp-is-segal A is-segal-A x y b f (ϕ y v) = ϕ x (comp-is-segal A is-segal-A x y a f v)'
  synopsis: 'naturality of a representable transformation'
- name: comp-id-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y : A) (f : hom A x y) → comp-is-segal A is-segal-A x y y f (id-hom A y) = f'
  synopsis: 'the right unit law'
- name: ap
  type: '(A B : U) (x y : A) (f : A → B) (p : x = y) → f x = f y'
  synopsis: 'a function acts on a path'
- name: concat
  type: '(A : U) (x y z : A) (p : x = y) (q : y = z) → x = z'
  synopsis: 'concatenate two paths'
- name: contra-yon
  type: '(A : U) (is-segal-A : is-segal A) (a b : A) → hom A a b → ((z : A) → hom A z a → hom A z b)'
  synopsis: 'the inverse, by composition'
- name: contra-evid
  type: '(A : U) (a b : A) → ((z : A) → hom A z a → hom A z b) → hom A a b'
  synopsis: 'evaluation at the identity'
- name: comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z'
  synopsis: 'the chosen composite'
- name: id-hom
  type: '(A : U) (x : A) → hom A x x'
  synopsis: 'the identity arrow'
- name: hom
  type: '(A : U) (x y : A) → U'
  synopsis: 'the type of arrows, passed as an explicit type argument'
statement: '(contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x f = ϕ x f'
title: The pointwise round-trip
---

The other round-trip rebuilds a transformation from its identity-value and compares it to the original. They are not definitionally equal, so the comparison is a path, and we build it one layer at a time. Fix an object `x` and an arrow `f : x → a`. Unfolded, the rebuilt value is the composite of `f` with `ϕ a (id-hom A a)`. Naturality, which you proved in the previous section, rewrites that composite as `ϕ x` of the composite of `f` with the identity. The right unit law collapses that inner composite back to `f`, and `ap` transports the equality through `ϕ x`. Concatenate the two steps. Build it.

(The `#def` name `contra-yon-evid-twice-pointwise` is the geodesic's `Contra-yon-evid-twice-pointwise`: pointwise in both the object and the arrow.)

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
#def naturality
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : (comp-is-segal A is-segal-A x y b f (ϕ y v)) = (ϕ x (comp-is-segal A is-segal-A x y a f v))
  := zig-zag-concat (hom A x b)
       (comp-is-segal A is-segal-A x y b f (ϕ y v))
       (diagonal A is-segal-A a b x y f v ϕ)
       (ϕ x (comp-is-segal A is-segal-A x y a f v))
       (comp-coherence A is-segal-A a b x y f v ϕ)
       (simplified-id-coherence A is-segal-A a b x y f v ϕ)
#def contra-evid (A : U) (a b : A)
  : ((z : A) → hom A z a → hom A z b) → hom A a b
  := \ ϕ → ϕ a (id-hom A a)
#def contra-yon (A : U) (is-segal-A : is-segal A) (a b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := \ v z f → comp-is-segal A is-segal-A z a b f v
```

```rzk template
#def contra-yon-evid-twice-pointwise
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b) ( x : A) ( f : hom A x a)
  : (contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x f = ϕ x f
  := ?
```

```rzk solution
#def contra-yon-evid-twice-pointwise
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b) ( x : A) ( f : hom A x a)
  : (contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x f = ϕ x f
  := concat (hom A x b)
       ((contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x f)
       (ϕ x (comp-is-segal A is-segal-A x a a f (id-hom A a)))
       (ϕ x f)
       (naturality A is-segal-A a b x a f (id-hom A a) ϕ)
       (ap (hom A x a) (hom A x b)
         (comp-is-segal A is-segal-A x a a f (id-hom A a))
         f (ϕ x)
         (comp-id-is-segal A is-segal-A x a f))
```

## Conclusion

At a fixed object and arrow the rebuilt transformation agrees with the original. This is the heart of the hard round-trip. The remaining work is bookkeeping: glue these pointwise paths into a single path of transformations, which is exactly what function extensionality does.
