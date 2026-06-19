---
hints:
- text: 'This is `eq-htpy` again, now over the object `x`. Its domain is `A` and its codomain family is `\ x → (hom A x a → hom A x b)`.'
- text: 'The two transformations are the rebuilt one and `ϕ`: `contra-yon A is-segal-A a b (contra-evid A a b ϕ)` and `ϕ`.'
- text: 'The homotopy is the previous level, applied at each object: `\ x → contra-yon-evid-once-pointwise A is-segal-A a b ϕ x`.'
  when-goal: '= ϕ'
id: the-other-round-trip
inventory:
- name: eq-htpy
  type: '(X : U) (A : X → U) (f g : (x : X) → A x) → ((x : X) → f x = g x) → f = g'
  synopsis: 'a homotopy gives a path of functions (uses funext)'
- name: contra-yon-evid-once-pointwise
  type: '(A : U) (is-segal-A : is-segal A) (a b : A) (ϕ : (z : A) → hom A z a → hom A z b) (x : A) → (contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x = ϕ x'
  synopsis: 'the round-trip at a point (uses funext)'
- name: contra-yon
  type: '(A : U) (is-segal-A : is-segal A) (a b : A) → hom A a b → ((z : A) → hom A z a → hom A z b)'
  synopsis: 'the inverse, by composition'
- name: contra-evid
  type: '(A : U) (a b : A) → ((z : A) → hom A z a → hom A z b) → hom A a b'
  synopsis: 'evaluation at the identity'
- name: hom
  type: '(A : U) (x y : A) → U'
  synopsis: 'the type of arrows, passed as an explicit type argument'
- name: funext
  type: 'FunExt'
  synopsis: 'the function extensionality axiom'
statement: 'contra-yon A is-segal-A a b (contra-evid A a b ϕ) = ϕ'
title: The other round-trip
---

Now let the object vary too. The rebuilt transformation and `ϕ` agree at every object `x`, as functions, by the previous level. Function extensionality once more glues that family into a single path of transformations. This time the domain is `A` itself and the codomain family sends each object `x` to the function type `hom A x a → hom A x b`. Feed `eq-htpy` those, the two transformations, and the pointwise equality. Build it.

(The `#def` name `contra-yon-evid` is the geodesic's `Contra-yon-evid`: the full retraction homotopy.)

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
#def htpy-eq (X : U) (A : X → U) (f g : (x : X) → A x) (p : f = g)
  : (x : X) → f x = g x
  := ind-path ((x : X) → A x) f (\ g0 p0 → (x : X) → f x = g0 x) (\ x → refl) g p
#def homotopy (A B : U) (f g : A → B) : U := (a : A) → f a = g a
#def identity (A : U) : A → A := \ a → a
#def comp (A B C : U) (g : B → C) (f : A → B) : A → C := \ a → g (f a)
#def product (A B : U) : U := Σ (_ : A) , B
#def has-retraction (A B : U) (f : A → B) : U := Σ (r : B → A) , homotopy A A (comp A B A r f) (identity A)
#def has-section (A B : U) (f : A → B) : U := Σ (s : B → A) , homotopy B B (comp B A B f s) (identity B)
#def is-equiv (A B : U) (f : A → B) : U := product (has-retraction A B f) (has-section A B f)
#def FunExt : U := (X : U) → (A : X → U) → (f : (x : X) → A x) → (g : (x : X) → A x) → is-equiv (f = g) ((x : X) → f x = g x) (htpy-eq X A f g)
#assume funext : FunExt
#def eq-htpy uses (funext) (X : U) (A : X → U) (f : (x : X) → A x) (g : (x : X) → A x)
  : ((x : X) → f x = g x) → (f = g)
  := first (first (funext X A f g))
#def contra-evid (A : U) (a b : A)
  : ((z : A) → hom A z a → hom A z b) → hom A a b
  := \ ϕ → ϕ a (id-hom A a)
#def contra-yon (A : U) (is-segal-A : is-segal A) (a b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := \ v z f → comp-is-segal A is-segal-A z a b f v
#def contra-yon-evid-twice-pointwise
  (A : U) (is-segal-A : is-segal A) (a b : A)
  (ϕ : (z : A) → hom A z a → hom A z b) (x : A) (f : hom A x a)
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
#def contra-yon-evid-once-pointwise uses (funext)
  (A : U) (is-segal-A : is-segal A) (a b : A)
  (ϕ : (z : A) → hom A z a → hom A z b) (x : A)
  : (contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x = ϕ x
  := eq-htpy (hom A x a) (\ f → hom A x b)
       (\ f → (contra-yon A is-segal-A a b (contra-evid A a b ϕ)) x f)
       (\ f → ϕ x f)
       (\ f → contra-yon-evid-twice-pointwise A is-segal-A a b ϕ x f)
```

```rzk template
#def contra-yon-evid uses (funext)
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : contra-yon A is-segal-A a b (contra-evid A a b ϕ) = ϕ
  := ?
```

```rzk solution
#def contra-yon-evid uses (funext)
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : contra-yon A is-segal-A a b (contra-evid A a b ϕ) = ϕ
  := eq-htpy ( A) (\ x → (hom A x a → hom A x b))
       (contra-yon A is-segal-A a b (contra-evid A a b ϕ))
       ( ϕ)
       (\ x → contra-yon-evid-once-pointwise A is-segal-A a b ϕ x)
```

## Conclusion

The hard round-trip is complete: rebuilding a transformation from its identity-value returns the same transformation. With both round-trips in hand, the two Yoneda maps are mutually inverse, and the equivalence assembles in the final level.
