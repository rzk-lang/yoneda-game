---
forbidden:
- idJ
hints:
- text: 'The goal is again a family indexed by `t`, so start with `\ t → ?`. For a fixed `t` you owe an arrow `hom A (f t) b`.'
- text: 'The square gives you an arrow `hom A (f t) a` at each `t`, and `ϕ (f t)` is precisely the function from arrows into `a` to arrows into `b` at that object. Feed one to the other.'
id: transformed-square-fiberwise
inventory:
- name: id-codomain-square
  type: '(A : U) (is-segal-A : is-segal A) (a x y : A) (f : hom A x y) (v : hom A y a) → (t : Δ¹) → hom A (f t) a'
  synopsis: 'the codomain square, read fiberwise'
statement: '(t : Δ¹) → hom A (f t) b'
title: Transforming the square, fiberwise
---

Now apply `ϕ` to produce a square with boundary given by `f`, `ϕ y v`, `ϕ` of the composite, and `id-hom A b`.

Because the previous level stated the square fiberwise, this is a single application rather than a construction: at each `t` the column is already an arrow into `a`, and `ϕ` at the object `f t` carries it to an arrow into `b`.

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

#def eq-square-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( α : Δ¹ → Δ¹ → A)
  : comp-is-segal A is-segal-A (α 0₂ 0₂) (α 1₂ 0₂) (α 1₂ 1₂)
    ( \ t → α t 0₂) (\ s → α 1₂ s)
  = comp-is-segal A is-segal-A (α 0₂ 0₂) (α 0₂ 1₂) (α 1₂ 1₂)
    ( \ s → α 0₂ s) (\ t → α t 1₂)
  :=
  zig-zag-concat (hom A (α 0₂ 0₂) (α 1₂ 1₂))
  ( comp-is-segal A is-segal-A (α 0₂ 0₂) (α 1₂ 0₂) (α 1₂ 1₂)
    ( \ t → α t 0₂) (\ s → α 1₂ s))
  ( \ t → α t t)
  ( comp-is-segal A is-segal-A (α 0₂ 0₂) (α 0₂ 1₂) (α 1₂ 1₂)
    ( \ s → α 0₂ s) (\ t → α t 1₂))
  ( uniqueness-comp-is-segal A is-segal-A (α 0₂ 0₂) (α 1₂ 0₂) (α 1₂ 1₂)
    ( \ t → α t 0₂)
    ( \ s → α 1₂ s)
    ( \ t → α t t)
    ( \ (t , s) → α t s))
  ( uniqueness-comp-is-segal A is-segal-A (α 0₂ 0₂) (α 0₂ 1₂) (α 1₂ 1₂)
    ( \ s → α 0₂ s)
    ( \ t → α t 1₂)
    ( \ t → α t t)
    ( \ (t , s) → α s t))

#def id-codomain-square
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : ( t : Δ¹) → hom A (f t) a
  := \ t s →
      recOR
      ( s ≤ t ↦
        ( witness-comp-is-segal A is-segal-A x y a f v)
          ( t , s)
      , t ≤ s ↦
        ( comp-id-witness A x a
          ( comp-is-segal A is-segal-A x y a f v)) (s , t))
```

```rzk template
#def square-representable-transformation
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  := ?
```

```rzk solution
#def square-representable-transformation
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  :=
    \ t →
      ϕ
      ( f t)
      ( id-codomain-square A is-segal-A a x y f v t)
```

## Conclusion

Pushing the square through `ϕ` cost one line, because the square was stated in the form `ϕ` consumes. The result is another square, and squares are what the equality lemma eats.
