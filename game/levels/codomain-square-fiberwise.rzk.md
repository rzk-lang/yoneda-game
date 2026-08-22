---
forbidden:
- idJ
hints:
- text: 'The goal is a family of arrows indexed by `t`. Start with `\ t s → ?`: for fixed `t` and `s` you must produce a point of `A`.'
- text: 'Split on the diagonal with `recOR ( s ≤ t ↦ ? , t ≤ s ↦ ? )`. The two cases are the two triangular halves, and they must agree where `s ≡ t`.'
- text: 'The lower half is the composition witness of `f` and `v`, reparametrized: `(witness-comp-is-segal A is-segal-A x y a f v) (t , s)`.'
- text: 'The upper half is the unit triangle on the composite, reparametrized the other way: `(comp-id-witness A x a (comp-is-segal A is-segal-A x y a f v)) (s , t)`.'
id: codomain-square-fiberwise
inventory:
- name: witness-comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)'
  synopsis: 'the triangle witnessing the chosen composite'
- name: comp-id-witness
  type: '(A : U) (x y : A) (f : hom A x y) → hom2 A x y y f (id-hom A y) f'
  synopsis: 'the right-unit triangle'
- name: comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z'
  synopsis: 'the chosen composite'
statement: '(t : Δ¹) → hom A (f t) a'
title: The codomain square, fiberwise
---

The proof of naturality begins with a square. Fix a composable pair `f : x → y` and `v : y → a`. The goal asks for a family of arrows into `a`, one for each `t`, which is the same square as before with its type read differently: instead of a bare `Δ¹ → Δ¹ → A` whose four edges are checked afterwards, the type says outright that the `t`-th column runs from `f t` to `a`.

That is worth the trouble. The boundary is now part of the statement rather than something to verify, and the next step only has to apply `ϕ` fiberwise. Fill the interior with two triangles glued along the diagonal `s ≡ t`, as before.

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
```

```rzk template
#def id-codomain-square
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : ( t : Δ¹) → hom A (f t) a
  := ?
```

```rzk solution
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

## Conclusion

The square holds two composition relations at once. Its lower triangle records the diagonal as a composite of `f` and `v`; its upper triangle is the degenerate witness on that composite. Reading it fiberwise is what lets `ϕ` act on it in one line.
