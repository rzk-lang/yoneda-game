---
hints:
- text: 'A square `Δ¹ → Δ¹ → A` is built by `\ t s → recOR ( s ≤ t ↦ ? , t ≤ s ↦ ? )`. The two cases are the two triangular halves, and they must agree on the diagonal `s ≡ t`.'
- text: 'The lower half `s ≤ t` is the composition witness of `f` and `v`, reparametrized: `(witness-comp-is-segal A is-segal-A x y a f v) (t , s)`.'
- text: 'The upper half `t ≤ s` is the unit triangle on the composite, reparametrized: `(comp-id-witness A x a (comp-is-segal A is-segal-A x y a f v)) (s , t)`.'
id: codomain-square
inventory:
- 'witness-comp-is-segal : (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g) | the triangle witnessing the chosen composite'
- 'comp-id-witness : (A : U) (x y : A) (f : hom A x y) → hom2 A x y y f (id-hom A y) f | the right-unit triangle'
- 'comp-is-segal : (A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z | the chosen composite'
statement: '(t : Δ¹) → (s : Δ¹) → A'
title: The codomain square
---

The proof of naturality begins with a square. Fix a fiberwise transformation `ϕ` and a composable pair `f : x → y` and `v : y → a`. Build the square in `A` whose lower triangle is the composition witness of `f` and `v`, and whose upper triangle is the degenerate unit triangle on their composite. A square here is a map out of two copies of `Δ¹`. The tope split `recOR` glues the two triangles along the shared diagonal `s ≡ t`. The `#def` name `codomain-square` is short for the geodesic's `id-codomain-square`. Build it.

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
#def comp-id-witness (A : U) (x y : A) (f : hom A x y)
  : hom2 A x y y f (id-hom A y) f
  := \ (t , s) → f t
```

```rzk template
#def codomain-square
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  : ( t : Δ¹) → (s : Δ¹) → A
  := ?
```

```rzk solution
#def codomain-square
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  : ( t : Δ¹) → (s : Δ¹) → A
  := \ t s →
       recOR
       ( s ≤ t ↦ (witness-comp-is-segal A is-segal-A x y a f v) (t , s)
       , t ≤ s ↦ (comp-id-witness A x a (comp-is-segal A is-segal-A x y a f v)) (s , t))
```

## Conclusion

The square holds two composition relations at once. Its lower triangle records that the diagonal is a composite of `f` and `v`; its upper triangle is the degenerate witness on that composite. Pushing this square through `ϕ` is the next step.
