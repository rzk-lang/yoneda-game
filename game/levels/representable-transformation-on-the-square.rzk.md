---
forbidden:
- idJ
hints:
- text: 'Work column by column: `\ t → ?`, where for a fixed `t` you must produce an arrow `hom A (f t) b`.'
- text: 'The column of the square at `t` is `\ s → codomain-square A is-segal-A a b x y f v t s`, an arrow into `a`. Feed it to `ϕ (f t)`.'
- text: 'Put the two pieces together: a `\ t → …` that feeds the `t`-th column to `ϕ (f t)`. Assemble it yourself from the column and the application above.'
id: representable-transformation-on-the-square
inventory:
- name: codomain-square
  type: '(A : U) (is-segal-A : is-segal A) (a b x y : A) (f : hom A x y) (v : hom A y a) → (t : Δ¹) → (s : Δ¹) → A [ t ≡ 0₂ ↦ comp-is-segal A is-segal-A x y a f v s , t ≡ 1₂ ↦ v s , s ≡ 0₂ ↦ f t , s ≡ 1₂ ↦ a ]'
  synopsis: 'the square with edges f, v, the composite, and the constant at a'
statement: '(t : Δ¹) → hom A (f t) b'
title: Transforming the square
---

Now push the square through the transformation. Here `ϕ` becomes an argument, with the type it has had all along: `ϕ : (z : A) → hom A z a → hom A z b`, a fiberwise map carrying an arrow into `a` to an arrow into `b`. For each `t`, the column `\ s → codomain-square … t s` is an arrow into `a`, so `ϕ` carries it to an arrow into `b`. Apply `ϕ` column by column. The goal type asks only for a `t`-indexed family of arrows; the two end columns — at `t ≡ 0₂` the value `ϕ x` of the composite, and at `t ≡ 1₂` the value `ϕ y v` — are checked once you build it. Build it.

(The `#def` name `square-transformation` is short for the geodesic's `square-representable-transformation`.)

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
```

```rzk template
#def square-transformation
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  := ?
```

```rzk solution
#def square-transformation
  ( A : U) ( is-segal-A : is-segal A) ( a : A) ( b : A) ( x : A) ( y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  := \ t → ϕ (f t) (\ s → codomain-square A is-segal-A a b x y f v t s)
```

```rzk postcheck
-- label: the start column is ϕ x of the composite
#def square-transformation-start
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : square-transformation A is-segal-A a b x y f v ϕ 0₂ = ϕ x (comp-is-segal A is-segal-A x y a f v)
  := refl
-- label: the end column is ϕ y v
#def square-transformation-end
  ( A : U) ( is-segal-A : is-segal A) ( a b x y : A)
  ( f : hom A x y) ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : square-transformation A is-segal-A a b x y f v ϕ 1₂ = ϕ y v
  := refl
```

## Conclusion

The transformed square is again a square in `A`, now with codomain `b`. Like the original, it splits into two triangular halves along a diagonal. Naming that diagonal comes next.
