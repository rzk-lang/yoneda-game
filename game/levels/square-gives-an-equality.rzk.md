---
forbidden:
- idJ
hints:
- text: 'The square has a diagonal, `\ t → α t t`, running from `α 0₂ 0₂` to `α 1₂ 1₂`. Each triangular half of `α` is a filler exhibiting that diagonal as a composite: the lower half for the bottom-then-right pair, the upper half for the left-then-top pair.'
- text: 'A half of the square is a `hom2` on the nose. The lower one is `\ (t , s) → α t s`; the upper one is the same square read with its arguments swapped, `\ (t , s) → α s t`.'
- text: 'Uniqueness of composites turns each half into an equality: `uniqueness-comp-is-segal` applied to a half says the chosen composite of that pair equals the diagonal. That gives you two equalities, both pointing at the diagonal.'
- text: 'Two equalities into a common middle, and you want their far ends joined. That is exactly the shape `zig-zag-concat` takes: its second path runs backwards. The type it works in is `hom A (α 0₂ 0₂) (α 1₂ 1₂)`, passed by hand.'
id: square-gives-an-equality
inventory:
- name: uniqueness-comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) (h : hom A x z) (alpha : hom2 A x y z f g h) → comp-is-segal A is-segal-A x y z f g = h'
  synopsis: 'any witnessed arrow is the chosen composite'
- name: zig-zag-concat
  type: '(A : U) (x y z : A) (p : x = y) (q : z = y) → x = z'
  synopsis: 'join two paths that meet in the middle'
- name: comp-is-segal
  type: '(A : U) (is-segal-A : is-segal A) (x y z : A) (f : hom A x y) (g : hom A y z) → hom A x z'
  synopsis: 'the chosen composite'
- name: hom
  type: '(A : U) (x y : A) → U'
  synopsis: 'the type of arrows x → y, passed as an explicit type argument'
statement: 'comp-is-segal A is-segal-A (α 0₂ 0₂) (α 1₂ 0₂) (α 1₂ 1₂) (\ t → α t 0₂) (\ s → α 1₂ s) = comp-is-segal A is-segal-A (α 0₂ 0₂) (α 0₂ 1₂) (α 1₂ 1₂) (\ s → α 0₂ s) (\ t → α t 1₂)'
title: A square gives an equality
---

A square in a Segal type has two ways around it. Go along the bottom and then up the right side, or up the left side and then along the top. Both are composites of arrows between the same two corners, and the square's diagonal fills both. Uniqueness of composites then forces the two composites to be equal.

It is stated for an arbitrary square `α : Δ¹ → Δ¹ → A`, with no boundary data named, which is what makes it reusable: every later square is fed to it whole. It is best taken in one shot, so read the hints in order if you get stuck, and start from `zig-zag-concat`.

(The `#def` name is the geodesic's. The sHoTT library proves the same statement as `comp-eq-square-is-segal`, in a section that names the corners and edges separately.)

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
```

```rzk template
#def eq-square-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( α : Δ¹ → Δ¹ → A)
  : comp-is-segal A is-segal-A (α 0₂ 0₂) (α 1₂ 0₂) (α 1₂ 1₂)
    ( \ t → α t 0₂) (\ s → α 1₂ s)
  = comp-is-segal A is-segal-A (α 0₂ 0₂) (α 0₂ 1₂) (α 1₂ 1₂)
    ( \ s → α 0₂ s) (\ t → α t 1₂)
  := ?
```

```rzk solution
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

## Conclusion

The square is now a machine for producing equalities between composites. Nothing about its boundary was named, so any square at all can be fed to it, including one built by pushing another square through a transformation. That is the next step.
