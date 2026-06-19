---
hints:
- text: 'The result lives in `hom A a b`. You have `ϕ` and the objects `a`, `b`. Evaluate `ϕ` at the object `a`, then at an arrow into `a`.'
- text: 'The arrow you feed is the identity at `a`: `\ ϕ → ϕ a (id-hom A a)`.'
id: evaluation-at-the-identity
inventory:
- name: id-hom
  type: '(A : U) (x : A) → hom A x x'
  synopsis: 'the identity arrow'
statement: '((z : A) → hom A z a → hom A z b) → hom A a b'
title: Evaluation at the identity
---

A representable functor sends each object `z` to the arrows `hom A z a` into a fixed object `a`. A fiberwise transformation `ϕ` reassigns those arrows, fiber by fiber. The contravariant Yoneda lemma says that all of that data is already determined by one arrow: the value of `ϕ` at the identity. This first map extracts it. Feed `ϕ` the object `a` and the identity arrow at `a`, and read off the arrow `a → b`. Build it.

(The `#def` name `contra-evid` is the geodesic's `Contra-evid`: evaluation of a contravariant transformation at the identity.)

```rzk prelude
#lang rzk-1
#def Δ¹
  : 2 → TOPE
  := \ t → TOP
#def hom (A : U) (x y : A)
  : U
  := (t : Δ¹) → A [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ]
#def id-hom (A : U) (x : A)
  : hom A x x
  := \ t → x
```

```rzk template
#def contra-evid
  ( A : U) ( a : A) ( b : A)
  : ((z : A) → hom A z a → hom A z b) → hom A a b
  := ?
```

```rzk solution
#def contra-evid
  ( A : U) ( a : A) ( b : A)
  : ((z : A) → hom A z a → hom A z b) → hom A a b
  := \ ϕ → ϕ a (id-hom A a)
```

## Conclusion

Evaluation at the identity is one half of the Yoneda equivalence. It is short because all the work is hidden in the claim that it is invertible. The inverse comes next.
