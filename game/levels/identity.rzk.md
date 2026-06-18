---
id: identity
title: The identity morphism
statement: hom A x x
inventory:
- 'x       : A'
- 'λ-intro : introduce the interval coordinate'
---

A morphism $x \to y$ in $A$ is a path along the directed interval $\Delta^1$. The simplest one is the identity: the morphism from $x$ to itself that just stays put. Both endpoints of the path are $x$, so a constant path will do. Build it.

```rzk prelude
#lang rzk-1
#def Δ¹ : 2 → TOPE := \ t → TOP
#def hom (A : U) (x y : A) : U
  := (t : Δ¹) → A [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ]
```

```rzk template
#def identity (A : U) (x : A)
  : hom A x x
  := ?
```

```rzk solution
#def identity (A : U) (x : A)
  : hom A x x
  := \ t → x
```

## Conclusion

The constant path is the identity morphism. Both endpoints ask for $x$, so $x$ itself fills the hole — no need to move along the interval at all.
