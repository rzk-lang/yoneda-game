---
hints:
- text: '`is-equiv` is a pair of pairs. Each half is a map back to the source paired with a homotopy. For the identity, the map back is the identity and the homotopy is `refl` everywhere.'
- text: 'Build `((\ a → a , \ a → refl) , (\ a → a , \ a → refl))`: a retraction and a section, each the identity with a `refl` homotopy.'
id: the-identity-equivalence
statement: 'is-equiv A A (\ a → a)'
title: The identity is an equivalence
---

The identity map `\ a → a` is an equivalence: it is its own inverse on both sides. `is-equiv` asks for a retraction and a section, each a map back paired with a homotopy showing it inverts the map. Here every map back is the identity and every homotopy is `refl`. Build the bi-invertible data.

```rzk prelude
#lang rzk-1
#def homotopy (A B : U) (f g : A → B)
  : U
  := (a : A) → f a = g a
#def identity (A : U)
  : A → A
  := \ a → a
#def comp (A B C : U) (g : B → C) (f : A → B)
  : A → C
  := \ a → g (f a)
#def product (A B : U)
  : U
  := Σ (_ : A) , B
#def has-retraction (A B : U) (f : A → B)
  : U
  := Σ (r : B → A) , homotopy A A (comp A B A r f) (identity A)
#def has-section (A B : U) (f : A → B)
  : U
  := Σ (s : B → A) , homotopy B B (comp B A B f s) (identity B)
#def is-equiv (A B : U) (f : A → B)
  : U
  := product (has-retraction A B f) (has-section A B f)
```

```rzk template
#def is-equiv-identity (A : U)
  : is-equiv A A (\ a → a)
  := ?
```

```rzk solution
#def is-equiv-identity (A : U)
  : is-equiv A A (\ a → a)
  := ( (\ a → a , \ a → refl) , (\ a → a , \ a → refl))
```

## Conclusion

The identity is an equivalence, witnessed by itself twice over. `is-equiv` is a pair of pairs: a retraction with its homotopy, and a section with its homotopy.
