---
hints:
- text: 'Induct on the second path `q` with `ind-path`, keeping `p` fixed. When `q` is `refl`, the endpoint is `y` and you already hold `p`.'
- text: 'The motive sends an endpoint `c` and a path `y = c` to `x = c`. The base case is `p` itself, not `refl`. Build it with `ind-path A y (\ c r → x = c) p z q`.'
id: path-concatenation
inventory:
- name: ind-path
  type: '(A : U) (a : A) (C : (b : A) → a = b → U) (d : C a refl) (x : A) (p : a = x) → C x p'
  synopsis: 'path induction'
statement: x = z
title: Path concatenation
---

Two paths `p : x = y` and `q : y = z` compose into a path `x = z`. Induct on the second path `q`. When `q` is `refl`, the endpoint `z` is `y`, and you already hold `p : x = y`.

```rzk prelude
#lang rzk-1
#def ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) → (a = x) → U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
```

```rzk template
#def concat (A : U) (x y z : A) (p : x = y) (q : y = z)
  : x = z
  := ?
```

```rzk solution
#def concat (A : U) (x y z : A) (p : x = y) (q : y = z)
  : x = z
  := ind-path A y (\ z' q' → x = z') p z q
```

## Conclusion

This is `concat`. The base case is `p` itself, not `refl`: fixing `q` at `refl` leaves the first path untouched.
