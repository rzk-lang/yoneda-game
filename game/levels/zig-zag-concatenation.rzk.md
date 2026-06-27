---
hints:
- text: 'You have `p : x = y` and `q : z = y`, both ending at `y`. Reverse `q`, then concatenate.'
- text: '`rev A z y q : y = z`, so `concat A x y z p (rev A z y q) : x = z`.'
id: zig-zag-concatenation
inventory:
- name: rev
  type: '(A : U) (x y : A) (p : x = y) → y = x'
  synopsis: 'reverse a path'
- name: concat
  type: '(A : U) (x y z : A) (p : x = y) (q : y = z) → x = z'
  synopsis: 'concatenate two paths'
statement: x = z
title: Zig-zag concatenation
---

Two paths can point at the same target: `p : x = y` and `q : z = y` both end at `y`. To join them into a path `x = z`, reverse `q` and concatenate. This is the move the later naturality proof leans on.

`rev` and `concat` are already in scope from the earlier levels. Click the prelude for a reminder of how they are typed.

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
#def rev
  ( A : U) ( x y : A) ( p : x = y)
  : y = x
  := ind-path A x (\ y' p' → y' = x) refl y p
#def concat
  ( A : U) ( x y z : A) ( p : x = y) ( q : y = z)
  : x = z
  := ind-path A y (\ z' q' → x = z') p z q
```

```rzk template
#def zig-zag-concat (A : U) (x y z : A) (p : x = y) (q : z = y)
  : x = z
  := ?
```

```rzk solution
#def zig-zag-concat (A : U) (x y z : A) (p : x = y) (q : z = y)
  : x = z
  := concat A x y z p (rev A z y q)
```

## Conclusion

Reversing one path lets you concatenate two that share a codomain. The mirror case, paths that share a domain, is the optional next level.
