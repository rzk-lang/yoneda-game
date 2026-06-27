---
hints:
- text: 'You have `p : y = x` and `q : y = z`, both starting at `y`. Reverse `p`, then concatenate with `q`.'
- text: '`rev A y x p : x = y`, so `concat A x y z (rev A y x p) q : x = z`.'
id: zag-zig-concatenation
inventory:
- name: rev
  type: '(A : U) (x y : A) (p : x = y) → y = x'
  synopsis: 'reverse a path'
- name: concat
  type: '(A : U) (x y z : A) (p : x = y) (q : y = z) → x = z'
  synopsis: 'concatenate two paths'
statement: x = z
title: Zag-zig concatenation
---

The mirror image: `p : y = x` and `q : y = z` share their domain `y`. Reverse `p` and concatenate with `q` to get a path `x = z`.

As before, `rev` and `concat` carry over from the earlier levels. Click the prelude for a reminder of how they are typed.

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
#def zag-zig-concat (A : U) (x y z : A) (p : y = x) (q : y = z)
  : x = z
  := ?
```

```rzk solution
#def zag-zig-concat (A : U) (x y z : A) (p : y = x) (q : y = z)
  : x = z
  := concat A x y z (rev A y x p) q
```

## Conclusion

The two zig-zag concatenations handle paths meeting at a shared endpoint, whichever end it is.
