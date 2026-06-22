---
hints:
- text: '`idJ` does all the work. Hand it the same six arguments it needs, in order, as a single tuple.'
- text: 'Pass them comma-separated inside parentheses: `idJ (A , a , C , d , x , p)`.'
id: path-induction
statement: C x p
title: Path induction
---

To develop the path algebra we use **path induction**, the elimination rule for the identity type, also called the *J rule*. For a type `A`, a point `a : A`, and a family `C : (x : A) → (a = x) → U` over the paths out of `a`, it says that a single base case `d : C a refl` is enough to cover every endpoint `x` and every path `p : a = x`. Proving a statement for `refl` proves it for every path.

Rzk provides this as a built-in, `idJ`, which takes the arguments `A`, `a`, `C`, `d`, `x`, `p` packed into one tuple. Use it to define `ind-path`, the same rule but with its arguments applied one at a time, without commas or parentheses. From here on you build path proofs by supplying just the motive `C` and the base case `d`. Build it.

```rzk prelude
#lang rzk-1
```

```rzk template
#def ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) → (a = x) → U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := ?
```

```rzk solution
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

## Conclusion

`ind-path` is path induction. Every later path proof is an instance of it: choose the motive `C`, supply the base case `d`, and the rule handles the rest.
