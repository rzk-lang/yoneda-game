---
forbidden:
- idJ
hints:
- text: 'The second projection of a pair `p` is `second p`. Its type is the fiber `B (first p)`.'
id: second-projection
statement: 'B (first p)'
title: The second projection
---

A pair has two projections. The first, `first p`, is its point of the base `A`. The second, `second p`, lives in the fiber `B (first p)`. Recover the second component.

```rzk prelude
#lang rzk-1
```

```rzk template
#def snd (A : U) (B : A → U) (p : Σ (x : A) , B x)
  : B (first p)
  := ?
```

```rzk solution
#def snd (A : U) (B : A → U) (p : Σ (x : A) , B x)
  : B (first p)
  := second p
```

## Conclusion

`second p` lives in `B (first p)`, the fiber over the first projection. The type of the second component depends on the first.
