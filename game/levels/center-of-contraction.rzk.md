---
hints:
- text: 'An `is-contr` proof is a pair. Its first component is the center: `first is-contr-A`.'
id: center-of-contraction
statement: A
title: The center of contraction
---

An `is-contr` proof is a pair: a center point, and a family of paths from it to everything. Its first component is the center. Extract it.

```rzk prelude
#lang rzk-1
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
```

```rzk template
#def center-contraction (A : U) (is-contr-A : is-contr A)
  : A
  := ?
```

```rzk solution
#def center-contraction (A : U) (is-contr-A : is-contr A)
  : A
  := first is-contr-A
```

## Conclusion

The first projection of the proof is the center of contraction. Every other point is just a path away.
