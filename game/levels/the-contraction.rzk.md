---
hints:
- text: 'The contracting homotopy is the second component of the proof: `second is-contr-A`.'
id: the-contraction
statement: '(z : A) → center-contraction A is-contr-A = z'
title: The contraction
---

The second component of an `is-contr` proof is the contraction: for every point `z`, a path from the center to `z`. Extract it.

```rzk prelude
#lang rzk-1
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
#def center-contraction (A : U) (is-contr-A : is-contr A)
  : A
  := first is-contr-A
```

```rzk template
#def homotopy-contraction (A : U) (is-contr-A : is-contr A)
  : (z : A) → (center-contraction A is-contr-A) = z
  := ?
```

```rzk solution
#def homotopy-contraction (A : U) (is-contr-A : is-contr A)
  : (z : A) → (center-contraction A is-contr-A) = z
  := second is-contr-A
```

## Conclusion

The second projection is the contracting homotopy. It is what later lets a Segal type pin down a unique composite.
