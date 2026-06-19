---
hints:
- text: 'A dependent pair is written `(a , b)`: the base point, then the fiber point.'
id: forming-a-pair
statement: 'Σ (x : A) , B x'
title: Forming a pair
---

A dependent pair packages a point `a : A` with a point `b : B a` of the fiber above it. Build the pair.

```rzk prelude
#lang rzk-1
```

```rzk template
#def make-pair (A : U) (B : A → U) (a : A) (b : B a)
  : Σ (x : A) , B x
  := ?
```

```rzk solution
#def make-pair (A : U) (B : A → U) (a : A) (b : B a)
  : Σ (x : A) , B x
  := (a , b)
```

## Conclusion

The pair `(a , b)` inhabits the Σ-type. The first component chooses a point of the base, and the second lives in the fiber over it.
