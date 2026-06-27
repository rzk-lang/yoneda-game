---
hints:
- text: 'Every point has a trivial path to itself. That path is `refl`.'
id: reflexivity
statement: x = x
title: Reflexivity
---

A **path** `p : x = y` identifies two points of a type. The simplest one is `refl`, the trivial path from a point to itself. Build the path from `x` to `x`.

```rzk prelude
#lang rzk-1
```

```rzk template
#def refl-path (A : U) (x : A)
  : x = x
  := ?
```

```rzk solution
#def refl-path (A : U) (x : A)
  : x = x
  := refl
```

## Conclusion

`refl` is the trivial identification. Path induction lets every proof about a general path reduce to this one case.
