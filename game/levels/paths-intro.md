---
id: paths-intro
role: bridge-in
title: Start here
---

This chapter builds the homotopy-type-theory toolkit the later proofs lean on, starting with **paths**. A path `p : x = y` identifies two points of a type, and `refl` is the trivial path from a point to itself. The key move is **path induction**: to prove something about an arbitrary path, it is enough to prove it for `refl`.

These lemmas are standard, so most are marked as pre-tests. If you already know your path algebra, mark them known and move on. Path concatenation and the zig-zag stay mandatory, and the zig-zag is the move the later naturality proofs need.

*By the end you will be able to:* reverse a path, concatenate paths, apply a function to a path, and join two paths that share an endpoint.
