---
id: naturality-intro
role: bridge-in
title: Start here
---

A representable functor sends each object `z` to the arrows `hom A z a` into a fixed object `a`. A fiberwise transformation `ϕ : (z : A) → hom A z a → hom A z b` reassigns those arrows, one fiber at a time. Classically you would then have to check that `ϕ` is natural. In a pre-∞-category you do not: naturality is automatic. This section proves it, following Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/).

The plan is geometric. From a composable pair you build a square, push it through `ϕ`, and read two composition relations off its halves. Uniqueness of composites turns each into an equality, and the right unit law and path concatenation glue them into naturality.

*By the end you will be able to:* build the codomain square, transform it by `ϕ`, and assemble the naturality equality.
