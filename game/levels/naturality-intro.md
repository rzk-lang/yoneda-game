---
id: naturality-intro
role: bridge-in
title: Start here
---

Fix a Segal type `A` and an element `a : A`. The family of types `hom A z a`, indexed by `z : A`, contains all arrows with codomain `a`, and is the contravariant functor represented by `a`. Given another element `b : A`, a fiberwise map `ϕ : (z : A) → hom A z a → hom A z b` converts an arrow with codomain `a` into an arrow with codomain `b`. Classically you would then have to check that `ϕ` is natural. In a pre-∞-category you do not: naturality is automatic. This section proves it, following Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/). The Yoneda lemma itself, later in the game, gives a more precise characterization.

The plan is geometric. From a composable pair you build a square, push it through `ϕ`, and read two composition relations off its halves. Uniqueness of composites turns each into an equality, and the right unit law and path concatenation glue them into naturality.

A word before you start. This section is harder than the earlier ones, and it rewards a pen and paper: draw the square and its two triangles as you build them, since the game does not yet render the diagrams. The terms are also wordy, because Rzk has no implicit arguments, so each lemma is spelled out with the ambient type, its Segal witness, the objects, and the arrows. Do not let that distract you. Most of these are the same standing context, `A`, `is-segal-A`, the objects, `f`, `v`, and `ϕ`, and fill in mechanically. Only one or two arguments at each step carry the real content, and the hints point straight at those.

*By the end you will be able to:* build the codomain square, transform it by `ϕ`, and assemble the naturality equality.
