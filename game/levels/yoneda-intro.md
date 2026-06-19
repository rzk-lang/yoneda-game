---
id: yoneda-intro
role: bridge-in
title: Start here
---

The whole game has been building to this. A representable functor sends each object `z` to the arrows `hom A z a` into a fixed object `a`. A fiberwise transformation `ϕ : (z : A) → hom A z a → hom A z b` reassigns those arrows. The contravariant Yoneda lemma says something striking: all of that fiberwise data is determined by a single arrow, the value of `ϕ` at the identity. Evaluation at the identity is an equivalence between the type of such transformations and the type `hom A a b`. This section proves it, following Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/).

The plan is short to state. Two maps go back and forth: evaluation at the identity, and its inverse by composition. One round-trip is immediate, from the left unit law. The other takes real work: rebuild a transformation from its identity-value, then show pointwise, with naturality and the right unit law, that it returns the original, and glue the pointwise paths together with function extensionality.

A word before you start. This section assumes function extensionality, the axiom you met in the equivalences chapter, written here as `funext`. The definitions that use it carry a `uses (funext)` annotation, and an untouched such template may show a red unused-variable mark until you apply the axiom. The terms are also the heaviest in the game, since Rzk has no implicit arguments and these definitions stack the whole naturality machinery on top of the function-extensionality machinery. As before, most arguments are the standing context and fill in mechanically. The hints point at the one or two that carry the content.

*By the end you will be able to:* define the two Yoneda maps, prove both round-trips, and assemble the equivalence.
