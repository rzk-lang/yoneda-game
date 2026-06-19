---
id: equivalences-summary
role: summary
title: Wrap-up
---

You can show the identity is an equivalence, and you have the two directions between paths of functions and homotopies: `htpy-eq` one way by path induction, and `eq-htpy` the other way from the function extensionality axiom. That axiom, `#assume funext`, is the one piece of input the Yoneda development assumes, and its use is tracked by `uses (funext)`. The round-trips in the Yoneda lemma turn homotopies into paths with exactly this `eq-htpy`.
