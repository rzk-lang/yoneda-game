---
id: equivalences-intro
role: bridge-in
title: Start here
---

An **equivalence** is a map with a two-sided inverse, up to homotopy: `is-equiv f` packages a retraction and a section, each with a homotopy witnessing that it inverts `f`. A **homotopy** between functions is a pointwise path, `(a : A) → f a = g a`.

This section also introduces **function extensionality** as an axiom, `#assume funext : FunExt`. It says the map from a path of functions to a homotopy is an equivalence. From it we read off `eq-htpy`, turning a homotopy back into a path. A definition that uses the axiom is marked `uses (funext)`.

The openers are pre-tests. The closing puzzle, deriving `eq-htpy` from the axiom, stays mandatory.

*By the end you will be able to:* show the identity is an equivalence, turn a path of functions into a homotopy, and turn a homotopy into a path using function extensionality.
