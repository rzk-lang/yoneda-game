# Content map: the ∞-Yoneda game

This note decomposes Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/) into sections and levels for the game. It is a planning artefact, meant to be reviewed before the bulk of the levels are authored. We gate the structure first, then fill in prose and proofs, mirroring how the engine's own game and the `rzk-game-template` were built.

The source is a self-contained proof of the contravariant ∞-Yoneda lemma. It needs only pre-∞-categories: no covariant-family machinery is introduced. It treats the homotopy-type-theory lemmas it uses as imported prerequisites. We give those prerequisites their own front sections, so the game builds its HoTT foundation first and reaches the directed shapes already equipped.

## Vocabulary

We follow the `game.yaml` schema: a game is a list of **sections**, each holding **levels** that are either prose or puzzles. We avoid "curriculum" and "world".

The geodesic names the Segal condition `Is-pre-∞-category`. The engine's existing game uses `is-segal`, with `comp-is-segal` and `witness-comp-is-segal` for the chosen composite and its witness. We recommend standardising on `is-segal` throughout the game. This reuses the engine levels verbatim and lets the later geodesic machinery be rephrased over the same `comp-is-segal` / `witness-comp-is-segal` names, so only the genuinely new definitions (naturality, Yoneda) introduce fresh vocabulary. We keep "pre-∞-category" in the prose as the standard synonym.

### Grouping into chapters (future)

With the HoTT prerequisites added, the game runs to a dozen-odd sections that fall into three natural blocks: HoTT foundations, directed shapes and Segal types, and the Yoneda lemma. A grouping above sections — call it **chapters** — would carry this structure in the table of contents. The engine has no such feature today, so for now we keep a flat list of sections and use the chapter headings below only for readability. Worth filing as an engine follow-up against `rzk-game` if the structure earns its keep.

## The geodesic's rungs

The source builds up through these rungs, in dependency order. Rung 0 collects the HoTT prerequisites it imports; the rest is the directed development.

- **0. HoTT foundations.** Path algebra (`refl`, `ap`, `concat`, `rev`, the zig-zag concatenations), Σ-types (`Σ`, `first`, `second`, `first-path-Σ`), contractibility (`is-contr`, `homotopy-contraction`), equivalences (`is-equiv`), function extensionality (`FunExt`, `eq-htpy`).
- **A. Shapes.** `Δ₁`, `Δ₂` — the directed simplices over the interval cube.
- **B. Hom.** `Hom` — arrows as extension types over `Δ₁`.
- **C. Hom2.** `Hom2` — commutative triangles over `Δ₂`.
- **D. Segal + composition.** `Is-pre-∞-category`, `Comp-…`, `Witness-comp-…`, `Uniqueness-comp-…`.
- **E. Identity + unit laws.** `Id-hom`, the two unit triangles, the two unit-law equalities.
- **F. Naturality of representable transformations.** Nine definitions building `id-codomain-square` up to `Naturality-contravariant-fiberwise-representable-transformation`: every fibrewise transformation `ϕ` is automatically natural.
- **G. The Yoneda lemma.** `Contra-evid` (evaluation at the identity), `Contra-yon` (its inverse), the two round-trips, and `Contra-yoneda-lemma` (the equivalence).
- **H. Naturality of the equivalence.** Naturality of `Contra-evid` in the family and in the object.

Associativity is automatic in the geodesic and omitted there. The engine's game, by contrast, develops it at length (the arrow type, the tetrahedron, the triple composite). That arc is genuine depth but sits off the geodesic's critical path to Yoneda.

## Proposed sections

Status is **port** (copy/trim an existing engine level) or **new** (author from scratch or from the geodesic). The "from" notes cite the engine level id or the geodesic definition. The three chapter headings are for readability only; the table of contents stays a flat list of sections.

### Chapter I — HoTT foundations

These sections need no shapes. Their preludes are small and self-contained, so they keep recheck fast and let players warm up on plain HoTT before the directed layer. The definitions and the axiom are given in the prelude (`Σ`, `is-contr`, `is-equiv`, `FunExt`); the lemmas are the puzzles (`ap`, `concat`, `rev`, the zig-zag concatenations, `first-path-Σ`, `homotopy-contraction`, `eq-htpy`).

A HoTT-fluent player should not have to grind through lemmas they already know. So each lemma puzzle is marked `role: pretest` with `remedies` pointing to the relevant sHoTT page. The player can then mark it "I already know this", which satisfies it as a `prereq` for the directed sections downstream (authoring.md: a puzzle is satisfied once solved or once its pre-test is marked known). The chapter is thus fast-trackable lemma by lemma: novices solve and learn, experts skip ahead. The granularity is a dial — every lemma a pretest, or one representative pretest per section — settled in the conventions note.

**1. Paths and path algebra — new.** `refl`, then `ap` (functions act on paths), `rev` (inversion), `concat` (composition), and the `zig-zag-concat` / `zag-zig-concat` reassociations the naturality proofs later need.

**2. Σ-types — new.** `Σ`, `first`, `second` given; `first-path-Σ` (the path induced on first components) as the puzzle.

**3. Contractibility — new.** `is-contr` given; `homotopy-contraction` (every point is connected to the centre) as the puzzle. Feeds the Segal condition and uniqueness of composites.

**4. Equivalences and function extensionality — new.** `is-equiv` given with a simple equivalence puzzle; `FunExt` introduced as an assumed axiom (`#assume`), and `eq-htpy` derived from it. This is where `#assume` / `uses (…)` first appears, well before Yoneda — a deliberate early test of that engine feature.

### Chapter II — Directed shapes and Segal types

**5. Morphisms and triangles — port.** Opens the directed layer. Direct port of the engine's `morphisms` section.

- `my-id` — the identity morphism (`hom A x x`). [port]
- `const-triangle` — the constant triangle. [port]
- `rut`, `lut` — the right- and left-unit triangles. [port]

Prelude: `Δ¹`, `Δ²`, `hom`, `id-hom`, `hom2`. Covers rungs A–C and the witnesses of E.

**6. Functions act on cells — port.** Functoriality, before any Segal structure. Direct port of the engine's `functions` section.

- `map-point` — a function on a point. [port]
- `ap-hom` — a function on a morphism. [port]

**7. Composition in Segal types — port.** Rung D as the engine already builds it.

- `compose` — the composite as the centre of a contractible type. [port]
- `compose-witness` — the witnessing triangle. [port]

Prelude pulls `is-contr` (chapter I) and adds `is-segal`.

**8. Identity and unit laws — port + new.** Rung E in full. The engine has the unit *triangles* (ported in section 5); the geodesic also needs the unit *laws*, the equalities that composing with the identity returns the original arrow. These are new and depend on uniqueness of composites.

- `uniqueness-comp` — any witnessed composite equals the chosen one (`Uniqueness-comp-…`). [new]
- `comp-id-law` — right unit law (`Comp-id-is-pre-∞-category`). [new]
- `id-comp-law` — left unit law (`Id-comp-is-pre-∞-category`). [new]

Prelude adds `uniqueness-comp-is-segal`, pulling `first-path-Σ` and `homotopy-contraction` from chapter I.

**Optional: Associativity in Segal types — port.** The engine's six-level associativity arc (the arrow type, `arr-in-arr-is-segal`, the tetrahedron, the triple composite). Ready to port, genuine depth, off the critical path. Natural place to add breadth after section 7.

### Chapter III — The Yoneda lemma

**9. Naturality of representable transformations — new.** Rung F, the technical heart before Yoneda. Nine geodesic definitions; a candidate decomposition, each level closing one hole:

- `id-codomain-square` — glue the composition and unit witnesses into a square (`recOR`). [new]
- `square-transformation` — apply `ϕ` columnwise. [new]
- `diagonal-transformation` — its diagonal arrow. [new]
- the two triangle witnesses and their coherence equalities. [new, possibly merged]
- `naturality` — `Naturality-contravariant-fiberwise-representable-transformation`. [new, the payoff]

Prelude carries chapters I–II plus `concat`, `ap`, the zig-zag concatenations. This is the section most likely to need splitting or merging once the proofs are written.

**10. The Yoneda lemma — new.** Rung G, the headline.

- `contra-evid` — evaluation at the identity. [new]
- `contra-yon` — the inverse via composition. [new]
- `contra-evid-yon` — the easy round-trip, from the left unit law. [new]
- `contra-yon-evid` — the hard round-trip, pointwise then glued by funext. [new]
- `contra-yoneda-lemma` — `Contra-evid` is an equivalence. [new, capstone]

Prelude pulls `is-equiv`, `eq-htpy`, and funext from chapter I.

**11. Naturality of the equivalence — new, optional capstone.** Rung H. Naturality of `Contra-evid` in the family (by `refl`) and in the object. A satisfying coda, not required for the lemma itself.

## Critical path versus optional depth

- **Critical path to Yoneda:** sections 1–11 minus the two optional items. The HoTT foundations (1–4) are now on the path, since the lemma genuinely consumes their results.
- **Optional depth:** the associativity arc (after section 7) and section 11. Both are strong content; neither blocks the headline.

The HoTT sections trim to exactly what the geodesic consumes — not all of HoTT, only the lemmas that later sections pull. That keeps chapter I from sprawling.

## Engine-gap candidates (decide per-case)

Per the handoff, engine gaps are handled case by case as they arise. The candidates this map surfaces:

- **funext as an assumption.** Chapter I section 4 introduces `#assume funext : FunExt`, and sections 4 and 10 carry `uses (funext)`. We must confirm the game schema and gating accept `#assume` in a prelude and the `uses (…)` annotation. Moving this into chapter I means we hit the question early, by design, rather than at the Yoneda capstone.
- **Sections with variables.** The geodesic proves the round-trips inside `#section` / `#variable` with automatic generalisation. These can be inlined into ordinary `#def`s to sidestep the feature if the engine does not carry it into a level.
- **Diagram rendering.** The source embeds inline SVG triangles and squares as illustration. These are prose only and need no engine support; they are a nice-to-have for the game UI (cf. the roadmap's D12).
- **Prelude recheck latency.** Sections 8–10 carry the largest preludes. Prelude-context reuse is still deferred upstream, so this is where per-level latency may first hurt. Watch it.

## Authoring gotchas to respect

- The goal is recovered from the `template` `#def`; do not restate it. An empty editable region cannot pass.
- Gating scans only proof bodies, intersected with prelude names, minus inventory tokens. A gated solution must use only granted names.
- Π-types: grouped binders `(x y : A)` are allowed only in `#def` parameters, not in a raw Π-type expression. Keep goal types single-binder.

## Settled decisions (user, 2026-06-19)

- **HoTT lemmas are puzzles.** The lemmas are authored as playable puzzles; only the definitions and the funext axiom are given in preludes. Each lemma puzzle is a `pretest` with `remedies` to sHoTT, so a fluent player can fast-track it (see Chapter I).
- **Port then extend.** Build order: port the directed sections first (Chapter II — morphisms, functions, composition, and optionally associativity) as the proven opening, then author the new content outward, Chapter I (HoTT foundations) and Chapter III (Yoneda). The game's final order is I → II → III; only the build order differs. The vertical-slice option is deferred.

## Next sub-phase

Port-then-extend is chosen, so the next sub-phase ports section 5 (Morphisms and triangles) over the scaffold level — `my-id`, `const-triangle`, `rut`, `lut` — proving the port pipeline before the new content begins. The prose, teaching, and naming conventions are settled first (see `notes/conventions.md`).
