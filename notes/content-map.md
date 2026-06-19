# Content map: the ∞-Yoneda game

This note decomposes Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/) into sections and levels for the game. It is a planning artefact, meant to be reviewed before the bulk of the levels are authored. We gate the structure first, then fill in prose and proofs, mirroring how the engine's own game and the `rzk-game-template` were built.

The source is a self-contained proof of the contravariant ∞-Yoneda lemma. It needs only pre-∞-categories: no covariant-family machinery is introduced. It builds up through eight rungs, which we use as the spine of the map.

## Vocabulary

We follow the `game.yaml` schema: a game is a list of **sections**, each holding **levels** that are either prose or puzzles. We avoid "curriculum" and "world".

The geodesic names the Segal condition `Is-pre-∞-category`. The engine's existing game uses `is-segal`, with `comp-is-segal` and `witness-comp-is-segal` for the chosen composite and its witness. We recommend standardising on `is-segal` throughout the game. This reuses the engine levels verbatim and lets the later geodesic machinery be rephrased over the same `comp-is-segal` / `witness-comp-is-segal` names, so only the genuinely new definitions (naturality, Yoneda) introduce fresh vocabulary. We keep "pre-∞-category" in the prose as the standard synonym.

## The geodesic's rungs

The extraction of the source gives eight rungs, in dependency order:

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

Status is **port** (copy/trim an existing engine level) or **new** (author from the geodesic). The "from" column cites the engine level id or the geodesic definition.

### 1. Morphisms and triangles — port

Opens the game on the substrate. Direct port of the engine's `morphisms` section.

- `my-id` — the identity morphism (`hom A x x`). [port]
- `const-triangle` — the constant triangle. [port]
- `rut`, `lut` — the right- and left-unit triangles. [port]

Prelude: `Δ¹`, `Δ²`, `hom`, `id-hom`, `hom2`. Covers rungs A–C and the witnesses of E.

### 2. Functions act on cells — port

Functoriality, before any Segal structure. Direct port of the engine's `functions` section.

- `map-point` — a function on a point. [port]
- `ap-hom` — a function on a morphism. [port]

Prelude: as section 1.

### 3. Composition in Segal types — port

Rung D as the engine already builds it.

- `compose` — the composite as the centre of a contractible type. [port]
- `compose-witness` — the witnessing triangle. [port]

Prelude adds `is-contr`, `is-segal`. Covers D, minus uniqueness.

### 4. Identity and unit laws — port + new

Rung E in full. The engine has the unit *triangles* (ported in section 1); the geodesic also needs the unit *laws*, the equalities that composing with the identity returns the original arrow. These are new and depend on uniqueness of composites.

- `uniqueness-comp` — any witnessed composite equals the chosen one (`Uniqueness-comp-…`). [new]
- `comp-id-law` — right unit law (`Comp-id-is-pre-∞-category`). [new]
- `id-comp-law` — left unit law (`Id-comp-is-pre-∞-category`). [new]

Prelude adds `uniqueness-comp-is-segal` and the HoTT lemmas it needs (`first-path-Σ`, `homotopy-contraction`). This is the first prelude heavy enough to watch for recheck latency.

### 5. Naturality of representable transformations — new

Rung F, the technical heart before Yoneda. Nine geodesic definitions; a candidate decomposition into levels, each closing one hole:

- `id-codomain-square` — glue the composition and unit witnesses into a square (`recOR`). [new]
- `square-transformation` — apply `ϕ` columnwise (`square-representable-transformation`). [new]
- `diagonal-transformation` — its diagonal arrow. [new]
- the two triangle witnesses and their coherence equalities (`witness-comp-…`, `witness-id-…` and the two `coherence-…`). [new, possibly merged]
- `naturality` — `Naturality-contravariant-fiberwise-representable-transformation`. [new, the payoff]

Prelude carries everything through section 4 plus `concat`, `ap`, `zig-zag-concat`, `zag-zig-concat`. This is the section most likely to need splitting or merging once the proofs are written.

### 6. The Yoneda lemma — new

Rung G, the headline.

- `contra-evid` — evaluation at the identity. [new]
- `contra-yon` — the inverse via composition. [new]
- `contra-evid-yon` — the easy round-trip, from the left unit law. [new]
- `contra-yon-evid` — the hard round-trip, pointwise then glued by funext. [new]
- `contra-yoneda-lemma` — `Contra-evid` is an equivalence. [new, capstone]

Prelude adds `is-equiv`, `eq-htpy`, and funext (see engine-gap candidates).

### 7. Naturality of the equivalence — new, optional capstone

Rung H. Naturality of `Contra-evid` in the family (by `refl`) and in the object. A satisfying coda, not required for the lemma itself.

## Critical path versus optional depth

- **Critical path to Yoneda:** sections 1, 2, 3, 4, 5, 6. This is the shortest spine that reaches the lemma.
- **Optional depth:** the engine's associativity arc (six levels: the arrow type, `arr-in-arr-is-segal`, the associativity tetrahedron, the triple composite) and section 7. Both are strong content; neither blocks the headline.

The engine's associativity levels are ready to port, so they are cheap to include as a bonus section after section 3. The map leaves them out of the critical path but flags them as the natural place to add breadth.

## Engine-gap candidates (decide per-case)

Per the handoff, engine gaps are handled case by case as they arise. The candidates this map surfaces:

- **funext as an assumption.** The last round-trip and the lemma carry `uses (funext)` against `#assume funext : FunExt`. We must confirm the game schema and gating accept `#assume` in a prelude and the `uses (…)` annotation. This is the most likely blocker; verify before authoring section 6.
- **Sections with variables.** The geodesic proves the round-trips inside `#section` / `#variable` with automatic generalisation. These can be inlined into ordinary `#def`s to sidestep the feature if the engine does not carry it into a level.
- **Diagram rendering.** The source embeds inline SVG triangles and squares as illustration. These are prose only and need no engine support; they are a nice-to-have for the game UI (cf. the roadmap's D12).
- **Prelude recheck latency.** Sections 4–6 carry the largest preludes. Prelude-context reuse is still deferred upstream, so this is where per-level latency may first hurt. Watch it.

## Authoring gotchas to respect

- The goal is recovered from the `template` `#def`; do not restate it. An empty editable region cannot pass.
- Gating scans only proof bodies, intersected with prelude names, minus inventory tokens. A gated solution must use only granted names.
- Π-types: grouped binders `(x y : A)` are allowed only in `#def` parameters, not in a raw Π-type expression. Keep goal types single-binder.

## Open slicing decision (for the user)

With the map in hand, the remaining choice is how to ship the first milestone:

- **(a) Vertical slice.** Author a thin path straight to the first Yoneda-flavoured payoff and ship it live, then iterate.
- **(b) Port first, then extend.** Port sections 1–3 (and optionally the associativity arc) as the opening, then build sections 4–7.

The handoff recommends (b) then (a). The map is laid out to support either.

## Next sub-phase

Port section 1 (Morphisms and triangles) into `game/game.yaml` and `game/levels/`, replacing the single scaffold level. This is the smallest concrete step and proves the port pipeline before the new content begins.
