# Conventions: prose, teaching, and naming

This note records the conventions for authoring the ∞-Yoneda game. It covers naming and notation (following the sHoTT library), the prose register, and the teaching design. It is settled with the user (2026-06-19) and should be applied to every level. The companion `notes/content-map.md` records the sections and their order.

## Source of truth

The [sHoTT library](https://rzk-lang.github.io/sHoTT/) is authoritative for code style: identifier names, casing, and notation. A local checkout lives at `/Users/nikolaikudasov/git/rzk-lang/sHoTT`; cross-check each name against it before using it.

Riehl's [geodesic](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/) is authoritative for the mathematical content and ordering, but not for code style. That file is self-contained and uses its own naming (`Hom`, `Is-pre-∞-category`, subscript `Δ₁`), which sHoTT does not follow. Where we diverge from it, we say so (see Deviations).

## Naming

- **sHoTT casing.** Lowercase-kebab identifiers: `hom`, `hom2`, `is-segal`, `comp-is-segal`, `witness-comp-is-segal`, `id-hom`, `is-contr`, `is-equiv`. Never inherit the geodesic's capitalized forms.
- **Prefixes and suffixes carry meaning.** `is-` marks a predicate. `witness-` marks a witness. The chosen element of a contractible structure takes that structure as a suffix, as in `comp-is-segal`. Facts that depend on the Segal structure keep the `-is-segal` suffix (`comp-id-is-segal`, `id-comp-is-segal`, `uniqueness-comp-is-segal`).
- **Segal, not pre-∞-category, in code.** We use `is-segal` and its family throughout, matching the engine and sHoTT's segal chapter. "Pre-∞-category" stays in the prose as the standard synonym.
- **Confirm each HoTT name against sHoTT.** The HoTT lemmas (`ap`, `concat`, `rev`, `zig-zag-concat`, `zag-zig-concat`, `first`, `second`, `first-path-Σ`, `homotopy-contraction`, `eq-htpy`) are imported names; spell them exactly as the library does.

### Level id and `#def` name are decoupled

The `#def` name is shown in the interface and can be hard to read on a small screen, so we keep it short and readable. The level `id` is hidden (it is the stable handle used by `prereqs` and the file path), so we keep it long and descriptive.

- `id`: long and descriptive (for example `naturality-of-representable-transformation`).
- `#def` name: short and still meaningful (for example `naturality`).
- When the `#def` name is a shortened form of the faithful sHoTT or geodesic name, say so in the level's prose, so the player can connect it to the literature.

This decouples the two on purpose, and differs from the engine's existing levels, where `id` and `#def` name coincide.

### Inventory entries

Each inventory line carries the granted name, its type, and a very short human synopsis. The leading token must be the exact granted name, since gating keys on it.

```
name : type | synopsis
```

For example:

```
id-hom : (A : U) → (x : A) → hom A x x | the identity arrow at x
```

Non-name tools (interval coordinates, λ-introduction, and so on) take a pseudo-token and a synopsis, as in `λ-intro : | introduce the interval coordinate`. We confirm the rendering of the `|` separator at the first ported level and adjust if the interface wants something else.

## Notation

- **Superscript simplices** `Δ¹ Δ² Δ³`, as sHoTT writes them. Not the geodesic's subscript `Δ₁`.
- **Directed primitives as in Rzk and sHoTT:** the cube `2`, the points `0₂` and `1₂`, the topes `≤`, `TOPE`, `TOP`, extension types `A [ Φ ↦ a ]`, and `recOR` for tope splits. Greek letters for the variables sHoTT writes in Greek (`ϕ`, `α`).
- **`#lang rzk-1`** is the first line of every prelude. Preludes are read-only and concatenated in order; `make format-game` canonicalizes them.
- **One spelling per object.** Each object has a single fixed Unicode spelling across the whole game, so the same notion never appears two ways.

## Prose

- **American spelling for this project.** This overrides the usual British-`-ise` preference; here we write `formalization`, `normalization`, `generalize`, `fiber`, `behavior`.
- **No em-dash chains.** Do not write in the `... — ... — ...` pattern, and avoid em-dash appositions generally. Prefer two short sentences, a colon, or parentheses.
- **Two registers, both lighter than a paper.** Section prose (bridge-in and summary) sets up and reflects. Puzzle prose is short, concrete, in the second person, and ends with a call to action ("Build it."), matching the existing `identity.rzk.md`. The takeaway goes under a `## Conclusion` heading, shown on success.
- **Do not restate the goal.** The `statement` front-matter and the recovered `#def` type already carry the goal. Prose motivates it; it does not repeat the type.
- **Introduce notation at its defining occurrence.** Use `$...$` for inline math, and Unicode where it reads naturally.
- **Lowercase specialized terms.** Write "Segal type", "pre-∞-category", "extension type" in lowercase. Capitalize only proper nouns (Segal, Yoneda, Riehl). We drop the geodesic's title-casing of specialized terms.
- **Hedged, honest claims.** State limitations plainly and do not oversell, in the spirit of the author's usual style.

### A naming note inside the game

Players meet the sHoTT names and notation for the first time in the game, so we include a short prose page that explains the naming and notation conventions. It sits as a section item in the HoTT (or early sHoTT) chapter, where these names first appear. It also points out the main deviations (see below), so the in-game vocabulary connects to the literature.

## Teaching

- **One hole per level.** Each puzzle closes exactly one `?`. Long proofs are scaffolded across several small puzzles, as the engine's associativity arc does, never as one large body.
- **BOPPPS per section,** via the role tags: `bridge-in` and `outcomes` prose, a `pretest` puzzle with `remedies`, the `core` puzzles, and a `summary` page. Mark optional enrichment `extra` (★) so it does not gate completion.
- **Inventory is the unlocked toolset.** Gating (`gated: true`) enforces that a solution uses only granted names. Order hints from general to specific, and add a `when-goal` hint for the step the goal makes obvious.
- **Fast-track the HoTT prerequisites, but check comprehension.** In the HoTT chapter, most lemmas are `pretest` with `remedies` to sHoTT, so a fluent player marks them "I already know this" and satisfies the downstream `prereqs`. One or two culminating puzzles per HoTT section stay `core` (mandatory), so even a fast-tracking player demonstrates understanding. This use of the pre-test is a mild abuse of the feature; a proper mechanism is requested upstream (`notes/engine-followups.md`).

## Deviations

We record deviations on two axes, both in the prose at the point of deviation and, for the notable ones, in the in-game naming note.

- **From the sHoTT library.** When we rename or shorten a library identifier (for example, a short `#def` name standing in for a longer library name), we note it.
- **From Riehl's geodesic.** When we depart from the source's naming, notation, or structure (for example, lowercasing `Hom` to `hom`, using `is-segal` for `Is-pre-∞-category`, or superscript `Δ¹` for subscript `Δ₁`), we note it.
