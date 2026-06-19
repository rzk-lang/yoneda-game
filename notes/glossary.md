# Glossary

This note fixes the shared vocabulary for the game, and gives a cross-walk between our names and the names used by the sHoTT library, by Riehl's geodesic, and in standard category theory. It is the reference for consistent prose, for the in-game naming note, and for the deviations recorded in `notes/conventions.md`.

We follow sHoTT's code style, so the game name and the sHoTT name almost always agree. Where the geodesic differs (it is a self-contained file with its own conventions), the difference is a deviation we note.

## Game and engine vocabulary

The words for the game's own structure, with the choices from the terminology todo settled.

- **Game.** The whole thing: a `game.yaml` table of contents over a tree of files.
- **Section.** A lesson: an ordered list of items under a title. The unit `game.yaml` groups by.
- **Level.** One item in a section, either a **prose** page or a **puzzle**.
- **Puzzle.** A level with a hole to fill: front-matter, prose, and the `prelude` / `template` / `solution` rzk blocks.
- **Chapter.** A grouping above sections, into named blocks. Not a feature of `rzk-game` today; reserved here for that future grouping (see `notes/engine-followups.md`). For now the table of contents is a flat list of sections.
- **Avoid** "curriculum" and "world". Use "game", "chapter" (future), "section", "level".

Authoring terms:

- **Goal / statement.** The type to inhabit, recovered from the `template` `#def` and shown in the Goal panel via the `statement` front-matter.
- **Prelude / template / solution.** The read-only given definitions; the editable starting text with a `?`; the reference solution that doubles as a test.
- **Inventory.** The named lemmas and moves a puzzle grants, one per line, `name : type | synopsis`. The leading token is the granted name.
- **Gating.** With `gated: true`, a solution that uses a name outside the inventory fails the check.
- **Hints.** An ordered list, general to specific; a `when-goal` hint fires for a given goal shape.
- **Roles.** A puzzle is `core` (gates completion), `pretest` (self-assessment, markable "I already know this"), or `extra` (★, optional). Prose pages take `bridge-in`, `outcomes`, or `summary`. `prereqs` list the puzzle ids that must be satisfied first; `remedies` are labelled pointers shown when stuck.
- **Fast-track.** Marking a `pretest` "I already know this" satisfies it as a `prereq` without solving it.

## Mathematical cross-walk

Game and sHoTT names agree unless noted. The Geodesic column gives Riehl's name where it differs; "—" means it agrees. Rkz primitives are flagged as such (they have no definition to import).

### HoTT foundations

| Game / sHoTT | Geodesic | Standard | Meaning |
| --- | --- | --- | --- |
| `ap` | — | action on paths | a function's action on an identification |
| `concat` | — | transitivity | concatenation of paths |
| `rev` | — | symmetry | inversion of a path |
| `zig-zag-concat`, `zag-zig-concat` | — | (mixed concatenations) | reassociating concatenations used in the naturality proof |
| `first`, `second` | — | π₁, π₂ | projections from a Σ-type (Rzk primitives) |
| `Σ` | — | dependent sum | the Σ-type |
| `is-contr` | — | contractibility | a type with a center to which everything is equal |
| `homotopy-contraction` | — | (contraction) | the homotopy from any point to the center |
| `first-path-Σ` | — | (action on π₁) | the path on first components induced by a path of pairs |
| `is-equiv` | — | equivalence | the predicate of being an equivalence |
| `FunExt` (`#assume funext`) | — | function extensionality | the assumed axiom |
| `eq-htpy` | — | (funext map) | a homotopy gives a path of functions |

### Shapes and hom

| Game / sHoTT | Geodesic | Standard | Meaning |
| --- | --- | --- | --- |
| `Δ¹`, `Δ²`, `Δ³` | `Δ₁`, `Δ₂` | the n-simplices | the directed simplex shapes |
| `2` | — | the directed interval | the interval cube (Rzk primitive) |
| `0₂`, `1₂` | — | the endpoints | the interval's endpoints (Rzk primitives) |
| `≤`, `TOPE`, `TOP` | — | the tope layer | the strict order and tope sorts (Rzk primitives) |
| `A [ Φ ↦ a ]` | — | extension type | a type of fillers with a prescribed boundary |
| `recOR` | — | tope split | a case split over covering topes (Rzk primitive) |
| `hom` | `Hom` | morphism, arrow | the type of arrows `x → y` |
| `hom2` | `Hom2` | commutative triangle | the type of fillers of a 2-simplex |
| `arr` | (not in source) | the arrow type | `Δ¹ → A`; an engine addition for associativity |

### Segal types and composition

| Game / sHoTT | Geodesic | Standard | Meaning |
| --- | --- | --- | --- |
| `is-segal` | `Is-pre-∞-category` | Segal type, pre-∞-category | composites exist and are unique |
| `comp-is-segal` | `Comp-is-pre-∞-category` | the composite | the chosen composite `g ∘ f` |
| `witness-comp-is-segal` | `Witness-comp-is-pre-∞-category` | (witness) | the triangle witnessing the composite |
| `uniqueness-comp-is-segal` | `Uniqueness-comp-is-pre-∞-category` | (uniqueness) | any witnessed composite equals the chosen one |

### Identity and unit laws

| Game / sHoTT | Geodesic | Standard | Meaning |
| --- | --- | --- | --- |
| `id-hom` | `Id-hom` | identity morphism | the constant arrow at a point |
| `comp-id-is-segal` | `Comp-id-is-pre-∞-category` | right unit law | composing with the identity on the right returns the arrow |
| `id-comp-is-segal` | `Id-comp-is-pre-∞-category` | left unit law | composing with the identity on the left returns the arrow |

### Naturality and Yoneda

These late definitions take short `#def` names with long, descriptive level ids (see `notes/conventions.md`). The Geodesic column gives the faithful source name to cite in prose.

| Game (`#def`) | Geodesic | Standard | Meaning |
| --- | --- | --- | --- |
| `naturality` | `Naturality-contravariant-fiberwise-representable-transformation` | naturality | every fiberwise transformation of representables is natural |
| `contra-evid` | `Contra-evid` | the Yoneda map | evaluation at the identity arrow |
| `contra-yon` | `Contra-yon` | the inverse map | the inverse, given by composition |
| `contra-yoneda-lemma` | `Contra-yoneda-lemma` | the Yoneda lemma | `contra-evid` is an equivalence |

Standard terms that appear only in prose: **representable functor** (`hom A z a` as a functor in `z`), **natural transformation** (a fiberwise `ϕ` between representables), and **covariant family**. The geodesic deliberately avoids the covariant-family machinery and works with the explicit representable family, so the game does too.
