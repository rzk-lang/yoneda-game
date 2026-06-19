# Engine follow-ups (upstream to rzk-game)

Feature requests and gaps this game surfaces against the [`rzk-game`](https://github.com/rzk-lang/rzk-game) engine. These are requests, not blockers: the game is authored around them. Nikolai files the issues himself; the drafts below are ready to paste.

## Requested features

### Chapters: a grouping above sections

The game runs to a dozen-odd sections that fall into three natural blocks (HoTT foundations, directed shapes and Segal types, the Yoneda lemma). The table of contents has only a flat list of sections, so this structure cannot be expressed. A grouping above sections, "chapters", would carry it.

Draft: *Add an optional grouping above sections (chapters) to `game.yaml`, so a large game can present its sections in named blocks. Sections without a chapter stay top-level, for backward compatibility.*

### A real fast-track or placement mechanism

The HoTT chapter is prerequisite material that a fluent player should be able to skip. We currently do this by marking the lemmas `role: pretest` and letting the player mark each one "I already know this", which satisfies the downstream `prereqs`. This is a mild abuse: the pre-test exists for per-puzzle self-assessment, not chapter-level skipping, and it forces every skippable lemma into a pretest role.

Draft: *Add a way to fast-track or place out of a block of prerequisite puzzles in one action, rather than marking each pre-test "I already know this" individually. For example, a section- or chapter-level "I already know this material" that satisfies the section's puzzles as prereqs, or an explicit placement test that unlocks a later section.*

## Gaps tracked per-case (see content-map.md)

These are handled case by case as authoring reaches them, not filed up front:

- **funext as an assumption.** Confirm the schema and gating accept `#assume funext : FunExt` in a prelude and the `uses (…)` annotation. First needed in the HoTT chapter (function extensionality) and again at the Yoneda capstone.
- **Sections with variables.** The geodesic proves the Yoneda round-trips inside `#section` / `#variable` with automatic generalization. Confirm the engine carries this into a level, or inline the proofs into ordinary `#def`s.
- **Diagram rendering.** The source illustrates triangles and squares with inline SVG. Pure illustration, no engine support needed; a nicer in-game renderer would be the roadmap's D12.
- **Prelude recheck latency.** Prelude-context reuse is still deferred upstream. The largest preludes (unit laws, naturality, Yoneda) are where per-level latency may first hurt.
