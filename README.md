# yoneda-game (work in progress)

The **∞-Yoneda Game** — an interactive Rzk game following Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/), built on the [`rzk-game`](https://github.com/rzk-lang/rzk-game) engine.

> **Status: work in progress.** The first section (Morphisms and triangles) is in place; the rest of the geodesic to the Yoneda lemma is added over later updates.

## How it works

The game is just data: a `game/game.yaml` table of contents and `game/levels/*.rzk.md` files (Rzk source in fenced `prelude` / `template` / `solution` blocks, plus Markdown prose). There is no Haskell toolchain here — [`rzk-game-action`](https://github.com/rzk-lang/rzk-game-action) fetches the prebuilt engine and bundler from a pinned [`rzk-game`](https://github.com/rzk-lang/rzk-game) release, bundles `game/` into `game.json`, assembles the static site, and `.github/workflows/deploy.yml` publishes it to GitHub Pages.

## Authoring locally

Pin `engine-version` in `deploy.yml` to a released tag for reproducible builds. To iterate on content off-CI, run the bundler from a `rzk-game` checkout over this repo's `game/`.
