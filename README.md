# yoneda-game (work in progress)

The **∞-Yoneda Game** — an interactive Rzk game following Emily Riehl's [geodesic to the Yoneda lemma](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/), built on the [`rzk-game`](https://github.com/rzk-lang/rzk-game) engine.

> **Status: work in progress.** Eight sections in three chapters cover homotopy type theory, synthetic pre-∞-categories, and the contravariant Yoneda lemma.

## How it works

The game content is a `game/game.yaml` table of contents, prose levels in `game/levels/*.md`, and puzzles in `game/levels/*.rzk.md`. Puzzle files contain Markdown prose and fenced Rzk `prelude`, `template`, and `solution` blocks. There is no Haskell toolchain here — [`rzk-game-action`](https://github.com/rzk-lang/rzk-game-action) fetches the prebuilt engine and bundler from a pinned [`rzk-game`](https://github.com/rzk-lang/rzk-game) release, bundles `game/` into `game.json`, assembles the static site. `.github/workflows/deploy.yml` builds the site on pushes and pull requests to `main`, and on manual runs. Only pushes to `main` publish `public/` to the `gh-pages` branch for GitHub Pages.

## Authoring locally

Pin `engine-version` in `deploy.yml` to a released tag for reproducible builds. To iterate on content off-CI, run the bundler from a `rzk-game` checkout over this repo's `game/`.
