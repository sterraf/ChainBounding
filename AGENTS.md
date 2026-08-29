# AGENTS.md

Lean 4 + Mathlib formalization of chain bounding / Zorn's Lemma. Lake package `ChainBounding`. No tests, lint, or CI configured.

## Commands
- Build all: `lake build`
- Build/check one file: `lake build GreatestGoodChain`
- Interactive editing requires elan's `lake` toolchain (env is `leanprover/lean4:v4.8.0-rc1`).

## Gotchas
- Mathlib is pinned to a 2024 rev in `lake-manifest.json`. Do not run `lake update`; it pulls a much newer mathlib incompatible with the pinned toolchain and will break compilation.
- The real content is the root module `GreatestGoodChain.lean` (thm `zorn`, `unbounded_chain`, `bourbaki_witt_of_complete`, etc., in `namespace ChainBounding`). `ChainBounding/Basic.lean` (`ChainBounding.Basic` target, imported from root `ChainBounding.lean`) is only a placeholder — don't extend it expecting it to be the library entrypoint.
- Custom infix notation: `⊑` = initial segment (`IsSegment`), `⊏` = proper initial segment (`IsPropSegment`), defined at the top of `GreatestGoodChain.lean`.
- `lakefile.lean` sets project options `pp.unicode.fun` and `pp.proofs.withType`; keep new proofs in the same mathlib style (docstringed lemmas, named variables).
- `.lake/` is gitignored and locally pre-built; avoid committing build artifacts.