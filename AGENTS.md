# AGENTS.md

Lean 4 + Mathlib formalization of chain bounding / Zorn's Lemma. Lake package `ChainBounding`. No tests, lint, or CI configured.

## Commands
- Build all: `lake build`
- Check the main file: `lake env lean GreatestGoodChain.lean` (`lake build GreatestGoodChain` does NOT work — the `lean_lib` only roots `ChainBounding`, so Lake reports "unknown target").
- After changing dependencies: `lake update` (pin Mathlib first, see gotcha), then `lake exe cache get` to fetch prebuilt Mathlib oleans.

## Gotchas
- Toolchain is `leanprover/lean4:v4.34.0-rc2` (matches Mathlib master, Aug 2026). Mathlib is pinned to a full 40-char SHA in `lakefile.lean`: `lake update` fails with "failed to parse latest release tag" without that pin (Mathlib has no release tags). Keep the pin when bumping.
- The real content is the root module `GreatestGoodChain.lean` (thm `zorn`, `unbounded_chain`, `bourbaki_witt_of_complete`, etc., in `namespace ChainBounding`). `ChainBounding/Basic.lean` (`ChainBounding.Basic` target, imported from root `ChainBounding.lean`) is only a placeholder — don't extend it expecting it to be the library entrypoint.
- Custom infix notation: `⊑` = initial segment (`IsSegment`), `⊏` = proper initial segment (`IsPropSegment`), defined at the top of `GreatestGoodChain.lean`.
- `lakefile.lean` sets project options `pp.unicode.fun` and `pp.proofs.withType`; keep new proofs in the same mathlib style (docstringed lemmas, named variables).
- `.lake/` is gitignored and locally pre-built; avoid committing build artifacts.
