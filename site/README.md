# absinterp documentation site

Nested Verso project that builds the `absinterp` documentation website
and a minimal talk deck. Kept strictly separate from the root Lean
package — `lake build`, `lake build Tests`, and `lake test` at the
repository root are unaffected.

## Layout

```text
site/
├── lean-toolchain            # must match the root's Lean toolchain
├── lakefile.toml             # Verso dependency + two exes
├── Main.lean                 # entry point for the site
├── AbsinterpDocs.lean        # barrel importing AbsinterpDocs.Basic
├── AbsinterpDocs/
│   ├── Basic.lean            # root #doc (Manual)
│   ├── Home.lean
│   ├── Architecture.lean
│   ├── ReadingGuide.lean
│   └── IMPCollectingShowcase.lean
├── SlidesMain.lean           # entry point for the slide deck
├── AbsinterpSlides.lean      # barrel importing AbsinterpSlides.Intro
└── AbsinterpSlides/
    └── Intro.lean            # single-deck slide content
```

## Verso revision strategy

This project is pinned to the Verso tag
[`v4.30.0-rc1`](https://github.com/leanprover/verso/tree/v4.30.0-rc1),
which exactly matches the repository-wide Lean toolchain
(`leanprover/lean4:v4.30.0-rc1`). That tag was chosen because:

- it is a shipped Verso release with a matching toolchain file, so the
  transitive dependency graph (subverso, MD4Lean, plausible) is
  reproducible;
- it avoids the risk of a `main`-based pin silently picking up
  incompatible nightly churn;
- the exact-toolchain match means the nested project's Lean binary is
  identical to the one the root project uses, so there is no
  elanswitching overhead.

Upgrade plan: when Lean `v4.30.0` stable ships (and a corresponding
Verso `v4.30.0` tag exists), move the pin to that stable tag. If the
root `absinterp` toolchain moves ahead of Verso's releases (as happened
briefly with `v4.30.0-rc2`), prefer the newest Verso tag whose
toolchain still matches over a `main`-based pin.

## First build

The first build fetches Verso and its transitive dependencies
(`subverso`, `MD4Lean`, `plausible`, plus their own deps). This can
take a while (several minutes) depending on network and disk.

```bash
cd site
lake update verso
lake build site
```

Subsequent builds are incremental.

## Build the documentation site

```bash
cd site
lake exe site
```

Output lands under `site/_out/html-multi/`. Preview locally with any
static web server, for example:

```bash
cd site/_out/html-multi
python3 -m http.server 8000
```

and open <http://localhost:8000>.

## Build the slide deck

```bash
cd site
lake exe slides
```

The slides executable emits a single-file HTML at
`site/_out/slides/html-single/index.html`. Open that file in a
browser.

The current slide deck uses `VersoManual` as the backing genre, with
each top-level section acting as a logical slide. When Verso ships a
dedicated slides genre whose toolchain matches ours, migrate
`AbsinterpSlides/Intro.lean` to that genre.

## GitHub Pages deployment

The workflow at `.github/workflows/docs-site.yml` builds the docs site
on every push to `main` and publishes the emitted HTML to GitHub Pages.
Repository settings must have Pages enabled with the "GitHub Actions"
source for the workflow to succeed.

Published URL:
`https://<owner>.github.io/<repo>/` — for this repository, once enabled
that resolves to `https://maokami.github.io/absinterp/`.

## Do not

- Do not add imports from the root `AbsInterp` or `Examples` libraries
  into site sources; the nested project intentionally does not depend
  on the root Lean package. Reference the source by link or filename
  instead.
- Do not move the root project's `lakefile.toml` or toolchain to
  accommodate Verso. The two projects stay independent.
