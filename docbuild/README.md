# Documentation build

`doc-gen4` is required from this side package only, so that `lake build` in the
repository root never depends on it (and never needs network access to
resolve it).

```
cd docbuild
lake update doc-gen4
lake build KolmogorovMathlib:docs KolmogorovCounterexamples:docs
```

The generated HTML is written to `docbuild/.lake/build/doc`.

**The `doc-gen4` revision is pinned** in `lakefile.toml` to the tag `v4.28.0`,
the one whose `lean-toolchain` is `leanprover/lean4:v4.28.0`.  Do not put
`rev = "main"` back: `main` now carries `leanprover/lean4:v4.34.0-rc2`, and
`lake update doc-gen4` obeys a dependency's toolchain — it rewrites
`docbuild/lean-toolchain`, downloads that toolchain and then fails, because
Mathlib at the pinned revision is built for v4.28.0.  When this repository
moves to a new Lean release, move this pin to the matching `doc-gen4` tag.

The side package shares the root package's `packagesDir`
(`../.lake/packages`), so `lake update doc-gen4` also checks out `doc-gen4`'s
own dependencies there.  At the pinned revision their revisions agree with the
root `lake-manifest.json`; with an unpinned `doc-gen4` they do not, and the
update silently moves a shared package (`Cli`) out from under the main build.

Scale, measured on this repository: `:docs` covers the transitive imports too,
so the run generates Mathlib's documentation as well — a full build is
about 9,900 jobs and takes roughly 40 minutes on 8 cores from a warm olean
cache, and `docbuild/.lake/build/doc` is about 800 MB (472 MB of it Mathlib, 79 MB this library).

`lake update doc-gen4` ends by running Mathlib's post-update hook
(`lake exe cache get`), which can fail here with "Failed to prune ProofWidgets
cloud release" even though the dependency resolution itself succeeded and
`docbuild/lake-manifest.json` was written.  `scripts/ci_local.sh` therefore
runs the update only when that manifest is missing, and checks that the
manifest exists rather than the exit status of the update.  Commit
`docbuild/lake-manifest.json` so that neither a contributor nor CI needs the
update at all.
