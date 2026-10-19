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

**The `doc-gen4` revision is pinned** in `lakefile.toml` to the tag `v4.35.0`,
whose `lean-toolchain` is `leanprover/lean4:v4.35.0`. Keep this tag, the root
Mathlib pin and both toolchain files synchronized. Do not use `rev = "main"`:
a mismatched dependency can rewrite `docbuild/lean-toolchain` and move shared
package checkouts away from the revisions required by the root project.

The side package shares the root package's `packagesDir`
(`../.lake/packages`), so `lake update doc-gen4` also checks out `doc-gen4`'s
own dependencies there.  At the pinned revision their revisions agree with the
root `lake-manifest.json`; with an unpinned `doc-gen4` they do not, and the
update silently moves a shared package (`Cli`) out from under the main build.

The `:docs` target also generates documentation for transitive imports,
including Mathlib, so this build needs more time and disk space than the
library build alone.

`lake update doc-gen4` ends by running Mathlib's post-update hook
(`lake exe cache get`), which can fail here with "Failed to prune ProofWidgets
cloud release" even though the dependency resolution itself succeeded and
`docbuild/lake-manifest.json` was written.  `scripts/ci_local.sh` therefore
runs the update only when that manifest is missing, and checks that the
manifest exists rather than the exit status of the update.  Commit
`docbuild/lake-manifest.json` so that neither a contributor nor CI needs the
update at all.
