# Reusable proof skeleton

This repo doubles as a reusable harness for formalizing a *new* conjecture in
Lean 4 + mathlib with the autonomous overnight routine. It separates **skeleton-
invariant** infrastructure from **problem-specific** content, and it provisions
dependencies from an artifact **you control** so cloud startup is fast and
reproducible — independent of upstream mathlib cache GC or GitHub clone scope.

## Why provisioning works this way

The routine runs in a restricted cloud environment where:

- **Upstream `git clone` of mathlib is blocked.** GitHub git goes through a
  scoped proxy that only permits repos in your auth scope; the network *domain*
  allowlist does not change this. (Source can still be fetched as a `codeload`
  tarball, which is plain HTTPS.)
- **The upstream olean cache is not durable for a pinned rev.** mathlib garbage-
  collects caches for old toolchain versions; a pinned project eventually gets
  `BlobNotFound` / 404 for every file.

So instead of depending on either, we **snapshot a known-good `.lake/packages`
(source + compiled oleans) once and publish it as a GitHub Release asset on this
repo**, which the setup script restores. The cloud environment caches the result
(filesystem snapshot), so subsequent sessions start warm with no download.

## Lifecycle

### 1. Bootstrap a problem's dependencies (rare; run locally / full network)

```bash
# optionally move to the latest stable mathlib first:
bash scripts/bootstrap_deps.sh --bump-latest
# or snapshot the currently pinned deps as-is:
bash scripts/bootstrap_deps.sh
```

This builds `.lake`, packs `.lake/packages` into `lake-packages-<ver>.tar.zst`,
uploads it as a Release asset (splitting if > 1.9 GB), and writes
`scripts/deps.lock` (toolchain, mathlib rev, release tag, sha256, part count).
Then commit the pin:

```bash
git add scripts/deps.lock lean-toolchain lakefile.toml lake-manifest.json
git commit -m "Pin deps <ver>" && git push
```

Requires `lake`, `zstd`, and an authenticated `gh`. Do **not** run it in the
routine environment — it needs a full build and outbound network.

**Pin policy:** chase latest at bootstrap (latest mathlib's cache is hot, so the
build is fast), then *freeze* for the life of the problem. A finished proof wants
reproducibility, not a moving dependency.

### 2. Per-session provisioning (automatic, cached)

`scripts/setup_env.sh` is the cloud environment's **setup script**. It installs
elan, then restores the pinned artifact named in `deps.lock` into
`.lake/packages` (falling back to the upstream Cloudflare cache only when no
artifact is pinned yet). It **fails loudly** if oleans do not materialize, so a
broken environment is never snapshotted as "warm". The result is cached, so it
runs about once a week, not per session.

`scripts/restore_deps.sh` is a repo-committed **SessionStart hook**
(`.claude/settings.json`) safety-net: if a session ever starts with
`.lake/packages` missing but the artifact still cached under `$HOME`, it
re-extracts it with no network. It is a strict no-op when deps are already
present (so it costs nothing locally).

### 3. Switch to a new conjecture

```bash
bash scripts/new_problem.sh my-conjecture     # archive current, lay down skeleton
$EDITOR ConjectureProof/Statement.lean        # state MainProp
bash scripts/freeze_statement.sh              # freeze the statement checksum
bash scripts/bootstrap_deps.sh --bump-latest  # build + publish deps (local)
```

`new_problem.sh` archives the current problem under `archive/<name>/`, then
resets `Statement`/`Lemmas`/`Main` and `blueprint/PROGRESS.md` from
`scripts/templates/`. The fresh `Main.lean` carries the single sanctioned
`sorry`, so the project builds at `[IN PROGRESS]`.

## What is invariant vs problem-specific

| Invariant (the skeleton)                         | Problem-specific (swapped each problem)        |
| ------------------------------------------------ | ---------------------------------------------- |
| `lakefile.toml`, `ConjectureProof.lean`          | `ConjectureProof/Statement.lean` (+ checksum)  |
| `scripts/*.sh`, `scripts/templates/`             | `ConjectureProof/Lemmas.lean`, `Main.lean`     |
| `.claude/settings.json`                          | `blueprint/PROGRESS.md`                         |
| `ConjectureProof/Audit.lean`                     | `scripts/deps.lock` (version pins + artifact)  |
| `CLAUDE.md`, `ROUTINE_PROMPT.md`, this file      | `lean-toolchain`, `lake-manifest.json`         |

## Renaming the `ConjectureProof` namespace (optional)

`ConjectureProof` is just the internal Lean library/namespace name; it does not
need to reflect the conjecture (its identity lives in `Statement.lean` and
`PROGRESS.md`). Renaming is therefore **not recommended per problem**. If you do
want `ConjectureProof` → `NewName`, change all of:

1. `lakefile.toml`: package `name`, `defaultTargets`, and the `[[lean_lib]]` `name`.
2. Rename the directory `ConjectureProof/` and the root module `ConjectureProof.lean`.
3. `namespace ConjectureProof` / `end ConjectureProof` in `Statement.lean`,
   `Lemmas.lean`, `Main.lean`, and `open ConjectureProof` in `Audit.lean`
   (and the same lines in `scripts/templates/`).
4. Every `import ConjectureProof.*` line.
5. `scripts/check_integrity.sh`: `SRC`, `STATEMENT`, `MAIN`, and the `Audit.lean` path.
6. `scripts/statement.sha256` path (regenerate with `scripts/freeze_statement.sh`).
7. Docs: `CLAUDE.md`, `README.md`, `ROUTINE_PROMPT.md`.
8. Re-run `lake build` (the library name changed).

## Network allowlist the routine environment needs

- `*.lean-lang.org` — elan toolchain downloads.
- `codeload.github.com`, `github.com`, `release-assets.githubusercontent.com`,
  `objects.githubusercontent.com` — release-asset restore (these are in the
  default **Trusted** list; if you use a **Custom** allowlist, keep "include
  defaults" checked).
- `mathlib4.lean-cache.cloud` — only needed for the upstream-cache fallback
  (i.e. before you have published your own artifact).
