# Where the PlaneMap work lives

Date: 3 October 2026

There are two repositories. They are not a fork of each other.

| Place | What it is |
| --- | --- |
| This folder, `/Users/fulkanjou/mathlib4-planemap` | The working copy. A shallow clone of public Mathlib, plus your PlaneMap commit. Lean builds here. |
| https://github.com/kylemath/mathlib4-planemap | The public backup. Only your PlaneMap files. No Mathlib history. |

## This folder

`origin` is `https://github.com/leanprover-community/mathlib4.git`. Your GitHub account cannot push there. `git push` with no arguments uses `origin`, so it returns a 403.

The clone is shallow. `.git/shallow` stops the history at one Mathlib commit, so this folder also cannot be pushed as a new Mathlib repository. GitHub rejects that push with `did not receive expected object`.

A remote named `mine` points at the backup URL. Pushing `master` to `mine` from this folder fails for the same shallow-history reason, and the backup now has a different first commit. Leave `mine` unused.

Local history that matters:

- Mathlib base: `300d0e535721bc098547106fc297d8ba2a63f6bb`
- Your commit on top: `5efe00e` (`updates`)

That commit is already copied to the backup as `970b2fc`.

## Daily work

Edit and build in this folder. Record commits here:

```bash
git add -A
git commit -m "what changed"
```

Stop there. The commit is safe on this machine. It is not on GitHub yet.

## Putting a new commit on GitHub

Do this once:

```bash
git clone https://github.com/kylemath/mathlib4-planemap.git ~/mathlib4-planemap-backup
```

After each new commit in this folder, send that one commit to the backup and push:

```bash
git format-patch -1 --stdout | git -C ~/mathlib4-planemap-backup am
git -C ~/mathlib4-planemap-backup push
```

`git format-patch -1` means the latest commit in this folder. If you made several, run those two lines once per commit, oldest first. Skip `5efe00e`. It is already on GitHub.

The patch applies when the commit only touches the PlaneMap files. A commit that also edits other Mathlib files will not apply cleanly in the backup, because those files are not in that repository.

## Restoring onto a fresh Mathlib checkout

```bash
git clone --depth 1 --branch master https://github.com/leanprover-community/mathlib4.git
cd mathlib4
git fetch --depth 1 origin 300d0e535721bc098547106fc297d8ba2a63f6bb
git checkout 300d0e535721bc098547106fc297d8ba2a63f6bb
git clone --depth 1 https://github.com/kylemath/mathlib4-planemap.git /tmp/planemap-files
cp -R /tmp/planemap-files/Mathlib /tmp/planemap-files/MathlibTest /tmp/planemap-files/PlaneMapAudit.md /tmp/planemap-files/PlaneMapFiveColorStatus.md .
```

Copy this workflow note across as well if you want it in that checkout. It is not in the `5efe00e` backup until you commit it here and run the publish step above.
