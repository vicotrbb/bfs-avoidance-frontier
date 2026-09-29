# Research artifact v1.1.0

The GitHub release distributes:

- `bfs-avoidance-frontier-v1.1.0.pdf`: the revised article.
- `bfs-avoidance-frontier-v1.1.0.tar.gz`: all versioned sources, data, b-files, certificates, verification scripts, and retained receipts.
- `RELEASE.json`: source commit, archive member hashes, and asset provenance.
- `VERIFICATION.log`: validation output from a fresh extraction.
- `SHA256SUMS`: detached checksums for the release assets.

GitHub's generated source archives also contain the versioned research files. The explicitly packaged archive adds a deterministic root directory and is verified by the publication workflow.

## Build and verify

```sh
make verify-python
make verify-lean
make recompute
make paper
make verify-publication
```

Prepare a package from the committed source:

```sh
python3 release/package.py
```

The command writes `release/dist/` and verifies that the worktree's tracked files match the committed source. It never publishes. Untracked local files, caches, `.DS_Store`, and `.git` are excluded. The package includes all tracked scientific artifacts and their executed validation receipts.

Extract the archive in a fresh directory, check its member digests against `RELEASE.json`, then run `make verify-python`, `make verify-lean`, and `make verify-publication`. Use `make recompute` to repeat the largest enumeration as well. The publication workflow records fresh-extraction results in `VERIFICATION.log` before generating the final detached checksums.

## Formal and computational scope

The article proves both structural results for arbitrary k. Lean verifies the general parent-sequence results and the binary inductive-tree results. Finite enumeration independently checks the retained counts and examples over the documented ranges. The arbitrary-k tree reconstruction is part of the paper's proof.

## Zenodo

The Zenodo record hosts the same article PDF, classified as a Preprint under CC BY 4.0, and links this versioned GitHub release. The archive uses the component licenses in `LICENSES.md`. Publication provenance records the public record URL, assigned DOI, observed DOI resolution status, and matching PDF checksum after publication.
