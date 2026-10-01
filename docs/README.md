# Generated API reference

[`API.md`](API.md) is a **historical** native-display reference for all 58 public
declarations, three production modules and three private test/example modules,
analyzed at `74622e47c5bd8b98c1bc72a5bf2a768805fa52ed`. It retains displayed
signatures (including implicit arguments, abbreviations and noncomputable
modifiers) and the original project docstrings. Its checkout-relative links to
declarations still reach the same source lines: the five subsequently normalized
license/author headers kept their four-line length and every byte from `module`
onward. They **did** change five whole-file hashes; this historical snapshot is
not a fresh extraction or exact-input manifest for the current checkout. No
JavaScript, fonts, remote styles, source PDF, external documentation text or
interactive dependency website is shipped.

## Reproduction

The nine exact historical Lean/configuration input hashes, six native-record
hashes, 58-name inventory, analyzed revision and output SHA256 are in the
**unchanged** [`api-manifest.json`](api-manifest.json). The 28,197-byte API file's
SHA256 is `141e10522619aa70ce502261ac40bce834953e35fe37902b452108cfacebb065`;
`proof_certification: false`. For exact-input reproduction, use a **separate
checkout of the prior official release** (access to this currently private
repository is required), not a checkout with the normalized headers:

```sh
git clone https://github.com/FormalFrontier/toric-ideals.git /path/to/toric-api-original
cd /path/to/toric-api-original
git checkout --detach 852dc998e56222e6c9fbba565e07cb9307614fd6
```

Run the commands below there, never run the unchanged historical generator with
the changed-header current inputs or rehash them into the old manifest. Header
normalization leaves the displayed signatures, docstrings and source-line anchors
unchanged; it does not certify new native extraction. A later change to their
actual content or locations would need separately reviewed API documentation.

At the exact original P checkout, when the analyzed development commit is present,
its actual Git objects must match every source input. When that object is absent
in a parentless checkout, the freshly reproduced manifest must instead equal
that original checkout's committed manifest byte-for-byte: all nine
source/configuration hashes, six native-record
hashes, module/public inventories, tool revision and output hash. Every input must
also equal P's own committed file. Present wrong objects, stale inputs,
altered native records and uncommitted manifests are refused. This binds inspected
inputs and output, not provenance or native execution; it does not promise the
development revision is available at GitHub.

Build native doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its
committed dependency manifest and Lean `v4.34.0-rc2` in a separate checkout using
`lake build doc-gen4`. This core-only tool must not change this library's pins.
In the **original P checkout**, fetch its matching mathlib cache, then build all
six modules as in the root README. Use fresh analysis/render directories and a
full immutable analyzed revision, not a moving branch. Repeat `single` for each module in
`scripts/generate_api.py`, with its corresponding source path. Create the output
directories first: the native SQLite opener does not create them.

```sh
mkdir /tmp/toric-analysis /tmp/toric-render
lake env /path/to/doc-gen4 single --build /tmp/toric-analysis ToricIdeals.MonoidAlgebra.FiberNormalization api.db https://github.com/FormalFrontier/toric-ideals/blob/FULL_SOURCE_COMMIT/ToricIdeals/MonoidAlgebra/FiberNormalization.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/toric-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/toric-render --manifest /tmp/toric-render/manifest.json /tmp/toric-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/toric-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/toric-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

Only the Markdown reference and manifest are distributed, not intermediate HTML,
assets or dependency pages. Native source URIs identify the analyzed revision;
the distributed Markdown uses checkout-relative links.

## Checks and provenance

The purpose-specific adapter requires six module records and exactly the expected
58 names, native kinds and origins. Native metadata calls abbreviations `def`;
their displayed signatures retain `abbrev`. The exact display inventory is four
abbreviations, 13 noncomputable definitions, the predicate `Normal` and 40 theorems.
Every header text token is retained, normalizing whitespace only. Module
documentation comes from the exact simple
single module-comment block in each shipped source. Missing docstrings, malformed
markup, unsafe/partial/incorrect kinds, source/pin drift and invalid links are
refused. The adapter is not a Lean parser, native-output authenticator, proof
checker or release certificate. Native receipts and independent mathematical and
whole-artifact review remain required.

Atlas adapted the bounded renderer and its controls through other Formal
Frontier documentation adapters from Anchor's original ideal-completion recipe.
The adapter's lineage and original acceptance state are preserved in the private
development provenance; no approval of a predecessor transfers to a new artifact.
Collective credit and Apache-2.0 terms are preserved. Original library
signatures/docstrings retain their own provenance; Lean, mathlib and doc-gen4
are separately credited tools/dependencies, not copied documentation.
