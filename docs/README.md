# Generated API reference

[`API.md`](API.md) is the release-local reference for all 58 public declarations,
three production modules and three private test/example modules. It retains
native displayed signatures, including implicit arguments, abbreviation and
noncomputable modifiers, and the original project docstrings. Source links point
to files shipped in this checkout. No JavaScript, fonts, remote styles, source
PDF, external documentation text or interactive dependency website is shipped.

## Reproduction

The exact analyzed Lean/configuration inputs are identified by full revision and
SHA256 in [`api-manifest.json`](api-manifest.json). Final artifact review binds
the manifest and generated file to its own commit/tree. Later documentation-only
changes do not alter the mathematical inputs; source or pin changes require fresh
native generation and affected verification.

When the analyzed development commit is present, its actual Git objects must
match every source input. When that object is absent in a parentless checkout,
the freshly reproduced manifest must instead equal the release's committed
manifest byte-for-byte: all nine source/configuration hashes, six native-record
hashes, module/public inventories, tool revision and output hash. Every input must
also equal the release's own committed file. Present wrong objects, stale inputs,
altered native records and uncommitted manifests are refused. This binds inspected
inputs and output, not provenance or native execution; it does not promise the
development revision is available at GitHub.

Build native doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its
committed dependency manifest and Lean `v4.34.0-rc2` in a separate checkout using
`lake build doc-gen4`. This core-only tool must not change this library's pins.
Fetch this library's matching mathlib cache, then build all six modules as in the
root README. Use fresh analysis/render directories and a full immutable analyzed
revision, not a moving branch. Repeat `single` for each module in
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
Every header text token is retained,
normalizing whitespace only. Module documentation comes from the exact simple
single module-comment block in each shipped source. Missing docstrings, malformed
markup, unsafe/partial/incorrect kinds, source/pin drift and invalid links are
refused. The adapter is not a Lean parser, native-output authenticator, proof
checker or release certificate. Native receipts and independent mathematical and
whole-artifact review remain required.

Atlas adapted this bounded renderer and its controls from minimal-primes
`bed9ea5b7d022529b6b9ee1888c81c3f02683aa6` and integral-closure
`bbc5da98d729c8737c7cef0df2f80c6323584b2e`, ultimately from Anchor's original
Formal Frontier ideal-completion recipe
`f0c8c34386109116e4912fb425a8ad15d9dc42a4`. The minimal assembly was unaccepted
when reused; no approval transfers. Collective credit and Apache-2.0 terms are
preserved. Original library signatures/docstrings remain under the library's
provenance record. Lean, mathlib and doc-gen4 are separately credited tools and
dependencies; their implementation and documentation are not copied here.
