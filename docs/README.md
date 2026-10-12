# API reference and normalization guide

[`FiberNormalization.md`](FiberNormalization.md) describes the **current** general
ring/arbitrary-function normalization contract and its kernel criteria. See the
[mathematical overview](../README.md) for the library's scope.

[`API.md`](API.md) is a **historical** native-display reference for 58 public
declarations in three production modules, with three private test/example modules,
analyzed at `74622e47c5bd8b98c1bc72a5bf2a768805fa52ed`. It retains displayed
signatures (including implicit arguments, abbreviations and noncomputable
modifiers) and the original project docstrings. In particular, it displays the
commutative normalization specialization, not the current general contract or its
kernel criteria. Its source-line anchors refer to that historical input layout and
need not identify the corresponding declaration lines in this checkout. This
snapshot is not an extraction or exact-input manifest for the current checkout. No
JavaScript, fonts, remote styles, source PDF, external documentation text or
interactive dependency website is shipped.

## Historical reproduction

The nine exact historical Lean/configuration input hashes, six native-record
hashes, 58-name inventory, analyzed revision and original generated-output SHA256
are in the **unchanged** [`api-manifest.json`](api-manifest.json);
`proof_certification: false`. Its output hash applies to the **original generated
API bytes**: 28,197 bytes, SHA256
`141e10522619aa70ce502261ac40bce834953e35fe37902b452108cfacebb065`.
The opening of `API.md` is a historical-scope presentation annotation; every byte
from its first `## Module` heading onward is the original extraction. The annotated
file does **not** match that original output hash, and the manifest does not bind
this checkout's current generalized sources.

The historical `frozenSource` input binding, displayed signatures and source
anchors belong to the original inputs in prior official release
`852dc998e56222e6c9fbba565e07cb9307614fd6`, not to the current normalization API.
For exact-input reproduction, use a **separate checkout of that original release**,
not this checkout:

```sh
git clone https://github.com/FormalFrontier/toric-ideals.git /path/to/toric-api-original
cd /path/to/toric-api-original
git checkout --detach 852dc998e56222e6c9fbba565e07cb9307614fd6
```

Run the commands below there, never run the unchanged historical generator with
current inputs or rehash them into the old manifest. For the historical input
layout, header-only normalization leaves the displayed signatures, docstrings and
source-line anchors unchanged; it does not provide a new native extraction or
describe the current general-ring/arbitrary-function API. Changes to their content
or locations are outside this snapshot.

At that exact original-release checkout, when the analyzed development commit is
present, its actual Git objects must match every source input. When that object is
absent in a parentless checkout, the freshly reproduced manifest must instead
equal that original checkout's committed manifest byte-for-byte: all nine
source/configuration hashes, six native-record
hashes, module/public inventories, tool revision and output hash. Every input must
also equal that release's own committed file. Present wrong objects, stale inputs,
altered native records and uncommitted manifests are refused. This binds inspected
inputs and output, not provenance or native execution; it does not promise the
development revision is available at GitHub.

Build native doc-gen4 at `97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its
committed dependency manifest and Lean `v4.34.0-rc2` in a separate checkout using
`lake build doc-gen4`. This core-only tool must not change this library's pins.
In the **original-release checkout**, fetch its matching mathlib cache, then build
all six modules as in that release's root README. Use fresh analysis/render
directories and a full immutable analyzed revision, not a moving branch. Repeat
`single` for each module in `scripts/generate_api.py`, with its corresponding source
path. Create the output directories first: the native SQLite opener does not
create them.

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
the Markdown's checkout-relative source links and anchors refer to the historical
source layout, not necessarily this checkout.

## Technical checks and attribution

The historical purpose-specific adapter requires six module records and exactly
the expected 58 names, native kinds and origins. Native metadata calls abbreviations
`def`; their displayed signatures retain `abbrev`. The exact display inventory is
four abbreviations, 13 noncomputable definitions, the predicate `Normal` and 40
theorems. Every header text token is retained, normalizing whitespace only. Module
documentation comes from the exact simple single module-comment block in each
historical source. Missing docstrings, malformed markup, unsafe/partial/incorrect
kinds, source/pin drift and invalid links are refused. The adapter is not a Lean
parser, native-output authenticator, proof checker or release certificate.

Atlas adapted the bounded renderer and its controls through other Formal
Frontier documentation adapters from Anchor's original ideal-completion recipe.
Collective credit and Apache-2.0 terms are preserved. The original library's
signatures and docstrings retain their attribution; Lean, mathlib and doc-gen4
are separately credited tools/dependencies, not copied documentation.
