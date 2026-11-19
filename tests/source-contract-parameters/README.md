# Source parameter gate fixtures

These are local source-contract checks. Passing them does not authenticate either
Split return or certify the original source.

Load `Parameter_Export.thy` with the resident Isabelle session and the repository's
normal theory directories. The theory checks its theorem dependencies for skipped
proofs and oracles, writes a kernel receipt, and generates
`target/source-contract-development/Parameter_Check.ML`. Do not edit that export.

From the CeTA repository, run the generated predicates against each freshly
extracted family:

```sh
OBSERVER_XML_DIRECTORY=../ferrum-prolog-release/target/source-contract-development/original /work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script tests/source-contract-parameters/Check.ML
OBSERVER_XML_DIRECTORY=../ferrum-prolog-release/target/source-contract-development/renamed /work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script tests/source-contract-parameters/Check.ML
```

The fixtures check parameter initialization from raw or contextual groundness,
positive-branch coordinate transport, and restricted replacement syntax. Missing
context, missing branch freeness, wrong coordinates and wrong replacement
parameters must be rejected. Supplying `[selected]` tests the conditional binding
rule only: it does not authenticate that premise for the family. The branch
semantics and opaque-guard counterexample are checked in Isabelle.

Native extraction must select `PROLOG_CONTEXT_CONSTRUCTION=historical` to retain
the intended graph. Default ordered construction produces a different graph;
its diagnostic failure is retained in the development evidence. The extraction
commands and hashes are recorded in the evidence manifest.

For head successor transport, load `Successor_Export.thy`, then run
`Check_Successors.ML` with the same Poly/ML command and each XML directory above.
The generated module and kernel receipt are in `target/source-head-successors`.
Each variant must pass 68 assertions (24 positive, 44 rejection controls).
These check clause-coordinate transport and fresh body-only output syntax for
eight actual rows. They do not prove the full runtime invariant or either Split.

For the conditioned matching-node contract, load `Matching_Export.thy` and run
`Check_Matching.ML` against each retained XML directory. The export and kernel
receipt reside in `target/source-conditioned-matching`. The kernel checks the
full conditional node contract; executable fixtures validate its matching,
coordinate and caller-coverage premises. Complete successor conditions and the
source-family invariant remain proof obligations.

The matching suite passes 42 assertions per variant (17 positive, 25 rejection
controls), including synthetic positive/negative caller-slot coverage examples.

For the repeated-parameter copy-node contract, load `Copy_Node_Export.thy` and
run `Check_Copy_Node.ML` against each retained XML directory. The export and
kernel receipt are in `target/source-copy-node`. The full conditional node rule
is kernel checked; fixtures validate actual rows 0:22 and 35:2 and their
head/coordinate syntax. Proper-spine, free-output, parameter-relation and complete
successor conditions remain source-family proof obligations.

The copy-node suite passes 24 assertions per variant: 9 positives and 15 rejection
controls, including synthetic caller-slot examples.

For the recursive cons-node contract, load `Cons_Node_Export.thy` and run
`Check_Cons_Node.ML` against each retained XML directory. The export and kernel
receipt are in `target/source-cons-node`. Fixtures check rows 0:23 and 35:3,
linear cons-head shape, arity, tail/parameter coordinates and fresh body-output
maps. Incoming runtime facts and complete successor conditions remain explicit
source-family obligations; proper spine length alone does not prove finiteness.

The cons-node suite passes 32 assertions per variant: 11 positives and 21 rejection
controls. Its head-shape adapter is local test code, not production discovery.

For the recursive-entry fragment, load `Recursive_Entry_Export.thy` and run
`Check_Recursive_Entry.ML` against each retained XML directory. The export and
kernel receipt reside in `target/source-recursive-entry`. Each variant passes
28 assertions (10 positive, 18 rejection controls) on edges 0:23 → 0:27 and
35:3 → 35:7. Three separate kernel examples check permitted caller sharing and
reject aliased outputs and a helper output in the input. Runtime incoming facts
remain premises; module-boundary transfer and actual returns remain open.

For recursive-entry link transport, load `Recursive_Entry_Link_Export.thy`, run
`python3 tests/source-contract-parameters/audit_recursive_boundaries.py`, then
run `Check_Recursive_Entry_Link.ML` using the same Poly/ML command with
`BOUNDARY_FIXTURES=target/source-recursive-entry-link/original.fixtures` and again
with `renamed.fixtures`. Each variant must pass 34 assertions (6 positive,
28 rejection controls). The audit uses retained native diagnostic maps, not
production proof search. These coordinate tests do not discharge checked-link,
Split-boundary, caller-context or actual-return premises. Removing identity maps
is allowed; removing necessary nonidentity maps must fail.

For the shared-caller obstruction, load `Shared_Caller_Obstruction.thy` and run
`swipl -q -s tests/source-contract-parameters/Check_Shared_Caller.pl` from this
checkout. The theory checks four structural facts; the Prolog fixture executes
the original source with 11 assertions. Evidence is retained in
`target/source-shared-caller-obstruction`. This is a counterexample to inferred
continuation freeness, not to termination or copied-or-scalar parameter returns.

For the local ground-caller repair, load `Ground_Caller_Test.thy` and run
`swipl -q -s tests/source-contract-parameters/Check_Ground_Caller.pl` from this
checkout. Five rules and four kernel fixture facts are checked; the original
source passes ten Prolog assertions. Receipts are in `target/source-ground-caller`.
The checks cover the wider caller mode and ground-output resolution, not full
observer-node, saved-alternative, Split or source certification.

For the integrated free-or-ground copy node, load `Caller_Copy_Node_Export.thy`,
then run `Check_Caller_Copy_Node.ML` with each retained `OBSERVER_XML_DIRECTORY`.
Run `swipl -q -s tests/source-contract-parameters/Check_Caller_Copy_Node.pl` for
original-source success, failure, cut and saved-alternative controls. Artifacts
are in `target/source-caller-copy-node`. The theorem is a complete conditional
node contract; actual family entry/successor facts and both Splits remain open.

For recursive caller-mode successor integration, load `Recursive_Caller_Export.thy`
and run `Check_Recursive_Caller.ML` against both retained XML directories.
Run `swipl -q -s tests/source-contract-parameters/Check_Recursive_Caller.pl` for
original-source recursive-clause controls. Artifacts reside in
`target/source-recursive-caller`. The widened entry fragment is discharged in
the conditional cons-node successor rule; actual incoming facts, complete
successor conditions, boundaries and returns remain open.

For Split-prefix caller initialization, load `Split_Prefix_Entry_Export.thy`,
run `python3 tests/source-contract-parameters/audit_split_prefix_entry.py`, then
run `Check_Split_Prefix_Entry.ML` with `PREFIX_FIXTURES` pointing to each
`target/source-split-prefix-entry/{original,renamed}.fixtures` file. Each variant
must pass 30 assertions (6 positive, 24 rejection controls). The theorem proves
singleton attached-caller invariant initialization, not helper-step preservation,
full boundary reconstruction or actual returns. The shorter Split 44 payload
does not contain the incoming parameter.

For acquired extraction caller protection, load `Acquired_Univ_Caller_Export.thy`
and run `Check_Acquired_Univ_Caller.ML` with both retained XML directories.
Run `swipl -q -s tests/source-contract-parameters/Check_Acquired_Univ_Caller.pl`
for source sharing and freshness controls. Evidence resides in
`target/source-acquired-univ-caller`. The rule derives protection of live caller
values and preserves their leaf invariant through actual constructor extraction;
full finite/mode preservation, normalized block simulation and returns remain open.

### Acquired normalized equality connection

Load `Acquired_Univ_Normalized_Check.thy` in the resident Isabelle session to
check conditional finite/leaf preservation and write the kernel receipt. Run
`swipl -q -s tests/source-contract-parameters/Check_Acquired_Univ_Normalized.pl`
from the CeTA root for eight executable analogue controls. Artifacts are in
`target/source-acquired-univ-normalized`; evidence is recorded in
`docs/data/source-acquired-univ-normalized-20261119.json`. Entry finiteness,
block exits, both actual returns and recursive family assembly remain open.

### Acquired entry finiteness

Load `Acquired_Univ_Entry_Check.thy` for the kernel receipt, then run
`swipl -q -s tests/source-contract-parameters/Check_Acquired_Univ_Entry.pl`
from CeTA for eight semantic controls. The new rule derives normalized entry
finiteness from matching resolution and the exact continuation, retaining finite
saved alternatives. Actual block-coordinate assembly and exits remain open.
Evidence: `docs/data/source-acquired-univ-entry-20261119.json`.

### Acquired block row simulation gate

Load `Acquired_Block_Rows_Export.thy`, then run `Check_Acquired_Block_Rows.ML`
with `OBSERVER_XML_DIRECTORY` set to either retained original or renamed XML
folder. The generated checker validates the full observer equality rows 10/13
and univ/exit row 6 in modules 0/47. Each variant has 32 assertions (6 positive,
26 negative). This supplies local conditional simulation receipts; runtime
initialization, restricted caller composition and helper returns remain open.
Evidence: `docs/data/source-acquired-block-rows-20261119.json`.

### Acquisition normalization witness

Load `Acquired_Univ_Witness_Check.thy` for the kernel receipt. Run
`Check_Acquired_Univ_Witness.ML` with each retained `OBSERVER_XML_DIRECTORY`
for 16 coordinate assertions per variant (10 positive, 6 negative), reusing
the pinned acquired-caller export. The new theorem derives source freeness and
pair separation, then obtains the conditional common normalization valuation.
Restricted caller composition and both returns remain open. Evidence:
`docs/data/source-acquired-univ-witness-20261119.json`.

### Synchronized normalized product

Load `Normalized_Univ_Product_Check.thy` to check the conditional joint product
and three kernel controls. Run `swipl -q -s
tests/source-contract-parameters/Check_Normalized_Univ_Product.pl` from CeTA
for six sharing controls. The product keeps restricted caller preservation and
helper simulation on one execution; acquired-entry instantiation and both
returns remain open. Evidence:
`docs/data/source-normalized-univ-product-20261119.json`.

### Acquired joint caller entry

Load `Acquired_Univ_Product_Check.thy` for the product, projection controls and
saved-finiteness guard receipt. Run
`swipl -q -s tests/source-contract-parameters/Check_Acquired_Univ_Product.pl`
from CeTA for eight original-source sharing controls. Caller entry finiteness,
leaf preservation and fresh-output protection are derived from acquisition;
initial helper representation and global coverage remain premises. Evidence:
`docs/data/source-acquired-univ-product-20261119.json`.

### Acquired normalization witness/product

Load `Acquired_Witness_Product_Check.thy` for the composed theorem and three
interface controls. Replay `Check_Acquired_Block_Rows.ML` with each retained
source directory to check the 32 row assertions per variant. The theorem derives
initial helper representation and composes the normalization edge with the
product path; actual source correspondence and global coverage remain premises.
Evidence: `docs/data/source-acquired-witness-product-20261119.json`.

### Checked acquisition-link correspondence

Load `Acquired_Univ_Link_Check.thy` for the kernel receipt. Run
`Check_Acquired_Univ_Link.ML` with original and renamed XML directories for 10
assertions each (2 positive, 8 negative). The theorem derives all target entry
identities from the checked complete-state link; actual source-resolution
identity and block instantiation remain open. Evidence:
`docs/data/source-acquired-univ-link-20261119.json`.

### Actual acquired resolution

Load `Acquired_Univ_Resolution_Check.thy` for the actual-step identity receipt.
Retained regressions: `Check_Acquired_Univ_Link.ML` with both XML variants (10
assertions each), and `Check_Acquired_Univ_Product.pl` (eight source controls).
The theorem derives the actual MGU, successor evaluation and old saved state;
common-witness link/product assembly remains open. Evidence:
`docs/data/source-acquired-univ-resolution-20261119.json`.

### Resolution-link context discharge

Load `Acquired_Resolution_Link_Check.thy` for the same-unifier link theorem and
four namespace controls. Retained executable regression:
`Check_Acquired_Univ_Link.ML` under both XML variants (10 assertions each).
Source-row component extraction and joint block instantiation remain open.
Evidence: `docs/data/source-acquired-resolution-link-20261119.json`.

### Full checked acquired-row witness

Load `Actual_Acquired_Row_Check.thy` for the theorem receipt. Replay retained
`Check_Acquired_Univ_Caller.ML` on both XML variants (34 assertions each).
Full-row checking and the actual step now provide one MGU and target valuation;
joint caller/extraction-block assembly remains open. Evidence:
`docs/data/source-actual-acquired-row-20261119.json`.

### Attached/helper common MGU

Load `Acquired_Joint_MGU_Check.thy` for the common-witness theorem and positive/
negative projection controls. The negative demonstrates why a helper-only MGU
cannot be lifted to a caller-attached MGU without proof. Retained executable
regression: `Check_Normalized_Univ_Product.pl` (six sharing controls).
Evidence: `docs/data/source-acquired-joint-mgu-20261119.json`.


Attached acquired row (2026-11-19): load `Attached_Acquired_Row_Check.thy` in
the resident Isabelle session. It checks the actual attached MGU to checked-row
composition and positive/negative MGU controls. Run
`swipl -q -s tests/source-contract-parameters/Check_Normalized_Univ_Product.pl`
for six retained sharing analogues. Evidence is in
`docs/data/source-attached-acquired-row-20261119.json`. M1 remains open.


Actual attached univ product: load `Actual_Univ_Product_Check.thy`.
The receipt and fresh retained control logs are in
`target/source-actual-univ-product`; the manifest records remaining premises.


Load `Actual_Witness_Product_Check.thy` to check the actual witness product and
strengthened attached row. Fresh original/renamed block-row controls and kernel
receipt: `target/source-actual-witness-product`. See its manifest for scope.


Joint witness product: load `Joint_Witness_Product_Check.thy`; run
`swipl -q -s tests/source-contract-parameters/Check_Joint_Witness_Product.pl`.
Receipt and five control results: `target/source-joint-witness-product`.


Checked acquisition block: load `Checked_Acquired_Block_Check.thy`. Fresh
original/renamed block-row controls and builtin controls are recorded in
`target/source-checked-acquired-block`; see its manifest for remaining premises.


Partial caller review: load `Partial_Caller_Obstruction.thy` and run
`swipl -q -s tests/source-contract-parameters/Check_Partial_Caller_Obstruction.pl`.
This is an expected negative invariant control with a successful original-source
query; it does not certify the proposed subterm-closure repair.


Parameter subterm repair: load `Parameter_Subterms_Check.thy`; positive admission
and negative variable/oversized controls are kernel checked. Receipt and retained
source controls: `target/source-parameter-subterms`. Actual image coverage remains open.


Ground output images: load `Ground_Output_Images_Check.thy`. It checks actual
copy-head output images and caller values whose variable support is covered by
the output, plus repeated-variable positive/negative controls. Evidence is in
`target/source-ground-output-images`; outside-output MGU transport remains open.


Attached partial copy: load `Attached_Partial_Copy_Check.thy`, and run
`swipl -q -s tests/source-contract-parameters/Check_Attached_Partial_Copy.pl`.
Receipt and seven source controls: `target/source-attached-partial-copy`.


Partial copy node: load `Partial_Copy_Node_Check.thy`. Original/renamed
copy-coordinate fixtures and 17 source controls are in
`target/source-partial-copy-node`. Node successor initialization remains explicit.


Partial-copy coordinates: load `Partial_Copy_Coordinates_Check.thy`. Receipt,
original/renamed coordinate controls and source controls are in
`target/source-partial-copy-coordinates`; full successor initialization remains open.


### M1: recursive entry with arbitrary finite caller output (2026-11-19)

`lpp_checked_recursive_partial_entry` derives the tracked parameter, proper
finite tail, finite caller output and fresh separated helper output from the
actual cons-head MGU and checked coordinates. It removes the old free-or-ground
caller-output restriction. `lpp_observer_recursive_partial_node_contract`
integrates these facts with the subterm replacement invariant; successor and
failure initialization remain explicit. `lpp_split_prefix_partial_initial`
constructs the caller/tail observer invariant at the checked prefix payload.
This establishes prefix entry, not preservation through a successful helper.

Isabelle checked all three results without skipped proofs or oracles. Original
and renamed structural fixtures passed 28 checks each; nine source controls
passed, covering partial compound outputs, freshness, tail routing, parameter
copying, repeated-output mismatch and rollback. The structural fixtures reuse
the existing coordinate checker; they do not certify the new whole family.

Broad obligation 1 remains incomplete: whole-family initialization, remaining
node preservation and return-time spine preservation are open. Obligation 2
still needs complete source-path and boundary coverage. Neither actual helper
return (obligation 3) nor recursive family discharge (obligation 4) is proved.
The next assembly task is to connect the actual cons successor and checked
prefix payload without an externally supplied entry invariant. Production code
and generated checking logic are unchanged; no production replay is claimed.
Evidence: CeTA `docs/data/source-recursive-partial-entry-20261119.json`.


### M1: cons-to-prefix invariant composition (2026-11-19)

`lpp_recursive_partial_prefix_initial` composes the actual cons-head MGU entry
proof with the checked prefix payload initializer. A recursive-entry invariant
is no longer a premise: incoming finite call, proper spine, tracked parameter,
and both coordinate checks establish it. Isabelle checked the composition and
its dependency closure without skipped proofs or oracles. Existing positive and
negative coordinate/source controls are retained in the predecessor manifest;
no new production or source execution is claimed for this composition.

This proves initialization of the displayed prefix runtime, not correspondence
of every source boundary with that runtime or preservation through a helper
return. Full source-state shape/transport integration, remaining node invariants,
whole-family initialization and return-time spine preservation remain open.
All four broad obligations remain incomplete. Evidence: CeTA
`docs/data/source-recursive-partial-prefix-20261119.json`.


### M1: widened recursive entry through observer links (2026-11-19)

`lpp_checked_recursive_partial_entry_transport` preserves the arbitrary-finite-
output entry fragment under the existing five-coordinate check.
`lpp_stable_functor_link_with_recursive_partial_entry` carries it in the same
valuation as the checked target representation, context and residual edge.
`lpp_stable_functor_link_with_partial_prefix` initializes the prefix invariant in
that valuation. Isabelle checked all three without skipped proofs or oracles.
The existing coordinate harness passed 34 checks per original/renamed variant,
including wrong coordinates, helper aliasing, growing tails and missing bindings.
These are coordinate controls, not acceptance of an actual Split boundary.

The checked-link, incoming entry and source-context premises remain explicit;
full boundary reconstruction and correspondence with the displayed prefix
runtime are not discharged. Whole-family initialization, remaining invariant
preservation and both actual helper returns remain open. All four broad
obligations remain incomplete. Production code is unchanged. Evidence: CeTA
`docs/data/source-recursive-partial-link-20261119.json`.


### M1: finite (o,i,o) observational initialization (2026-11-19)

`lpp_partial_query_initial` derives an initial finite ground parameter template,
its tracked-parameter relation, structural observations for both arbitrary finite
arguments, and the subterm observer invariant for the displayed initial call.
It assumes neither integer-valued parameters nor free/ground output mode nor
variable separation between input and output. The caller-coordinate equalities
remain explicit. Isabelle checked the theorem without skipped proofs or oracles.

This is the observational initialization fragment only. Membership in the actual
source observer family, original query admission, node conditions, and complete
preservation are not proved. It does not discharge either helper return or any
recursive family premise. All four broad obligations remain incomplete. No
production changes or new execution campaign are included. Evidence: CeTA
`docs/data/source-partial-query-initial-20261119.json`.


### M1: parameter equality under the subterm invariant (2026-11-19)

The runtime parameter equality contract and its conditioned node contract now
have subterm-invariant counterparts. Checked marker/copy/scalar replacements
remain in the original replacement set; inclusion into the widened set and its
groundness establish preservation of the enlarged caller invariant. This removes
the mismatch between equality nodes and the arbitrary-output copy/cons nodes.
The source selected-free fact, tracked parameter, coordinate coverage,
success/failure initialization and strict-descent lower contracts remain explicit.

Isabelle checked all three new contracts and the existing four accepted binding
forms/five rejection controls without skipped proofs or oracles. These controls
exercise the existing binding checker; no new executable checker is introduced.
Actual source-row assembly, arithmetic integration, original query-to-family
representation and full preservation are still open. Neither helper return nor
recursive family assembly is discharged. All four broad obligations remain
incomplete; production code is unchanged. Evidence: CeTA
`docs/data/source-subterm-equality-20261119.json`.


### M1: attached arithmetic with subterm replacements (2026-11-19)

`LP_Prolog_Attached_Subterm_Arithmetic` proves that actual arithmetic steps
preserve the widened leaf-stack invariant, including attached continuations and
saved alternatives. A successful source builtin also establishes the tracked
scalar parameter relation. Groundness of the original parameter is explicit;
integer-valued inputs are not assumed. Failure/error behavior is retained.
Isabelle checked the four results without skipped proofs or oracles. Five SWI
source controls passed: scalar success, caller sharing, compound-output rejection,
rollback and noninteger-parameter error. These executable checks are source
examples, not proofs of equivalence with the formal arithmetic profile.

The result covers leaf preservation, not the complete observer invariant:
finiteness, checked node integration, source-row coverage and full query/family
initialization remain open. Both actual helper returns and recursive assembly
remain unproved. All four broad obligations remain incomplete; production code
is unchanged. Evidence: CeTA `docs/data/source-subterm-arithmetic-20261119.json`.


### M1: arithmetic finite execution and leaf preservation (2026-11-19)

`lpp_actual_is_finite_step` and `lpp_attached_is_finite_step` preserve finite
execution for the actual arithmetic domain transition and attached continuation.
`lpp_attached_is_subterm_invariants` combines this with widened leaf-stack
preservation on the same result state. Failure and error outcomes remain covered;
no successful evaluation or integer input is assumed for the step theorem.
Isabelle checked all three without skipped proofs or oracles. The five retained
arithmetic source controls passed again. Documentation validation passed.

Checked observer-successor representation and node conditions remain to be
integrated. This result does not establish whole-family preservation, query
admission, actual helper returns or recursive assembly. All four broad
obligations remain incomplete. Production code is unchanged. Evidence: CeTA
`docs/data/source-arithmetic-finite-20261119.json`.


### M1: full invariant in checked arithmetic normalization (2026-11-19)

`lpp_checked_attached_is_invariant_contract` carries both finite execution and
caller leaf observations to the checked intermediate equality state, in the
valuation supplying target representation, source facts and strict residual
descent. The arithmetic-domain premise is derived from the incoming invariant.
The replacement set is generic, so the widened subterm invariant is admitted.
No substitution is applied to caller observations until the equality executes.

Isabelle checked the contract without skipped proofs or oracles; five retained
arithmetic source controls passed. Actual row instantiation, target node-condition
initialization and canonical node packaging remain open. The lower answer
contract is still an explicit strict-descent obligation. Whole-family preservation,
query-to-family initialization, both helper returns and recursive discharge are
not established. All four broad obligations remain incomplete. Production code
is unchanged. Evidence: CeTA `docs/data/source-arithmetic-observer-20261119.json`.


### M1: conditioned arithmetic module child (2026-11-19)

`lpp_checked_conditioned_is_invariant_contract` derives target table bounds from
the checked arithmetic link and packages the intermediate equality state as a
premised module child with the full observer invariant. The lower answer contract
receives this representation and strict residual descent. Target node-condition
initialization remains an explicit premise; it is not inferred from representation.
Isabelle checked the result without skipped proofs or oracles. Five retained
arithmetic source controls passed again; they do not establish module assembly.

Canonical node packaging, actual row instantiation, query/family initialization
and whole-family preservation remain open. Neither helper-return contract nor
recursive family discharge is established. All four broad obligations remain
incomplete. Production code is unchanged. Evidence: CeTA
`docs/data/source-conditioned-arithmetic-20261119.json`.


### M1: canonical arithmetic observer node (2026-11-19)

`lpp_observer_arithmetic_node_contract` packages checked arithmetic normalization
as a canonical observer node with the full leaf/finite-execution invariant.
It restores scope handling and lifts a represented child's answer contract along
the strict residual path using `lp_answer_contract_start`. The actual source
shape and target node-condition initializer remain explicit; recursive lower
contracts are used only under strict descent.

Isabelle checked the node theorem and dependencies without skipped proofs or
oracles. Five retained arithmetic source controls passed. This closes arithmetic
node packaging, not source-row instantiation or target-condition discharge.
Whole-family initialization/preservation, actual helper returns and recursive
assembly remain open. All four broad obligations remain incomplete. Production
code is unchanged. Evidence: CeTA `docs/data/source-arithmetic-node-20261119.json`.


### M1: arithmetic target scalar coordinate (2026-11-19)

Inspection of retained original/renamed tables identifies arithmetic rows 0:15
and 47:15, both targeting row 19. Their equality target has output V0 and scalar
V1; the checked-link binding maps V1 to the fresh result variable.
`lpp_arithmetic_target_parameter` derives the output value, scalar value and
tracked-parameter fact from the represented equality shape and the original
parameter's groundness. Isabelle checked it without skipped proofs or oracles.
The structural audit records four target mappings and hashes its input XML.
It does not validate a complete checked link or authenticate a boundary.

This identifies and proves the scalar-coordinate fragment of target initialization.
It has not yet been wired into the canonical node initializer; remaining target
conditions, original parameter transport through V2, actual source-row assembly,
whole-family preservation and query admission remain open. Neither helper return
nor recursive assembly is discharged. All four broad obligations remain incomplete.
Evidence: CeTA `docs/data/source-arithmetic-target-20261119.json`.


### M1: scalar facts integrated into arithmetic node (2026-11-19)

`lpp_observer_arithmetic_parameter_node_contract` derives the output/scalar
coordinate values and tracked scalar fact from the represented target equality,
then supplies them to target initialization. The target shape and original
parameter groundness remain explicit. `lpp_arithmetic_target_payload_parameter`
separately derives preservation of the incoming tracked parameter through a
checked payload coordinate. The retained targets use payload index 1 / V2;
this payload lemma is not yet integrated into the node initializer.

Isabelle checked both results without skipped proofs or oracles. A structural
audit confirms the three separate coordinates in four original/renamed target
mappings; it does not authenticate actual boundaries. Remaining target conditions,
source-row instantiation, query/family initialization and whole-family preservation
remain open. Both helper returns and recursive assembly remain unproved. All four
broad obligations remain incomplete. Evidence: CeTA
`docs/data/source-arithmetic-parameter-node-20261119.json`.


### M1: incoming payload parameter integrated into arithmetic node (2026-11-19)

`lpp_observer_arithmetic_payload_node_contract` derives the incoming parameter's
tracked relation through the represented source payload and explicit source/target
payload coordinates. It supplies that fact together with the derived scalar fact
to the target initializer. Original incoming tracking and both payload coordinates
remain premises; arbitrary target conditions are not silently discharged.

Isabelle checked the node and dependency closure without skipped proofs or
oracles. Five source controls and the four retained structural target mappings
passed again. Actual checked-row instantiation, other target conditions,
query/family initialization and whole-family preservation remain open. Neither
helper return nor recursive assembly is proved. All four broad obligations remain
incomplete. Production code is unchanged. Evidence: CeTA
`docs/data/source-arithmetic-payload-node-20261119.json`.


### M1: actual arithmetic static row premises checked (2026-11-19)

The existing Isabelle-generated source-action checker accepts arithmetic rows
0:15 and 47:15 against the retained original and renamed tables. The fixture
checks source output, scalar-result and parameter-payload coordinates and rejects
wrong scalar values, missing scalar bindings, parameter aliasing and nonfresh
result variables. Each variant passed 16 checks. The generated checker was reused
unchanged; this is a development fixture, not native source discovery or replay.

This validates static premises for arithmetic-node instantiation. Incoming runtime
parameter facts, remaining target node conditions, boundary assembly and complete
family coverage are still unproved. No actual helper return or recursive family
premise is discharged. All four broad obligations remain incomplete. Evidence:
CeTA `docs/data/source-arithmetic-rows-20261119.json`.


### M1: ground equality for partial output patterns (2026-11-19)

The arithmetic return boundary selects an arbitrary finite output, so a
free-selected-variable equality rule is insufficient. The new
`lpp_subterm_ground_equality_images` derives restricted images from the actual
MGU when the replacement set covers subterms of the selected ground value.
`lpp_parameter_subterm_equality_leaf` instantiates this for the widened parameter
set. Finite selected output, finite continuation and caller-variable coverage
remain explicit. No free/ground output-mode assumption is introduced.

Isabelle checked both results without skipped proofs or oracles. Five direct
equality controls and seven retained partial-output source controls passed,
covering sharing, repeated-pattern mismatch, compound/scalar mismatch and rollback.
These are executable examples, not source-boundary certification. Integration into
the actual equality node and whole-family preservation remain open. Both helper
returns and recursive assembly remain unproved; all four broad obligations are
incomplete. Evidence: CeTA `docs/data/source-subterm-ground-equality-20261119.json`.


### M1: arbitrary finite output equality integrated through node (2026-11-19)

Restricted subterm images now lift through actual attached equality and saved
alternatives (`LP_Prolog_Attached_Subterm_Equality`), the conditioned observer
answer contract (`LP_Prolog_Observer_Conditioned_Subterm_Equality`), and the
canonical parameter-equality node (`LP_Prolog_Partial_Parameter_Equality_Node`).
The node no longer assumes the selected runtime output is free. Its full incoming
invariant supplies finiteness; allowed ground replacements, tracked parameter,
caller coverage and success/failure successor conditions remain explicit. Lower
answer contracts require strict residual descent.

Isabelle checked the complete dependency chain without skipped proofs or oracles.
Five direct equality controls and seven retained partial-output source controls
passed. Actual source-boundary instantiation, remaining node conditions,
query/family initialization and whole-family preservation remain open. Neither
helper return nor recursive assembly is authenticated. All four broad obligations
remain incomplete. Production code unchanged. Evidence: CeTA
`docs/data/source-partial-equality-node-20261119.json`.


### M1: actual partial-output equality row checked (2026-11-19)

The retained equality row 19:0 passes the unchanged Isabelle-generated source
checker in both original and renamed tables. Seven checks per variant cover the
actual source action, both returned coordinates, the empty free-variable table,
and rejection of wrong/missing return bindings and swapped success/failure links.
This confirms that the partial-output node rule addresses an actual row whose
selected output has no static freeness evidence. Both success payload coordinates
select the tracked right-hand value.

The executable checks validate static premises only. Dynamic incoming tracking,
successor initialization, return-contract coverage and family invariant assembly
remain open. No actual helper return or recursive premise is discharged. All four
broad obligations remain incomplete. Production code and generated checking logic
are unchanged. Evidence: CeTA `docs/data/source-partial-equality-row-20261119.json`.


### M1: equality successor tracked-value integration (2026-11-19)

`lpp_partial_equality_successor_values` derives the refreshed successor value
from the actual successful equality MGU: it equals the ground right-hand value,
equals the substituted selected output, and preserves parameter tracking.
`lpp_observer_partial_equality_successor_node_contract` feeds the derived equality
and tracking facts into successor initialization, with no free-output premise.
The arithmetic boundary's variable right-hand side and checked refresh coordinate
are explicit; other successor conditions and failure initialization remain open.

Isabelle checked both theorems and a positive/negative fixture for the retained
3/6-prefix V1-to-V0 return coordinate without skipped proofs or oracles. This
advances local preservation, not complete return-contract authentication.
Whole-family initialization/coverage, helper returns and recursive assembly remain
open; all four broad obligations remain incomplete. Production code unchanged.
Evidence: CeTA `docs/data/source-partial-equality-successor-20261119.json`.


### M1: actual-answer spine from partial recursive entry (2026-11-19)

`lpp_partial_prefix_actual_return_spine` derives initialization of the existing
actual-answer spine theorem from the widened recursive entry and checked prefix
coordinates. Every actual answer of the displayed single-frame prefix retains
the exact initial tail length. It requires an actual answer and does not prove
helper termination, returned-element finiteness or leaf effects. Saved alternatives
created by execution are handled by the existing semantic theorem; externally
supplied initial alternatives are outside this single-frame statement.

Isabelle checked the result without skipped proofs or oracles. Five source
controls passed: shared-element binding, exact tail length, open/cyclic spine
exclusion and rollback. Full source-boundary correspondence, return leaf effects,
query/family initialization and complete preservation remain open. Neither helper
return contract nor recursive assembly is authenticated. All four broad
obligations remain incomplete. Evidence: CeTA
`docs/data/source-partial-prefix-spine-20261119.json`.


`Subterm_Residual_Obstruction.thy` checks the M1 coverage obstruction: an allowed
strict compound subterm cannot instantiate the existing four replacement
patterns with the original parameter fixed. Whole-parameter coverage is the
positive control. Reuse `Check_Partial_Caller_Obstruction.pl` for eight source
controls. This fixture does not establish failure of every possible full-residual
simulation. Evidence: `docs/data/source-subterm-residual-obstruction-20261119.json`.


`Restricted_Prefix_Output_Check.thy` checks initialization of the old restricted
invariant with a fresh helper-output leaf, mode extraction from every frame,
and actual copy-step preservation using an explicit output coordinate. The
positive free-helper and negative partial-caller controls prevent conflating
the two outputs. `Check_Recursive_Partial_Entry.pl` supplies nine source controls.
See `docs/data/source-restricted-prefix-output-20261119.json`. Family coordinate
preservation, both returns and recursive assembly remain open.


`Observer_Output_Alias_Check.thy` checks output-interface equality preservation,
initialization, scope/projection transport and extraction of active output mode.
Controls reject a wrong slot and stale saved-frame equality.
`audit_output_alias.py` inventories seven retained output coordinates per variant
and rejects seven wrong slots per variant; it is structural evidence only.
Evidence: `docs/data/source-observer-output-alias-20261119.json`. Integration into
node/family invariants and actual module boundary projections remains open.


`Observer_Output_Copy_Node_Check.thy` checks the combined restricted/output-alias
invariant at partial Split initialization and the actual conditioned/canonical
copy node. The node derives output mode and passes the combined invariant to
its lower contract. Positive/negative controls distinguish this invariant from
the leaf invariant alone; `Check_Recursive_Partial_Entry.pl` supplies nine source
controls. Evidence: `docs/data/source-observer-output-copy-node-20261119.json`.
Other nodes, actual boundaries and full family preservation remain open.


`Observer_Output_Arithmetic_Check.thy` checks combined-invariant arithmetic and
scalar-equality node contracts. Controls prove scalar subterm coverage and
reject assuming that arbitrary compound parameters supply that coverage.
`Check_Subterm_Arithmetic.pl` supplies five source controls. Evidence:
`docs/data/source-observer-output-arithmetic-20261119.json`. Actual boundary
connection, remaining nodes and full family preservation remain open.


`Observer_Output_Rebase_Check.thy` checks combined-invariant rebasing and the
module-link contract, with the retained arithmetic/equality payload shape and a
wrong-scalar-coordinate negative control. `audit_output_rebase.py` verifies the
four retained original/renamed boundary shapes and rejects wrong output slots.
It also checks that the new scalar is not a projection of the old return tuple.
Evidence: `docs/data/source-observer-output-rebase-20261119.json`. Actual checked
link and strengthened target conditions remain family assembly obligations.


`Conditioned_Output_Link_Check.thy` checks full target-condition transport and
instantiates equality row 19:0 with proved scalar success/failure initialization.
Negative controls reject compound-as-scalar and wrong-coordinate evidence.
`Check_Equality_Condition_Coordinates.ML` reuses the unchanged generated source
checker and pins the fixture's exact source/refresh/return/ground coordinates:
twelve checks per original/renamed variant. Evidence:
`docs/data/source-conditioned-output-link-20261119.json`. Incoming boundary and
complete module/family assembly remain open.


`Equality_Output_Module_Check.thy` assembles all four retained equality-module
rows with the combined invariant and an explicit caller-continuation contract.
`LP_Prolog_Observer_Output_Return` supplies the actual scalar, parameter, leaf and
finiteness facts to that continuation. Kernel checking rejects skipped proofs and
oracles. `Check_Equality_Output_Module.ML` passes seventeen checks per retained
original/renamed variant, including missing-row and wrong-return-payload controls;
it reuses unchanged generated checking logic and does not freshly evaluate the
full-table control checker. Evidence:
`docs/data/source-equality-output-module-20261119.json`. Incoming links, caller
continuation and both Split return contracts remain open.


`Observer_Output_Rebase_Check.thy` now also assembles the conditioned incoming
arithmetic-to-equality boundary: strict descent, target module representation,
combined invariant and caller execution equality hold together. Identity scalar
coordinates pass and wrong scalar bindings are rejected. Static link checking and
the source scalar/context/representation facts remain explicit premises.
Evidence: `docs/data/source-equality-incoming-boundary-20261119.json`.


`Arithmetic_Boundary_Condition_Check.thy` discharges retained arithmetic row 15's
scalar successor-condition callback from the actual normalized row-19 runtime.
It carries the combined invariant and checks compound-as-scalar rejection.
`Check_Arithmetic_Rows.ML` now pins the exact retained source/target payload shapes;
eighteen static/shape checks pass per original/renamed variant. Its dynamic-open
marker still denotes static harness scope. Evidence:
`docs/data/source-arithmetic-boundary-condition-20261119.json`.


`Boundary_Residual_Obstruction_Check.thy` proves that absent residual heads prevent
both table-link acceptance and strict residual descent. `audit_boundary_residual.py`
finds that obstruction at 0:19 and 47:19 in all five retained local residuals and
their union, for original and renamed sources. Positive controls locate the real
incoming arithmetic clauses. This limits the preceding conditional module-link
approach; it does not audit the certified global residual. Evidence:
`docs/data/source-boundary-residual-obstruction-20261119.json`.


`Global_Boundary_Projection_Check.thy` pairs the global six-to-four residual
projection with observer payload rebasing and combined-invariant preservation.
`audit_global_boundary_projection.py` checks the exact clauses and empty-prefix
triples in both pinned residual certificates, rejecting wrong structural slots
and missing calls. The structural interpretation and full family representation
remain open. Evidence: `docs/data/source-global-boundary-projection-20261119.json`.


`Global_Boundary_Observation_Check.thy` derives an actual encoded helper-output
observation from the retained boundary representation, covered slot and combined
invariant. It preserves observed pairs through projection and includes positive
variable/negative constructor-leaf controls. Native encoding and global valuation
initialization remain open. Evidence:
`docs/data/source-global-boundary-observation-20261119.json`.


`Global_Boundary_Valuation_Check.thy` initializes fresh output/scalar structural
coordinates while preserving the source valuation elsewhere and its runtime
representation. The global boundary edge holds for this valuation. The certificate
audit now records disjoint coordinate sets and rejects collisions. Compatibility
with the incoming residual path and native encoding remain explicit open work.
Evidence: `docs/data/source-global-boundary-valuation-20261119.json`.


`Global_Arithmetic_Path_Check.thy` preserves the incoming output observation over
the arithmetic edge and equality-boundary projection, initializing only fresh
scalar coordinates. `audit_global_arithmetic_path.py` checks both retained path
fragments in original/renamed certificates and rejects overwritten observations
and nonfresh scalar pairs. Evidence:
`docs/data/source-global-arithmetic-path-20261119.json`. Native encoding and full
source/family integration remain open.


`Actual_Global_Arithmetic_Check.thy` ties a nonempty actual arithmetic transition
to the global path using its evaluated scalar, retaining the combined invariant
at the normalized equality state. Post-equality preservation and full-family
assembly remain open. Five source controls in `Check_Subterm_Arithmetic.pl` pass.
Evidence: `docs/data/source-actual-global-arithmetic-20261119.json`.


`Equality_Output_Preservation_Check.thy` verifies the shared actual post-equality
combined-invariant rule, its integration into the existing equality contract and
the retained four-row module. Caller coverage has positive and missing-slot
negative controls; five executable source controls pass. Global return-coordinate
correspondence and full family assembly remain open. Evidence:
`docs/data/source-output-equality-preservation-20261119.json`.


`Global_Equality_Return_Check.thy` connects actual scalar unification, preserved
restricted leaf history and reuse of the scalar observation to the duplicated
global return tuple. `audit_global_equality_return.py` checks the exact success
and return clauses/triples in both pinned artifacts with six negative controls.
Complete helper returns and caller continuations remain open. Evidence:
`docs/data/source-global-equality-return-20261119.json`.


`Global_Equality_Contract_Check.thy` and `Global_Arithmetic_Contract_Check.thy`
assemble the actual arithmetic/equality fragment into answer contracts against
the global residual, including failure and exact caller preservation on rebasing.
The caller continuation remains explicit. Five source controls and renewed
arithmetic/return audits pass. Evidence:
`docs/data/source-global-arithmetic-equality-contract-20261119.json`.


`audit_global_symbol_translation.py` checks every ordered clause and triple
(including nested data, sharing and successful prefixes) against the retained
JSON subjects in both variants. Nine mutations per variant are rejected;
whitespace is a positive control. This is artifact correspondence only, not
native observation semantics or a kernel-checked helper-return contract.
Evidence: `docs/data/source-global-symbol-translation-20261119.json`.


`Native_Structural_Encoding_Check.thy` supplies concrete structural names,
kernel-checked substitution/equation preservation and a conditional runtime
observation bridge. The arithmetic/equality contract is instantiated with this
encoder. Eight literal names and a constructor-arity negative are checked by
executable evaluation; variable preservation/leaf distinction are kernel checked.
Source signature discipline, all-row assembly and runtime-data transport remain
open. Evidence: `docs/data/source-native-structural-encoding-20261119.json`.


`Global_Runtime_Signature_Check.thy` transports the arithmetic/equality contract
and boundary residual tuples to the checker symbol type while retaining source
invariants. Observation premises discharge groundness of query positions 3–5;
sharing/free-runtime/free-shadow controls are kernel checked.
`audit_global_dependency_coverage.py` checks complete dependency triple sets in
both variants, including ordered prefixes, eight negatives and harmless
triple-reordering/duplicate-removal positives. Full-family assembly and concrete
certificate instantiation remain open. Evidence:
`docs/data/source-global-runtime-signature-20261119.json`.


`Global_Copy_Observation_Check.thy` preserves the combined invariant through
actual attached copy steps and transports actual copied-output observations
through both retained global success shapes. Free-or-ground helper mode,
tracking, finiteness and caller coverage remain explicit. The coordinate audit
checks four original/renamed cases and 16 mutations; 17 existing caller/partial
source controls pass. Full row and family assembly remain open. Evidence:
`docs/data/source-global-copy-observation-20261119.json`.


`Global_Copy_Successor_Check.thy` checks actual successor coordinates, functor
facts, complete helper return environments for both copy shapes, and reuse of
incoming observations at the actual successor valuation. The constructor name
is not an additional tracked numeric parameter. `audit_copy_successor_payloads.py`
checks four original/renamed cases and rejects 16 mutations;
`Check_Copy_Successor.pl` supplies five source controls. Full row contexts,
both Split contracts and recursive assembly remain open. Evidence:
`docs/data/source-global-copy-successor-20261119.json`.


`Global_Copy_Context_Check.thy` derives both retained copy-success context
shapes from actual resolution, including groundness, the nil spine shape,
reflexive equation, functor fact and complete return payload as applicable.
`audit_copy_contexts.py` checks four original/renamed cases and 20 rejected
mutations. Extra recursive node conditions, failure alternatives and full row
contracts remain open. Evidence:
`docs/data/source-global-copy-context-20261119.json`.


`Global_Copy_Contract_Check.thy` assembles the six-to-two singleton copy
choice into an answer contract, preserving the joint invariant and authenticating
the copied-output observation on success, and discharging local empty failure.
The cut continuation remains an explicit answer-contract premise. The state
audit checks both variants and rejects ten mutations, including added saved
alternatives. Fifteen source controls pass. Full node and family assembly remain
open. Evidence: `docs/data/source-global-copy-contract-20261119.json`.


`Global_Copy_Return_Check.thy` composes the six-to-two copy choice with its
singleton cut and caller activation. The caller receives the actual copied
parameter, tracking, output observation, leaf effects and finiteness; its answer
contract remains explicit. Compound ground parameters are allowed. Seven source
controls and the two-variant singleton audit pass (ten mutations rejected).
Full return-boundary/family assembly remains open. Evidence:
`docs/data/source-global-copy-return-20261119.json`.


`Copy_Empty_Interface_Check.thy` proves that empty-payload rebasing breaks the
output alias for a non-truth copied parameter, with compound-negative and
truth-positive controls. `Global_Copy_Boundary_Check.thy` instead retains the
runtime interface while composing the cut contract and exact zero-argument
residual return path. The caller contract remains explicit.
`audit_copy_zero_boundary.py` checks four paths and rejects 20 mutations.
Evidence: `docs/data/source-copy-empty-interface-20261119.json`.


`Global_Functor_Copy_Contract_Check.thy` checks the ten-to-six copy entry and
its cut-to-caller composition. Actual nil resolution and the incoming functor
relation justify unchanged constructor/name observations; copied-output leaf
history and joint invariant are preserved. Caller contract and helper mode
remain explicit. Source-state and payload audits reject 26 mutations in total;
12 source controls pass. Full family and Split contracts remain open. Evidence:
`docs/data/source-global-functor-copy-contract-20261119.json`.


`Global_Copy_Invariant_Check.thy` derives helper-output mode and output leaf
effect from the joint invariant and observed-slot memberships, and integrates
them into both copy caller contracts. Kernel controls cover free, compound-ground
and rejected partially instantiated helper outputs. Seventeen caller/partial
source controls pass. Recursive-entry initialization and full family assembly
remain open. Evidence: `docs/data/source-global-copy-invariant-20261119.json`.


`Recursive_Split_Observer_Check.thy` initializes the exact Split 30/44 observer
slots and composes that initialization with actual cons resolution. It supplies
joint invariant, caller coverage, helper mode and leaf effect. Twelve positive
coordinate controls, 48 rejected mutations and nine partial-caller source
controls pass. All-path/family assembly and both return contracts remain open.
Evidence: `docs/data/source-recursive-split-observer-20261119.json`.


`Global_Cons_Invariant_Check.thy` preserves the full joint invariant through
actual cons-head steps, including saved frames and backtracking. Call/caller
finiteness and template groundness are derived from existing invariant/tracking
premises. Both source variants pass 22 positive and 42 negative coordinate
controls in total; nine partial-entry source controls pass. Cons residual
observations and full node/family assembly remain open. Evidence:
`docs/data/source-global-cons-invariant-20261119.json`.


`Global_Cons_Observation_Check.thy` derives actual resolved head/tail structures
from the incoming list observation and successful cons MGU, then authenticates
the exact encoded shadow split. Child histories initialize at their current
trees. `audit_cons_observation_split.py` checks four original/renamed cases and
rejects 20 mutations. Other successor coordinates and full row/family assembly
remain open. Evidence: `docs/data/source-global-cons-observation-20261119.json`.


`Global_Fresh_Output_Observation_Check.thy` authenticates the actual body-only
output's freeness, encoded leaf observation and separation from the instantiated
selected call. The cons case derives post-resolution finiteness. Runtime free
variables remain distinct from structural leaf constructors. Both source variants
pass 22 positive and 42 negative controls in total; nine source controls pass.
Full residual/node/family assembly remains open. Evidence:
`docs/data/source-global-fresh-output-observation-20261119.json`.


`Global_Cons_Output_Check.thy` preserves parameter identity and the caller-output
observation/history, then assembles all five cons-successor observations at the
actual coordinate valuation. `audit_cons_five_coordinates.py` checks four cases
and rejects 40 mutations; nine partial-entry source controls pass. Extra
functor/name coordinates and full residual/node/family assembly remain open.
Evidence: `docs/data/source-global-cons-output-20261119.json`.


`Global_Cons_Residual_Check.thy` composes the five actual successor observations
with strict descent through the retained six-to-ten cons clause. Exact
original/renamed clause/triple audits reject 12 mutations; source-coordinate
audits reject 40. Failure handling, full node/family assembly and the larger cons
successor remain open. Evidence:
`docs/data/source-global-cons-residual-20261119.json`.


`Global_Cons_Context_Check.thy` authenticates the simple cons successor's total
return payload, tracked parameter, ground/list-shape context and free helper
output using the actual MGU and checked maps. The resident kernel check has no
skips or oracles. `audit_cons_context_payload.py` passes both source fixtures and
rejects 16 mutations; the coordinate audit rejects 40 and nine source controls
pass. Full node/failure and recursive family assembly remain open. Evidence:
`docs/data/source-global-cons-context-20261119.json`.


`Global_Cons_Contract_Check.thy` composes simple cons choice invariant preservation,
five successor observations, strict residual descent and payload/context facts.
Its empty failure case is discharged; the actual successful continuation contract
is explicit. Kernel checking has no skips or oracles. State/context/residual
audits reject 10/16/12 mutations, and `Check_Cons_Contract.pl` passes six source
controls. Full recursive assembly and both Split returns remain open. Evidence:
`docs/data/source-global-cons-contract-20261119.json`.
