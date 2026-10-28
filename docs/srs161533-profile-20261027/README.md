---
type: Historical Report
---
# Current CeTA profile: SRS_Standard/ICFP_2010/161533.ari

Both the current production executable and its privately compiled profiling
counterpart accepted the same compact certificate. Production SHA-256:
`8b5e6c3560cf10f1952b68b52931e2e6becac7b8e93f1a19776b277edef3d28c`.
The generated CPF source hashes match the committed unified export manifest,
including the proved usable-rule membership optimization. No checker source or
production binary was changed in this profiling task.

## Production measurement

Focused production wall time: **65.695 seconds**, versus 86.683 seconds in the
32-worker campaign. Mutator CPU: 41.232 s; GC CPU: 23.803 s (36.6% of total CPU).
Allocation: 214,578,948,768 bytes; maximum live heap: 9,006,402,848 bytes;
total RTS memory: 18,667 MiB. This is one fresh isolated measurement, not a
full campaign rerun.

The compact certificate is 641,687,909 bytes. It contains 6,042,852 term
applications, 5,870,205 labelled-symbol occurrences and 118,712 rule occurrences
across its intermediate systems. The processor chain has three flat-context
closures, one finite-model semantic-labelling step, polynomial rule removal,
and an empty-system leaf. There is no usable-rule processor on this proof path.

## Instrumented profile

Build flags: `-O2 -prof -fprof-auto -rtsopts`, including generated code and parsing
adapter. Instrumented wall time: 182.190 seconds; sampled mutator time: 139.80 s.
Instrumentation changes timing/allocation, so the following percentages describe
instrumented mutator execution, exclude GC, and must not be added to the
production GC percentage. Inclusive rows overlap as indicated.

| Stage | Inclusive time | Allocation |
|---|---:|---:|
| XML parsing and CPF decoding, `parse_xml_string` | 59.9% | 57.5% |
| ↳ XML document construction, `doc_of_string` | 27.8% | 28.7% |
| ↳ CPF decoding, `parse_xml` | 29.0% | 25.8% |
| ↳ XML text normalization, `map_xml_text` | 3.2% | 3.0% |
| Input character conversion, `cachedCharacters` | 7.4% | 22.9% |
| Complete termination check | 31.3% | 9.0% |
| ↳ Polynomial rule removal | 16.7% | 3.5% |
| ↳ Finite-model semantic labelling | 13.8% | 5.0% |

Parsing/representation is the largest bottleneck, with GC a substantial extra
production cost. `xml_do` alone accounts for 17.9% aggregate self time. Its
code repeatedly matches XML tag character lists and calls `explode tag`.
The input conversion already uses cached ASCII characters, but it still
allocates list structure for the entire input. XML construction, text mapping,
and CPF conversion create further intermediate representations.

## Secondary bottleneck: rule-bucket list scans

The rule database uses a tree keyed by left-hand-side root symbol and arity,
but each bucket contains a list. It is therefore not enough that the outer
container is an RBT:

* Rule removal's `delete_rules → delete_values → delete_value → removeAll`
  consumes **9.2%** inclusive time. `removeAll` has 86,359,959 entries in this
  subtree; its structural term comparisons trigger 178,952,652 `equal_lab`
  entries. Deleting many rules repeatedly scans the same buckets.
* Semantic labelling's new problem construction uses
  `insert_values → insert_value → insertb → membera`, consuming **6.8%**.
  There are 28,767,374 list-membership entries and 173,082,528 label-equality
  entries in this subtree: repeated duplicate checks during insertion.
* Rule partitioning costs **4.1%**, including RBT construction and membership.
* Actual finite-model evaluation/label construction accounts for about **3.9%**;
  checking labelled-rule membership adds **2.0%**. It is not the dominant stage.

Entry counts are profiling call-tree entries, not counts of independent proof
obligations. The label equality counts include recursive label comparisons.

## Remedies suggested by this evidence

1. Reduce input/XML/CPF intermediate allocation. A compact byte-oriented input
   and lower-allocation parser are the largest opportunity, but must preserve
   character handling, exact CPF semantics, and rejection behavior. Cache or
   precompute tag representations rather than repeatedly converting literals.
2. Prove batch rule-bucket operations equivalent to the current ones: build or
   deduplicate each bucket once, and filter each affected bucket once against
   an indexed deletion set. Preserve observable ordering and all multimap
   invariants; regenerate from Isabelle rather than editing generated Haskell.
3. Repeated labelled-symbol/term comparison may additionally benefit from a
   verified shared representation or interning. Reducing repeated scans should
   precede that more invasive change.

This is a different bottleneck from h31's usable-rule closure membership.
Further whitespace removal cannot eliminate the 641.7 MB of remaining explicit
term/label structure. GC tuning alone cannot remove its representation costs.
Raw profiling output, command receipts, identities, XML counts and selected
call-tree paths accompany this report. No optimization was implemented here.
