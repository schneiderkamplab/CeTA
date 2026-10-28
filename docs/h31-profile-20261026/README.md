---
type: Historical Report
---
# h31 compact-child checking profile

Profiled the complete source-bound higher-order delegation for h31 against its
compact 13,756,001-byte first-order child. Both the production and instrumented
checkers returned CERTIFIED YES. Original input/capsule and compact-child hashes,
commands, binary identities and generated-source hashes are recorded alongside.
The production binary and Isabelle theories were not modified.

## Production measurement

Unified -O2 CeTA: 67.48 seconds wall time; 66.22 seconds mutator CPU,
0.818 seconds GC CPU (98.8% productivity). Heap allocation: 12.94 GB;
maximum residency: 276.5 MB; total RTS memory: 574 MiB. This is a focused
measurement, not a new full-frontier refresh.

## Instrumented diagnosis

Private category build with -O2 -prof -fprof-auto. Instrumentation changes
allocation and timing considerably (218.77 seconds elapsed), so profile
percentages describe the instrumented execution, not exact production fractions.

Top aggregate self-time cost centres:

| Function | Instrumented self time |
|---|---:|
| Labelings.equal_lab | 58.4% |
| Arith.equal_char | 24.2% |
| Term_Rewriting.equal_term | 3.1% |
| Arith.membera | 2.7% |

One `check_ur_closed_term_rm_af` closure subtree accounts for 83.1% inclusive
time. The generated code explicitly performs `membera ur lr` inside a loop over
rules returned by the root/arity map for each relevant subterm. Membership
compares whole term pairs and labelled symbol strings. Call-tree entry totals:
453,709,076 equal_lab; 441,398,460 equal_term; 322,382,538 membera;
9,364,669,535 equal_char. These are instrumented entry counts, not independent
logical obligations. One membership branch alone contributes 325,079,743
label comparisons and 6,457,398,135 character comparisons.

The child has 135,433 name occurrences but just 134 distinct name strings;
mean name length is 44.26 bytes and the maximum is 136. Repeated structural
comparison dominates; the presence of size-change processors in the certificate
does not make graph composition the main hotspot in this profile.

## Recommended optimization order

1. Prepare rule membership once per exact usable-rule context, or remove already
   usable rules from each root/arity bucket once. Retain the same matching/cap and
   argument-filter obligations for remaining rules, with an Isabelle equivalence
   proof before regenerating Haskell.
2. Cache repeated subterm closure work only within that complete context.
3. Consider verified symbol/label interning to replace repeated long-string
   comparisons with identifiers. This is supplementary to eliminating repeated
   list scans; changing names ad hoc would violate the delegation interface.

GC tuning and further whitespace removal are not the primary remedy for h31.
No implementation optimization was made in this profiling task.

## Re-export scope

Only the 36 retained delegation children were compacted and rechecked. Other
certificates have NOT been re-exported/compacted and remeasured, and no fresh
Ferrum replay across all categories was run. The previous 5,412-root measurements
therefore still describe their original certificate representation. The Ferrum
exporter change is isolated in commit 8336ef2 and is not deployed in the parent
thread's production binary.
