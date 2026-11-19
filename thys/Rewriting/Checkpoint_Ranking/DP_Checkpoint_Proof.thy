theory DP_Checkpoint_Proof
 imports DP_Checkpoint_Check
begin

type_synonym ('f,'v) checkpoint_schema_receipts =
 "(nat * ('f,'v) term list) option list"
type_synonym ('f,'v) checkpoint_argument_registry =
 "('f * 'f * 'f * ('f,'v) checkpoint_schema_receipts) list"
type_synonym ('f,'v) checkpoint_ground_registry =
 "('f * 'f * 'f * 'f * 'f * 'f * 'f * ('f,'v) checkpoint_schema_receipts) list"
type_synonym ('f,'v) checkpoint_list_registry =
 "('f * 'f * 'f * 'f * 'f * 'f * 'f * 'f * 'f * 'f * 'f *
 ('f,nat) term list * ('f,'v) checkpoint_schema_receipts * ('f,'v) checkpoint_schema_receipts) list"
type_synonym ('f,'v) checkpoint_transition_receipts =
 "(nat * 'f checkpoint_atom list *
 (((nat * 'f list * ('f,'v) term list * nat list) * ('f checkpoint_atom * ('f,'v) term list)) list) *
 'f checkpoint_atom list) list"

datatype ('f,'v) checkpoint_certificate = Checkpoint_Certificate
 nat "('f,'v) rule list" "('f,'v) rule list" "'f list" "'f * 'f * 'f * 'f" "'f list" "'f list"
 "('f * nat) list" "('f * nat) list"
 "('f,'v) checkpoint_argument_registry" "('f,'v) checkpoint_ground_registry"
 "('f,'v) checkpoint_list_registry" "('f * nat * 'f checkpoint_atom list) list"
 "('f,'v) checkpoint_transition_receipts"

fun check_checkpoint_proof where
 "check_checkpoint_proof pair_list support
 (Checkpoint_Certificate version ordered_pairs ordered_support constructors (L,N,Z,S) controls checkpoints heights coordinates arguments grounds list_regs annotation receipts) =
 (version=2 \<and> set ordered_pairs = set pair_list \<and> set ordered_support = set support \<and> distinct (map fst heights) \<and> distinct (map fst coordinates) \<and>
 set controls\<subseteq>set (map fst heights) \<and> set checkpoints\<subseteq>set (map fst coordinates) \<and>
 check_checkpoint_certificate (set constructors) L N Z S (set controls) (set checkpoints)
 (\<lambda>f. (case map_of heights f of None \<Rightarrow> 0 | Some n \<Rightarrow> n)) (\<lambda>f. (case map_of coordinates f of None \<Rightarrow> 0 | Some n \<Rightarrow> n))
 ordered_pairs ordered_support arguments grounds list_regs annotation receipts)"

lemma check_checkpoint_proof_sound:
 fixes pair_list support :: "('f,'v) rule list" and nfs minimal :: bool
 assumes checked: "check_checkpoint_proof pair_list support certificate"
 shows "finite_dpp (nfs,minimal,set pair_list,{},{},{},set support)"
 using checked
 by (cases certificate; auto split: prod.splits; metis check_checkpoint_certificate_sound)

ML \<open>
val thms = @{thms check_checkpoint_proof_sound};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted checkpoint certificate format" else ();
\<close>
end
