theory DP_Checkpoint_Check
 imports DP_Checkpoint_Registry
begin

text \<open>The complete checkpoint certificate check has no semantic premises
supplied by the caller. Return interfaces are derived only from summary records
whose checks cover the original support rules.\<close>

definition check_checkpoint_certificate where
 "check_checkpoint_certificate C L N Z S U K height_map coord_map pair_list support
 argument_registry ground_registry list_registry annotation receipts =
 ({N,Z,S}\<subseteq>C \<and> L\<notin>{N,Z,S} \<and>
 list_all (checkpoint_skeleton_safe_rule C) support \<and>
 check_checkpoint_control U K height_map pair_list support \<and>
 list_all (check_checkpoint_argument_registration C N Z S support) argument_registry \<and>
 list_all (check_checkpoint_ground_registration C N Z S support) ground_registry \<and>
 list_all (check_checkpoint_list_registration C L N Z S support) list_registry \<and>
 check_checkpoint_annotation_table U K coord_map annotation \<and>
 list_all (check_checkpoint_transition
 (check_checkpoint_inference N Z S (map checkpoint_argument_interface argument_registry)
 (map checkpoint_ground_interface ground_registry) (map checkpoint_list_interface list_registry))
 pair_list annotation) receipts \<and>
 check_checkpoint_transition_coverage K coord_map pair_list annotation receipts)"

lemma check_checkpoint_certificate_sound:
 fixes pair_list support :: "('f,'v) rule list" and nfs minimal :: bool
 assumes checked: "check_checkpoint_certificate C L N Z S U K height_map coord_map pair_list support
 argument_registry ground_registry list_registry annotation receipts"
 shows "finite_dpp (nfs,minimal,set pair_list,{},{},{},set support)"
proof -
 let ?checker = "check_checkpoint_inference N Z S (map checkpoint_argument_interface argument_registry)
 (map checkpoint_ground_interface ground_registry) (map checkpoint_list_interface list_registry)"
 have constructors: "{N,Z,S}\<subseteq>C" and leaf: "L\<notin>{N,Z,S}"
 and safe: "checkpoint_skeleton_safe C (set support)"
 and control: "check_checkpoint_control U K height_map pair_list support"
 and arguments: "list_all (check_checkpoint_argument_registration C N Z S support) argument_registry"
 and ground: "list_all (check_checkpoint_ground_registration C N Z S support) ground_registry"
 and lists: "list_all (check_checkpoint_list_registration C L N Z S support) list_registry"
 and table: "check_checkpoint_annotation_table U K coord_map annotation"
 and transitions: "list_all (check_checkpoint_transition ?checker pair_list annotation) receipts"
 and coverage: "check_checkpoint_transition_coverage K coord_map pair_list annotation receipts"
 using checked by (auto simp: check_checkpoint_certificate_def checkpoint_skeleton_safe_list)
 show ?thesis
 by (rule checked_checkpoint_certificate[OF control safe table transitions coverage])
    (rule checked_checkpoint_registered_inference[OF constructors leaf arguments ground lists]; assumption)
qed

ML \<open>
val thms = @{thms check_checkpoint_certificate_sound};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted complete checkpoint checker" else ();
\<close>
end
