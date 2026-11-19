theory DP_Checkpoint_Test
 imports DP_Checkpoint_Control
begin

definition two_control_edges :: "(nat,nat) rule list" where
 "two_control_edges = [(Fun 0 [],Fun 1 []),(Fun 1 [],Fun 0 [])]"

lemma two_control_cycle_covered:
 "check_checkpoint_control {0,1} {0} id two_control_edges []"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma missing_checkpoint_rejected:
 "\<not> check_checkpoint_control {0,1} {} id two_control_edges []"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma wrong_height_rejected:
 "\<not> check_checkpoint_control {0,1} {0} (\<lambda>_. 0) two_control_edges []"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma rewritten_control_rejected:
 "\<not> check_checkpoint_control {0,1} {0} id two_control_edges [(Fun 1 [],Fun 2 [])]"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma omitted_control_root_rejected:
 "\<not> check_checkpoint_control {0} {0} id two_control_edges []"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma disconnected_cycle_rejected:
 "\<not> check_checkpoint_control {0,1,2} {0} id
   (two_control_edges @ [(Fun 2 [],Fun 2 [])]) []"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma divergent_support_does_not_invalidate_coverage:
 "check_checkpoint_control {0,1} {0} id two_control_edges [(Fun 2 [],Fun 2 [])]"
 by (simp add: check_checkpoint_control_def two_control_edges_def)

lemma checkpoint_self_loop_covered:
 "check_checkpoint_control {(0::nat)} {0} (\<lambda>_. 0) [(Fun 0 [],Fun 0 [])] []"
 by (simp add: check_checkpoint_control_def)

lemma checkpoint_self_loop_not_finite:
 "\<not> finite_dpp (False,False,{(Fun (0::nat) [],Fun 0 [])},{},{},{},{}::(nat,nat) trs)"
proof -
 have loop: "min_ichain (False,False,{(Fun (0::nat) [],Fun 0 [])},{},{},{},{}::(nat,nat) trs)
   (\<lambda>_. Fun 0 []) (\<lambda>_. Fun 0 []) (\<lambda>_. Var)"
  by (simp add: ichain.simps)
 show ?thesis using loop unfolding finite_dpp_def by blast
qed

ML \<open>
val checked = @{thms two_control_cycle_covered missing_checkpoint_rejected wrong_height_rejected
 rewritten_control_rejected omitted_control_root_rejected disconnected_cycle_rejected
 divergent_support_does_not_invalidate_coverage checkpoint_self_loop_covered checkpoint_self_loop_not_finite};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checkpoint negative controls" else ();
\<close>
end
