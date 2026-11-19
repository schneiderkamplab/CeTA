theory Checkpoint_DP_Processor
 imports "Framework.Dependency_Pair_Problem_Spec" "../Rewriting/Checkpoint_Ranking/DP_Checkpoint_Proof"
begin

definition check_checkpoint_dpp where
 "check_checkpoint_dpp I d certificate =
 (dpp_ops.Pw I d = [] \<and> dpp_ops.Q I d = [] \<and> dpp_ops.R I d = [] \<and>
 check_checkpoint_proof (dpp_ops.P I d) (dpp_ops.Rw I d) certificate)"

lemma check_checkpoint_dpp_sound:
 assumes implementation: "dpp_spec I"
 and checked: "check_checkpoint_dpp I d certificate"
 shows "finite_dpp (dpp_ops.dpp I d)"
proof -
 interpret dpp_spec I by (rule implementation)
 have Pw: "dpp_ops.Pw I d = []" and Q: "dpp_ops.Q I d = []"
 and R: "dpp_ops.R I d = []"
 and verified: "check_checkpoint_proof (dpp_ops.P I d) (dpp_ops.Rw I d) certificate"
 using checked by (auto simp: check_checkpoint_dpp_def)
 have finite: "finite_dpp (dpp_ops.nfs I d,dpp_ops.minimal I d,
 set (dpp_ops.P I d),{},{},{},set (dpp_ops.Rw I d))"
 by (rule check_checkpoint_proof_sound[OF verified])
 show ?thesis using finite by (simp add: dpp_sound Pw Q R)
qed

ML \<open>
val thms = @{thms check_checkpoint_dpp_sound};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted common checkpoint DP adapter" else ();
\<close>
end
