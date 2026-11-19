theory DP_Checkpoint_Processor
 imports DP_Checkpoint_Order "TRS.QDP_Framework"
begin

text \<open>One checkpoint transition is a root dependency-pair instance and
its complete finite support-rewriting connection. The support system itself
need not terminate. Neither lemma introduces a minimal-chain assumption.\<close>

definition checkpoint_dp_step where
 "checkpoint_dp_step P R = rrstep P O (rstep R)\<^sup>*"

lemma checkpoint_dp_SN_finite:
 assumes sn: "SN (checkpoint_dp_step P R)"
 shows "finite_dpp (nfs,minimal,P,{}, {},{},R)"
 unfolding finite_dpp_def
proof (clarify)
 fix s t sigma
 assume chain: "min_ichain (nfs,minimal,P,{}, {},{},R) s t sigma"
 have pairs: "(s i,t i)\<in>P" for i using chain by (auto simp: ichain.simps)
 have root: "(s i\<cdot>sigma i,t i\<cdot>sigma i)\<in>rrstep P" for i
  using pairs[of i] by (auto simp: rrstep_def')
 have support: "(t i\<cdot>sigma i,s (Suc i)\<cdot>sigma (Suc i))\<in>(rstep R)\<^sup>*" for i
  using chain by (auto simp: ichain.simps)
 have infinite: "chain (checkpoint_dp_step P R) (\<lambda>i. s i\<cdot>sigma i)"
  using root support unfolding checkpoint_dp_step_def by (metis relcompI)
 have "\<exists>f. chain (checkpoint_dp_step P R) f"
  by (rule exI[of _ "\<lambda>i. s i\<cdot>sigma i"]) (rule infinite)
 then show False using sn unfolding SN_defs by auto
qed

lemma checkpoint_dp_ranking:
 assumes order: "wf W"
 and control: "\<And>s t. (s,t)\<in>checkpoint_dp_step P R \<Longrightarrow> s\<notin>K \<Longrightarrow> height t < (height s::nat)"
 and descent: "\<And>s t. (s,t)\<in>checkpoint_returns (checkpoint_dp_step P R) K \<Longrightarrow> (rank t,rank s)\<in>W"
 shows "finite_dpp (nfs,minimal,P,{}, {},{},R)"
 by (rule checkpoint_dp_SN_finite, rule checkpoint_ranking[OF order control descent])

ML \<open>
val checked = @{thms checkpoint_dp_SN_finite checkpoint_dp_ranking};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checkpoint DP processor proof" else ();
\<close>
end
