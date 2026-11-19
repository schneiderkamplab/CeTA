theory DP_Checkpoint_Path
 imports DP_Checkpoint_Control
begin

text \<open>A path annotation keeps its initial checkpoint as an explicit
coordinate. Shared control nodes therefore do not merge facts from different
prefixes. Each rule obligation includes the complete finite support derivation;
a successful-prefix fact must be justified inside that obligation.\<close>

definition checkpoint_rule_contract where
 "checkpoint_rule_contract R pre post pair =
  (\<forall>sigma t. pre (fst pair\<cdot>sigma) \<longrightarrow>
   (snd pair\<cdot>sigma,t)\<in>(rstep R)\<^sup>* \<longrightarrow> post t)"

lemma checkpoint_rule_contract_step:
 assumes contracts: "list_all (checkpoint_rule_contract R pre post) pairs"
 and edge: "(s,t)\<in>checkpoint_dp_step (set pairs) R"
 and pre: "pre s"
 shows "post t"
proof -
 obtain l r sigma where pair: "(l,r)\<in>set pairs"
 and source: "s=l\<cdot>sigma"
 and support: "(r\<cdot>sigma,t)\<in>(rstep R)\<^sup>*"
  using edge unfolding checkpoint_dp_step_def rrstep_def' by auto
 show ?thesis using contracts pair pre source support
  by (auto simp: list_all_iff checkpoint_rule_contract_def)
qed

lemma checkpoint_return_annotation:
 assumes entry: "\<And>s t. s\<in>K \<Longrightarrow> (s,t)\<in>R \<Longrightarrow> A s t"
 and internal: "\<And>origin s t. A origin s \<Longrightarrow> s\<notin>K \<Longrightarrow> (s,t)\<in>R \<Longrightarrow> A origin t"
 and returned: "(s,t)\<in>checkpoint_returns R K"
 shows "A s t"
proof -
 obtain u where start: "s\<in>K" and first: "(s,u)\<in>R"
 and rest: "(u,t)\<in>(checkpoint_internal R K)\<^sup>*"
  using returned unfolding checkpoint_returns_def by auto
 have initial: "A s u" by (rule entry[OF start first])
 have "A s u \<Longrightarrow> A s t" using rest
  by (induct rule: rtrancl_induct) (auto simp: checkpoint_internal_def intro: internal)
 then show ?thesis using initial by simp
qed

lemma checked_checkpoint_path_ranking:
 assumes control: "check_checkpoint_control U K h pairs support"
 and order: "wf W"
 and entry: "\<And>origin. checkpoint_at K origin \<Longrightarrow>
  list_all (checkpoint_rule_contract (set support) (\<lambda>s. s=origin) (A origin)) pairs"
 and internal: "\<And>origin. list_all (checkpoint_rule_contract (set support)
  (\<lambda>s. A origin s \<and> \<not>checkpoint_at K s) (A origin)) pairs"
 and boundary: "\<And>origin t. checkpoint_at K origin \<Longrightarrow> checkpoint_at K t \<Longrightarrow>
  A origin t \<Longrightarrow> (rank t,rank origin)\<in>W"
 shows "finite_dpp (nfs,minimal,set pairs,{}, {},{},set support)"
proof (rule checked_checkpoint_dp_ranking[OF control order])
 fix s t
 assume returned: "(s,t)\<in>checkpoint_returns (checkpoint_dp_step (set pairs) (set support)) {t. checkpoint_at K t}"
 have annotation: "A s t"
 proof (rule checkpoint_return_annotation[OF _ _ returned])
  fix s t
  assume start: "s\<in>{t. checkpoint_at K t}"
  and edge: "(s,t)\<in>checkpoint_dp_step (set pairs) (set support)"
  show "A s t"
   by (rule checkpoint_rule_contract_step[OF entry edge]) (use start in auto)
 next
  fix origin s t
  assume annotation: "A origin s" and outside: "s\<notin>{t. checkpoint_at K t}"
  and edge: "(s,t)\<in>checkpoint_dp_step (set pairs) (set support)"
  show "A origin t"
   by (rule checkpoint_rule_contract_step[OF internal edge]) (use annotation outside in auto)
 qed
 show "(rank t,rank s)\<in>W"
  using returned annotation boundary by (auto simp: checkpoint_returns_def)
qed

ML \<open>
val thms = @{thms checkpoint_rule_contract_step checkpoint_return_annotation checked_checkpoint_path_ranking};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted checkpoint paths" else ();
\<close>
end
