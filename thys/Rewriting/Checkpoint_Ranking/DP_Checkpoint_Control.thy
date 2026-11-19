theory DP_Checkpoint_Control
 imports DP_Checkpoint_Processor
begin

fun checkpoint_at where
 "checkpoint_at K (Var x) = False"
| "checkpoint_at K (Fun f ts) = (f\<in>K)"

fun checkpoint_height where
 "checkpoint_height h (Var x) = 0"
| "checkpoint_height h (Fun f ts) = (h f::nat)"

fun checkpoint_pair_control where
 "checkpoint_pair_control U K h (Fun f ss,Fun g ts) =
   (f\<in>U \<and> g\<in>U \<and> (f\<notin>K \<longrightarrow> h g < (h f::nat)))"
| "checkpoint_pair_control U K h _ = False"

fun checkpoint_support_control where
 "checkpoint_support_control U (Fun f ts,r) = (f\<notin>U)"
| "checkpoint_support_control U _ = False"

definition check_checkpoint_control where
 "check_checkpoint_control U K h pairs rules =
  (list_all (checkpoint_pair_control U K h) pairs \<and>
   list_all (checkpoint_support_control U) rules)"

lemma checkpoint_support_control_correct:
 "checkpoint_support_control U (l,r) = checkpoint_opaque_root U l"
 by (cases l) (auto simp: checkpoint_opaque_root_def)

lemma checkpoint_control_sound:
 assumes checked: "check_checkpoint_control U K h pairs rules"
 and edge: "(s,t)\<in>checkpoint_dp_step (set pairs) (set rules)"
 and outside: "\<not> checkpoint_at K s"
 shows "checkpoint_height h t < checkpoint_height h s"
proof -
 obtain l r sigma where pair: "(l,r)\<in>set pairs"
  and s: "s=l\<cdot>sigma"
  and steps: "(r\<cdot>sigma,t)\<in>(rstep (set rules))\<^sup>*"
  using edge unfolding checkpoint_dp_step_def rrstep_def' by auto
 have control: "checkpoint_pair_control U K h (l,r)"
  using checked pair unfolding check_checkpoint_control_def list_all_iff by auto
 obtain f ss g ts where l: "l=Fun f ss" and r: "r=Fun g ts"
  and g: "g\<in>U" and height: "f\<notin>K \<Longrightarrow> h g < h f"
  using control by (cases l; cases r) auto
 have stable: "\<And>a b. (a,b)\<in>set rules \<Longrightarrow> checkpoint_opaque_root U a"
  using checked unfolding check_checkpoint_control_def list_all_iff
  by (auto simp: checkpoint_support_control_correct)
 have root: "\<exists>us. t=Fun g us"
  by (rule checkpoint_control_root_steps[where R="set rules" and K=U, OF _ g steps[unfolded r, simplified]])
     (use stable in blast)
 obtain us where t: "t=Fun g us" using root by blast
 show ?thesis using outside height by (simp add: s l t)
qed

lemma checked_checkpoint_dp_ranking:
 assumes checked: "check_checkpoint_control U K h pairs rules"
 and order: "wf W"
 and descent: "\<And>s t. (s,t)\<in>checkpoint_returns (checkpoint_dp_step (set pairs) (set rules)) {t. checkpoint_at K t}
   \<Longrightarrow> (rank t,rank s)\<in>W"
 shows "finite_dpp (nfs,minimal,set pairs,{}, {},{},set rules)"
 by (rule checkpoint_dp_ranking[OF order, where height="checkpoint_height h" and K="{t. checkpoint_at K t}" and rank=rank])
    (auto intro: checkpoint_control_sound[OF checked] descent)

ML \<open>
val checked = @{thms checkpoint_support_control_correct checkpoint_control_sound checked_checkpoint_dp_ranking};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checkpoint control checker" else ();
\<close>
end
