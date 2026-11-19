theory LP_Cut_Domain_NO_Certificate
  imports LP_Cut_Domain_NO_Pending
begin

context cut_runtime_domain
begin


lemma no_trace_path:
  "lpc_no_trace fuel P s steps t \<Longrightarrow>
   no_path P (lp_cut_state_eval s LPIVar)
     (map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps)"
  by (induct steps arbitrary: s) (auto intro: no_step_sound split: prod.splits)

lemma no_trace_last:
  "lpc_no_trace fuel P s steps t \<Longrightarrow> last (s # map snd steps) = t"
  by (induct steps arbitrary: s) (auto split: prod.splits)

lemma no_trace_pump:
  assumes program: "lp_cut_source_program P"
    and loop: "lpc_no_trace fuel P [LPCGoals [LPCAtom a]] steps
      ([LPCGoals [LPCAtom a]] @ after)"
    and progress: "steps \<noteq> []"
    and suffix: "(lp_cut_barriers after \<and> lp_cut_barriers before) \<or>
      list_all (\<lambda>x. lpc_no_suffix_safe (snd x)) steps"
  shows "\<not> SN_on (mgu_source P)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
proof -
  let ?core = "lp_cut_state_eval [LPCGoals [LPCAtom a]] LPIVar"
  obtain u us where steps: "map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps = u#us"
    using progress by (cases steps) auto
  have path: "no_path P ?core (u#us)"
    using no_trace_path[OF loop] steps by simp
  have nonempty: "map snd steps \<noteq> []" using progress by simp
  have last_finite: "last (map snd steps) = [LPCGoals [LPCAtom a]] @ after"
    using no_trace_last[OF loop] progress by (cases steps) auto
  have last_mapped: "last (map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps)) =
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
    using last_map[OF nonempty, of "\<lambda>s. lp_cut_state_eval s LPIVar"] last_finite by simp
  have last: "last (u#us) = ?core @ lp_cut_state_eval after LPIVar"
  proof -
    have mapped: "map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps) = u#us"
      using steps by (simp only: map_map o_def)
    have eq: "last (u#us) = lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
      using last_mapped mapped by metis
    show ?thesis using eq by (simp only: lp_cut_state_map_def map_append)
  qed
  have bar: "lp_cut_barriers (lp_cut_state_eval bs LPIVar)" if "lp_cut_barriers bs" for bs
    using that
  proof (induct bs)
    case Nil then show ?case by (simp add: lp_cut_state_map_def)
  next
    case (Cons e es)
    have head: "lp_cut_is_barrier (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar) e)"
      using Cons.prems by (cases e) auto
    show ?case using Cons head by (simp add: lp_cut_state_map_def)
  qed
  have core: "map (lp_cut_scope_entry r) ?core = ?core" for r
    by (simp add: lp_cut_state_map_def)
  show ?thesis
  proof (cases "lp_cut_barriers after \<and> lp_cut_barriers before")
    case True
    have after: "lp_cut_barriers (lp_cut_state_eval after LPIVar)"
      using bar True by blast
    have before: "lp_cut_barriers (lp_cut_state_eval before LPIVar)"
      using bar True by blast
    show ?thesis using no_barrier_pump[OF program path last after core before]
      by (simp add: lp_cut_state_map_def)
  next
    case False
    have safe_eval: "lpc_no_suffix_safe (lp_cut_state_eval s LPIVar) = lpc_no_suffix_safe s" for s
      by (cases s rule: lpc_no_suffix_safe.cases) (auto simp: lp_cut_state_map_def)
    have safe: "lpc_no_suffix_safe v" if "v \<in> set (?core#u#us)" for v
      using suffix False steps that
      by (auto simp: list_all_iff safe_eval; force)
    show ?thesis using no_pending_pump[OF program path last safe core]
      by (simp add: lp_cut_state_map_def)
  qed
qed

theorem no_check_source_sound:
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have pump: "\<not> SN_on (mgu_source P)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
    by (rule no_trace_pump)
      (use checked in \<open>auto simp: lpc_no_check_source_def\<close>)
  have reach: "(lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar,
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar) \<in> (mgu_source P)\<^sup>*"
    by (rule no_trace_sound[where fuel=fuel and steps=initial_steps])
      (use checked in \<open>simp add: lpc_no_check_source_def\<close>)
  have no: "\<not> SN_on (mgu_source P)
    {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
  proof
    assume sn: "SN_on (mgu_source P)
      {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
    have included: "{lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}
      \<subseteq> (mgu_source P)\<^sup>* ``
        {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
      using reach by auto
    have "SN_on (mgu_source P)
      {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
      by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
    then show False using pump by contradiction
  qed
  show ?thesis using checked no
    by (simp add: lpc_no_check_source_def lp_cut_state_map_def)
qed

end
end
