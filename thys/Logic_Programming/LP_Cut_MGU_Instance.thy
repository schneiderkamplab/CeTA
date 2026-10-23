theory LP_Cut_MGU_Instance
  imports LP_Cut_MGU_Scopes LP_Cut_Instance
begin

lemma lpc_mgu_scope_word_SN:
  assumes program: "lp_cut_source_program P" and sn: "SN_on (lp_cut_mgu_source P) {s}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_scope_word rs s}"
  using sn
proof (induct rs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons ab rs)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "SN_on (lp_cut_mgu_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
    by (rule lpc_mgu_scope_swap_preserves_SN[OF program Cons.prems])
  show ?case using Cons.hyps[OF first] by (simp add: ab)
qed

theorem lpc_mgu_checked_instance_SN:
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and sn: "SN_on (lp_cut_mgu_source P)
      {lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)}"
  shows "SN_on (lp_cut_mgu_source P) {lp_cut_state_eval s \<eta>}"
proof -
  have source: "s=lp_cut_scope_word swaps
      (lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst bindings) t)"
    using checked by (auto simp: lp_cut_check_instance_def Let_def)
  have shape: "lp_cut_state_eval s \<eta> = lp_cut_scope_word swaps
      (lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>))"
    by (simp add: source lp_cut_scope_word_map[symmetric] lp_cut_state_eval_subst)
  show ?thesis using lpc_mgu_scope_word_SN[OF program sn, of swaps] shape by simp
qed

definition lpc_check_free_instance where
  "lpc_check_free_instance F H bindings =
    (let \<mu>=lp_cut_instance_subst bindings in
      list_all (\<lambda>x. is_Var (\<mu> x) \<and> the_Var (\<mu> x)\<in>set F) H \<and>
      distinct H \<and> distinct (map \<mu> H))"

theorem lpc_checked_instance_free_knowledge:
  assumes checked: "lpc_check_free_instance F H bindings"
    and known: "lpc_free_knowledge (set F) \<eta>"
  shows "lpc_free_knowledge (set H) (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  have variable: "\<And>x. x\<in>set H \<Longrightarrow> \<exists>y\<in>set F. ?mu x=Var y"
  proof -
    fix x assume "x\<in>set H"
    then have "is_Var (?mu x)" "the_Var (?mu x)\<in>set F"
      using checked by (auto simp: lpc_check_free_instance_def Let_def list_all_iff)
    then show "\<exists>y\<in>set F. ?mu x=Var y" by (cases "?mu x") auto
  qed
  have mu_injective: "inj_on ?mu (set H)"
    using checked by (simp add: lpc_check_free_instance_def Let_def distinct_map)
  have eta_injective: "inj_on \<eta> (set F)" using known by (simp add: lpc_free_knowledge_def)
  have free: "\<And>x. x\<in>set H \<Longrightarrow> \<exists>y. lp_ieval (?mu x) \<eta> = LPIVar y"
  proof -
    fix x assume "x\<in>set H"
    then obtain y where y: "y\<in>set F" "?mu x=Var y" using variable by blast
    obtain z where "\<eta> y=LPIVar z" using known y(1) by (auto simp: lpc_free_knowledge_def)
    then show "\<exists>z. lp_ieval (?mu x) \<eta> = LPIVar z" by (auto simp: y(2))
  qed
  have injective: "inj_on (\<lambda>x. lp_ieval (?mu x) \<eta>) (set H)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>set H" and y: "y\<in>set H"
      and same: "lp_ieval (?mu x) \<eta> = lp_ieval (?mu y) \<eta>"
    obtain u where u: "u\<in>set F" "?mu x=Var u" using variable[OF x] by blast
    obtain v where v: "v\<in>set F" "?mu y=Var v" using variable[OF y] by blast
    have "\<eta> u=\<eta> v" using same u v by simp
    then have "u=v" using eta_injective u(1) v(1) by (auto simp: inj_on_def)
    then have "?mu x=?mu y" using u v by simp
    then show "x=y" using mu_injective x y by (auto simp: inj_on_def)
  qed
  show ?thesis using free injective by (auto simp: lpc_free_knowledge_def)
qed

lemma lpc_free_instance_rejects_alias:
  "x\<noteq>y \<Longrightarrow> \<not>lpc_check_free_instance [z] [x,y] [(x,Var z),(y,Var z)]"
  by (simp add: lpc_check_free_instance_def lp_cut_instance_subst_def)

end
