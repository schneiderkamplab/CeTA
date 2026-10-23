theory LP_Cut_Instance
  imports LP_Cut_Scope_Source LP_Cut_Knowledge
begin

fun lp_cut_scope_word where
  "lp_cut_scope_word [] s = s"
| "lp_cut_scope_word ((a,b)#rs) s =
    lp_cut_scope_word rs (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s)"

lemma lp_cut_scope_word_SN:
  assumes program: "lp_cut_source_program P" and sn: "SN_on (lp_cut_source P) {s}"
  shows "SN_on (lp_cut_source P) {lp_cut_scope_word rs s}"
  using sn
proof (induct rs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons ab rs)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "SN_on (lp_cut_source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
    by (rule lp_cut_scope_swap_preserves_SN[OF program Cons.prems])
  show ?case using Cons.hyps[OF first] by (simp add: ab)
qed

lemma lp_cut_scope_entry_map:
  "lp_cut_scope_entry r (lp_cut_entry_map f e) =
    lp_cut_entry_map f (lp_cut_scope_entry r e)"
  by (cases e) (simp_all add: map_map o_def lp_cut_scope_goal_map)

lemma lp_cut_scope_word_map:
  "lp_cut_scope_word rs (lp_cut_state_map f s) =
    lp_cut_state_map f (lp_cut_scope_word rs s)"
proof (induct rs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons ab rs)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have commute: "map (lp_cut_scope_entry (lp_cut_scope_swap a b))
      (lp_cut_state_map f s) = lp_cut_state_map f
      (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s)"
    by (simp add: lp_cut_state_map_def map_map o_def lp_cut_scope_entry_map)
  show ?case by (simp only: ab lp_cut_scope_word.simps commute Cons.hyps)
qed

fun lp_cut_guard_subst where
  "lp_cut_guard_subst \<mu> (LPCHeadGuard a h b) = LPCHeadGuard (a\<cdot>\<mu>) h b"
| "lp_cut_guard_subst \<mu> (LPCEqGuard a c b) = LPCEqGuard (a\<cdot>\<mu>) (c\<cdot>\<mu>) b"

lemma lp_cut_guard_subst_holds:
  "lp_cut_guard_holds (lp_cut_guard_subst \<mu> g) \<eta> =
    lp_cut_guard_holds g (\<lambda>x. lp_ieval (\<mu> x) \<eta>)"
  by (cases g) (simp_all add: lp_ieval_finite_subst)

definition lp_cut_instance_subst where
  "lp_cut_instance_subst bindings x = (case map_of bindings x of None\<Rightarrow>Var x | Some t\<Rightarrow>t)"

definition lp_cut_check_instance where
  "lp_cut_check_instance s G guards t H guards' bindings swaps =
    (let \<mu>=lp_cut_instance_subst bindings in
      s=lp_cut_scope_word swaps (lp_cut_state_map (\<lambda>u. u\<cdot>\<mu>) t) \<and>
      list_all (\<lambda>x. vars_term (\<mu> x) \<subseteq> set G) H \<and>
      list_all (\<lambda>g. lp_cut_guard_subst \<mu> g\<in>set guards) guards')"

lemma lp_cut_entry_eval_subst:
  "lp_cut_entry_map (\<lambda>u. lp_ieval u \<eta>)
      (lp_cut_entry_map (\<lambda>u. u\<cdot>\<mu>) e) =
    lp_cut_entry_map (\<lambda>u. lp_ieval u (\<lambda>x. lp_ieval (\<mu> x) \<eta>)) e"
  by (cases e) (simp_all add: map_map o_def lp_cut_map_comp lp_ieval_finite_subst)

lemma lp_cut_state_eval_subst:
  "lp_cut_state_eval (lp_cut_state_map (\<lambda>u. u\<cdot>\<mu>) t) \<eta> =
    lp_cut_state_eval t (\<lambda>x. lp_ieval (\<mu> x) \<eta>)"
  by (simp add: lp_cut_state_map_def map_map o_def lp_cut_entry_eval_subst)

theorem lp_cut_checked_instance_knowledge:
  assumes checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and knowledge: "lp_cut_knowledge (set G) guards \<eta>"
  shows "lp_cut_knowledge (set H) guards'
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  have ground: "\<forall>x\<in>set H. lp_seg_ground (lp_ieval (?mu x) \<eta>)"
    using checked knowledge
    by (auto simp: lp_cut_check_instance_def Let_def lp_cut_knowledge_def
      lp_seg_ground_eval list_all_iff)
  have guards: "\<And>g. g\<in>set guards' \<Longrightarrow>
    lp_cut_guard_holds g (\<lambda>x. lp_ieval (?mu x) \<eta>)"
  proof -
    fix g assume member: "g\<in>set guards'"
    have in_source: "lp_cut_guard_subst ?mu g\<in>set guards"
      using checked member by (auto simp: lp_cut_check_instance_def Let_def list_all_iff)
    have "lp_cut_guard_holds (lp_cut_guard_subst ?mu g) \<eta>"
      using knowledge in_source by (auto simp: lp_cut_knowledge_def list_all_iff)
    then show "lp_cut_guard_holds g (\<lambda>x. lp_ieval (?mu x) \<eta>)"
      by (simp only: lp_cut_guard_subst_holds)
  qed
  show ?thesis using ground guards by (auto simp: lp_cut_knowledge_def list_all_iff)
qed

theorem lp_cut_checked_instance_SN:
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and sn: "SN_on (lp_cut_source P)
      {lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)}"
  shows "SN_on (lp_cut_source P) {lp_cut_state_eval s \<eta>}"
proof -
  have source: "s=lp_cut_scope_word swaps
      (lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst bindings) t)"
    using checked by (auto simp: lp_cut_check_instance_def Let_def)
  have shape: "lp_cut_state_eval s \<eta> = lp_cut_scope_word swaps
      (lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>))"
    by (simp add: source lp_cut_scope_word_map[symmetric]
      lp_cut_state_eval_subst)
  show ?thesis using lp_cut_scope_word_SN[OF program sn, of swaps] shape by simp
qed

text \<open>Instance edges are proof obligations, not zero-cost cycle removal.
Their residual clause is checked separately, so cyclic instance-only graphs
cannot be accepted by structural closure alone.\<close>

end
