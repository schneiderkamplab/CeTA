theory LP_Cut_Domain_NO_Finite
  imports LP_Cut_Domain_NO_Shape LP_Cut_Fresh_Representation LP_Cut_Domain_NO_Certificate
begin

text \<open>Checked witness substitutions have finite images. This invariant
retains finite variable support through the witness relation and its pumping
construction, including in the rational and unrestricted domains.\<close>
abbreviation cut_goal_finite where
  "cut_goal_finite g \<equiv> list_all cut_finite_runtime (lp_cut_terms g)"
fun cut_choice_finite where
  "cut_choice_finite (LPCGoals gs) = list_all cut_goal_finite gs"
| "cut_choice_finite (LPCClause gs c m) = list_all cut_goal_finite gs"
| "cut_choice_finite (LPCBarrier m) = True"
lemma cut_finite_goal_subst:
  "cut_goal_finite g \<Longrightarrow> (\<And>x. cut_finite_runtime (s x)) \<Longrightarrow>
    cut_goal_finite (lp_cut_map (\<lambda>t. lp_isubst t s) g)"
  by (cases g) (auto intro: cut_finite_substitute)
lemma cut_finite_goal_bind:
  "(\<And>x. cut_finite_runtime (s x)) \<Longrightarrow>
    cut_goal_finite (lp_cut_bind m (\<lambda>t. lp_ieval t s) g)"
  by (cases g) (auto intro: cut_domain_eval[where D=cut_finite_runtime, OF _ cut_finite_function])
lemma cut_finite_lower:
  "lp_cut_lower m a gs \<Longrightarrow> cut_finite_runtime a \<Longrightarrow>
    list_all cut_goal_finite gs"
  by (induct rule: lp_cut_lower.induct)
    (auto dest: cut_finite_arguments)
lemma cut_finite_prune:
  "list_all cut_choice_finite es \<Longrightarrow> list_all cut_choice_finite (lp_cut_prune m es)"
  by (induct es) (auto split: lp_cut_entry.splits)
lemma cut_finite_admin:
  "lp_cut_admin s = Some t \<Longrightarrow> list_all cut_choice_finite s \<Longrightarrow>
    list_all cut_choice_finite t"
  by (induct s rule: lp_cut_admin.induct)
    (auto intro: cut_finite_prune split: lp_cut_goal.splits)

lemma cut_finite_bind_terms:
  "lp_cut_terms (lp_cut_bind m f g) = map f (lp_cut_terms g)"
  by (cases g) simp_all

context cut_runtime_domain
begin
lemma no_step_finite:
  assumes step: "(s,t)\<in>mgu_source P"
    and finite: "list_all cut_choice_finite s"
  shows "list_all cut_choice_finite t"
  using step finite
proof (cases rule: mgu_source.cases)
  case (resolve c a gs sigma rho m es)
  have rho: "\<And>x. cut_finite_runtime (rho x)" and sigma: "\<And>x. cut_finite_runtime (sigma x)"
    using resolve by auto
  have eval: "cut_finite_runtime (lp_ieval u rho)" for u
    by (rule cut_domain_eval[OF rho cut_finite_function])
  have subst: "cut_finite_runtime (lp_isubst u sigma)" if "cut_finite_runtime u" for u
    by (rule cut_finite_substitute[OF that sigma])
  show ?thesis using resolve finite
    by (auto simp: list_all_iff lp_cut_terms_mapped cut_finite_bind_terms intro!: eval subst)
qed (auto simp: list_all_iff lp_cut_terms_mapped cut_finite_bind_terms
  intro: cut_finite_substitute
  dest: cut_finite_admin[unfolded list_all_iff] cut_finite_lower[unfolded list_all_iff])

lemma no_run_finite:
  fixes sequence :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes start: "list_all cut_choice_finite (sequence 0)"
    and steps: "\<And>n. (sequence n,sequence (Suc n))\<in>mgu_source P"
  shows "list_all cut_choice_finite (sequence n)"
  by (induct n) (rule start, rule no_step_finite[OF steps], assumption)

lemma no_checked_finite_run:
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
  obtains sequence where
    "sequence 0 = [LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
    "\<And>n. (sequence n,sequence (Suc n))\<in>mgu_source P"
    "\<And>n. list_all cut_choice_finite (sequence n)"
proof -
  have no: "\<not> SN_on (mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
    using no_check_source_sound[OF checked] by blast
  obtain sequence where start:
      "sequence 0 = [LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
    and steps: "\<And>n. (sequence n,sequence (Suc n))\<in>mgu_source P"
    using no unfolding SN_on_def by blast
  have initial: "list_all cut_choice_finite (sequence 0)"
    by (simp add: start cut_finite_function list_all_iff)
  have finite: "list_all cut_choice_finite (sequence n)" for n
    by (rule no_run_finite[OF initial steps])
  show thesis by (rule that[OF start steps finite])
qed
end

lemma cut_finite_variable_support:
  "cut_finite_runtime (cut_tree t) \<Longrightarrow> finite (logic_variables t)"
  by (simp add: cut_finite_domain_iff logic_variables_def logic_finite_variables_finite)


lemma cut_finite_goal_support:
  "cut_goal_finite (cut_igoal g) \<Longrightarrow> t\<in>set (logic_goal_terms g) \<Longrightarrow>
    finite (logic_variables t)"
  by (cases g) (auto simp: list_all_iff intro!: cut_finite_variable_support
    dest: cut_finite_arguments[unfolded list_all_iff] split: logic_atom.splits)

ML \<open>
  val results = @{thms cut_runtime_domain.no_checked_finite_run
    cut_runtime_domain.no_step_finite cut_finite_goal_support}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut finite witnesses: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut finite witnesses: oracle dependencies: " ^ commas names)
\<close>

end
