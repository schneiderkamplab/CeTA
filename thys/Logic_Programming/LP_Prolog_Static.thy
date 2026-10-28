theory LP_Prolog_Static
  imports LP_Prolog_Errors
begin

text \<open>Static source isolation shares the LP-with-cut machine, including
rational substitutions and ordered alternatives. No relation is assumed for
external builtins: the theorem excludes their reachability instead. Predicate
identity includes arity. Meta-calls and dynamic expansion are excluded.\<close>

fun lpp_static_goal where
  "lpp_static_goal A (LPCAtom a) = (\<exists>f ts. a=LPIFun (LPCUser f) ts \<and> (f,length ts)\<in>A)"
| "lpp_static_goal A (LPCMeta a) = False"
| "lpp_static_goal A (LPCExpand a m) = False"
| "lpp_static_goal A g = True"

fun lpp_static_template where
  "lpp_static_template A (LPCAtom a) = (\<exists>f ts. a=Fun (LPCUser f) ts \<and> (f,length ts)\<in>A)"
| "lpp_static_template A (LPCMeta a) = False"
| "lpp_static_template A (LPCExpand a m) = False"
| "lpp_static_template A g = True"

fun lpp_static_entry where
  "lpp_static_entry A (LPCGoals gs) = list_all (lpp_static_goal A) gs"
| "lpp_static_entry A (LPCClause gs c m) = list_all (lpp_static_goal A) gs"
| "lpp_static_entry A (LPCBarrier m) = True"

definition lpp_static_state where
  "lpp_static_state A s = list_all (lpp_static_entry A) s"

definition lpp_static_program where
  "lpp_static_program A P = list_all (\<lambda>c. list_all (lpp_static_template A) (snd c)) P"

lemma lpp_static_substitute:
  "lpp_static_goal A g \<Longrightarrow> lpp_static_goal A (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>) g)"
  by (cases g) auto

lemma lpp_static_evaluate:
  "lpp_static_template A g \<Longrightarrow> lpp_static_goal A (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>) g)"
  by (cases g) auto

lemma lpp_static_prune:
  "lpp_static_state A es \<Longrightarrow> lpp_static_state A (lp_cut_prune m es)"
  by (induct es) (auto simp: lpp_static_state_def split: lp_cut_entry.splits if_splits)

lemma lpp_static_admin:
  "lp_cut_admin s = Some t \<Longrightarrow> lpp_static_state A s \<Longrightarrow> lpp_static_state A t"
  by (induct s rule: lp_cut_admin.induct)
    (auto simp: lpp_static_state_def split: lp_cut_goal.splits intro: lpp_static_prune[unfolded lpp_static_state_def])

lemma lpp_static_source_preserved:
  assumes "(s,t)\<in>lp_cut_source P" "lpp_static_program A P" "lpp_static_state A s"
  shows "lpp_static_state A t"
  using assms
  by (cases rule: lp_cut_source.cases;
    auto simp: lpp_static_state_def lpp_static_program_def list_all_iff
      intro: lpp_static_substitute lpp_static_evaluate
      dest: lpp_static_admin[unfolded lpp_static_state_def]; metis nth_mem lpp_static_evaluate)

lemma lpp_static_mgu_preserved:
  "(s,t)\<in>lp_cut_mgu_source P \<Longrightarrow> lpp_static_program A P \<Longrightarrow>
   lpp_static_state A s \<Longrightarrow> lpp_static_state A t"
  using lp_cut_mgu_source_subset lpp_static_source_preserved by blast

definition lpp_builtin_active where
  "lpp_builtin_active B s = (\<exists>f ts gs es.
    s=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es \<and> (f,length ts)\<in>B)"

lemma lpp_static_no_builtin:
  "lpp_static_state A s \<Longrightarrow> A\<inter>B={} \<Longrightarrow> \<not>lpp_builtin_active B s"
  by (auto simp: lpp_builtin_active_def lpp_static_state_def)

text \<open>Overapproximation for termination: ordinary source steps, arbitrary
external transitions at builtin calls, and uncaught terminal errors. This is
not a nontermination semantics.\<close>
definition lp_prolog_extension where
  "lp_prolog_extension P B X E = lp_prolog_stop_extension
    (lp_cut_mgu_source P \<union> {(s,t)\<in>X. lpp_builtin_active B s}) E"

lemma lp_prolog_static_coverage:
  assumes "lpp_static_state A s" "A\<inter>B={}" "(s,t)\<in>lp_prolog_extension P B X E"
  shows "(s,t)\<in>lp_prolog_stop_extension (lp_cut_mgu_source P) E"
  using assms lpp_static_no_builtin
  by (auto simp: lp_prolog_extension_def lp_prolog_stop_extension_def)

lemma lp_prolog_static_preserved:
  assumes "lpp_static_state A s" "lpp_static_program A P" "A\<inter>B={}"
    "(s,t)\<in>lp_prolog_extension P B X E"
  shows "lpp_static_state A t"
  using lp_prolog_static_coverage[OF assms(1,3,4)] assms(1,2) lpp_static_mgu_preserved
  by (auto simp: lp_prolog_stop_extension_def lpp_static_state_def)

theorem lp_prolog_static_termination:
  assumes sn: "SN_on (lp_cut_mgu_source P) {s}"
    and safe: "lpp_static_state A s"
    and program: "lpp_static_program A P"
    and disjoint: "A\<inter>B={}"
  shows "SN_on (lp_prolog_extension P B X E) {s}"
proof -
  have base: "SN_on (lp_prolog_stop_extension (lp_cut_mgu_source P) E) {s}"
    by (rule lp_prolog_uncaught_errors_preserve_termination[OF sn])
  have "lpp_static_state A s \<longrightarrow> SN_on (lp_prolog_extension P B X E) {s}"
  proof (rule SN_on_induct[OF base singletonI], intro impI)
    fix x
    assume ih: "\<And>y. (x,y)\<in>lp_prolog_stop_extension (lp_cut_mgu_source P) E \<Longrightarrow>
      lpp_static_state A y \<longrightarrow> SN_on (lp_prolog_extension P B X E) {y}"
    assume sx: "lpp_static_state A x"
    show "SN_on (lp_prolog_extension P B X E) {x}"
      by (rule step_reflects_SN_on)
        (use ih lp_prolog_static_coverage[OF sx disjoint]
          lp_prolog_static_preserved[OF sx program disjoint] in blast)
  qed
  then show ?thesis using safe by blast
qed

end
