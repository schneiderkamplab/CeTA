theory LP_Cut_Domain_NO_Steps
  imports LP_Cut_Domain_NO_Renaming
begin

context cut_runtime_domain
begin


theorem no_resolve_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_resolve fuel P a gs c m es k V images successor"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a#gs) c m#es) LPIVar,
          lp_cut_state_eval successor LPIVar)\<in>mgu_source P"
proof -
  have index: "c<length P"
    and short: "\<forall>x\<in>vars_term a. length x<k" "lp_cut_short_goals k gs"
    and mgu: "lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
    using checked by (auto simp: lpc_no_resolve_def)
  have actual: "mgu_resolve (lp_ieval a LPIVar)
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) (fst (P!c)) (snd (P!c))
      (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
      (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (lp_prefix k x)) LPIVar)"
    by (rule checked_mgu_resolve[OF mgu short])
  show ?thesis
    using mgu_source.resolve[OF index actual, of m "lp_cut_state_eval es LPIVar"] checked
    by (simp add: lpc_no_resolve_def lp_cut_state_map_def map_map o_def
      lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

theorem no_resolve_swap_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_resolve_swap fuel P a gs c m es k V images x y successor"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a#gs) c m#es) LPIVar,
          lp_cut_state_eval successor LPIVar)\<in>mgu_source P"
proof -
  have index: "c<length P"
    and short: "\<forall>v\<in>vars_term a. length v<k" "lp_cut_short_goals k gs"
    and mgu: "lpc_check_mgu fuel [(a,fst (P!c)\<cdot>(\<lambda>v. Var (lp_prefix k v)))] V images"
    using checked by (auto simp: lpc_no_resolve_swap_def)
  have actual: "mgu_resolve (lp_ieval a LPIVar)
      (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) (fst (P!c)) (snd (P!c))
      (\<lambda>v. lp_ieval (lpc_mgu_substitution V images v) LPIVar)
      (\<lambda>v. lp_ieval (lpc_mgu_substitution V images (lp_prefix k v)) LPIVar)"
    by (rule checked_mgu_resolve[OF mgu short])
  show ?thesis
    using mgu_source.resolve[OF index mgu_resolve_output_swap[OF actual, of x y],
      of m "lp_cut_state_eval es LPIVar"] checked
    by (simp add: lpc_no_resolve_swap_def lp_cut_state_map_def map_map o_def
      lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

lemma no_admin_sound:
  "lp_cut_check_admin s t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>mgu_source P"
  by (rule mgu_source.admin)
    (simp add: lp_cut_check_admin_def lp_cut_admin_map)

lemma no_case_sound:
  assumes checked: "lp_cut_check_case P m f ts gs es successor"
  shows "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) LPIVar,
          lp_cut_state_eval successor LPIVar)\<in>mgu_source P"
proof -
  have fresh: "lp_cut_fresh m
      (lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) LPIVar)"
    using checked by (simp add: lp_cut_check_case_def)
  show ?thesis using mgu_source.case_call[of m f "map (\<lambda>t. lp_ieval t LPIVar) ts"
    "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs" "lp_cut_state_eval es LPIVar" P] fresh checked
    by (simp add: lp_cut_check_case_def lp_cut_state_map_def map_map o_def)
qed

lemma no_meta_sound:
  assumes checked: "lp_cut_check_meta m a gs es body"
  shows "(lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#es) LPIVar,
          lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) LPIVar)\<in>mgu_source P"
proof -
  have fresh: "lp_cut_fresh m (lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#es) LPIVar)"
    using checked by (simp add: lp_cut_check_meta_def)
  have lower: "lp_cut_lower m (lp_ieval a LPIVar) (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) body)"
    by (rule lp_cut_lower_finite_sound) (use checked in \<open>simp add: lp_cut_check_meta_def\<close>)
  have callable: "\<exists>f ts. lp_ieval a LPIVar = LPIFun f ts"
    using checked by (cases a) (auto simp: lp_cut_check_meta_def)
  show ?thesis using mgu_source.meta[OF _ lower callable, of "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
    "lp_cut_state_eval es LPIVar" P] fresh
    by (simp add: lp_cut_state_map_def)
qed

lemma no_unify_sound:
  assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
  shows "(lp_cut_state_eval (LPCGoals (LPCUnify a b#gs)#es) LPIVar,
    lp_cut_state_eval (LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) gs)#es) LPIVar)
    \<in>mgu_source P"
  using mgu_source.unify[OF checked_mgu_unify[OF checked, of gs],
    of "lp_cut_state_eval es LPIVar" P]
  by (simp add: lp_cut_state_map_def map_map o_def lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst)

lemma no_backtrack_sound:
  assumes "c<length P" "lp_cut_check_clash fuel k a (fst (P!c))"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a#gs) c m#es) LPIVar,
    lp_cut_state_eval es LPIVar)\<in>mgu_source P"
  using mgu_source.backtrack[OF assms(1) lp_cut_check_clash_sound[OF assms(2), where \<eta>=LPIVar],
    of "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs" m "lp_cut_state_eval es LPIVar"]
  by (simp add: lp_cut_state_map_def)

lemma no_unify_fail_sound:
  assumes "lp_cut_check_equality fuel a b LPCAlwaysFailure"
  shows "(lp_cut_state_eval (LPCGoals (LPCUnify a b#gs)#es) LPIVar,
    lp_cut_state_eval es LPIVar)\<in>mgu_source P"
  using mgu_source.unify_fail[OF lp_cut_equality_failure[OF assms, where \<eta>=LPIVar],
    of "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs" "lp_cut_state_eval es LPIVar"]
  by (simp add: lp_cut_state_map_def)

theorem no_step_sound:
  "lpc_no_step fuel P s action t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>mgu_source P"
  by (induct fuel P s action t rule: lpc_no_step.induct)
    (auto intro: no_admin_sound no_case_sound no_meta_sound no_resolve_sound no_resolve_swap_sound no_unify_sound
      no_backtrack_sound no_unify_fail_sound)

theorem no_trace_sound:
  "lpc_no_trace fuel P s steps t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>(mgu_source P)\<^sup>*"
proof (induct steps arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons entry rest)
  obtain action u where entry: "entry=(action,u)" by (cases entry) auto
  have step: "(lp_cut_state_eval s LPIVar,lp_cut_state_eval u LPIVar)\<in>mgu_source P"
    using Cons.prems entry by (auto intro: no_step_sound)
  have tail: "(lp_cut_state_eval u LPIVar,lp_cut_state_eval t LPIVar)\<in>(mgu_source P)\<^sup>*"
    using Cons.hyps Cons.prems entry by auto
  show ?case using step tail by (meson r_into_rtrancl rtrancl_trans)
qed

theorem no_trace_progress:
  assumes checked: "lpc_no_trace fuel P s steps t" and nonempty: "steps\<noteq>[]"
  shows "(lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>(mgu_source P)\<^sup>+"
proof -
  obtain action u rest where steps: "steps=(action,u)#rest"
    using nonempty by (cases steps) auto
  have first: "(lp_cut_state_eval s LPIVar,lp_cut_state_eval u LPIVar)\<in>mgu_source P"
    using checked steps by (auto intro: no_step_sound)
  have tail: "(lp_cut_state_eval u LPIVar,lp_cut_state_eval t LPIVar)\<in>(mgu_source P)\<^sup>*"
    using checked steps by (auto intro: no_trace_sound)
  show ?thesis using first tail by (meson rtrancl_into_trancl2)
qed

theorem no_exact_cycle_sound:
  assumes checked: "lpc_no_trace fuel P s steps s" and nonempty: "steps\<noteq>[]"
  shows "\<not>SN_on (mgu_source P) {lp_cut_state_eval s LPIVar}"
  using no_trace_progress[OF checked nonempty]
  by (meson SN_on_irrefl SN_on_trancl singletonI)


end
end
