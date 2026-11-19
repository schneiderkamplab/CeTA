theory LP_Cut_Ranked_Forward
  imports LP_Cut_Ranked_Erasure
begin

abbreviation cut_erased_state ::
  "('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_choice list \<Rightarrow>
    ('f lp_cut_symbol,'v) lp_iterm lp_cut_entry list" where
  "cut_erased_state s \<equiv> cut_state (map cut_unrank_choice s)"
lemma cut_erased_fresh[simp]: "lp_cut_fresh m (cut_erased_state s) = logic_fresh_mark m s"
  by (simp only: cut_fresh cut_unrank_fresh)
lemma cut_erased_admin:
  "lp_cut_admin (cut_erased_state s) = map_option cut_erased_state (logic_admin s)"
  by (simp only: cut_admin cut_unrank_admin; cases "logic_admin s"; simp)

context cut_runtime_domain
begin

lemma ranked_fresh_failure:
  assumes fresh: "logic_freshening r (logic_arguments a @ active)
      (logic_arguments (cut_rank_atom h) @ body)"
    and caller: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
    and clause: "list_all (arity_correct (logic_symbol_arity snd)) (logic_arguments (cut_rank_atom h))"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and failure: "\<not>(\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
        logic_tree_arity_correct (logic_symbol_arity snd) t) s \<and>
      logic_atom_map (logic_subst s) a =
        logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h))"
  shows "\<not>(\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom (cut_unrank_atom a)) s = lp_ieval (cut_head h) r)"
proof
  assume "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom (cut_unrank_atom a)) s = lp_ieval (cut_head h) r"
  then obtain s t where sd: "logic_substitution_in (\<lambda>t. D (cut_tree t)) s"
    and td: "logic_substitution_in (\<lambda>t. D (cut_tree t)) t"
    and eq: "logic_atom_map (logic_subst s) (cut_unrank_atom a) = logic_atom_map (logic_eval t) h"
    using atom_unifiable_iff by blast
  have inverse: "cut_rank_runtime_atom (cut_unrank_atom a) = a" by (rule cut_rank_unrank_atom[OF caller])
  have correct: "list_all (logic_tree_arity_correct (logic_symbol_arity snd)) (logic_arguments a)"
    using caller by (cases a) simp
  have unifies: "\<exists>u. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) u \<and>
    logic_atom_map (logic_subst u) a =
      logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) (cut_rank_atom h)"
    apply (subst inverse[symmetric])
    apply (rule cut_rank_typed_fresh_unifier[where D="\<lambda>t. D (cut_tree t)" and z=undefined,
      OF _ _ clause sd td _ eq])
    using fresh apply (simp only: inverse)
    using correct apply (simp only: inverse)
    by (rule projection; assumption)
  show False using failure unifies by blast
qed

lemma ranked_equalizer_failure:
  assumes left: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and right: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and failure: "\<not>(\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) s \<and> logic_subst s a = logic_subst s b)"
  shows "\<not>(\<exists>s. (\<forall>x. D (s x)) \<and>
    lp_isubst (cut_tree (cut_unrank_tree a)) s = lp_isubst (cut_tree (cut_unrank_tree b)) s)"
proof
  assume "\<exists>s. (\<forall>x. D (s x)) \<and>
    lp_isubst (cut_tree (cut_unrank_tree a)) s = lp_isubst (cut_tree (cut_unrank_tree b)) s"
  then obtain s where sd: "logic_substitution_in (\<lambda>t. D (cut_tree t)) s"
    and eq: "logic_subst s (cut_unrank_tree a) = logic_subst s (cut_unrank_tree b)"
    using equalizable_iff by blast
  have ia: "cut_rank_tree (cut_unrank_tree a) = a" by (rule cut_rank_unrank_tree[OF left])
  have ib: "cut_rank_tree (cut_unrank_tree b) = b" by (rule cut_rank_unrank_tree[OF right])
  have unifies: "\<exists>u. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) u \<and> logic_subst u a = logic_subst u b"
    apply (subst ia[symmetric], subst ib[symmetric])
    apply (rule cut_rank_typed_equalizer[where D="\<lambda>t. D (cut_tree t)" and z=undefined,
      OF _ _ sd _ eq])
    using left apply (simp only: ia)
    using right apply (simp only: ib)
    by (rule projection; assumption)
  show False using failure unifies by blast
qed

lemma ranked_forward_step:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem snd (cut_rank_program P) p modes"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and correct: "logic_runtime_state_correct snd s"
    and step: "logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) s t"
  shows "(cut_erased_state s,cut_erased_state t) \<in> source (cut_program P)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  show ?thesis by (rule source.admin) (simp only: cut_erased_admin admin option.map)
next
  case (case_call m f ts gs es)
  obtain f0 k where f: "f=(f0,k)" by (cases f) auto
  have len: "length ts=k" using correct case_call by (simp add: f)
  have fresh: "lp_cut_fresh m (cut_erased_state (LogicGoals (LogicAtom (LAtom f ts)#gs)#es))"
    using case_call by (simp only: cut_erased_fresh)
  show ?thesis using source.case_call[OF fresh[unfolded f, simplified], where P="cut_program P"] case_call
    by (simp add: f len cut_rank_slice cut_slice map_map o_def)
next
  case (resolve c ren a gs sigma m es)
  have original_index: "c<length P" using resolve by (simp add: cut_rank_program_def)
  have index: "c<length (cut_program P)" using original_index by simp
  have eval_comp: "logic_subst sigma \<circ> logic_eval (LVar \<circ> ren) = logic_eval (sigma \<circ> ren)"
    by (rule ext) (simp add: logic_subst_composition o_def)
  have eq: "logic_atom_map (logic_subst sigma) a =
      logic_atom_map (logic_eval (sigma \<circ> ren)) (cut_rank_atom (fst (P!c)))"
    using resolve by (auto simp: logic_mgu_def logic_atom_map_comp eval_comp cut_rank_program_nth[OF original_index])
  have erased_eq: "logic_atom_map (logic_subst (cut_unrank_tree \<circ> sigma)) (cut_unrank_atom a) =
      logic_atom_map (logic_eval (cut_unrank_tree \<circ> sigma \<circ> ren)) (fst (P!c))"
    using arg_cong[OF eq, where f=cut_unrank_atom]
    by (simp add: cut_unrank_atom_subst cut_unrank_rank_atom_eval o_assoc)
  have native_eq: "lp_isubst (cut_atom (cut_unrank_atom a)) (cut_tree \<circ> cut_unrank_tree \<circ> sigma) =
      lp_ieval (fst (cut_program P!c)) (cut_tree \<circ> cut_unrank_tree \<circ> sigma \<circ> ren)"
    using arg_cong[OF erased_eq, where f=cut_atom]
    by (simp add: cut_program_nth[OF original_index] cut_atom_subst cut_head_eval o_assoc)
  have ds: "\<forall>x. D ((cut_tree \<circ> cut_unrank_tree \<circ> sigma) x)"
    and dr: "\<forall>x. D ((cut_tree \<circ> cut_unrank_tree \<circ> sigma \<circ> ren) x)"
    using resolve by (auto simp: logic_mgu_def logic_substitution_in_def)
  show ?thesis using source.resolve[OF index native_eq ds dr,
    where m=m and gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] resolve
    by (simp add: cut_program_nth[OF original_index] cut_rank_program_nth[OF original_index]
      eval_comp map_map o_def cut_unrank_goal_eval_bind cut_unrank_goal_subst
      cut_goal_subst cut_goal_eval_bind logic_subst_composition cut_atom_selectors)
next
  case (backtrack c ren a gs m)
  have original_index: "c<length P" using backtrack by (simp add: cut_rank_program_def)
  have index: "c<length (cut_program P)" using original_index by simp
  have head_atom: "logic_atom_correct snd (arity_correct (logic_symbol_arity snd))
      (cut_rank_atom (fst (P!c)))"
    using program nth_mem[of c "cut_rank_program P"] original_index
    by (auto simp: logic_cut_problem_def cut_rank_program_def case_prod_unfold)
  have head: "list_all (arity_correct (logic_symbol_arity snd)) (logic_arguments (cut_rank_atom (fst (P!c))))"
    using head_atom by (cases "cut_rank_atom (fst (P!c))") simp
  have caller: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
    using correct backtrack by (simp add: cut_atom_selectors)
  have fresh: "logic_freshening ren (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (cut_rank_atom (fst (P!c))) @ concat (map logic_goal_terms (map cut_rank_goal (snd (P!c)))))"
    using backtrack by (simp add: cut_rank_program_nth[OF original_index])
  have failed: "\<not>(\<exists>sigma. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) sigma \<and>
    logic_atom_map (logic_subst sigma) a =
      logic_atom_map (logic_subst sigma \<circ> logic_eval (LVar \<circ> ren)) (cut_rank_atom (fst (P!c))))"
    using backtrack by (simp add: cut_rank_program_nth[OF original_index])
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (cut_atom (cut_unrank_atom a)) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding cut_program_nth[OF original_index] fst_conv
    by (rule ranked_fresh_failure[OF fresh caller head projection failed])
  show ?thesis using source.backtrack[OF index failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and m=m and es="cut_erased_state t"] backtrack by (simp add: cut_atom_selectors)
next
  case (unify a b sigma gs es)
  have eq: "logic_subst sigma a = logic_subst sigma b" using unify by (auto simp: logic_mgu_def)
  have erased_eq: "logic_subst (cut_unrank_tree \<circ> sigma) (cut_unrank_tree a) =
      logic_subst (cut_unrank_tree \<circ> sigma) (cut_unrank_tree b)"
    using arg_cong[OF eq, where f=cut_unrank_tree] by (simp add: cut_unrank_subst)
  have native_eq: "lp_isubst (cut_tree (cut_unrank_tree a)) (cut_tree \<circ> cut_unrank_tree \<circ> sigma) =
      lp_isubst (cut_tree (cut_unrank_tree b)) (cut_tree \<circ> cut_unrank_tree \<circ> sigma)"
    using arg_cong[OF erased_eq, where f=cut_tree] by (simp add: cut_tree_subst o_assoc)
  have ds: "\<forall>x. D ((cut_tree \<circ> cut_unrank_tree \<circ> sigma) x)"
    using unify by (auto simp: logic_mgu_def logic_substitution_in_def)
  show ?thesis using source.unify[OF native_eq ds,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] unify
    by (simp add: map_map o_def cut_unrank_goal_subst cut_goal_subst)
next
  case (unify_fail a b gs)
  have ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    using correct unify_fail by simp_all
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> lp_isubst (cut_tree (cut_unrank_tree a)) sigma =
      lp_isubst (cut_tree (cut_unrank_tree b)) sigma)"
    by (rule ranked_equalizer_failure[OF ca cb projection]) (use unify_fail in auto)
  show ?thesis using source.unify_fail[OF failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_erased_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp only: cut_erased_fresh)
  have lower: "lp_cut_lower m (cut_tree (cut_unrank_tree (LFun f ts)))
      (map cut_igoal (map cut_unrank_goal body))"
    by (rule cut_lower, rule cut_unrank_lower) (use meta in blast)
  show ?thesis using source.meta[OF _ lower,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree (cut_unrank_tree a)) body)"
    by (rule cut_diverges_unlowerable, rule cut_unrank_lower_diverges) (use meta_diverges in blast)
  show ?thesis using source.meta_unlowerable[OF failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] meta_diverges by simp
qed

theorem ranked_termination:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem snd (cut_rank_program P) p modes"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and native: "\<And>ts :: (('f \<times> nat) logic_symbol,string) fo_term list.
      logic_query (logic_symbol_arity snd) (LogicUser p) modes (LAtom (LogicUser p) ts) \<Longrightarrow>
      SN_on (source (cut_program P)) {cut_erased_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]}"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (logic_symbol_arity snd) (LogicUser p) modes (LAtom (LogicUser p) ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) (s n) (s (Suc n))"
  have start_correct: "logic_runtime_state_correct snd (s 0)"
    using query by (simp add: init logic_query_def list_all_iff)
  have correct: "logic_runtime_state_correct snd (s n)" for n
    by (rule logic_cut_run_arity[where run=s and D="\<lambda>t. D (cut_tree (cut_unrank_tree t))", OF program start_correct]) (use steps in simp)
  have chain: "\<forall>n. ((cut_erased_state \<circ> s) n,(cut_erased_state \<circ> s) (Suc n)) \<in> source (cut_program P)"
    proof (intro allI)
    fix n
    show "((cut_erased_state \<circ> s) n,(cut_erased_state \<circ> s) (Suc n)) \<in> source (cut_program P)"
      unfolding o_apply by (rule ranked_forward_step[OF program _ correct]) (use projection steps in auto)
  qed
  have bad: "\<exists>f. f 0 \<in> {cut_erased_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]} \<and>
      (\<forall>n. (f n,f (Suc n)) \<in> source (cut_program P))"
    by (rule exI[of _ "cut_erased_state \<circ> s"], rule conjI) (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
ML \<open>
  val results = @{thms cut_runtime_domain.ranked_fresh_failure cut_runtime_domain.ranked_equalizer_failure cut_runtime_domain.ranked_forward_step cut_runtime_domain.ranked_termination}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked forward simulation: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked forward simulation: oracle dependency"
\<close>
end
