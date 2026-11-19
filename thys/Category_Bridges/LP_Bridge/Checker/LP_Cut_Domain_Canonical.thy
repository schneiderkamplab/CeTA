theory LP_Cut_Domain_Canonical
  imports LP_Cut_Domain_Table
    Category_LP_Bridge.LP_Cut_Execution_Representation
begin

lemma cut_native_embedded_substitution[simp]:
  "lp_isubst (cut_tree (logic_embed t)) s = lp_ieval (cut_term t) s"
  by (simp add: cut_tree_embed lp_ieval_subst)

context cut_runtime_domain
begin

lemma atom_unifiable_iff:
  "(\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r) \<longleftrightarrow>
   (\<exists>s r. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution_in (\<lambda>t. D (cut_tree t)) r \<and> logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h)"
proof
  assume "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r"
  then obtain s r where ds: "\<forall>x. D (s x)" and dr: "\<forall>x. D (r x)"
    and eq: "lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r" by blast
  have backward: "logic_atom_map (logic_subst (cut_tree_back \<circ> s)) a = logic_atom_map (logic_eval (cut_tree_back \<circ> r)) h"
    by (rule cut_atom_injective[THEN iffD1])
      (use eq in \<open>simp add: cut_atom_subst cut_head_eval o_def\<close>)
  show "\<exists>s r. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution_in (\<lambda>t. D (cut_tree t)) r \<and> logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h"
    by (rule exI[of _ "cut_tree_back \<circ> s"], rule exI[of _ "cut_tree_back \<circ> r"])
      (simp add: backward[unfolded o_def] logic_substitution_in_def o_def ds dr)
next
  assume "\<exists>s r. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and>
    logic_substitution_in (\<lambda>t. D (cut_tree t)) r \<and> logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h"
  then obtain s r where ds: "logic_substitution_in (\<lambda>t. D (cut_tree t)) s"
    and dr: "logic_substitution_in (\<lambda>t. D (cut_tree t)) r"
    and eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h" by blast
  have forward: "lp_isubst (cut_atom a) (cut_tree \<circ> s) = lp_ieval (cut_head h) (cut_tree \<circ> r)"
    using arg_cong[OF eq, where f=cut_atom] by (simp add: cut_atom_subst cut_head_eval)
  show "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r"
    by (rule exI[of _ "cut_tree \<circ> s"], rule exI[of _ "cut_tree \<circ> r"])
      (use ds dr forward in \<open>simp add: logic_substitution_in_def o_def\<close>)
qed

lemma equalizable_iff:
  "(\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s) \<longleftrightarrow>
    (\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b)"
proof
  assume "\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
  then obtain s where ds: "\<forall>x. D (s x)"
    and eq: "lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
  have backward: "logic_subst (cut_tree_back \<circ> s) a = logic_subst (cut_tree_back \<circ> s) b"
    by (rule cut_tree_injective[THEN iffD1]) (use eq in \<open>simp add: cut_tree_subst o_def\<close>)
  show "\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b"
    by (rule exI[of _ "cut_tree_back \<circ> s"])
      (simp add: backward[unfolded o_def] logic_substitution_in_def o_def ds)
next
  assume "\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree t)) s \<and> logic_subst s a = logic_subst s b"
  then obtain s where ds: "logic_substitution_in (\<lambda>t. D (cut_tree t)) s"
    and eq: "logic_subst s a = logic_subst s b" by blast
  have forward: "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_isubst (cut_tree b) (cut_tree \<circ> s)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  show "\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
    by (rule exI[of _ "cut_tree \<circ> s"])
      (use ds forward in \<open>simp add: logic_substitution_in_def o_def\<close>)
qed


lemma typed_fresh_failure:
  assumes fresh: "logic_freshening r (logic_arguments a @ active) (logic_arguments h @ body)"
    and caller: "logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) a"
    and clause: "logic_atom_correct A (arity_correct (logic_symbol_arity A)) h"
    and projection: "\<And>t. D (cut_tree t) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined t))"
    and failure: "\<not>(\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree t) \<and>
        logic_tree_arity_correct (logic_symbol_arity A) t) s \<and>
      logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) h)"
  shows "\<not>(\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r)"
proof
  assume "\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r"
  then obtain s t where sd: "logic_substitution_in (\<lambda>t. D (cut_tree t)) s"
    and td: "logic_substitution_in (\<lambda>t. D (cut_tree t)) t"
    and eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval t) h"
    using atom_unifiable_iff by blast
  have ca: "list_all (logic_tree_arity_correct (logic_symbol_arity A)) (logic_arguments a)"
    using caller by (cases a) simp
  have ch: "list_all (arity_correct (logic_symbol_arity A)) (logic_arguments h)"
    using clause by (cases h) simp
  have "\<exists>u. logic_substitution_in (\<lambda>x. D (cut_tree x) \<and> logic_tree_arity_correct (logic_symbol_arity A) x) u \<and>
    logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) h"
    by (rule logic_typed_fresh_unifier[where D="\<lambda>t. D (cut_tree t)" and z=undefined,
        OF fresh ca ch sd td projection eq])
  then show False using failure by blast
qed

lemma typed_equalizable_iff:
  assumes ca: "logic_tree_arity_correct (logic_symbol_arity A) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity A) b"
    and projection: "\<And>t. D (cut_tree t) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined t))"
  shows "(\<exists>s. (\<forall>x. D (s x)) \<and> lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s)
    \<longleftrightarrow> (\<exists>s. logic_substitution_in (\<lambda>t. D (cut_tree t) \<and>
      logic_tree_arity_correct (logic_symbol_arity A) t) s \<and> logic_subst s a = logic_subst s b)"
  using logic_arity_unifiable_iff[where D="\<lambda>t. D (cut_tree t)" and z=undefined,
    OF ca cb projection]
  by (simp add: equalizable_iff)

lemma canonical_step:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem A P p modes"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
    and correct: "logic_runtime_state_correct A s"
    and step: "logic_cut_step A (\<lambda>t. D (cut_tree t)) P s t"
  shows "(cut_state s,cut_state t) \<in> source (cut_program P)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: source.admin simp: cut_admin)
next
  case (case_call m f ts gs es)
  then show ?thesis
    using source.case_call[of m f "map cut_tree ts" "map cut_igoal gs" "cut_state es" "cut_program P"]
    by (simp add: cut_slice map_map o_def lp_cut_fresh_def logic_fresh_mark_def image_image)
next
  case (resolve c ren a gs sigma m es)
  have index: "c<length (cut_program P)" using resolve by simp
  have eval_comp: "(logic_subst sigma \<circ> logic_eval (LVar \<circ> ren)) = logic_eval (sigma \<circ> ren)"
    by (rule ext) (simp add: logic_subst_composition o_def)
  have eq: "logic_atom_map (logic_subst sigma) a = logic_atom_map (logic_eval (sigma \<circ> ren)) (fst (P!c))"
    using resolve by (auto simp: logic_mgu_def logic_atom_map_comp eval_comp)
  have native_eq: "lp_isubst (cut_atom a) (cut_tree \<circ> sigma) =
    lp_ieval (fst (cut_program P!c)) (cut_tree \<circ> (sigma \<circ> ren))"
    using arg_cong[OF eq, where f=cut_atom] index
    by (simp add: cut_program_nth cut_atom_subst cut_head_eval)
  have ds: "\<forall>x. D ((cut_tree \<circ> sigma) x)"
    and dr: "\<forall>x. D ((cut_tree \<circ> (sigma \<circ> ren)) x)"
    using resolve by (auto simp: logic_mgu_def logic_substitution_in_def)
  show ?thesis
    using source.resolve[OF index native_eq ds dr, where m=m and gs="map cut_igoal gs" and es="cut_state es"] resolve
    by (cases a) (simp add: cut_program_nth eval_comp map_map o_def cut_goal_subst cut_goal_eval_bind
        logic_subst_composition)
next
  case (backtrack c ren a gs m)
  have source_index: "c<length P" using backtrack by simp
  have index: "c<length (cut_program P)" using source_index by simp
  have head: "logic_atom_correct A (arity_correct (logic_symbol_arity A)) (fst (P!c))"
    using program nth_mem[OF source_index] by (auto simp: logic_cut_problem_def case_prod_unfold)
  have caller: "logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) a"
    using correct backtrack by simp
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (cut_atom a) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding cut_program_nth[OF source_index] fst_conv
    by (rule typed_fresh_failure[where A=A, OF backtrack(3) caller head projection backtrack(4)])
  show ?thesis using source.backtrack[OF index failure,
    where gs="map cut_igoal gs" and m=m and es="cut_state t"] backtrack
    by (cases a) simp
next
  case (unify a b sigma gs es)
  have eq: "logic_subst sigma a = logic_subst sigma b"
    using unify by (auto simp: logic_mgu_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) = lp_isubst (cut_tree b) (cut_tree \<circ> sigma)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  have ds: "\<forall>x. D ((cut_tree \<circ> sigma) x)"
    using unify by (auto simp: logic_mgu_def logic_substitution_in_def)
  show ?thesis using source.unify[OF native_eq ds, where gs="map cut_igoal gs" and es="cut_state es"] unify
    by (simp add: map_map o_def cut_goal_subst)
next
  case (unify_fail a b gs)
  have ca: "logic_tree_arity_correct (logic_symbol_arity A) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity A) b"
    using correct unify_fail by simp_all
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> lp_isubst (cut_tree a) sigma = lp_isubst (cut_tree b) sigma)"
    using unify_fail by (simp add: typed_equalizable_iff[OF ca cb projection])
  show ?thesis using source.unify_fail[OF failure, where gs="map cut_igoal gs" and es="cut_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
  have lower: "lp_cut_lower m (cut_tree (LFun f ts)) (map cut_igoal body)"
    by (rule cut_lower) (use meta in blast)
  show ?thesis using source.meta[OF _ lower, where gs="map cut_igoal gs" and es="cut_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree a) body)"
    by (rule cut_diverges_unlowerable) (use meta_diverges in blast)
  show ?thesis using source.meta_unlowerable[OF failure, where gs="map cut_igoal gs" and es="cut_state es"] meta_diverges by simp
qed

theorem canonical_termination:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem A P p modes"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
    and native: "\<And>ts :: ('f logic_symbol,string) fo_term list.
      logic_query (logic_symbol_arity A) (LogicUser p) modes (LAtom (LogicUser p) ts) \<Longrightarrow>
      SN_on (source (cut_program P)) {cut_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]}"
  shows "logic_cut_terminates_in A (\<lambda>t. D (cut_tree t)) P p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (logic_symbol_arity A) (LogicUser p) modes (LAtom (LogicUser p) ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step A (\<lambda>t. D (cut_tree t)) P (s n) (s (Suc n))"
  have start_correct: "logic_runtime_state_correct A (s 0)"
    using query by (simp add: init logic_query_def list_all_iff)
  have correct: "logic_runtime_state_correct A (s n)" for n
    by (rule logic_cut_run_arity[where run=s and D="\<lambda>t. D (cut_tree t)", OF program start_correct]) (use steps in simp)
  have chain: "\<forall>n. ((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n)) \<in> source (cut_program P)"
    proof (intro allI)
    fix n
    show "((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n)) \<in> source (cut_program P)"
      unfolding o_apply by (rule canonical_step[OF program _ correct]) (use projection steps in auto)
  qed
  have bad: "\<exists>f. f 0 \<in> {cut_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]} \<and>
      (\<forall>n. (f n,f (Suc n)) \<in> source (cut_program P))"
    by (rule exI[of _ "cut_state \<circ> s"], rule conjI) (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
end
