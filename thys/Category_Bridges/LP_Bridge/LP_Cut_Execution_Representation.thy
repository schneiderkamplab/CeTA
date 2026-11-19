theory LP_Cut_Execution_Representation
  imports LP_Cut_Representation Category_Properties.LP_Cut_Arity_Properties
    Category_Properties.LP_Freshening_Properties
begin

lemma cut_tree_list_injective[simp]:
  "map cut_tree ts = map cut_tree us \<longleftrightarrow> ts=us"
proof
  assume eq: "map cut_tree ts=map cut_tree us"
  show "ts=us" using arg_cong[OF eq, where f="map cut_tree_back"] by (simp add: map_map o_def)
qed simp
lemma cut_atom_injective[simp]: "cut_atom a = cut_atom b \<longleftrightarrow> a=b"
  by (cases a; cases b) simp
lemma cut_atom_subst:
  "cut_atom (logic_atom_map (logic_subst s) a) = lp_isubst (cut_atom a) (cut_tree \<circ> s)"
  by (cases a) (simp add: map_map o_def cut_tree_subst)
lemma cut_head_eval:
  "cut_atom (logic_atom_map (logic_eval s) h) = lp_ieval (cut_head h) (cut_tree \<circ> s)"
  by (cases h) (simp add: map_map o_def cut_tree_eval)
lemma cut_atom_unifiable_iff:
  fixes a :: "('f,('f logic_symbol,'v) logic_tree) logic_atom"
  shows "(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>r.
      lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r) \<longleftrightarrow>
    (\<exists>s r. logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h)"
proof
  assume "\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>r.
      lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r"
  then obtain s r :: "'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm" where eq:
    "lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r" by blast
  have "cut_atom (logic_atom_map (logic_subst (cut_tree_back \<circ> s)) a) =
      cut_atom (logic_atom_map (logic_eval (cut_tree_back \<circ> r)) h)"
    using eq by (simp add: cut_atom_subst cut_head_eval o_def)
  then show "\<exists>s r. logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h"
    by (simp; blast)
next
  assume "\<exists>s r. logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h"
  then obtain s r where eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h" by blast
  have "lp_isubst (cut_atom a) (cut_tree \<circ> s) = lp_ieval (cut_head h) (cut_tree \<circ> r)"
    using arg_cong[OF eq, where f=cut_atom] by (simp add: cut_atom_subst cut_head_eval)
  then show "\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>r.
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) r" by blast
qed
lemma cut_equalizable_iff:
  fixes a :: "('f logic_symbol,'v) logic_tree"
  shows "(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s) \<longleftrightarrow>
    (\<exists>s. logic_subst s a = logic_subst s b)"
proof
  assume "\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s"
  then obtain s :: "'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm" where eq: "lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
  have "cut_tree (logic_subst (cut_tree_back \<circ> s) a) = cut_tree (logic_subst (cut_tree_back \<circ> s) b)"
    using eq by (simp add: cut_tree_subst o_def)
  then show "\<exists>s. logic_subst s a = logic_subst s b" by (simp; blast)
next
  assume "\<exists>s. logic_subst s a = logic_subst s b"
  then obtain s where "logic_subst s a = logic_subst s b" by blast
  then have "lp_isubst (cut_tree a) (cut_tree \<circ> s) = lp_isubst (cut_tree b) (cut_tree \<circ> s)"
    by (metis cut_tree_subst)
  then show "\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s" by blast
qed

lemma cut_fresh_failure:
  fixes a :: "('f,('f logic_symbol,'v) logic_tree) logic_atom"
  assumes fresh: "logic_freshening r (logic_arguments a @ active) (logic_arguments h @ body)"
    and caller: "logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) a"
    and clause: "logic_atom_correct A (arity_correct (logic_symbol_arity A)) h"
    and failure: "\<not>(\<exists>s. logic_substitution_in (logic_tree_arity_correct (logic_symbol_arity A)) s \<and>
      logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) h)"
  shows "\<not>(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>t.
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) t)"
proof
  assume "\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>t.
    lp_isubst (cut_atom a) s = lp_ieval (cut_head h) t"
  then obtain s t where eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval t) h"
    using cut_atom_unifiable_iff by blast
  have ca: "list_all (logic_tree_arity_correct (logic_symbol_arity A)) (logic_arguments a)"
    using caller by (cases a) simp
  have ch: "list_all (arity_correct (logic_symbol_arity A)) (logic_arguments h)"
    using clause by (cases h) simp
  have "\<exists>u. logic_substitution_in (\<lambda>x. True \<and> logic_tree_arity_correct (logic_symbol_arity A) x) u \<and>
    logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u \<circ> logic_eval (LVar \<circ> r)) h"
    by (rule logic_typed_fresh_unifier[where D="\<lambda>_. True" and z=undefined,
        OF fresh ca ch _ _ _ eq]) (simp_all add: logic_substitution_in_def)
  then show False using failure by simp
qed

lemma cut_typed_equalizable_iff:
  fixes a b :: "('f logic_symbol,'v) logic_tree"
  assumes "logic_tree_arity_correct (logic_symbol_arity A) a"
    "logic_tree_arity_correct (logic_symbol_arity A) b"
  shows "(\<exists>s :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. lp_isubst (cut_tree a) s = lp_isubst (cut_tree b) s)
    \<longleftrightarrow> (\<exists>s. logic_substitution_in (logic_tree_arity_correct (logic_symbol_arity A)) s \<and>
      logic_subst s a = logic_subst s b)"
  using logic_arity_unifiable_iff[where D="\<lambda>_. True" and z=undefined, OF assms]
  by (simp add: cut_equalizable_iff logic_substitution_in_def)

text \<open>For valid programs and arity-correct states, each infinite-domain
step is included in the native termination overapproximation. Failed unification
uses the proved projection and freshening results, not a termination restriction
principle.\<close>
lemma cut_infinite_step_native:
  fixes P :: "('f,'v) logic_cut_program"
  assumes program: "logic_cut_problem A P p modes"
    and correct: "logic_runtime_state_correct A s"
    and step: "logic_cut_step A (\<lambda>_. True) P s t"
  shows "(cut_state s,cut_state t) \<in> lp_cut_source (cut_program P)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: lp_cut_source.admin simp: cut_admin)
next
  case (case_call m f ts gs es)
  then show ?thesis
    using lp_cut_source.case_call[of m f "map cut_tree ts" "map cut_igoal gs" "cut_state es" "cut_program P"]
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
  show ?thesis
    using lp_cut_source.resolve[OF index native_eq, where m=m and gs="map cut_igoal gs" and es="cut_state es"] resolve
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
  have failure: "\<not>(\<exists>sigma :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm. \<exists>rho.
    lp_isubst (cut_atom a) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding cut_program_nth[OF source_index] fst_conv
    by (rule cut_fresh_failure[OF backtrack(3) caller head]) (use backtrack in simp)
  show ?thesis using lp_cut_source.backtrack[OF index failure,
    where gs="map cut_igoal gs" and m=m and es="cut_state t"] backtrack
    by (cases a) simp
next
  case (unify a b sigma gs es)
  have eq: "logic_subst sigma a = logic_subst sigma b"
    using unify by (auto simp: logic_mgu_def)
  have native_eq: "lp_isubst (cut_tree a) (cut_tree \<circ> sigma) = lp_isubst (cut_tree b) (cut_tree \<circ> sigma)"
    using arg_cong[OF eq, of cut_tree] by (simp add: cut_tree_subst)
  show ?thesis using lp_cut_source.unify[OF native_eq, where gs="map cut_igoal gs" and es="cut_state es"] unify
    by (simp add: map_map o_def cut_goal_subst)
next
  case (unify_fail a b gs)
  have ca: "logic_tree_arity_correct (logic_symbol_arity A) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity A) b"
    using correct unify_fail by simp_all
  have failure: "\<not>(\<exists>sigma :: 'v \<Rightarrow> ('f lp_cut_symbol,'v) lp_iterm.
    lp_isubst (cut_tree a) sigma = lp_isubst (cut_tree b) sigma)"
    using unify_fail by (simp add: cut_typed_equalizable_iff[OF ca cb])
  show ?thesis using lp_cut_source.unify_fail[OF failure, where gs="map cut_igoal gs" and es="cut_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp add: lp_cut_fresh_def logic_fresh_mark_def image_image)
  have lower: "lp_cut_lower m (cut_tree (LFun f ts)) (map cut_igoal body)"
    by (rule cut_lower) (use meta in blast)
  show ?thesis using lp_cut_source.meta[OF _ lower, where gs="map cut_igoal gs" and es="cut_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree a) body)"
    by (rule cut_diverges_unlowerable) (use meta_diverges in blast)
  show ?thesis using lp_cut_source.meta_unlowerable[OF failure, where gs="map cut_igoal gs" and es="cut_state es"] meta_diverges by simp
qed

theorem cut_native_termination:
  fixes P :: "('f,'v) logic_cut_program"
  assumes program: "logic_cut_problem A P p modes"
    and native: "\<And>ts :: ('f logic_symbol,'v) fo_term list.
      logic_query (logic_symbol_arity A) (LogicUser p) modes (LAtom (LogicUser p) ts) \<Longrightarrow>
      SN_on (lp_cut_source (cut_program P)) {cut_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]}"
  shows "lp_cut_infinite_terminates A P p modes"
proof (unfold lp_cut_infinite_terminates_def logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (logic_symbol_arity A) (LogicUser p) modes (LAtom (LogicUser p) ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step A (\<lambda>_. True) P (s n) (s (Suc n))"
  have start_correct: "logic_runtime_state_correct A (s 0)"
    using query by (simp add: init logic_query_def list_all_iff)
  have correct: "logic_runtime_state_correct A (s n)" for n
    by (rule logic_cut_run_arity[where run=s and D="\<lambda>_. True", OF program start_correct]) (use steps in simp)
  have chain: "\<forall>n. ((cut_state \<circ> s) n,(cut_state \<circ> s) (Suc n)) \<in> lp_cut_source (cut_program P)"
    by (simp only: o_apply; intro allI; rule cut_infinite_step_native[where A=A and P=P, OF program correct]; rule spec[OF steps])
  have bad: "\<exists>f. f 0 \<in> {cut_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]} \<and>
      (\<forall>n. (f n,f (Suc n)) \<in> lp_cut_source (cut_program P))"
    by (rule exI[of _ "cut_state \<circ> s"], rule conjI) (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

end
