theory LP_Unification_Factorisation
  imports Category_LP_Bridge.LP_Cut_Finite_Unification
begin

text \<open>A successful finite unification algorithm factors every tree-valued
solution, including rational and unrestricted infinite trees. Completeness of
finite unification is used only to obtain a successful run from a finite witness;
no implication between the three termination semantics is assumed.\<close>

lemma lp_ieval_eliminate:
  assumes "eta x = lp_ieval t eta"
  shows "lp_ieval (u \<cdot> Term.subst x t) eta = lp_ieval u eta"
proof -
  have "(\<lambda>y. lp_ieval (Term.subst x t y) eta) = eta"
    using assms by (auto simp: Term.subst_def fun_eq_iff)
  then show ?thesis by (simp add: lp_ieval_finite_subst)
qed

lemma lp_unify_tree_factor:
  assumes run: "Unification.unify E bs = Some cs"
    and solution: "\<forall>(s,t)\<in>set E. lp_ieval s eta = lp_ieval t eta"
  shows "lp_ieval (Unification.subst_of cs x) eta = lp_ieval (Unification.subst_of bs x) eta"
  using run solution
proof (induct E bs arbitrary: cs rule: Unification.unify.induct)
  case (1 bs) then show ?case by simp
next
  case (2 f ss g ts E bs)
  obtain us where dec: "Unification.decompose (Fun f ss) (Fun g ts) = Some us"
    and run: "Unification.unify (us@E) bs = Some cs"
    using "2.prems"(1) by (auto split: option.splits)
  have eq: "map (\<lambda>t. lp_ieval t eta) ss = map (\<lambda>t. lp_ieval t eta) ts"
    using "2.prems"(2) by simp
  have sol: "\<forall>(s,t)\<in>set (us@E). lp_ieval s eta = lp_ieval t eta"
    using "2.prems"(2) dec eq
    by (auto dest: decompose_Some simp: set_zip in_set_conv_nth; metis nth_map)
  show ?case by (rule "2.hyps"[OF dec run sol])
next
  case (3 x' t E bs)
  show ?case
  proof (cases "t=Var x'")
    case True
    show ?thesis by (rule "3.hyps"(1)[OF True]) (use "3.prems" True in auto)
  next
    case False
    have occurs: "x'\<notin>vars_term t" and run: "Unification.unify (subst_list (Term.subst x' t) E) ((x',t)#bs)=Some cs"
      using "3.prems"(1) False by (auto split: if_splits)
    have eq: "eta x'=lp_ieval t eta" using "3.prems"(2) by simp
    have sol: "\<forall>(s,t)\<in>set (subst_list (Term.subst x' t) E). lp_ieval s eta=lp_ieval t eta"
      using "3.prems"(2) by (auto simp: subst_list_def lp_ieval_eliminate[OF eq])
    have ih: "lp_ieval (Unification.subst_of cs x) eta=lp_ieval (Unification.subst_of ((x',t)#bs) x) eta"
      by (rule "3.hyps"(2)[OF False occurs run sol])
    show ?thesis using ih by (simp add: subst_compose lp_ieval_eliminate[OF eq])
  qed
next
  case (4 f ts x' E bs)
  have occurs: "x'\<notin>vars_term (Fun f ts)"
    and run: "Unification.unify (subst_list (Term.subst x' (Fun f ts)) E) ((x',Fun f ts)#bs)=Some cs"
    using "4.prems"(1) by (auto split: if_splits)
  have eq: "eta x'=lp_ieval (Fun f ts) eta" using "4.prems"(2) by simp
  have sol: "\<forall>(s,t)\<in>set (subst_list (Term.subst x' (Fun f ts)) E). lp_ieval s eta=lp_ieval t eta"
    using "4.prems"(2) by (auto simp: subst_list_def lp_ieval_eliminate[OF eq])
  have ih: "lp_ieval (Unification.subst_of cs x) eta=lp_ieval (Unification.subst_of ((x',Fun f ts)#bs) x) eta"
    by (rule "4.hyps"[OF occurs run sol])
  show ?case using ih by (simp add: subst_compose lp_ieval_eliminate[OF eq])
qed


lemma lp_mgu_tree_factor:
  assumes computed: "Unification.mgu s t = Some mu"
    and solution: "lp_ieval s eta = lp_ieval t eta"
  shows "lp_ieval (mu x) eta = eta x"
proof -
  obtain cs where run: "Unification.unify [(s,t)] [] = Some cs"
    and mu: "mu = Unification.subst_of cs"
    using computed by (auto simp: Unification.mgu_def split: option.splits)
  show ?thesis using lp_unify_tree_factor[OF run, of eta x] solution
    by (simp add: mu)
qed

lemma lp_finite_solution_universal_mgu:
  fixes s t :: "('f,'v) term"
    and tau :: "'v \<Rightarrow> ('f,'v) term"
  assumes finite_solution: "s \<cdot> tau = t \<cdot> tau"
  obtains mu where "s \<cdot> mu = t \<cdot> mu"
    and "\<And>(eta :: 'v \<Rightarrow> ('f,'v) lp_iterm) x. lp_ieval s eta = lp_ieval t eta \<Longrightarrow>
      lp_ieval (mu x) eta = eta x"
proof -
  obtain mu where computed: "Unification.mgu s t = Some mu"
    using ex_mgu_if_subst_apply_term_eq_subst_apply_term[OF finite_solution] by blast
  have unifies: "s \<cdot> mu=t \<cdot> mu"
    using mgu_sound[OF computed] by (auto simp: is_imgu_def unifiers_def)
  show thesis by (rule that[OF unifies lp_mgu_tree_factor[OF computed]])
qed

ML \<open>
  val results = @{thms lp_unify_tree_factor lp_finite_solution_universal_mgu}
  val _ = if Thm_Deps.has_skip_proof results then error "LP unification: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "LP unification: oracle dependency"
\<close>
end
