theory LP_Cut_Scoped_Return_Models
 imports LP_Cut_Return_Models
begin

text \<open>Only reachable source predicates need a return model. The checked
predicate set is closed under every body of every matching source clause;
unreachable library clauses are retained in the source program.\<close>

definition lpc_scoped_model_program where
  "lpc_scoped_model_program P F M = (\<forall>c<length P. \<exists>g ts.
    fst (P!c)=Fun g ts \<and> (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow>
      list_all (lpc_control_goal F) (snd (P!c)) \<and>
      lpc_model_program [P!c] M))"

fun lpc_scoped_model_frame where
  "lpc_scoped_model_frame F M K (LPCGoals gs,eta) =
    (list_all (lpc_control_igoal F) gs \<and> lpc_model_goals M K gs eta)"
| "lpc_scoped_model_frame F M K (LPCClause gs c m,eta) =
    (list_all (lpc_control_igoal F) gs \<and> lpc_model_goals M K gs eta)"
| "lpc_scoped_model_frame F M K (LPCBarrier m,eta) = True"

lemma lpc_scoped_model_resolution:
  fixes m :: nat
  assumes program: "lpc_scoped_model_program P F M"
    and index: "c<length P" and f: "f\<in>F"
    and equation: "lp_isubst (LPIFun (LPCUser f) ts) sigma = lp_ieval (fst (P!c)) rho"
    and tail: "list_all (lpc_control_igoal F) gs"
    and before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
  defines "hs \<equiv> map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
    map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs"
  shows "list_all (lpc_control_igoal F) hs"
    "lpc_model_goals M K hs (\<lambda>x. lp_isubst (eta x) sigma)"
proof -
  obtain g us where head: "fst (P!c)=Fun g us" and selected:
    "\<And>f. g=LPCUser f \<Longrightarrow> f\<in>F \<Longrightarrow>
      list_all (lpc_control_goal F) (snd (P!c)) \<and> lpc_model_program [P!c] M"
    using program index by (auto simp: lpc_scoped_model_program_def)
  have gf: "g=LPCUser f" using equation by (simp add: head)
  have body: "list_all (lpc_control_goal F) (snd (P!c))"
    and model: "lpc_model_program [P!c] M" using selected[OF gf f] by auto
  show "list_all (lpc_control_igoal F) hs"
    using lpc_control_bind(1)[OF body] lpc_control_subst(1)[OF tail] by (auto simp: hs_def)
  have bound: "0<length [P!c]" by simp
  have eq: "lp_isubst (LPIFun (LPCUser f) ts) sigma=lp_ieval (fst ([P!c]!0)) rho"
    using equation by simp
  show "lpc_model_goals M K hs (\<lambda>x. lp_isubst (eta x) sigma)"
    using lpc_model_resolution[OF model bound eq before, of m] by (auto simp: hs_def)
qed

theorem lpc_scoped_model_answer_preserved:
  assumes program: "lpc_scoped_model_program P F M"
    and step: "lpc_answer_transition P ss event tt"
    and known: "list_all (lpc_scoped_model_frame F M K) ss"
  shows "list_all (lpc_scoped_model_frame F M K) tt"
  using step known
proof (cases rule: lpc_answer_transition.cases)
  case (resolve c a gs sigma rho m eta es)
  obtain f ts where a: "a=LPIFun (LPCUser f) ts" and f: "f\<in>F"
    and tail: "list_all (lpc_control_igoal F) gs"
    and before: "lpc_model_goals M K (LPCAtom (LPIFun (LPCUser f) ts)#gs) eta"
    using known resolve by (auto simp: lpc_control_igoal_iff)
  have equation: "lp_isubst (LPIFun (LPCUser f) ts) sigma=lp_ieval (fst (P!c)) rho"
    using resolve by (simp add: a lpc_mgu_resolve_def)
  have bound: "c<length P" using resolve by simp
  note preserved = lpc_scoped_model_resolution[OF program bound f equation tail before, of m]
  show ?thesis using resolve known preserved by simp
qed (use known in \<open>auto simp: lpc_model_goals_def list_all_iff lpc_control_igoal_iff
  dest: subsetD[OF lpc_answer_prune_subset]\<close>)

lemma lpc_scoped_model_frame_forget:
  "lpc_scoped_model_frame F M K (e,eta) \<Longrightarrow> lpc_model_frame M K (e,eta)"
  by (cases e) simp_all

lemma lpc_scoped_model_forget:
  "list_all (lpc_scoped_model_frame F M K) ss \<Longrightarrow> list_all (lpc_model_frame M K) ss"
  by (auto simp: list_all_iff split: prod.splits intro: lpc_scoped_model_frame_forget)

end
