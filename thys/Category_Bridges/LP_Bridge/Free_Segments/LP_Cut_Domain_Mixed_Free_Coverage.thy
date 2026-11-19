theory LP_Cut_Domain_Mixed_Free_Coverage
 imports LP_Cut_Domain_Joint_Free
begin

context cut_runtime_domain
begin

lemma mixed_free_unifier_sound:
  fixes a h :: "('f lp_cut_symbol,string) term" and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes vars: "vars_term a \<subseteq> G \<union> F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G \<inter> vars_term a. s x=Var x"
    and eq: "a\<cdot>s=h\<cdot>r"
    and domains: "\<And>x. D (eta x)"
  shows "\<exists>sigma rho :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and> lp_isubst (lp_ieval a eta) sigma=lp_ieval h rho"
proof -
  obtain sigma where ds: "\<forall>x. D (sigma x)"
    and eq: "lp_isubst (lp_ieval a eta) sigma=lp_ieval h (\<lambda>x. lp_ieval (r x) eta)"
    using uniform_free_comparison[where theta=eta, OF vars ground free same _ eq domains] by auto
  have dr: "\<forall>x. D (lp_ieval (r x) eta)" by (auto intro: valuation_domain domains)
  show ?thesis by (rule exI[of _ sigma], rule exI[of _ "\<lambda>x. lp_ieval (r x) eta"]) (simp add: ds dr eq)
qed

theorem check_mixed_free_call_sound:
  fixes a h :: "('f lp_cut_symbol,string) term" and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_mixed_free_call fuel k G F a h"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
    and domains: "\<And>x. D (eta x)"
  shows "\<exists>sigma rho :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and> lp_isubst (lp_ieval a eta) sigma=lp_ieval h rho"
proof -
  let ?h = "h\<cdot>(\<lambda>x. Var (lp_prefix k x))"
  let ?V = "sorted_list_of_set (vars_term a \<union> vars_term ?h)"
  let ?N = "lp_cut_normalize fuel [(?h,a)] (map (\<lambda>x. LPCAtom (Var x)) ?V)"
  show ?thesis
  proof (cases ?N)
    case None
    then show ?thesis using checked by (simp only: lpc_check_mixed_free_call_def Let_def option.simps; blast)
  next
    case (Some opt)
    note outer=Some
    show ?thesis
    proof (cases opt)
      case None
      then show ?thesis using checked outer by (simp only: lpc_check_mixed_free_call_def Let_def option.simps; blast)
    next
      case (Some gs)
      let ?images = "map lpc_free_goal_term gs"
      let ?s = "lpc_mgu_substitution ?V ?images"
      have all: "vars_term a \<subseteq> set G \<union> set F \<and>
        (\<forall>x\<in>set G \<inter> vars_term a. ?s x=Var x) \<and> a\<cdot>?s=?h\<cdot>?s"
        by (rule checked[unfolded lpc_check_mixed_free_call_def Let_def outer Some option.simps])
      have vars: "vars_term a \<subseteq> set G \<union> set F" using all by (rule conjunct1)
      have same: "\<forall>x\<in>set G \<inter> vars_term a. ?s x=Var x" by (rule conjunct1[OF conjunct2[OF all]])
      have eq: "a\<cdot>?s=h\<cdot>(\<lambda>x. ?s (lp_prefix k x))"
        using conjunct2[OF conjunct2[OF all]]
        by (simp only: subst_subst_compose[symmetric] subst_compose_def Term.eval_term.simps)
      show ?thesis by (rule mixed_free_unifier_sound[OF vars ground free same eq domains])
    qed
  qed
qed


end
end
