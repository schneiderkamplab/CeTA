theory LP_Cut_Mixed_Free_Coverage
  imports LP_Cut_MGU_Coverage LP_Cut_MGU_Normalize
begin

text \<open>A mixed ground/free call must not be treated as an arbitrary
non-ground call. A finite unifier is sufficient if it leaves all known ground
arguments unchanged. No freeness is inferred from absence of groundness.\<close>

lemma lpc_mixed_free_unifier_sound:
  fixes a h :: "('f,string) term" and eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes vars: "vars_term a \<subseteq> G \<union> F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G \<inter> vars_term a. s x=Var x"
    and eq: "a\<cdot>s=h\<cdot>r"
  shows "\<exists>sigma rho :: string \<Rightarrow> ('f,string) lp_iterm. lp_isubst (lp_ieval a eta) sigma=lp_ieval h rho"
proof -
  obtain f where inj: "inj_on f F" and repr: "\<forall>x\<in>F. eta x=LPIVar (f x)"
    using lpc_free_knowledge_representation[OF free] by blast
  let ?sigma = "\<lambda>y. if y\<in>f ` F then lp_ieval (s (inv_into F f y)) eta else LPIVar y"
  have images: "lp_isubst (eta x) ?sigma=lp_ieval (s x) eta" if x: "x\<in>vars_term a" for x
  proof (cases "x\<in>F")
    case True
    then show ?thesis using repr inj by (simp add: inv_into_f_f)
  next
    case False
    have g: "x\<in>G" using vars x False by blast
    have "lp_seg_ground (eta x)" using ground g by blast
    then show ?thesis using same g x by (simp add: lp_seg_ground_subst)
  qed
  have "lp_isubst (lp_ieval a eta) ?sigma=lp_ieval (a\<cdot>s) eta"
    unfolding lp_ieval_subst lp_ieval_finite_subst
    by (rule lp_ieval_cong) (use images in auto)
  also have "...=lp_ieval h (\<lambda>x. lp_ieval (r x) eta)"
    by (simp add: eq lp_ieval_finite_subst)
  finally show ?thesis by blast
qed

fun lpc_free_goal_term where
  "lpc_free_goal_term (LPCAtom t) = t"
| "lpc_free_goal_term _ = Var []"

definition lpc_check_mixed_free_call where
  "lpc_check_mixed_free_call fuel k G F a h =
    (let h'=h\<cdot>(\<lambda>x. Var (lp_prefix k x));
      V=sorted_list_of_set (vars_term a \<union> vars_term h') in
      vars_term a \<subseteq> set G \<union> set F \<and>
      (case lp_cut_normalize fuel [(h',a)] (map (\<lambda>x. LPCAtom (Var x)) V) of
        Some (Some gs) \<Rightarrow>
          (let images=map lpc_free_goal_term gs;
               s=lpc_mgu_substitution V images in
           (\<forall>x\<in>set G \<inter> vars_term a. s x=Var x) \<and> a\<cdot>s=h'\<cdot>s)
      | _ \<Rightarrow> False))"

theorem lpc_check_mixed_free_call_sound:
  fixes a h :: "('f,string) term" and eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lpc_check_mixed_free_call fuel k G F a h"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
  shows "\<exists>sigma rho :: string \<Rightarrow> ('f,string) lp_iterm. lp_isubst (lp_ieval a eta) sigma=lp_ieval h rho"
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
      show ?thesis by (rule lpc_mixed_free_unifier_sound[OF vars ground free same eq])
    qed
  qed
qed

end
