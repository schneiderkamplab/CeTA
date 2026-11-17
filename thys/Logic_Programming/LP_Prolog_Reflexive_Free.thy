theory LP_Prolog_Reflexive_Free
 imports LP_Cut_MGU_Unify_Free LP_Prolog_Equation_Congruence
begin

lemma lpc_mgu_reflexive_context_free:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and equal: "lp_ieval a eta=lp_ieval b eta"
 and free: "lpc_free_knowledge F eta"
 and subset: "C\<subseteq>F"
 and occurs: "C\<subseteq>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpc_free_knowledge C (\<lambda>x. lp_isubst (eta x) sigma)"
proof -
 obtain r where inj: "inj_on r F" and repr: "\<forall>x\<in>F. eta x=LPIVar (r x)"
   using lpc_free_knowledge_representation[OF free] by blast
 have comparison: "lp_isubst (lp_ieval a eta) LPIVar=lp_isubst (lp_ieval b eta) LPIVar"
   using equal by simp
 obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
   "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
     lp_isubst (lp_isubst (eta x) sigma) delta=eta x"
   using lpc_mgu_unify_context_factor[OF mgu comparison] by auto
 have equation: "lp_isubst (lp_isubst (eta x) sigma) delta=eta x" if "x\<in>C" for x
   using factor occurs that by blast
  have variables: "\<forall>x\<in>C. \<exists>y. lp_isubst (eta x) sigma=LPIVar y"
  proof (intro ballI)
    fix x assume x: "x\<in>C"
    have val_eq: "eta x=LPIVar (r x)" using repr subset x by blast
    have "lp_isubst (lp_isubst (eta x) sigma) delta=LPIVar (r x)"
      using equation[OF x] val_eq by simp
    then show "\<exists>y. lp_isubst (eta x) sigma=LPIVar y"
      by (rule lpc_isubst_variable_reflect)
  qed
  have distinct: "inj_on (\<lambda>x. lp_isubst (eta x) sigma) C"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>C" and y: "y\<in>C" and eq: "lp_isubst (eta x) sigma=lp_isubst (eta y) sigma"
    have old_eq: "eta x=eta y"
    proof -
      have "eta x=lp_isubst (lp_isubst (eta x) sigma) delta" by (rule sym[OF equation[OF x]])
      also have "...=lp_isubst (lp_isubst (eta y) sigma) delta" by (rule arg_cong[OF eq])
      also have "...=eta y" by (rule equation[OF y])
      finally show ?thesis .
    qed
    have eta_inj: "inj_on eta F" using free unfolding lpc_free_knowledge_def by (rule conjunct2)
    have xf: "x\<in>F" using subset x by blast
    have yf: "y\<in>F" using subset y by blast
    show "x=y" by (rule inj_onD[OF eta_inj old_eq xf yf])
  qed
  show ?thesis using variables distinct by (simp add: lpc_free_knowledge_def)
qed

definition lpp_reflexive_free_candidates where
 "lpp_reflexive_free_candidates F gs k = filter (\<lambda>x. length x<k \<and>
   list_ex (\<lambda>g. list_ex (\<lambda>t. x\<in>vars_term t) (lp_cut_terms g)) gs) F"

definition lpp_context_unify_free where
 "lpp_context_unify_free ctx F G a b gs k =
   (if lpp_check_context_equation_rewrite ctx a b
    then map (lp_prefix k) (lpp_reflexive_free_candidates F gs k)
    else lpc_unify_untouched_free F G a b gs k)"

lemma lpp_context_unify_free_sound:
 assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
 and free: "lpc_free_knowledge (set F) eta"
 and bounds: "2 * k \<le> l"
 and observed: "lpp_evaluation_context_holds E SP ctx eta"
 shows "lpc_free_knowledge (set (lpp_context_unify_free ctx F G a b gs k))
   (lp_cut_resolution_env k l eta sigma eta)"
proof (cases "lpp_check_context_equation_rewrite ctx a b")
 case False
 show ?thesis using lpc_unify_untouched_free_sound[OF mgu ground free bounds]
   by (simp add: lpp_context_unify_free_def False)
next
 case True
 have equal: "lp_ieval a eta=lp_ieval b eta"
   by (rule lpp_context_equation_rewrite_sound[OF True observed])
 let ?C="set (lpp_reflexive_free_candidates F gs k)"
 let ?value="\<lambda>x. lp_isubst (eta x) sigma"
 let ?env="lp_cut_resolution_env k l eta sigma eta"
 have subset: "?C\<subseteq> set F"
 and occurs: "?C\<subseteq>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   by (auto simp: lpp_reflexive_free_candidates_def list_ex_iff)
 have known: "lpc_free_knowledge ?C ?value"
   by (rule lpc_mgu_reflexive_context_free[OF mgu equal free subset occurs])
  have env: "?env (lp_prefix k x)=?value x" if x: "x \<in> ?C" for x
  proof -
    have short: "length x<k" using x by (simp add: lpp_reflexive_free_candidates_def)
    have upper: " \<not> l \<le> k+length x" using short bounds by arith
    show ?thesis by (simp add: lp_cut_resolution_env_def lp_prefix_def upper)
  qed
  have variables: "\<forall>x \<in> lp_prefix k ` ?C. \<exists>v. ?env x=LPIVar v"
    using known env by (auto simp: lpc_free_knowledge_def)
  have injective: "inj_on ?env (lp_prefix k ` ?C)"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> lp_prefix k ` ?C" and y: "y \<in> lp_prefix k ` ?C"
      and eq: "?env x=?env y"
    obtain u v where u: "u \<in> ?C" "x=lp_prefix k u" and v: "v \<in> ?C" "y=lp_prefix k v"
      using x y by blast
    have same: "?value u=?value v" using eq env[OF u(1)] env[OF v(1)] u(2) v(2) by simp
    have inj: "inj_on ?value ?C" using known by (simp add: lpc_free_knowledge_def)
    have "u=v" by (rule inj_onD[OF inj same u(1) v(1)])
    then show "x=y" using u v by simp
  qed
  show ?thesis using True variables injective
    by (simp add: lpp_context_unify_free_def lpc_free_knowledge_def)
qed

ML \<open>
val checked = @{thms lpc_mgu_reflexive_context_free lpp_context_unify_free_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted reflexive free-variable preservation" else ();
\<close>
end
