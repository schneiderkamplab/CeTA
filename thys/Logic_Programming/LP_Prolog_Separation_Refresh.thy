theory LP_Prolog_Separation_Refresh
 imports LP_Prolog_Separation_Equality_Contract LP_Prolog_Functor_Reflexive_Contract
begin

fun lpp_separation_terms where
 "lpp_separation_terms (LPPSeparate a b) = [a,b]"

definition lpp_check_reflexive_separation where
 "lpp_check_reflexive_separation k facts gs =
   list_all (\<lambda>observation. list_all (\<lambda>t. (\<forall>x\<in>vars_term t. length x<k) \<and>
     t\<in>set (concat (map lp_cut_terms gs))) (lpp_separation_terms observation)) facts"

text \<open>Only facts occurring in the actual continuation are eligible. A
reflexive MGU need not preserve unrelated captured terms. Refresh translates
proven runtime preservation into the actual resolution environment.\<close>

lemma lpp_separation_refresh_after:
 fixes eta :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 assumes preserved: "lpp_separation_holds (\<lambda>x. lp_isubst (eta x) sigma) observation"
 and short: "\<forall>t\<in>set (lpp_separation_terms observation). \<forall>x\<in>vars_term t. length x<k"
 and bounds: "2 * k \<le>l"
 and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
 shows "lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)
   (lpp_separation_subst observation (lp_cut_refresh k G))"
 using preserved short lp_cut_resolution_active[OF _ bounds ground]
 by (cases observation) (auto simp: lp_ieval_subst[symmetric])

lemma lpp_reflexive_separation_refresh:
 fixes eta :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 assumes checked: "lpp_check_reflexive_separation k facts gs"
 and separated: "list_all (lpp_separation_holds eta) facts"
 and mgu: "lpc_mgu_unify input_value input_value (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 and bounds: "2 * k \<le>l"
 and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
 shows "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho))
   (map (\<lambda>observation. lpp_separation_subst observation (lp_cut_refresh k G)) facts)"
proof -
 have preserved: "lpp_separation_holds (\<lambda>x. lp_isubst (eta x) sigma) observation"
   if member: "observation\<in>set facts" for observation
 proof -
  obtain a b where shape: "observation=LPPSeparate a b" by (cases observation) auto
  have covered: "a\<in>set (concat (map lp_cut_terms gs))" "b\<in>set (concat (map lp_cut_terms gs))"
    using checked member unfolding lpp_check_reflexive_separation_def
    by (auto simp: list_all_iff shape dest!: bspec[where x="LPPSeparate a b"])
  obtain g h where members: "g\<in>set gs" "a\<in>set (lp_cut_terms g)"
    "h\<in>set gs" "b\<in>set (lp_cut_terms h)"
    using covered by auto
  have terms: "lp_cut_terms (lp_cut_map f z)=map f (lp_cut_terms z)" for f z
    by (cases z) auto
  have runtime: "lp_cut_map (\<lambda>t. lp_ieval t eta) g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    "lp_ieval a eta\<in>set (lp_cut_terms (lp_cut_map (\<lambda>t. lp_ieval t eta) g))"
    "lp_cut_map (\<lambda>t. lp_ieval t eta) h\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    "lp_ieval b eta\<in>set (lp_cut_terms (lp_cut_map (\<lambda>t. lp_ieval t eta) h))"
    using members by (auto simp: terms)
  have fin: "lpp_finite_term (lp_ieval a eta)" "lpp_finite_term (lp_ieval b eta)"
    using finite runtime by (auto simp: lpp_finite_goals_def list_all_iff)
  have disjoint: "set2_lp_iterm (lp_ieval a eta)\<inter>set2_lp_iterm (lp_ieval b eta)={}"
    using separated member by (auto simp: list_all_iff shape dest!: bspec[where x="LPPSeparate a b"])
  have after: "set2_lp_iterm (lp_isubst (lp_ieval a eta) sigma)\<inter>
    set2_lp_iterm (lp_isubst (lp_ieval b eta) sigma)={}"
    by (rule lpp_reflexive_mgu_continuation_separation[OF mgu runtime fin disjoint])
  show ?thesis using after by (simp add: shape lp_ieval_subst[symmetric])
 qed
 have refreshed: "lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)
    (lpp_separation_subst observation (lp_cut_refresh k G))"
    if "observation\<in>set facts" for observation
    by (rule lpp_separation_refresh_after[OF preserved[OF that] _ bounds ground])
      (use checked that in \<open>auto simp: lpp_check_reflexive_separation_def list_all_iff\<close>)
 show ?thesis using refreshed by (simp add: list_all_iff)
qed

lemma lpp_reflexive_separation_missing_continuation:
 assumes nonempty: "facts\<noteq>[]"
 shows "\<not>lpp_check_reflexive_separation k facts []"
proof -
 have "\<not>list_all (\<lambda>t. False) (lpp_separation_terms observation)" for observation
   by (cases observation) simp
 then show ?thesis using nonempty by (cases facts) (auto simp: lpp_check_reflexive_separation_def)
qed


lemma lpp_reflexive_separation_pair_covered:
 "(\<forall>x\<in>vars_term a\<union>vars_term b. length x<k) \<Longrightarrow>
   lpp_check_reflexive_separation k [LPPSeparate a b] [LPCUnify a b]"
 by (auto simp: lpp_check_reflexive_separation_def)

lemma lpp_reflexive_separation_unobserved_rejected:
 "x\<noteq>y \<Longrightarrow> \<not>lpp_check_reflexive_separation k
   [LPPSeparate (Var x) (Var y)] [LPCAtom (Var x)]"
 by (simp add: lpp_check_reflexive_separation_def)

ML \<open>
val checked = @{thms lpp_separation_refresh_after lpp_reflexive_separation_refresh
 lpp_reflexive_separation_missing_continuation lpp_reflexive_separation_pair_covered
 lpp_reflexive_separation_unobserved_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted reflexive separation refresh" else ();
\<close>
end
