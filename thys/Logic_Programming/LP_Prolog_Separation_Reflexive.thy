theory LP_Prolog_Separation_Reflexive
 imports LP_Prolog_Separation_Context
begin

lemma lpp_finite_inverse_support:
 assumes finite: "lpp_finite_term t"
 and inverse: "lp_isubst (lp_isubst t sigma) delta=t"
 shows "\<forall>z\<in>set2_lp_iterm (lp_isubst t sigma).
   \<exists>x\<in>set2_lp_iterm t. delta z=LPIVar x"
 using finite inverse
proof (induction rule: lpp_finite_term.induct)
 case (variable x)
 then show ?case by (cases "sigma x") auto
next
 case (node ts f)
 have eq: "map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) ts=map id ts"
   using node.prems by (simp add: o_def)
 have children: "\<forall>t\<in>set ts. lp_isubst (lp_isubst t sigma) delta=t"
   using eq by (simp only: map_eq_conv id_apply)
 show ?case using node.IH children by (auto simp: list_all_iff; blast)

qed

lemma lpp_finite_inverse_variable:
 assumes finite: "lpp_finite_term t"
 and inverse: "lp_isubst (lp_isubst t sigma) delta=t"
 and member: "x\<in>set2_lp_iterm t"
 shows "\<exists>y. sigma x=LPIVar y \<and> delta y=LPIVar x"
 using finite inverse member
proof (induction rule: lpp_finite_term.induct)
 case (variable z)
 then show ?case by (cases "sigma z") auto
next
 case (node ts f)
 have eq: "map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta) ts=map id ts"
   using node.prems by (simp add: o_def)
 have children: "\<forall>t\<in>set ts. lp_isubst (lp_isubst t sigma) delta=t"
   using eq by (simp only: map_eq_conv id_apply)
 show ?case using node.IH node.prems children by (auto simp: list_all_iff; blast)
qed

lemma lpp_reflexive_mgu_finite_goals:
 assumes mgu: "lpc_mgu_unify a a gs sigma"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have after: "lpp_finite_term (lp_isubst t sigma)"
   if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_mgu_unify_continuation_finite[where tau=LPIVar, OF mgu _ _ that])
     (use finite in \<open>auto simp: lpp_finite_goals_def list_all_iff\<close>)
 show ?thesis using after by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

lemma lpp_finite_inverse_separation:
 assumes finite: "lpp_finite_term a" "lpp_finite_term b"
 and inverse: "lp_isubst (lp_isubst a sigma) delta=a" "lp_isubst (lp_isubst b sigma) delta=b"
 and separated: "set2_lp_iterm a \<inter> set2_lp_iterm b={}"
 shows "set2_lp_iterm (lp_isubst a sigma) \<inter> set2_lp_iterm (lp_isubst b sigma)={}"
 using lpp_finite_inverse_support[OF finite(1) inverse(1)]
   lpp_finite_inverse_support[OF finite(2) inverse(2)] separated by fastforce

lemma lpp_reflexive_mgu_continuation_separation:
 assumes mgu: "lpc_mgu_unify a a gs sigma"
 and members: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
   "h\<in>set gs" "u\<in>set (lp_cut_terms h)"
 and finite: "lpp_finite_term t" "lpp_finite_term u"
 and separated: "set2_lp_iterm t \<inter> set2_lp_iterm u={}"
 shows "set2_lp_iterm (lp_isubst t sigma) \<inter> set2_lp_iterm (lp_isubst u sigma)={}"
proof -
 obtain delta where factor: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
   map (lp_cut_map (\<lambda>v. lp_isubst v LPIVar)) gs"
   using mgu unfolding lpc_mgu_unify_def by blast
 have inverse: "lp_isubst (lp_isubst v sigma) delta=v"
   if "k\<in>set gs" "v\<in>set (lp_cut_terms k)" for k v
 proof -
  have eq: "lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta) k =
    lp_cut_map (\<lambda>v. lp_isubst v LPIVar) k"
    using factor that(1) by (simp only: map_eq_conv; blast)
  show ?thesis using eq that(2) by (cases k) auto
 qed
 show ?thesis by (rule lpp_finite_inverse_separation[OF finite inverse[OF members(1,2)]
   inverse[OF members(3,4)] separated])
qed

lemma lpp_reflexive_mgu_continuation_free:
 assumes mgu: "lpc_mgu_unify a a gs sigma"
 and finite: "lpp_finite_goals gs"
 and covered: "F\<subseteq>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpc_free_knowledge F sigma"
proof -
 obtain delta where factor: "map (lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta)) gs =
   map (lp_cut_map (\<lambda>v. lp_isubst v LPIVar)) gs"
   using mgu unfolding lpc_mgu_unify_def by blast
 have images: "\<exists>y. sigma x=LPIVar y \<and> delta y=LPIVar x" if "x\<in>F" for x
 proof -
  have membership: "x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
    by (rule subsetD[OF covered that])
  obtain g t where members: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" "x\<in>set2_lp_iterm t"
    using membership by blast
  have eq: "lp_cut_map (\<lambda>v. lp_isubst (lp_isubst v sigma) delta) g =
    lp_cut_map (\<lambda>v. lp_isubst v LPIVar) g"
    using factor members(1) by (simp only: map_eq_conv; blast)
  have inverse: "lp_isubst (lp_isubst t sigma) delta=t"
    using eq members(2) by (cases g) auto
  have fin: "lpp_finite_term t"
    using finite members by (auto simp: lpp_finite_goals_def list_all_iff)
  show ?thesis by (rule lpp_finite_inverse_variable[OF fin inverse members(3)])
 qed
 show ?thesis using images by (auto simp: lpc_free_knowledge_def inj_on_def; fastforce)
qed

ML \<open>
val checked = @{thms lpp_reflexive_mgu_continuation_free lpp_finite_inverse_variable lpp_reflexive_mgu_finite_goals lpp_finite_inverse_support lpp_finite_inverse_separation
 lpp_reflexive_mgu_continuation_separation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted reflexive separation transport" else ();
\<close>
end
