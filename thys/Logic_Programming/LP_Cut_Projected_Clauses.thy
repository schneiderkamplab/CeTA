theory LP_Cut_Projected_Clauses
  imports LP_Cut_Projected_Relation
begin

definition lpc_check_projected_clauses where
  "lpc_check_projected_clauses filtering R Q = list_all
    (\<lambda>cl. length (snd cl)=1 \<and>
      (Fun (fst (fst cl)) (snd (fst cl)),Fun (fst (hd (snd cl))) (snd (hd (snd cl))))\<in>set R \<and>
      vars_term (af_term filtering (Fun (fst (hd (snd cl))) (snd (hd (snd cl))))) \<subseteq>
      vars_term (af_term filtering (Fun (fst (fst cl)) (snd (fst cl))))) Q"

lemma lpc_projected_clause_step:
  assumes checked: "lpc_check_projected_clauses filtering R Q"
    and step: "(qs,rs)\<in>lp_ild Q"
    and observed: "lpc_observes filtering qs m"
  shows "(qs,rs)\<in>lpc_projected_rel filtering (set R)"
proof -
  obtain f ts where qs: "qs=[(f,ts)]" and pr: "lp_iproject filtering (LPIFun f ts) m"
    using observed by (auto simp: lpc_observes_def)
  obtain c sigma rho where bound: "c<length Q"
    and matched: "lp_iatom_subst (f,ts) sigma = lp_atom_eval (fst (Q!c)) rho"
    and rs: "rs=map (\<lambda>b. lp_atom_eval b rho) (snd (Q!c))"
    using step unfolding qs by (cases rule: lp_ild.cases) auto
  have local_check: "(\<lambda>cl. length (snd cl)=1 \<and>
      (Fun (fst (fst cl)) (snd (fst cl)),Fun (fst (hd (snd cl))) (snd (hd (snd cl))))\<in>set R \<and>
      vars_term (af_term filtering (Fun (fst (hd (snd cl))) (snd (hd (snd cl))))) \<subseteq>
      vars_term (af_term filtering (Fun (fst (fst cl)) (snd (fst cl))))) (Q!c)"
    using checked nth_mem[OF bound] unfolding lpc_check_projected_clauses_def list_all_iff by (rule bspec)
  obtain g us h vs where clause: "Q!c=((g,us),[(h,vs)])"
    and rule: "(Fun g us,Fun h vs)\<in>set R"
    and variables: "vars_term (af_term filtering (Fun h vs)) \<subseteq> vars_term (af_term filtering (Fun g us))"
    using local_check
    by (cases "Q!c"; cases "fst (Q!c)"; cases "hd (snd (Q!c))")
      (auto simp: length_Suc_conv)
  have matched_term: "lp_ieval (Fun g us) rho = lp_isubst (LPIFun f ts) sigma"
    using matched clause by (auto simp: lp_iatom_subst_def lp_atom_eval_def)
  have left_pr: "lp_iproject filtering (lp_ieval (Fun g us) rho) m"
    unfolding matched_term by (rule lp_iproject_subst[OF pr])
  obtain n where right_pr: "lp_iproject filtering (lp_ieval (Fun h vs) rho) n"
    and edge: "(m,n)\<in>rstep (af_rule filtering ` set R)"
    by (rule lp_infinite_rule_projection[OF left_pr variables rule])
  have right_obs: "lpc_observes filtering rs n"
    using right_pr rs clause by (auto simp: lpc_observes_def lp_atom_eval_def)
  show ?thesis unfolding lpc_projected_rel_def
    using observed right_obs edge by blast
qed

lemma lpc_projected_clause_path:
  assumes checked: "lpc_check_projected_clauses filtering R Q"
    and path: "(qs,rs)\<in>(lp_ild Q)\<^sup>*"
    and initial: "lpc_observed filtering qs"
  shows "(qs,rs)\<in>(lpc_projected_rel filtering (set R))\<^sup>* \<and> lpc_observed filtering rs"
  using path initial
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step ys zs)
  have before: "(qs,ys)\<in>(lpc_projected_rel filtering (set R))\<^sup>*"
    and good: "lpc_observed filtering ys" using step.hyps(3)[OF step.prems] by auto
  obtain m where obs: "lpc_observes filtering ys m" using good unfolding lpc_observed_def by blast
  have edge: "(ys,zs)\<in>lpc_projected_rel filtering (set R)"
    by (rule lpc_projected_clause_step[OF checked step.hyps(2) obs])
  show ?case using rtrancl_into_rtrancl[OF before edge] lpc_projected_rel_observed[OF edge] by simp
qed

lemma lpc_projected_clause_strict_path:
  assumes checked: "lpc_check_projected_clauses filtering R Q"
    and path: "(qs,rs)\<in>(lp_ild Q)\<^sup>+"
    and initial: "lpc_observed filtering qs"
  shows "(qs,rs)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
proof -
  obtain ys where prefix_path: "(qs,ys)\<in>(lp_ild Q)\<^sup>*" and last: "(ys,rs)\<in>lp_ild Q"
    using path by (cases rule: tranclE) (auto intro: trancl_into_rtrancl)
  have before: "(qs,ys)\<in>(lpc_projected_rel filtering (set R))\<^sup>*"
    and good: "lpc_observed filtering ys"
    using lpc_projected_clause_path[OF checked prefix_path initial] by auto
  obtain m where obs: "lpc_observes filtering ys m" using good unfolding lpc_observed_def by blast
  have edge: "(ys,rs)\<in>lpc_projected_rel filtering (set R)"
    by (rule lpc_projected_clause_step[OF checked last obs])
  show ?thesis by (rule rtrancl_into_trancl1[OF before edge])
qed

end
