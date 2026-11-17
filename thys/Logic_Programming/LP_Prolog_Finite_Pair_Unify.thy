theory LP_Prolog_Finite_Pair_Unify
 imports LP_Prolog_Separation_Reflexive
begin

lemma lpp_separated_pair_mgu_finite_goals:
 assumes mgu: "lpc_mgu_unify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b]) gs sigma"
 and finite: "lpp_finite_term a" "lpp_finite_term b" "lpp_finite_goals gs"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?tau = "LPIVar(x := a,y := b)"
 have unchanged: "lp_isubst a ?tau=a" "lp_isubst b ?tau=b"
   by (rule lpp_finite_term_subst_untouched[OF finite(1)], use fresh in auto,
       rule lpp_finite_term_subst_untouched[OF finite(2)], use fresh in auto)
 have comparison: "lp_isubst (LPIFun f [LPIVar x,LPIVar y]) ?tau =
   lp_isubst (LPIFun f [a,b]) ?tau"
   using unchanged distinct by simp
 have images: "lpp_finite_term (?tau z)" for z using finite by simp
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   using finite(3) that by (auto simp: lpp_finite_goals_def list_all_iff)
 have after: "lpp_finite_term (lp_isubst t sigma)"
   if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_mgu_unify_continuation_finite[OF mgu comparison _ that])
     (auto intro: lpp_finite_term_substitute[OF old images])
 show ?thesis using after by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

lemma lpp_reflexive_then_pair_finite_goals:
 fixes tau :: "string \<Rightarrow> ('f,string) lp_iterm"
 and f :: "'f" and x y :: string and a b left right :: "('f,string) lp_iterm"
 defines "left \<equiv> LPIFun f [LPIVar x,LPIVar y]"
 and "right \<equiv> LPIFun f [a,b]"
 assumes first: "lpc_mgu_unify input_term input_term (LPCUnify left right#gs) sigma"
 and second: "lpc_mgu_unify (lp_isubst left sigma) (lp_isubst right sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs) tau"
 and finite: "lpp_finite_term a" "lpp_finite_term b" "lpp_finite_goals gs"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t tau))
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs))"
proof -
 let ?all = "LPCUnify left right#gs"
 have before: "lpp_finite_goals ?all"
   using finite by (simp add: left_def right_def lpp_finite_goals_def lp_cut_terms.simps)
 have after: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?all)"
   by (rule lpp_reflexive_mgu_finite_goals[OF first before])
 have free: "lpc_free_knowledge {x,y} sigma"
   by (rule lpp_reflexive_mgu_continuation_free[OF first before])
     (auto simp: left_def lp_cut_terms.simps)
 obtain n r where images: "sigma x=LPIVar n" "sigma y=LPIVar r"
   using free by (auto simp: lpc_free_knowledge_def)
 have unequal: "n\<noteq>r" using images free distinct
   by (auto simp: lpc_free_knowledge_def inj_on_def)
 have separated: "set2_lp_iterm (lp_isubst left sigma)\<inter>set2_lp_iterm (lp_isubst right sigma)={}"
 proof (rule lpp_reflexive_mgu_continuation_separation[OF first, where
   g="LPCUnify left right" and h="LPCUnify left right"])
  show "LPCUnify left right\<in>set ?all" by simp
  show "left\<in>set (lp_cut_terms (LPCUnify left right))" by (simp add: lp_cut_terms.simps)
  show "LPCUnify left right\<in>set ?all" by simp
  show "right\<in>set (lp_cut_terms (LPCUnify left right))" by (simp add: lp_cut_terms.simps)
  show "lpp_finite_term left" by (simp add: left_def)
  show "lpp_finite_term right" using finite by (simp add: right_def)
  show "set2_lp_iterm left\<inter>set2_lp_iterm right={}" using fresh by (simp add: left_def right_def)
 qed
 have fin: "lpp_finite_term (lp_isubst a sigma)" "lpp_finite_term (lp_isubst b sigma)"
   "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
   using after by (auto simp: left_def right_def lpp_finite_goals_def lp_cut_terms.simps)
 have no_alias: "{n,r}\<inter>(set2_lp_iterm (lp_isubst a sigma)\<union>set2_lp_iterm (lp_isubst b sigma))={}"
   using separated images by (simp add: left_def right_def)
 show ?thesis by (rule lpp_separated_pair_mgu_finite_goals[OF _ fin unequal no_alias])
   (use second images in \<open>simp add: left_def right_def\<close>)
qed

lemma lpp_argument_list_support:
 "set2_lp_iterm (lpp_argument_list ts)=(\<Union>t\<in>set ts. set2_lp_iterm t)"
 by (induction ts) auto

lemma lpp_normalized_univ_sequence_finite:
 fixes tau :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes first: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (lpp_argument_list (LPIFun (names f) []#ts))#gs) sigma"
 and second: "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (lpp_argument_list (LPIFun (names f) []#ts)) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs) tau"
 and finite: "list_all lpp_finite_term ts" "lpp_finite_goals gs"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t tau))
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs))"
proof (rule lpp_reflexive_then_pair_finite_goals[where
 f="LPCUser ''2:prolog_data_2e''" and x=x and y=y
 and a="LPIFun (names f) []" and b="lpp_argument_list ts" and input_term="LPIFun f ts"])
 show "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
     (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIFun (names f) [],lpp_argument_list ts])#gs) sigma"
   using first by simp
 show "lpc_mgu_unify
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) sigma)
   (lp_isubst (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIFun (names f) [],lpp_argument_list ts]) sigma)
   (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs) tau"
   using second by simp
 show "lpp_finite_term (LPIFun (names f) [])" by simp
 show "lpp_finite_term (lpp_argument_list ts)" using finite(1) by (simp add: lpp_argument_list_finite)
 show "lpp_finite_goals gs" by (rule finite(2))
 show "x\<noteq>y" by (rule distinct)
 show "{x,y}\<inter>(set2_lp_iterm (LPIFun (names f) [])\<union>set2_lp_iterm (lpp_argument_list ts))={}"
   using fresh by (auto simp: lpp_argument_list_support)
qed

ML \<open>
val checked = @{thms lpp_normalized_univ_sequence_finite lpp_reflexive_then_pair_finite_goals lpp_separated_pair_mgu_finite_goals};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite pair unification" else ();
\<close>
end
