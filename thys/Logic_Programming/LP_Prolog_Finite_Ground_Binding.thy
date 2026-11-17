theory LP_Prolog_Finite_Ground_Binding
 imports LP_Prolog_Finite_Scalar_Unify LP_Prolog_Evaluation_Context
begin

text \<open>Binding a runtime variable to a ground constructor tree preserves
  finite continuation goals. Groundness is required of the whole right side;
  neither freeness alone nor a finite representation of a cycle suffices.\<close>

lemma lpp_ground_binding_finite_comparison:
 assumes ground: "lp_seg_ground b"
 shows "lp_isubst (LPIVar x) (LPIVar(x := b)) = lp_isubst b (LPIVar(x := b))"
   and "lpp_finite_term ((LPIVar(x := b)) y)"
 using ground by (auto simp: lp_seg_ground_subst intro: lpp_ground_finite_term)

lemma lpp_ground_binding_mgu_finite_goals:
 assumes mgu: "lpc_mgu_unify (LPIVar x) b gs sigma"
 and ground: "lp_seg_ground b"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?mu = "LPIVar(x := b)"
 have comparison: "lp_isubst (LPIVar x) ?mu=lp_isubst b ?mu"
  by (rule lpp_ground_binding_finite_comparison(1)[OF ground])
 have images: "lpp_finite_term (?mu y)" for y
  by (rule lpp_ground_binding_finite_comparison(2)[OF ground])
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  using finite that by (auto simp: lpp_finite_goals_def list_all_iff)
 have mapped: "lpp_finite_term (lp_isubst t sigma)"
  if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  by (rule lpp_mgu_unify_continuation_finite[OF mgu comparison _ that])
    (auto intro: lpp_finite_term_substitute[OF old images])
 show ?thesis using mapped
  by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

lemma lpp_ground_binding_symbolic_finite_goals:
 assumes mgu: "lpc_mgu_unify (lp_ieval (Var x) eta) (lp_ieval value_term eta) gs sigma"
 and free: "lpc_free_knowledge F eta" and member: "x\<in>F"
 and ground: "\<forall>y\<in>vars_term value_term. lp_seg_ground (eta y)"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 obtain v where variable: "eta x=LPIVar v"
  using free member by (auto simp: lpc_free_knowledge_def)
 have value_term: "lp_seg_ground (lp_ieval value_term eta)" using ground by (simp add: lp_seg_ground_eval)
 show ?thesis by (rule lpp_ground_binding_mgu_finite_goals[OF _ value_term finite])
   (use mgu variable in simp)
qed

lemma lpp_finite_substitution_ground_images:
 assumes finite: "lpp_finite_term a" and ground: "lp_seg_ground (lp_isubst a sigma)"
 and member: "x\<in>set2_lp_iterm a"
 shows "lp_seg_ground (sigma x)"
 using finite ground member
 by (induction rule: lpp_finite_term.induct) (auto simp: list_all_iff)

lemma lpp_finite_substitution_cong:
 assumes finite: "lpp_finite_term a"
 and same: "\<And>x. x\<in>set2_lp_iterm a \<Longrightarrow> left_substitution x=right_substitution x"
 shows "lp_isubst a left_substitution=lp_isubst a right_substitution"
 using finite same
 by (induction rule: lpp_finite_term.induct) (auto simp: list_all_iff intro!: map_cong)

lemma lpp_ground_equality_mgu_finite_goals:
 assumes mgu: "lpc_mgu_unify a b gs sigma"
 and input: "lpp_finite_term a"
 and ground: "lp_seg_ground b"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 let ?mu = "\<lambda>x. if x\<in>set2_lp_iterm a then sigma x else LPIVar x"
 have unified: "lp_isubst a sigma=b"
  using mgu ground by (simp add: lpc_mgu_unify_def lp_seg_ground_subst)
 have same: "lp_isubst a ?mu=lp_isubst a sigma"
  by (rule lpp_finite_substitution_cong[OF input]) simp
 have comparison: "lp_isubst a ?mu=lp_isubst b ?mu"
  using same unified ground by (simp add: lp_seg_ground_subst)
 have images: "lpp_finite_term (?mu x)" for x
  using lpp_finite_substitution_ground_images[OF input ground[folded unified], of x]
  by (auto intro: lpp_ground_finite_term)
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  using finite that by (auto simp: lpp_finite_goals_def list_all_iff)
 have mapped: "lpp_finite_term (lp_isubst t sigma)"
  if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
  by (rule lpp_mgu_unify_continuation_finite[OF mgu comparison _ that])
    (auto intro: lpp_finite_term_substitute[OF old images])
 show ?thesis using mapped
  by (auto simp: lpp_finite_goals_def lpp_finite_goal_map list_all_iff)
qed

lemma lpp_checked_ground_equality_finite_goals:
 assumes checked: "vars_term b \<subseteq> set G"
 and known: "lp_cut_knowledge (set G) guards eta"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) gs sigma"
 and input: "lpp_finite_term (lp_ieval a eta)"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
 by (rule lpp_ground_equality_mgu_finite_goals[OF mgu input _ finite])
   (use checked known in \<open>auto simp: lp_cut_knowledge_def lp_seg_ground_eval\<close>)

lemma lpp_context_ground_equality_finite_goals:
 assumes checked: "vars_term b \<subseteq> set G \<union> lpp_source_context_ground ctx"
 and known: "lp_cut_knowledge (set G) guards eta"
 and observed: "lpp_evaluation_context_holds E SP ctx eta"
 and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) gs sigma"
 and input: "lpp_finite_term (lp_ieval a eta)"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
 by (rule lpp_ground_equality_mgu_finite_goals[OF mgu input _ finite])
   (use checked known lpp_evaluation_context_ground_sound[OF evaluation observed]
    in \<open>auto simp: lp_cut_knowledge_def lp_seg_ground_eval\<close>)

definition lpp_check_finite_ground_binding where
 "lpp_check_finite_ground_binding G F a b =
  (\<exists>x. a=Var x \<and> x\<in>set F \<and> vars_term b \<subseteq> set G)"

lemma lpp_checked_ground_binding_finite_goals:
 assumes checked: "lpp_check_finite_ground_binding G F a b"
 and known: "lp_cut_knowledge (set G) guards eta"
 and free: "lpc_free_knowledge (set F) eta"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) gs sigma"
 and finite: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 obtain x where shape: "a=Var x" and member: "x\<in>set F" and cover: "vars_term b \<subseteq> set G"
  using checked by (auto simp: lpp_check_finite_ground_binding_def)
 show ?thesis by (rule lpp_ground_binding_symbolic_finite_goals[OF mgu[unfolded shape] free member _ finite])
  (use known cover in \<open>auto simp: lp_cut_knowledge_def\<close>)
qed

lemma lpp_ground_binding_missing_freeness_rejected:
 "\<not> lpp_check_finite_ground_binding G [] a b"
 by (simp add: lpp_check_finite_ground_binding_def)

lemma lpp_ground_binding_missing_groundness_rejected:
 "\<not> lpp_check_finite_ground_binding [] [x] (Var x) (Fun f [Var y])"
 by (simp add: lpp_check_finite_ground_binding_def)

lemma lpp_ground_binding_constructor_checked:
 "lpp_check_finite_ground_binding [y] [x] (Var x) (Fun f [Fun tag [],Var y])"
 by (simp add: lpp_check_finite_ground_binding_def)

ML \<open>
val checked = @{thms lpp_context_ground_equality_finite_goals lpp_checked_ground_equality_finite_goals lpp_ground_equality_mgu_finite_goals lpp_checked_ground_binding_finite_goals lpp_ground_binding_mgu_finite_goals lpp_ground_binding_symbolic_finite_goals};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite ground binding" else ();
\<close>
end
