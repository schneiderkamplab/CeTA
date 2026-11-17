theory LP_Prolog_Finite_Partial_Head
 imports LP_Prolog_Finite_Ground_Head
begin

definition lpp_separated_variable_arguments where
 "lpp_separated_variable_arguments hs =
   (\<forall>i<length hs. \<forall>x. hs!i=Var x \<longrightarrow>
     (\<forall>j<length hs. j\<noteq>i \<longrightarrow> x\<notin>vars_term (hs!j)))"

lemma lpp_partial_head_finite_comparison:
 fixes hs :: "('f,string) term list"
   and actuals :: "('f,string) lp_iterm list"
   and sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes lengths: "length hs=length actuals"
   and separated: "lpp_separated_variable_arguments hs"
   and finite: "list_all lpp_finite_term actuals"
   and ground: "\<And>i. i<length hs \<Longrightarrow> (\<And>x. hs!i\<noteq>Var x) \<Longrightarrow> lp_seg_ground (actuals!i)"
   and equation: "map (\<lambda>t. lp_isubst t sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
 shows "\<exists>nu. (\<forall>x. lpp_finite_term (nu x)) \<and> map (\<lambda>t. lp_ieval t nu) hs=actuals"
proof -
 let ?direct = "\<lambda>x. \<exists>i<length hs. hs!i=Var x"
 let ?pos = "\<lambda>x. SOME i. i<length hs \<and> hs!i=Var x"
 let ?nu = "\<lambda>x. if ?direct x then actuals!?pos x
   else if x\<in>\<Union>(vars_term ` set hs) then rho x else LPIVar x"
 have position: "?pos x<length hs \<and> hs!?pos x=Var x" if "?direct x" for x
   using that by (rule someI_ex)
 have unique: "?pos x=i" if i: "i<length hs" "hs!i=Var x" for i x
 proof -
  have direct: "?direct x" using i by blast
  have p: "?pos x<length hs" "hs!?pos x=Var x" using position[OF direct] by blast+
  show ?thesis
  proof (rule ccontr)
   assume different: "?pos x\<noteq>i"
   have "x\<notin>vars_term (hs!?pos x)"
     using separated i p(1) different unfolding lpp_separated_variable_arguments_def by blast
   then show False by (simp add: p(2))
  qed
 qed
 have components: "lp_isubst (actuals!i) sigma=lp_ieval (hs!i) rho" if "i<length hs" for i
   using arg_cong[OF equation, of "\<lambda>xs. xs!i"] that lengths by simp
 have nondirect: "\<not>?direct x" if i: "i<length hs" and nonvar: "\<And>y. hs!i\<noteq>Var y"
   and x: "x\<in>vars_term (hs!i)" for i x
   using separated i nonvar x unfolding lpp_separated_variable_arguments_def by blast
 have images: "lpp_finite_term (?nu x)" for x
 proof (cases "?direct x")
  case True
  then show ?thesis using position[OF True] finite lengths
    by (auto simp: list_all_iff)
 next
  case False
  show ?thesis
  proof (cases "x\<in>\<Union>(vars_term ` set hs)")
   case False then show ?thesis using \<open>\<not>?direct x\<close> by auto
  next
   case True
   then obtain i where i: "i<length hs" "x\<in>vars_term (hs!i)"
     by (auto simp: in_set_conv_nth)
   have nonvar: "hs!i\<noteq>Var y" for y using False i by auto
   have g: "lp_seg_ground (lp_ieval (hs!i) rho)"
     using components[OF i(1)] ground[OF i(1) nonvar] by (simp add: lp_seg_ground_subst)
   have "lp_seg_ground (rho x)" using g i by (simp add: lp_seg_ground_eval)
   then show ?thesis using False True by (auto intro: lpp_ground_finite_term)
  qed
 qed
 have equal: "lp_ieval (hs!i) ?nu=actuals!i" if i: "i<length hs" for i
 proof (cases "hs!i")
  case (Var x)
  have direct: "?direct x" using i Var by blast
  show ?thesis using unique[OF i Var] direct by (simp add: Var)
 next
  case (Fun f ts)
  have nonvar: "hs!i\<noteq>Var y" for y using Fun by simp
  have same: "lp_ieval (hs!i) ?nu=lp_ieval (hs!i) rho"
  proof (rule lp_ieval_cong)
   fix x assume x: "x\<in>vars_term (hs!i)"
   have member: "x\<in>\<Union>(vars_term ` set hs)" using i x by auto
   show "?nu x=rho x" using nondirect[OF i nonvar x] member by auto
  qed
  show ?thesis using same components[OF i] ground[OF i nonvar]
    by (simp add: lp_seg_ground_subst)
 qed
 have "map (\<lambda>t. lp_ieval t ?nu) hs=actuals"
   by (rule nth_equalityI) (use lengths equal in auto)
 then show ?thesis by (intro exI[of _ "?nu"]) (simp add: images)
qed


lemma lpp_partial_head_resolution_finite:
 assumes mgu: "lpc_mgu_resolve (LPIFun f actuals) gs (Fun f hs) bs sigma rho"
   and separated: "lpp_separated_variable_arguments hs"
   and finite: "list_all lpp_finite_term actuals"
   and ground: "\<And>i. i<length hs \<Longrightarrow> (\<And>x. hs!i\<noteq>Var x) \<Longrightarrow> lp_seg_ground (actuals!i)"
   and continuation: "\<And>g t. g\<in>set gs \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow> lpp_finite_term t"
 shows "(\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). lpp_finite_term (lp_ieval t rho)) \<and>
   (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). lpp_finite_term (lp_isubst t sigma))"
proof -
 have equation: "map (\<lambda>t. lp_isubst t sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have lengths: "length hs=length actuals"
   using arg_cong[OF equation, of length] by simp
 obtain nu where images: "\<And>x. lpp_finite_term (nu x)"
   and exact: "map (\<lambda>t. lp_ieval t nu) hs=actuals"
   using lpp_partial_head_finite_comparison[OF lengths separated finite ground equation] by blast
 have comparison: "lp_isubst (LPIFun f actuals) LPIVar=lp_ieval (Fun f hs) nu"
   by (simp add: exact)
 have body: "lpp_finite_term (lp_ieval t rho)" if member: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
 proof (rule lpp_finite_term_eval)
  fix x assume x: "x\<in>vars_term t"
  show "lpp_finite_term (rho x)"
   by (rule lpp_mgu_body_variable_finite[OF mgu comparison member x images])
 qed
 have rest: "lpp_finite_term (lp_isubst t sigma)" if member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   by (rule lpp_mgu_continuation_finite[OF mgu comparison _ member])
     (simp add: continuation)
 show ?thesis using body rest by blast
qed

ML \<open>
val checked = [@{thm lpp_partial_head_finite_comparison},
 @{thm lpp_partial_head_resolution_finite}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted partial head comparison" else ();
\<close>
end
