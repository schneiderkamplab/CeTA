theory LP_Prolog_Finite_Fresh_Body
 imports LP_Prolog_Finite_Univ
begin

text \<open>A body-only variable is not merely free: under most-general
resolution it cannot occur inside the finite instantiated head. This supplies
runtime nonalias information for subsequent constructor decomposition.\<close>

lemma lpp_finite_subst_fixed_variable:
 assumes finite: "lpp_finite_term t"
 and fixed: "lp_isubst t sigma=t"
 and member: "x\<in>set2_lp_iterm t"
 shows "sigma x=LPIVar x"
 using finite fixed member
 apply (induction rule: lpp_finite_term.induct)
 apply (auto simp: list_all_iff)
 by (metis map_id map_eq_conv id_apply)

lemma lpp_mgu_fresh_body_avoids_finite_head:
 fixes a :: "('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
 and fresh: "x\<notin>vars_term h"
 and variable: "rho x=LPIVar y"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "y\<notin>set2_lp_iterm (lp_isubst a sigma)"
proof
 assume occurs: "y\<in>set2_lp_iterm (lp_isubst a sigma)"
 let ?nu = "rho(x := LPIFun undefined [])"
 have head: "lp_ieval h ?nu=lp_ieval h rho"
  by (rule lp_ieval_cong) (use fresh in auto)
 have comparison: "lp_isubst a sigma=lp_ieval h ?nu"
  using mgu head by (simp add: lpc_mgu_resolve_def)
 obtain delta where active: "lp_isubst (lp_isubst a sigma) delta=lp_isubst a sigma"
 and mapped: "map (lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u rho) delta)) bs =
   map (lp_cut_map (\<lambda>u. lp_ieval u ?nu)) bs"
  using mgu comparison unfolding lpc_mgu_resolve_def by blast
 have fixed_y: "delta y=LPIVar y"
  by (rule lpp_finite_subst_fixed_variable[OF finite active occurs])
 have goal_equal: "lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u rho) delta) g =
   lp_cut_map (\<lambda>u. lp_ieval u ?nu) g"
  using mapped body(1) by (simp add: map_eq_conv)
 have term_equal: "lp_isubst (lp_ieval t rho) delta=lp_ieval t ?nu"
  using goal_equal body(2) by (cases g) auto
 have evaluated: "lp_ieval t (\<lambda>z. lp_isubst (rho z) delta)=lp_ieval t ?nu"
  using term_equal by (simp add: lp_ieval_subst)
 have image: "lp_isubst (rho x) delta=?nu x"
  using lpc_ieval_variables_eq[OF evaluated body(3)] by simp
 show False using image variable fixed_y by simp
qed

lemma lpp_ieval_variable_support:
 "x\<in>vars_term t \<Longrightarrow> set2_lp_iterm (eta x) \<subseteq> set2_lp_iterm (lp_ieval t eta)"
 by (induction t) auto

definition lpp_check_fresh_decomposition where
 "lpp_check_fresh_decomposition h bs input_variable name_variable arguments_variable =
  (input_variable\<in>vars_term h \<and>
   name_variable\<in>lpc_body_only_variables h bs \<and>
   arguments_variable\<in>lpc_body_only_variables h bs \<and>
   name_variable\<noteq>arguments_variable)"

lemma lpp_check_fresh_decomposition_sound:
 assumes checked: "lpp_check_fresh_decomposition h bs input_variable name_variable arguments_variable"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "\<exists>n r. rho name_variable=LPIVar n \<and> rho arguments_variable=LPIVar r \<and>
   n\<noteq>r \<and> n\<notin>set2_lp_iterm (rho input_variable) \<and>
   r\<notin>set2_lp_iterm (rho input_variable)"
proof -
 have free: "lpc_free_knowledge (lpc_body_only_variables h bs) rho"
  by (rule lpc_mgu_body_only_knowledge[OF mgu])
 have name_member: "name_variable\<in>lpc_body_only_variables h bs"
  and args_member: "arguments_variable\<in>lpc_body_only_variables h bs"
  and unequal: "name_variable\<noteq>arguments_variable"
  using checked by (auto simp: lpp_check_fresh_decomposition_def)
 obtain n where name: "rho name_variable=LPIVar n"
  using free name_member by (auto simp: lpc_free_knowledge_def)
 obtain r where arguments: "rho arguments_variable=LPIVar r"
  using free args_member by (auto simp: lpc_free_knowledge_def)
 have different: "n\<noteq>r"
  using free name_member args_member unequal name arguments
  by (auto simp: lpc_free_knowledge_def inj_on_def)
 note vars = name arguments
 have avoided: "y\<notin>set2_lp_iterm (lp_isubst a sigma)"
  if body_member: "z\<in>lpc_body_only_variables h bs" and runtime: "rho z=LPIVar y" for z y
 proof -
  obtain g t where member: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "z\<in>vars_term t"
   and absent: "z\<notin>vars_term h"
   using body_member by (auto simp: lpc_body_only_variables_def)
  show ?thesis by (rule lpp_mgu_fresh_body_avoids_finite_head[OF mgu member absent runtime finite])
 qed
 have head: "lp_isubst a sigma=lp_ieval h rho" using mgu by (simp add: lpc_mgu_resolve_def)
 have included: "set2_lp_iterm (rho input_variable) \<subseteq> set2_lp_iterm (lp_isubst a sigma)"
  unfolding head by (rule lpp_ieval_variable_support)
   (use checked in \<open>simp add: lpp_check_fresh_decomposition_def\<close>)
 show ?thesis using checked avoided vars different included
  unfolding lpp_check_fresh_decomposition_def by blast
qed

lemma lpp_fresh_decomposition_clause_checked:
 "lpp_check_fresh_decomposition (Fun p [Var (0::nat)])
   [LPCAtom (Fun q [Var 0,Var 1,Var 2])] 0 1 2"
 by (simp add: lpp_check_fresh_decomposition_def lpc_body_only_variables_def)

lemma lpp_fresh_decomposition_missing_output_rejected:
 "\<not> lpp_check_fresh_decomposition (Fun p [Var (0::nat)])
   [LPCAtom (Fun q [Var 0,Var 1])] 0 1 2"
 by (simp add: lpp_check_fresh_decomposition_def lpc_body_only_variables_def)

lemma lpp_fresh_decomposition_input_alias_rejected:
 "\<not> lpp_check_fresh_decomposition h bs x x y"
 by (auto simp: lpp_check_fresh_decomposition_def lpc_body_only_variables_def)

lemma lpp_fresh_decomposition_output_alias_rejected:
 "\<not> lpp_check_fresh_decomposition h bs x y y"
 by (simp add: lpp_check_fresh_decomposition_def)

text \<open>The native clause receipt additionally binds freshness to the first
  source operation. A later univ goal cannot inherit entry separation through
  arbitrary intervening unification.\<close>

definition lpp_check_fresh_univ_clause where
 "lpp_check_fresh_univ_clause h bs input_variable name_variable arguments_variable =
  (lpp_check_fresh_decomposition h bs input_variable name_variable arguments_variable \<and>
   (\<exists>gs. bs=LPCAtom (Fun (LPCUser ''2:=..'') [Var input_variable,
     Fun (LPCUser ''2:prolog_data_2e'') [Var name_variable,Var arguments_variable]])#gs))"

lemma lpp_check_fresh_univ_clause_sound:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 shows "\<exists>n r. rho y=LPIVar n \<and> rho z=LPIVar r \<and>
   n\<noteq>r \<and> n\<notin>set2_lp_iterm (rho x) \<and> r\<notin>set2_lp_iterm (rho x)"
 by (rule lpp_check_fresh_decomposition_sound[OF _ mgu finite])
   (use checked in \<open>simp add: lpp_check_fresh_univ_clause_def\<close>)

lemma lpp_fresh_univ_intervening_unification_rejected:
 "\<not> lpp_check_fresh_univ_clause h (LPCUnify a b#bs) x y z"
 by (simp add: lpp_check_fresh_univ_clause_def)

lemma lpp_fresh_univ_head_alias_rejected:
 "y\<in>vars_term h \<Longrightarrow> \<not> lpp_check_fresh_univ_clause h bs x y z"
 by (auto simp: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def lpc_body_only_variables_def)

lemma lpp_finite_eval_variable:
 "x\<in>vars_term t \<Longrightarrow> lpp_finite_term (lp_ieval t eta) \<Longrightarrow> lpp_finite_term (eta x)"
 by (induction t) (auto simp: list_all_iff)

lemma lpp_fresh_univ_clause_finite_continuation:
 assumes checked: "lpp_check_fresh_univ_clause h bs x y z"
 and resolved: "lpc_mgu_resolve a gs h bs sigma rho"
 and finite: "lpp_finite_term (lp_isubst a sigma)"
 and constructor: "rho x=LPIFun f ts"
 and outcome: "lpp_univ_decompose_outcome names (rho x)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]) (LPPBuiltinSuccess mu)"
 and goals: "lpp_finite_goals rest"
 shows "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) rest)"
proof -
 obtain n r where fields: "rho y=LPIVar n" "rho z=LPIVar r"
 and distinct: "n\<noteq>r"
 and fresh: "n\<notin>set2_lp_iterm (rho x)" "r\<notin>set2_lp_iterm (rho x)"
  using lpp_check_fresh_univ_clause_sound[OF checked resolved finite] by blast
 have head: "lp_isubst a sigma=lp_ieval h rho"
  using resolved by (simp add: lpc_mgu_resolve_def)
 have member: "x\<in>vars_term h"
  using checked by (simp add: lpp_check_fresh_univ_clause_def lpp_check_fresh_decomposition_def)
 have input_finite: "lpp_finite_term (rho x)"
  by (rule lpp_finite_eval_variable[OF member]) (use finite head in simp)
 show ?thesis
  by (rule lpp_fresh_univ_finite_goals[OF _ _ distinct _ _ goals])
    (use outcome input_finite fresh in \<open>simp_all add: fields constructor\<close>)
qed

ML \<open>
val checked = [@{thm lpp_fresh_univ_clause_finite_continuation}, @{thm lpp_check_fresh_univ_clause_sound}, @{thm lpp_check_fresh_decomposition_sound}, @{thm lpp_mgu_fresh_body_avoids_finite_head}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted fresh body separation dependency" else ();
\<close>
end
