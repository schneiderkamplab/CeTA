theory LP_Prolog_Finite_Head_Check
 imports LP_Prolog_Finite_Partial_Head LP_Prolog_Finite_Direct_State
begin

fun lpp_head_argument_separated where
 "lpp_head_argument_separated hs i (Var x) =
   list_all (\<lambda>j. j=i \<or> x\<notin>vars_term (hs!j)) [0..<length hs]"
| "lpp_head_argument_separated hs i (Fun f ts) = True"

definition lpp_check_separated_head where
 "lpp_check_separated_head hs =
   list_all (\<lambda>i. lpp_head_argument_separated hs i (hs!i)) [0..<length hs]"

lemma lpp_check_separated_head_sound:
 assumes checked: "lpp_check_separated_head hs"
 shows "lpp_separated_variable_arguments hs"
 unfolding lpp_separated_variable_arguments_def
 proof (intro allI impI)
 fix i x j
 assume i: "i<length hs" and shape: "hs!i=Var x"
   and j: "j<length hs" and different: "j\<noteq>i"
 have local_check: "lpp_head_argument_separated hs i (hs!i)"
   using checked i by (simp add: lpp_check_separated_head_def list_all_iff)
 have "list_all (\<lambda>j. j=i \<or> x\<notin>vars_term (hs!j)) [0..<length hs]"
   using local_check by (simp add: shape)
 then show "x\<notin>vars_term (hs!j)" using j different by (auto simp: list_all_iff)
qed

fun lpp_check_head_argument_domain where
 "lpp_check_head_argument_domain G a (Var x) = True"
| "lpp_check_head_argument_domain G a (Fun f ts) = (vars_term a \<subseteq> set G)"

definition lpp_check_finite_head where
 "lpp_check_finite_head G actuals hs =
   (length actuals=length hs \<and>
     (list_all (\<lambda>a. vars_term a \<subseteq> set G) actuals \<or>
      (lpp_check_separated_head hs \<and>
       list_all (\<lambda>i. lpp_check_head_argument_domain G (actuals!i) (hs!i)) [0..<length hs])))"

lemma lpp_checked_head_finite_terms:
 assumes checked: "lpp_check_finite_head G actuals hs"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and mgu: "lpc_mgu_resolve (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals)) gs (Fun f hs) bs sigma rho"
   and finite: "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t eta) actuals)"
   and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have old: "lpp_finite_term t" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   using continuation that by (auto simp: lpp_finite_goals_def list_all_iff)
 show ?thesis
 proof (cases "list_all (\<lambda>a. vars_term a \<subseteq> set G) actuals")
  case True
  have ground: "lp_seg_ground (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals))"
    using True known by (auto simp: list_all_iff lp_seg_ground_eval)
  have body: "lpp_finite_term (lp_ieval t rho)" if "g\<in>set bs" "t\<in>set (lp_cut_terms g)" for g t
    by (rule lpp_ground_head_finite_body[OF mgu ground that])
  have rest: "lpp_finite_term (lp_isubst t sigma)" if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
    by (rule lpp_ground_head_finite_continuation[OF mgu ground old that])
  show ?thesis using body rest
    by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms lpp_finite_goal_map list_all_iff)
 next
  case False
  have separated: "lpp_separated_variable_arguments hs"
   using checked False lpp_check_separated_head_sound by (auto simp: lpp_check_finite_head_def)
  have ground: "lp_seg_ground ((map (\<lambda>t. lp_ieval t eta) actuals)!i)"
   if i: "i<length hs" and nonvar: "\<And>x. hs!i\<noteq>Var x" for i
  proof -
   obtain f ts where shape: "hs!i=Fun f ts" using nonvar by (cases "hs!i") auto
   have length: "length actuals=length hs"
    and checks: "list_all (\<lambda>j. lpp_check_head_argument_domain G (actuals!j) (hs!j)) [0..<length hs]"
    using checked False by (auto simp: lpp_check_finite_head_def)
   have selected: "lpp_check_head_argument_domain G (actuals!i) (hs!i)"
    using checks i by (auto simp: list_all_iff)
   have vars: "vars_term (actuals!i) \<subseteq> set G"
    using selected by (simp add: shape)
   show ?thesis using known vars i length by (auto simp: lp_seg_ground_eval)
  qed
  have terms: "(\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). lpp_finite_term (lp_ieval t rho)) \<and>
    (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). lpp_finite_term (lp_isubst t sigma))"
   by (rule lpp_partial_head_resolution_finite[OF mgu separated finite ground old])
  show ?thesis using terms
   by (auto simp: lpp_finite_goals_def lpp_finite_goal_bind_terms lpp_finite_goal_map list_all_iff)
 qed
qed


lemma lpp_checked_head_finite_direct_goals:
 assumes checked: "lpp_check_finite_head G actuals hs"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and mgu: "lpc_mgu_resolve (LPIFun f (map (\<lambda>t. lp_ieval t eta) actuals)) gs (Fun f hs) bs sigma rho"
   and finite: "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t eta) actuals)"
   and continuation: "lpp_finite_direct_goals gs"
   and body: "list_all lpp_direct_source_goal bs"
 shows "lpp_finite_direct_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 have terms: "lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
   by (rule lpp_checked_head_finite_terms[OF checked known mgu finite
     lpp_finite_direct_goals_terms[OF continuation]])
 have bound: "lpp_finite_direct_goal (lp_cut_bind m (\<lambda>t. lp_ieval t rho) g)"
   if "g\<in>set bs" for g
 proof (rule lpp_finite_direct_intro)
  show "list_all lpp_finite_term (lp_cut_terms (lp_cut_bind m (\<lambda>t. lp_ieval t rho) g))"
    using terms that by (auto simp: lpp_finite_goals_def list_all_iff)
  show "case lp_cut_bind m (\<lambda>t. lp_ieval t rho) g of
    LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts | LPCMeta a \<Rightarrow> False
    | LPCExpand a m \<Rightarrow> False | LPCUnify a b \<Rightarrow> \<exists>f. b=LPIFun (LPCUser f) [] | _ \<Rightarrow> True"
    by (rule lpp_direct_bind_shape) (use body that in \<open>auto simp: list_all_iff\<close>)
 qed
 have mapped: "lpp_finite_direct_goal (lp_cut_map (\<lambda>t. lp_isubst t sigma) g)"
   if "g\<in>set gs" for g
 proof (rule lpp_finite_direct_intro)
  show "list_all lpp_finite_term (lp_cut_terms (lp_cut_map (\<lambda>t. lp_isubst t sigma) g))"
    using terms that by (auto simp: lpp_finite_goals_def list_all_iff)
  show "case lp_cut_map (\<lambda>t. lp_isubst t sigma) g of
    LPCAtom a \<Rightarrow> \<exists>f ts. a=LPIFun f ts | LPCMeta a \<Rightarrow> False
    | LPCExpand a m \<Rightarrow> False | LPCUnify a b \<Rightarrow> \<exists>f. b=LPIFun (LPCUser f) [] | _ \<Rightarrow> True"
    by (rule lpp_direct_map_shape) (use continuation that in \<open>auto simp: list_all_iff\<close>)
 qed
 show ?thesis using bound mapped by (auto simp: list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_check_separated_head_sound}, @{thm lpp_checked_head_finite_terms},
 @{thm lpp_checked_head_finite_direct_goals}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked finite head" else ();
\<close>
end
