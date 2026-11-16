theory LP_Prolog_Scalar_Domain_Interface
 imports LP_Prolog_Scalar_Domain_Prefix LP_Prolog_Scalar_Recurrence_Interface
begin

definition lpp_domain_observations where
 "lpp_domain_observations operation observations actuals =
   (length actuals=length observations \<and>
    list_all (\<lambda>i. case observations!i of None \<Rightarrow> True | Some d \<Rightarrow>
      (\<exists>v. lpp_recurrent_scalar_member d v \<and>
       lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value v))) [0..<length observations])"

lemma lpp_domain_observed_environment:
 assumes lengths: "length H=length observations" and distinct: "distinct H"
   and observations: "lpp_domain_observations operation observations actuals"
 shows "lpp_recurrent_domain_environment operation (lpp_scalar_value_table H observations)
   (lpp_partial_arguments H actuals)"
proof -
 have each: "\<exists>v. lpp_recurrent_scalar_member d v \<and>
     lpp_stable_scalar_evaluation operation (lpp_partial_arguments H actuals x) (lpp_machine_value v)"
   if selected: "lpp_scalar_value_table H observations x=Some d" for x d
 proof -
  obtain i where bound: "i<length H" and name: "x=H!i" and entry: "observations!i=Some d"
    using lpp_scalar_table_position[OF lengths selected] by blast
  have actual_length: "length H=length actuals" using observations lengths
    by (simp add: lpp_domain_observations_def)
  have row: "case observations!i of None \<Rightarrow> True | Some d \<Rightarrow>
      (\<exists>v. lpp_recurrent_scalar_member d v \<and>
       lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value v))"
    using observations bound lengths by (auto simp: lpp_domain_observations_def list_all_iff)
  show ?thesis using row entry name lpp_partial_arguments_nth[OF actual_length distinct bound] by simp
 qed
 show ?thesis using each by (auto simp: lpp_recurrent_domain_environment_def)
qed

lemma lpp_domain_fresh_environment:
 assumes environment: "lpp_recurrent_domain_environment operation domains eta"
   and covered: "\<And>x d. domains x=Some d \<Longrightarrow> x\<in>set H"
 shows "lpp_recurrent_domain_environment operation domains (lpc_fresh_head_environment H eta)"
proof -
 have each: "\<exists>v. lpp_recurrent_scalar_member d v \<and>
     lpp_stable_scalar_evaluation operation (lpc_fresh_head_environment H eta x) (lpp_machine_value v)"
   if selected: "domains x=Some d" for x d
 proof -
  obtain v where member: "lpp_recurrent_scalar_member d v"
    and evaluated: "lpp_stable_scalar_evaluation operation (eta x) (lpp_machine_value v)"
    using environment selected by (auto simp: lpp_recurrent_domain_environment_def)
  have fresh: "lpp_stable_scalar_evaluation operation
      (lp_isubst (eta x) lpc_fresh_caller) (lpp_machine_value v)"
    using lpp_stable_scalar_evaluation_subst[OF evaluated, of lpc_fresh_caller]
    by (simp add: lpp_machine_value_named)
  show ?thesis using member fresh covered[OF selected]
    by (auto simp: lpc_fresh_head_environment_def)
 qed
 show ?thesis using each by (auto simp: lpp_recurrent_domain_environment_def)
qed

definition lpp_recurrent_domain_implies where
 "lpp_recurrent_domain_implies a b =
   (a=b \<or> b=LPPRecurrentInteger \<and> lpp_recurrent_integer_domain a)"
lemma lpp_recurrent_domain_implies_sound:
 "lpp_recurrent_domain_implies a b \<Longrightarrow> lpp_recurrent_scalar_member a v \<Longrightarrow>
   lpp_recurrent_scalar_member b v"
 by (auto simp: lpp_recurrent_domain_implies_def dest: lpp_recurrent_integer_member)

fun lpp_domain_output_check where
 "lpp_domain_output_check domains None t None = True"
| "lpp_domain_output_check domains (Some d) t (Some e) =
   (t=lpp_scalar_template_term e \<and>
    (case lpp_recurrent_template_domain domains e of None \<Rightarrow> False
     | Some result \<Rightarrow> lpp_recurrent_domain_implies result d))"
| "lpp_domain_output_check domains expected t recipe = False"

lemma lpp_domain_output_sound:
 assumes checked: "lpp_domain_output_check domains (Some d) t recipe"
   and environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains eta"
 shows "\<exists>v. lpp_recurrent_scalar_member d v \<and>
   lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (lp_ieval t eta) (lpp_machine_value v)"
proof -
 obtain e result where shape: "t=lpp_scalar_template_term e"
   and expression: "lpp_recurrent_template_domain domains e=Some result"
   and implies: "lpp_recurrent_domain_implies result d"
   using checked by (cases recipe) (auto split: option.splits)
 show ?thesis unfolding shape using lpp_recurrent_template_sound[OF expression environment]
   lpp_recurrent_domain_implies_sound[OF implies] by blast
qed

definition lpp_domain_outputs_check where
 "lpp_domain_outputs_check domains observations actuals recipes =
   (length actuals=length observations \<and> length recipes=length observations \<and>
    list_all (\<lambda>i. lpp_domain_output_check domains (observations!i) (actuals!i) (recipes!i)) [0..<length observations])"
lemma lpp_domain_outputs_sound:
 assumes checked: "lpp_domain_outputs_check domains observations actuals recipes"
   and environment: "lpp_recurrent_domain_environment (lpp_binary64_profile_operation fallback) domains eta"
 shows "lpp_domain_observations (lpp_binary64_profile_operation fallback) observations
   (map (\<lambda>t. lp_ieval t eta) actuals)"
proof -
 have lengths: "length actuals=length observations" using checked by (simp add: lpp_domain_outputs_check_def)
 have each: "\<exists>v. lpp_recurrent_scalar_member d v \<and>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
      (lp_ieval (actuals!i) eta) (lpp_machine_value v)"
   if bound: "i<length observations" and entry: "observations!i=Some d" for i d
 proof -
  have raw: "lpp_domain_output_check domains (observations!i) (actuals!i) (recipes!i)"
    using checked bound by (auto simp: lpp_domain_outputs_check_def list_all_iff)
  have row: "lpp_domain_output_check domains (Some d) (actuals!i) (recipes!i)" using raw entry by simp
  show ?thesis by (rule lpp_domain_output_sound[OF row environment])
 qed
 show ?thesis using lengths each
   by (auto simp: lpp_domain_observations_def list_all_iff split: option.splits)
qed

ML \<open>
val checked = [@{thm lpp_domain_observed_environment}, @{thm lpp_domain_fresh_environment}, @{thm lpp_domain_outputs_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar domain interface dependency" else ();
\<close>
end
