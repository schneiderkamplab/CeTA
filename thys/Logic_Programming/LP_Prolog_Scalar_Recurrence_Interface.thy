theory LP_Prolog_Scalar_Recurrence_Interface
 imports LP_Prolog_Scalar_Recurrence_Iteration LP_Prolog_Partial_Integer_Interface
begin

definition lpp_scalar_value_table where
 "lpp_scalar_value_table H observations x =
   (case map_of (zip H observations) x of None \<Rightarrow> None | Some result \<Rightarrow> result)"

definition lpp_scalar_observations where
 "lpp_scalar_observations operation observations actuals =
   (length actuals=length observations \<and>
    list_all (\<lambda>i. case observations!i of None \<Rightarrow> True | Some w \<Rightarrow>
      lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value w)) [0..<length observations])"

lemma lpp_scalar_table_nth:
 assumes lengths: "length H=length observations" and distinct: "distinct H" and bound: "i<length H"
 shows "lpp_scalar_value_table H observations (H!i)= observations!i"
 using map_of_zip_nth[OF lengths distinct, of i] bound lengths
 by (simp add: lpp_scalar_value_table_def)

lemma lpp_scalar_table_position:
 assumes lengths: "length H=length observations"
   and selected: "lpp_scalar_value_table H observations x=Some w"
 shows "\<exists>i<length H. x=H!i \<and> observations!i=Some w"
proof -
 have member: "(x,Some w)\<in>set (zip H observations)"
   using selected by (auto simp: lpp_scalar_value_table_def split: option.splits dest: map_of_SomeD)
 obtain i where index: "i<length (zip H observations)" and row: "(zip H observations)!i=(x,Some w)"
   using member by (auto simp: in_set_conv_nth)
 show ?thesis using index row lengths by auto
qed

lemma lpp_scalar_table_covered:
 assumes lengths: "length H=length observations"
   and selected: "lpp_scalar_value_table H observations x=Some w"
 shows "x\<in>set H"
 using lpp_scalar_table_position[OF lengths selected] by (auto intro: nth_mem)

lemma lpp_scalar_observed_argument:
 assumes lengths: "length H=length observations" and distinct: "distinct H"
   and observations: "lpp_scalar_observations operation observations actuals"
   and selected: "lpp_scalar_value_table H observations x=Some w"
 shows "lpp_stable_scalar_evaluation operation (lpp_partial_arguments H actuals x) (lpp_machine_value w)"
proof -
 obtain i where bound: "i<length H" and name: "x=H!i" and entry: "observations!i=Some w"
   using lpp_scalar_table_position[OF lengths selected] by blast
 have actual_length: "length H=length actuals" using observations lengths
   by (simp add: lpp_scalar_observations_def)
 have row: "case observations!i of None \<Rightarrow> True | Some v \<Rightarrow>
     lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value v)"
   using observations bound lengths by (auto simp: lpp_scalar_observations_def list_all_iff)
 have evaluated: "lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value w)"
   using row entry by simp
 show ?thesis using lpp_partial_arguments_nth[OF actual_length distinct bound] evaluated name by simp
qed

fun lpp_scalar_output_check where
 "lpp_scalar_output_check value_table None t None = True"
| "lpp_scalar_output_check value_table (Some w) t (Some e) =
    (t=lpp_scalar_template_term e \<and> lpp_scalar_template_evaluate value_table e=Some w)"
| "lpp_scalar_output_check value_table expected t recipe = False"

lemma lpp_scalar_output_sound:
 assumes checked: "lpp_scalar_output_check value_table (Some w) t recipe"
   and parameters: "\<And>x v. value_table x=Some v \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value v)"
 shows "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (lp_ieval t eta) (lpp_machine_value w)"
proof -
 obtain e where same: "t=lpp_scalar_template_term e" and evaluated: "lpp_scalar_template_evaluate value_table e=Some w"
   using checked by (cases recipe) auto
 show ?thesis unfolding same by (rule lpp_scalar_template_sound[OF evaluated parameters])
qed

definition lpp_scalar_outputs_check where
 "lpp_scalar_outputs_check value_table observations actuals recipes =
    (length actuals=length observations \<and> length recipes=length observations \<and>
     list_all (\<lambda>i. lpp_scalar_output_check value_table (observations!i) (actuals!i) (recipes!i)) [0..<length observations])"

lemma lpp_scalar_outputs_sound:
 assumes checked: "lpp_scalar_outputs_check value_table observations actuals recipes"
   and parameters: "\<And>x v. value_table x=Some v \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value v)"
 shows "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations (map (\<lambda>t. lp_ieval t eta) actuals)"
proof -
 have length: "length actuals=length observations"
   using checked by (simp add: lpp_scalar_outputs_check_def)
 have each: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (actuals!i) eta) (lpp_machine_value w)"
   if bound: "i<length observations" and entry: "observations!i=Some w" for i w
 proof -
  have raw: "lpp_scalar_output_check value_table (observations!i) (actuals!i) (recipes!i)"
    using checked bound by (auto simp: lpp_scalar_outputs_check_def list_all_iff)
  have row: "lpp_scalar_output_check value_table (Some w) (actuals!i) (recipes!i)"
    using raw entry by simp
  show ?thesis by (rule lpp_scalar_output_sound[OF row parameters])
 qed
 show ?thesis using length each
   by (auto simp: lpp_scalar_observations_def list_all_iff split: option.splits)
qed

ML \<open>
val checked = [@{thm lpp_scalar_observed_argument}, @{thm lpp_scalar_outputs_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence interface dependency" else ();
\<close>
end
