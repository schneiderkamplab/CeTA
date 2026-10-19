theory Higher_Order_Meta_Checker
  imports Higher_Order_Meta_Polynomial
begin

definition ho_meta_rule_polynomial where
  "ho_meta_rule_polynomial S ps G p = ho_meta_polynomial S G [] ps p"

definition ho_check_meta_rule_ge where
  "ho_check_meta_rule_ge S ps fuel G l r =
    (case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False | Some A \<Rightarrow>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      ho_check_polynomial_ge fuel G A (ho_meta_rule_polynomial S ps G l) (ho_meta_rule_polynomial S ps G r))"

definition ho_check_meta_rule_gt where
  "ho_check_meta_rule_gt S ps fuel G l r =
    (case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False | Some A \<Rightarrow>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      ho_check_polynomial_gt fuel G A (ho_meta_rule_polynomial S ps G l) (ho_meta_rule_polynomial S ps G r))"

theorem ho_check_meta_rule_ge_sound:
  assumes signature: "ho_check_polynomial_signature S ps"
    and check: "ho_check_meta_rule_ge S ps fuel G l r"
  shows "ho_meta_rule_weak S (ho_polynomial_interpretation ps) G l r"
proof -
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    and order: "ho_check_polynomial_ge fuel G A (ho_meta_rule_polynomial S ps G l) (ho_meta_rule_polynomial S ps G r)"
    using check by (auto simp: ho_check_meta_rule_ge_def split: option.splits)
  have ge: "ho_value_ge A (ho_pattern_interpretation S G [] (ho_polynomial_interpretation ps) e e l)
      (ho_pattern_interpretation S G [] (ho_polynomial_interpretation ps) e e r)"
    if "ho_env_value G e" for e
    using ho_check_polynomial_ge_sound[OF order that]
    by (simp add: ho_meta_rule_polynomial_def ho_meta_polynomial_eval[OF l signature] ho_meta_polynomial_eval[OF r signature])
  show ?thesis unfolding ho_meta_rule_weak_def using l r ge by blast
qed

theorem ho_check_meta_rule_gt_sound:
  assumes signature: "ho_check_polynomial_signature S ps"
    and check: "ho_check_meta_rule_gt S ps fuel G l r"
  shows "ho_meta_rule_strict S (ho_polynomial_interpretation ps) G l r"
proof -
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    and order: "ho_check_polynomial_gt fuel G A (ho_meta_rule_polynomial S ps G l) (ho_meta_rule_polynomial S ps G r)"
    using check by (auto simp: ho_check_meta_rule_gt_def split: option.splits)
  have gt: "ho_value_gt A (ho_pattern_interpretation S G [] (ho_polynomial_interpretation ps) e e l)
      (ho_pattern_interpretation S G [] (ho_polynomial_interpretation ps) e e r)"
    if "ho_env_value G e" for e
    using ho_check_polynomial_gt_sound[OF order that]
    by (simp add: ho_meta_rule_polynomial_def ho_meta_polynomial_eval[OF l signature] ho_meta_polynomial_eval[OF r signature])
  show ?thesis unfolding ho_meta_rule_strict_def using l r gt by blast
qed

definition ho_meta_polynomial_residual where
  "ho_meta_polynomial_residual S ps fuel R = filter (\<lambda>(G,l,r). \<not>ho_check_meta_rule_gt S ps fuel G l r) R"

definition ho_check_meta_removal where
  "ho_check_meta_removal S ps fuel R =
    (ho_check_polynomial_signature S ps \<and>
      list_all (\<lambda>(G,l,r). ho_check_meta_rule_ge S ps fuel G l r) R)"

theorem ho_check_meta_removal_sound:
  assumes check: "ho_check_meta_removal S ps fuel R"
    and residual: "wf ((ho_relation S V (ho_meta_polynomial_residual S ps fuel R) A)\<inverse>)"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have signature: "ho_check_polynomial_signature S ps"
    and weak: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_check_meta_rule_ge S ps fuel G l r"
    using check by (auto simp: ho_check_meta_removal_def list_all_iff)
  have ev: "ho_env_value V (\<lambda>n. ho_zero (V!n))" by (simp add: ho_env_value_def ho_zero_value)
  show ?thesis
  proof (rule ho_meta_semantic_rule_removal[OF residual ho_polynomial_signature_closed[OF signature]
      ho_polynomial_signature_value[OF signature] ev])
    fix G l r assume member: "(G,l,r)\<in>set R"
    show "ho_meta_rule_weak S (ho_polynomial_interpretation ps) G l r"
      by (rule ho_check_meta_rule_ge_sound[OF signature weak[OF member]])
  next
    fix G l r assume member: "(G,l,r)\<in>set R" and missing: "(G,l,r)\<notin>set (ho_meta_polynomial_residual S ps fuel R)"
    have strict: "ho_check_meta_rule_gt S ps fuel G l r"
      using member missing by (simp add: ho_meta_polynomial_residual_def)
    show "ho_meta_rule_strict S (ho_polynomial_interpretation ps) G l r"
      by (rule ho_check_meta_rule_gt_sound[OF signature strict])
  qed
qed


fun ho_check_meta where
  "ho_check_meta S R (HOMPolynomial ps fuel child)=(ho_check_meta_removal S ps fuel R \<and>
    ho_check_meta S (ho_meta_polynomial_residual S ps fuel R) child)"
| "ho_check_meta S R cert=ho_check_modular S R cert"

theorem ho_check_meta_sound:
  "ho_check_meta S R cert \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
  by (induction cert arbitrary: R)
    (auto intro: ho_check_modular_sound ho_check_meta_removal_sound
      ho_check_termination_sound ho_check_functional_access_schema_sound
      ho_check_lambda_access_schema_sound ho_check_semantic_schema_sound
      ho_check_component_schema_sound)

end

