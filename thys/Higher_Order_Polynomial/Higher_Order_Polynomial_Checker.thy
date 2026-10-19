theory Higher_Order_Polynomial_Checker
  imports Higher_Order_Polynomial_Dominance "Higher_Order_Computability.Higher_Order_General_Schema"
begin

fun ho_check_polynomial_ge where
  "ho_check_polynomial_ge fuel G (HBase b) p q =
    (ho_check_base_polynomial_ge G b (ho_polynomial_normalize fuel p) (ho_polynomial_normalize fuel q) \<or>
     ho_check_monotone_base_ge G b (ho_polynomial_normalize fuel p) (ho_polynomial_normalize fuel q))"
| "ho_check_polynomial_ge fuel G (HArrow A B) p q = ho_check_polynomial_ge fuel (A#G) B
    (HPApply A B (ho_polynomial_rename Suc p) (HPVar 0))
    (HPApply A B (ho_polynomial_rename Suc q) (HPVar 0))"

fun ho_check_polynomial_gt where
  "ho_check_polynomial_gt fuel G (HBase b) p q =
    (ho_check_base_polynomial_gt G b (ho_polynomial_normalize fuel p) (ho_polynomial_normalize fuel q) \<or>
     ho_check_monotone_base_gt G b (ho_polynomial_normalize fuel p) (ho_polynomial_normalize fuel q))"
| "ho_check_polynomial_gt fuel G (HArrow A B) p q = ho_check_polynomial_gt fuel (A#G) B
    (HPApply A B (ho_polynomial_rename Suc p) (HPVar 0))
    (HPApply A B (ho_polynomial_rename Suc q) (HPVar 0))"

theorem ho_check_polynomial_ge_sound:
  "ho_check_polynomial_ge fuel G A p q \<Longrightarrow> ho_env_value G e \<Longrightarrow>
    ho_value_ge A (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof (induction A arbitrary: G p q e)
  case (HBase b)
  have checked: "ho_value_ge (HBase b) (ho_polynomial_eval e (ho_polynomial_normalize fuel p))
      (ho_polynomial_eval e (ho_polynomial_normalize fuel q))"
    using HBase.prems by (simp only: ho_check_polynomial_ge.simps;
      blast intro: ho_check_base_polynomial_ge_sound ho_check_monotone_base_ge_sound)
  have eq: "ho_value_ge (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q) =
      ho_value_ge (HBase b) (ho_polynomial_eval e (ho_polynomial_normalize fuel p))
        (ho_polynomial_eval e (ho_polynomial_normalize fuel q))"
    by (rule ho_ge_beta[OF ho_polynomial_normalize_path ho_polynomial_normalize_path])
  show ?case using checked eq by simp
next
  case (HArrow A B)
  show ?case unfolding ho_value_ge.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have ev: "ho_env_value (A#G) (ho_env_cons x e)" by (rule ho_env_cons_value[OF x HArrow.prems(2)])
    have checked: "ho_check_polynomial_ge fuel (A#G) B
      (HPApply A B (ho_polynomial_rename Suc p) (HPVar 0))
      (HPApply A B (ho_polynomial_rename Suc q) (HPVar 0))" using HArrow.prems(1) by simp
    show "ho_value_ge B (App (ho_polynomial_eval e p) x) (App (ho_polynomial_eval e q) x)"
      using HArrow.IH(2)[OF checked ev] by (simp add: ho_polynomial_eval_rename ho_env_cons_def)
  qed
qed

theorem ho_check_polynomial_gt_sound:
  "ho_check_polynomial_gt fuel G A p q \<Longrightarrow> ho_env_value G e \<Longrightarrow>
    ho_value_gt A (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof (induction A arbitrary: G p q e)
  case (HBase b)
  have checked: "ho_value_gt (HBase b) (ho_polynomial_eval e (ho_polynomial_normalize fuel p))
      (ho_polynomial_eval e (ho_polynomial_normalize fuel q))"
    using HBase.prems by (simp only: ho_check_polynomial_gt.simps;
      blast intro: ho_check_base_polynomial_gt_sound ho_check_monotone_base_gt_sound)
  have eq: "ho_value_gt (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q) =
      ho_value_gt (HBase b) (ho_polynomial_eval e (ho_polynomial_normalize fuel p))
        (ho_polynomial_eval e (ho_polynomial_normalize fuel q))"
    by (rule ho_gt_beta[OF ho_polynomial_normalize_path ho_polynomial_normalize_path])
  show ?case using checked eq by simp
next
  case (HArrow A B)
  show ?case unfolding ho_value_gt.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value A x"
    have ev: "ho_env_value (A#G) (ho_env_cons x e)" by (rule ho_env_cons_value[OF x HArrow.prems(2)])
    have checked: "ho_check_polynomial_gt fuel (A#G) B
      (HPApply A B (ho_polynomial_rename Suc p) (HPVar 0))
      (HPApply A B (ho_polynomial_rename Suc q) (HPVar 0))" using HArrow.prems(1) by simp
    show "ho_value_gt B (App (ho_polynomial_eval e p) x) (App (ho_polynomial_eval e q) x)"
      using HArrow.IH(2)[OF checked ev] by (simp add: ho_polynomial_eval_rename ho_env_cons_def)
  qed
qed

definition ho_rule_polynomial where
  "ho_rule_polynomial S ps G p = ho_polynomial_translate ps (ho_compile S G [] (ho_erase_pattern p))"

definition ho_check_polynomial_rule_ge where
  "ho_check_polynomial_rule_ge S ps fuel G l r =
    (case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False | Some A \<Rightarrow>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      ho_check_polynomial_ge fuel G A (ho_rule_polynomial S ps G l) (ho_rule_polynomial S ps G r))"

definition ho_check_polynomial_rule_gt where
  "ho_check_polynomial_rule_gt S ps fuel G l r =
    (case ho_typeof S G [] (ho_erase_pattern l) of None \<Rightarrow> False | Some A \<Rightarrow>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      ho_check_polynomial_gt fuel G A (ho_rule_polynomial S ps G l) (ho_rule_polynomial S ps G r))"

theorem ho_check_polynomial_rule_ge_sound:
  assumes signature: "ho_check_polynomial_signature S ps"
    and check: "ho_check_polynomial_rule_ge S ps fuel G l r"
  shows "ho_rule_weak S (ho_polynomial_interpretation ps) G l r"
proof -
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    and order: "ho_check_polynomial_ge fuel G A (ho_rule_polynomial S ps G l) (ho_rule_polynomial S ps G r)"
    using check by (auto simp: ho_check_polynomial_rule_ge_def split: option.splits)
  have ge: "ho_value_ge A (ho_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern l))
      (ho_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern r))"
    if "ho_env_value G e" for e
    using ho_check_polynomial_ge_sound[OF order that]
    by (simp add: ho_source_interpretation_def ho_rule_polynomial_def ho_polynomial_translate_eval[OF signature])
  show ?thesis unfolding ho_rule_weak_def using l r ge by blast
qed

theorem ho_check_polynomial_rule_gt_sound:
  assumes signature: "ho_check_polynomial_signature S ps"
    and check: "ho_check_polynomial_rule_gt S ps fuel G l r"
  shows "ho_rule_strict S (ho_polynomial_interpretation ps) G l r"
proof -
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    and order: "ho_check_polynomial_gt fuel G A (ho_rule_polynomial S ps G l) (ho_rule_polynomial S ps G r)"
    using check by (auto simp: ho_check_polynomial_rule_gt_def split: option.splits)
  have gt: "ho_value_gt A (ho_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern l))
      (ho_source_interpretation S G [] (ho_polynomial_interpretation ps) e (ho_erase_pattern r))"
    if "ho_env_value G e" for e
    using ho_check_polynomial_gt_sound[OF order that]
    by (simp add: ho_source_interpretation_def ho_rule_polynomial_def ho_polynomial_translate_eval[OF signature])
  show ?thesis unfolding ho_rule_strict_def using l r gt by blast
qed

definition ho_polynomial_residual where
  "ho_polynomial_residual S ps fuel R = filter (\<lambda>(G,l,r). \<not>ho_check_polynomial_rule_gt S ps fuel G l r) R"

definition ho_check_polynomial_removal where
  "ho_check_polynomial_removal S ps fuel R =
    (ho_zero_arity_rules R \<and> ho_check_polynomial_signature S ps \<and>
      list_all (\<lambda>(G,l,r). ho_check_polynomial_rule_ge S ps fuel G l r) R)"

theorem ho_check_polynomial_removal_sound:
  assumes check: "ho_check_polynomial_removal S ps fuel R"
    and residual: "wf ((ho_relation S V (ho_polynomial_residual S ps fuel R) A)\<inverse>)"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have zero: "ho_zero_arity_rules R" and signature: "ho_check_polynomial_signature S ps"
    and weak: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_check_polynomial_rule_ge S ps fuel G l r"
    using check by (auto simp: ho_check_polynomial_removal_def list_all_iff)
  have ev: "ho_env_value V (\<lambda>n. ho_zero (V!n))" by (simp add: ho_env_value_def ho_zero_value)
  show ?thesis
  proof (rule ho_semantic_rule_removal[OF residual zero ho_polynomial_signature_closed[OF signature]
      ho_polynomial_signature_value[OF signature] ev])
    fix G l r assume member: "(G,l,r)\<in>set R"
    show "ho_rule_weak S (ho_polynomial_interpretation ps) G l r"
      by (rule ho_check_polynomial_rule_ge_sound[OF signature weak[OF member]])
  next
    fix G l r assume member: "(G,l,r)\<in>set R" and missing: "(G,l,r)\<notin>set (ho_polynomial_residual S ps fuel R)"
    have strict: "ho_check_polynomial_rule_gt S ps fuel G l r"
      using member missing by (simp add: ho_polynomial_residual_def)
    show "ho_rule_strict S (ho_polynomial_interpretation ps) G l r"
      by (rule ho_check_polynomial_rule_gt_sound[OF signature strict])
  qed
qed

datatype ho_termination_certificate = HOEmpty | HOApplication nat
  | HOGeneralSchema "nat list" nat
  | HOPartialSchema "nat list" "nat list" nat
  | HOPolynomial "ho_polynomial list" nat ho_termination_certificate

fun ho_check_termination where
  "ho_check_termination S R HOEmpty = (R=[])"
| "ho_check_termination S R (HOApplication c) = ho_check_application S R c"
| "ho_check_termination S R (HOGeneralSchema ranks fuel) = ho_check_general_schema S R ranks fuel"
| "ho_check_termination S R (HOPartialSchema ranks arities fuel) = ho_check_schema_with_arities S R ranks arities fuel"
| "ho_check_termination S R (HOPolynomial ps fuel proof) =
    (ho_check_polynomial_removal S ps fuel R \<and>
      ho_check_termination S (ho_polynomial_residual S ps fuel R) proof)"

theorem ho_check_termination_sound:
  "ho_check_termination S R cert \<Longrightarrow> wf ((ho_relation S V R A)\<inverse>)"
proof (induction cert arbitrary: R)
  case HOEmpty
  then show ?case by (simp add: ho_empty_rules_termination)
next
  case (HOApplication c)
  then show ?case by (simp add: ho_check_application_sound)
next
  case (HOGeneralSchema ranks fuel)
  then show ?case by (simp add: ho_check_general_schema_sound)
next
  case (HOPartialSchema ranks arities fuel)
  then show ?case by (simp add: ho_check_schema_with_arities_sound)
next
  case (HOPolynomial ps fuel cert)
  then show ?case by (auto intro: ho_check_polynomial_removal_sound)
qed

end
