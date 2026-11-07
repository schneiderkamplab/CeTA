theory LP_Prolog_Stable_Numeric_Path
 imports LP_Prolog_Stable_Numeric_Conditions
begin

type_synonym 'v lpp_stable_numeric_endpoint =
  "string * (string lp_cut_symbol,'v) term * 'v lpp_stable_endpoint_expression"

fun lpp_stable_endpoint_keys where
  "lpp_stable_endpoint_keys (coordinate,t,endpoint) =
    set_lpp_integer_expression (lpp_stable_endpoint_numeric_expression endpoint)"

definition lpp_stable_numeric_path_formula where
  "lpp_stable_numeric_path_formula inputs outputs receipts bindings =
    (let rename=lpp_numeric_rename bindings in Conjunction
      (map (lpp_stable_endpoint_formula Pre rename) inputs @
       map (lpp_stable_receipt_formula rename) receipts @
       map (lpp_stable_endpoint_formula Post rename) outputs))"

definition lpp_check_stable_numeric_path where
  "lpp_check_stable_numeric_path K G inputs outputs observations receipts bindings formula =
    (list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint K G t e) inputs \<and>
     list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint K G t e) outputs \<and>
     distinct (map fst inputs) \<and> distinct (map fst outputs) \<and>
     distinct (map fst bindings) \<and>
     list_all (\<lambda>e. lpp_stable_endpoint_keys e \<subseteq> set (map fst bindings)) (inputs@outputs) \<and>
     list_all (\<lambda>r. lpp_stable_receipt_keys r \<subseteq> set (map fst bindings)) receipts \<and>
     list_all2 (lpp_check_stable_numeric_observation K) observations receipts \<and>
     formula=lpp_stable_numeric_path_formula inputs outputs receipts bindings)"

text \<open>The complete formula contains both endpoints and every supplied
arithmetic observation. Bindings cover each referenced key. The separate
valuation-extension check will forbid overwriting output coordinates and will
justify every pre-state binding from its original input term.\<close>

lemma lpp_stable_condition_formula_typed:
  "IA4.formula (lpp_numeric_condition_formula test)"
  by (cases test) (auto simp: lpp_comparison_its_type split: prod.splits)

theorem lpp_check_stable_numeric_path_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_path K G inputs outputs observations receipts bindings formula"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
    and assigned: "\<And>key. key\<in>set (map fst bindings) \<Longrightarrow>
      rho (lpp_numeric_rename bindings key)=lpp_stable_key_value operation eta source_values key"
    and inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set inputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (rho (Pre coordinate))"
    and outputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set outputs \<Longrightarrow>
      lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e) (lp_ieval t eta) (rho (Post coordinate))"
  shows "IA4.satisfies (lpp_integer_assignment rho) formula"
proof -
  let ?rename = "lpp_numeric_rename bindings"
  have ins: "list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint K G t e) inputs"
    and outs: "list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint K G t e) outputs"
    and endpoint_keys: "\<And>e. e\<in>set (inputs@outputs) \<Longrightarrow> lpp_stable_endpoint_keys e \<subseteq> set (map fst bindings)"
    and condition_keys: "\<And>r. r\<in>set receipts \<Longrightarrow> lpp_stable_receipt_keys r \<subseteq> set (map fst bindings)"
    and tests: "list_all2 (lpp_check_stable_numeric_observation K) observations receipts"
    and formula: "formula=lpp_stable_numeric_path_formula inputs outputs receipts bindings"
    using checked by (auto simp: lpp_check_stable_numeric_path_def list_all_iff)
  have input_formula: "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_endpoint_formula Pre ?rename endpoint)"
    if member: "endpoint\<in>set inputs" for endpoint
  proof -
    obtain coordinate t e where shape: "endpoint=(coordinate,t,e)" by (cases endpoint) auto
    have check: "lpp_check_stable_endpoint K G t e" using ins member by (auto simp: shape list_all_iff)
    have keys: "set_lpp_integer_expression (lpp_stable_endpoint_numeric_expression e) \<subseteq> set (map fst bindings)"
      using endpoint_keys[of endpoint] member by (simp add: shape)
    show ?thesis unfolding shape
      by (rule lpp_stable_endpoint_formula_sound[where rho=rho and tag=Pre and rename="?rename" and operation=operation, OF check typed ground _ inputs[OF member[unfolded shape]]])
        (assumption | (rule assigned; erule subsetD[OF keys]))+
  qed
  have output_formula: "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_endpoint_formula Post ?rename endpoint)"
    if member: "endpoint\<in>set outputs" for endpoint
  proof -
    obtain coordinate t e where shape: "endpoint=(coordinate,t,e)" by (cases endpoint) auto
    have check: "lpp_check_stable_endpoint K G t e" using outs member by (auto simp: shape list_all_iff)
    have keys: "set_lpp_integer_expression (lpp_stable_endpoint_numeric_expression e) \<subseteq> set (map fst bindings)"
      using endpoint_keys[of endpoint] member by (simp add: shape)
    show ?thesis unfolding shape
      by (rule lpp_stable_endpoint_formula_sound[where rho=rho and tag=Post and rename="?rename" and operation=operation, OF check typed ground _ outputs[OF member[unfolded shape]]])
        (assumption | (rule assigned; erule subsetD[OF keys]))+
  qed
  have condition_formula: "list_all (\<lambda>r. IA4.satisfies (lpp_integer_assignment rho)
      (lpp_stable_receipt_formula ?rename r)) receipts"
    using tests observed condition_keys
  proof (induct rule: list_all2_induct)
    case Nil then show ?case by simp
  next
    case (Cons ob r obs rs)
    have current: "IA4.satisfies (lpp_integer_assignment rho)
      (lpp_stable_receipt_formula ?rename r)"
      by (rule lpp_stable_receipt_formula_sound[OF compatible Cons.hyps(1) _ typed])
        (use Cons.prems assigned in auto)
    show ?case using Cons current by auto
  qed
  show ?thesis using input_formula output_formula condition_formula
    by (auto simp: formula lpp_stable_numeric_path_formula_def Let_def list_all_iff lpp_stable_condition_formula_typed lpp_stable_receipt_formula_typed)
qed

lemma lpp_stable_numeric_path_formula_typed:
  "IA4.formula (lpp_stable_numeric_path_formula inputs outputs receipts bindings)"
  by (auto simp: lpp_stable_numeric_path_formula_def Let_def list_all_iff
    lpp_comparison_its_type lpp_expression_its_type lpp_stable_condition_formula_typed lpp_stable_receipt_formula_typed less_Suc_eq split: prod.splits)

ML \<open>
val checked = [@{thm lpp_check_stable_numeric_path_sound}, @{thm lpp_stable_numeric_path_formula_typed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable path dependency" else ();
\<close>
end
