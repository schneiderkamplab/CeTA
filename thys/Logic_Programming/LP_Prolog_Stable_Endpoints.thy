theory LP_Prolog_Stable_Endpoints
 imports LP_Prolog_Stable_Bound_Row
begin

datatype 'v lpp_stable_endpoint_expression =
    LPPStableEndpointInteger "'v lpp_integer_expression"
  | LPPStableEndpointBound "(string lp_cut_symbol,'v) term"

fun lpp_stable_endpoint_mode where
  "lpp_stable_endpoint_mode (LPPStableEndpointInteger e) = LPPStableInteger"
| "lpp_stable_endpoint_mode (LPPStableEndpointBound t) = LPPStableUpperBound"

fun lpp_stable_endpoint_numeric_expression where
  "lpp_stable_endpoint_numeric_expression (LPPStableEndpointInteger e) = map_lpp_integer_expression LPPIntegerKey e"
| "lpp_stable_endpoint_numeric_expression (LPPStableEndpointBound t) = LPPEVariable (LPPBoundKey t)"

fun lpp_check_stable_endpoint where
  "lpp_check_stable_endpoint K G t (LPPStableEndpointInteger e) =
    (t=lpp_expression_term e \<and> lpp_integer_endpoint e \<and> lpp_expression_check K e)"
| "lpp_check_stable_endpoint K G t (LPPStableEndpointBound expression) =
    (t=expression \<and> vars_term t \<subseteq> set G)"

fun lpp_stable_key_value where
  "lpp_stable_key_value operation eta rho (LPPIntegerKey x) = rho x"
| "lpp_stable_key_value operation eta rho (LPPBoundKey t) =
    lpp_stable_expression_bound operation (lp_ieval t eta)"

lemma lpp_checked_stable_endpoint:
  assumes checked: "lpp_check_stable_endpoint K G t endpoint"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
  shows "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode endpoint) (lp_ieval t eta)
    (lpp_expression_value (lpp_stable_endpoint_numeric_expression endpoint) (lpp_stable_key_value operation eta rho))"
proof (cases endpoint)
  case (LPPStableEndpointInteger e)
  have check: "lpp_check_numeric_endpoint K (coordinate_name,t,e)" for coordinate_name
    using checked by (simp add: LPPStableEndpointInteger)
  have result: "lp_ieval t eta=lpp_integer_value (lpp_expression_value e rho)"
    by (rule lpp_checked_numeric_endpoint[OF check typed])
  show ?thesis by (simp add: LPPStableEndpointInteger lpp_expression_rename_value o_def result)
next
  case (LPPStableEndpointBound expression)
  have equal: "t=expression" and finite: "lp_seg_ground (lp_ieval t eta)"
    using checked ground by (auto simp: LPPStableEndpointBound lp_seg_ground_eval)
  show ?thesis using finite by (simp add: LPPStableEndpointBound equal)
qed

fun lpp_stable_endpoint_formula where
  "lpp_stable_endpoint_formula tag rename (coordinate_name,t,endpoint) =
    lpp_comparison_its LPPIntEqual (Var (tag coordinate_name,IA.IntT))
      (lpp_expression_its (map_lpp_integer_expression rename (lpp_stable_endpoint_numeric_expression endpoint)))"

lemma lpp_stable_expression_value_cong:
  "(\<And>x. x\<in>set_lpp_integer_expression e \<Longrightarrow> f x=g x) \<Longrightarrow>
    lpp_expression_value e f=lpp_expression_value e g"
  by (induct e) auto

lemma lpp_stable_endpoint_formula_sound:
  assumes checked: "lpp_check_stable_endpoint K G t endpoint"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
    and assigned: "\<And>key. key\<in>set_lpp_integer_expression (lpp_stable_endpoint_numeric_expression endpoint) \<Longrightarrow> rho (rename key)=lpp_stable_key_value operation eta source_values key"
    and represented: "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode endpoint)
      (lp_ieval t eta) (rho (tag coordinate_name))"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_stable_endpoint_formula tag rename (coordinate_name,t,endpoint))"
proof -
  have determined: "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode endpoint) (lp_ieval t eta)
    (lpp_expression_value (lpp_stable_endpoint_numeric_expression endpoint) (lpp_stable_key_value operation eta source_values))"
    by (rule lpp_checked_stable_endpoint[OF checked typed ground])
  have equal: "rho (tag coordinate_name)=lpp_expression_value (lpp_stable_endpoint_numeric_expression endpoint)
    (lpp_stable_key_value operation eta source_values)"
    by (rule lpp_stable_coordinate_unique[OF represented determined])
  have environment: "lpp_expression_value (lpp_stable_endpoint_numeric_expression endpoint) (rho o rename)=
    lpp_expression_value (lpp_stable_endpoint_numeric_expression endpoint) (lpp_stable_key_value operation eta source_values)"
    by (rule lpp_stable_expression_value_cong) (use assigned in auto)
  show ?thesis by (simp add: lpp_comparison_typed_assignment lpp_expression_typed_assignment
    lpp_expression_rename_value environment equal algebra.eval.simps)
qed

ML \<open>
val checked = [@{thm lpp_checked_stable_endpoint}, @{thm lpp_stable_endpoint_formula_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable endpoint dependency" else ();
\<close>
end
