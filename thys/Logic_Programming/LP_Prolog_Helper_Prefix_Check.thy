theory LP_Prolog_Helper_Prefix_Check
  imports LP_Prolog_Helper_Caller_Primitives LP_Prolog_Partial_Integer_Row
begin

text \<open>A helper prefix retains the actual call term alongside its numeric
input evidence. The integer expressions are observations, not replacement
source arguments. All source recipes and primitive operations are checked.\<close>

record lpp_helper_call_site =
  lpphs_recipe :: lpp_helper_return_recipe
  lpphs_terms :: "(string lp_cut_symbol,string) term list"
  lpphs_positions :: "nat list"
  lpphs_output_position :: nat
  lpphs_output :: string
  lpphs_numeric :: "string lpp_integer_expression list"

definition lpp_check_helper_site where
  "lpp_check_helper_site P H K s =
    (lpp_check_helper_return_recipe P (lpphs_recipe s) \<and>
     lpp_check_helper_call_interface (lpphs_recipe s) (lpphs_positions s) (lpphs_output_position s) \<and>
     length (lpphs_terms s)=length (lpphr_head (lpphs_recipe s)) \<and>
     length (lpphs_numeric s)=length (lpphs_terms s) \<and>
     lpphs_terms s!lpphs_output_position s=Var (lpphs_output s) \<and>
     lpphs_output s\<notin>set H \<and> lpphs_output s\<notin>set K \<and>
     list_all (lpp_expression_check K) (lpphs_numeric s) \<and>
     list_all (\<lambda>i. lpphs_terms s!i=lpp_expression_term (lpphs_numeric s!i) \<and>
       lpp_integer_endpoint (lpphs_numeric s!i)) (lpphs_positions s))"

definition lpp_helper_site_arguments where
  "lpp_helper_site_arguments s rho = map (\<lambda>e. lpp_expression_value e rho) (lpphs_numeric s)"
definition lpp_helper_site_environment where
  "lpp_helper_site_environment s rho =
    lpp_recurrence_arguments (lpphr_head (lpphs_recipe s)) (lpp_helper_site_arguments s rho)"
definition lpp_helper_site_value where
  "lpp_helper_site_value s rho = lpp_expression_value (lpphr_expression (lpphs_recipe s))
    (lpp_recurrence_values (lpphr_prefix (lpphs_recipe s)) (lpp_helper_site_environment s rho))"
definition lpp_helper_site_guards where
  "lpp_helper_site_guards s rho =
    lpp_recurrence_guards (lpphr_prefix (lpphs_recipe s)) (lpp_helper_site_environment s rho)"

datatype lpp_helper_prefix_operation =
    LPPHPrimitive lpp_recurrence_operation | LPPHCall lpp_helper_call_site

fun lpp_helper_operation_goal where
  "lpp_helper_operation_goal (LPPHPrimitive op) = lpp_recurrence_goal op"
| "lpp_helper_operation_goal (LPPHCall s) =
    LPCAtom (Fun (LPCUser (lpphr_predicate (lpphs_recipe s))) (lpphs_terms s))"
fun lpp_helper_operation_known where
  "lpp_helper_operation_known K (LPPHPrimitive op) = lpp_recurrence_known K [op]"
| "lpp_helper_operation_known K (LPPHCall s) = lpphs_output s#K"
fun lpp_helper_operation_values where
  "lpp_helper_operation_values (LPPHPrimitive op) rho = lpp_recurrence_values [op] rho"
| "lpp_helper_operation_values (LPPHCall s) rho = rho(lpphs_output s:=lpp_helper_site_value s rho)"
fun lpp_helper_operation_guards where
  "lpp_helper_operation_guards (LPPHPrimitive op) rho = lpp_recurrence_guards [op] rho"
| "lpp_helper_operation_guards (LPPHCall s) rho = lpp_helper_site_guards s rho"
fun lpp_check_helper_operation where
  "lpp_check_helper_operation P H K (LPPHPrimitive op) = lpp_partial_recurrence_check H K [op]"
| "lpp_check_helper_operation P H K (LPPHCall s) = lpp_check_helper_site P H K s"

lemma lpp_caller_endpoint_value:
  assumes ctx: "lpp_caller_numeric_context H K rho eta names"
    and endpoint: "lpp_integer_endpoint e" and typed: "lpp_expression_check K e"
  shows "lp_ieval (lpp_expression_term e) eta=lpp_integer_value (lpp_expression_value e rho)"
  using ctx endpoint typed by (cases e) (auto simp: lpp_caller_numeric_context_def)

lemma lpp_helper_site_observations:
  assumes checked: "lpp_check_helper_site P H K s"
    and ctx: "lpp_caller_numeric_context H K rho eta names"
  shows "lpp_partial_observations (lpphs_positions s) (lpp_helper_site_arguments s rho)
    (map (\<lambda>t. lp_ieval t eta) (lpphs_terms s))"
proof -
  have lengths: "length (lpphs_terms s)=length (lpphs_numeric s)"
    using checked by (simp add: lpp_check_helper_site_def)
  have position: "i<length (lpphs_terms s)" if "i\<in>set (lpphs_positions s)" for i
    using checked that by (auto simp: lpp_check_helper_site_def lpp_check_helper_call_interface_def list_all_iff)
  have observed_value: "lp_ieval (lpphs_terms s!i) eta=lpp_integer_value (lpp_expression_value (lpphs_numeric s!i) rho)"
    if member: "i\<in>set (lpphs_positions s)" for i
  proof -
    have shape: "lpphs_terms s!i=lpp_expression_term (lpphs_numeric s!i)"
      and endpoint: "lpp_integer_endpoint (lpphs_numeric s!i)"
      and typed: "lpp_expression_check K (lpphs_numeric s!i)"
      using checked member position[OF member] lengths
      by (auto simp: lpp_check_helper_site_def list_all_iff intro: nth_mem)
    show ?thesis using lpp_caller_endpoint_value[OF ctx endpoint typed] by (simp only: shape)
  qed
  show ?thesis using lengths position observed_value
    by (auto simp: lpp_partial_observations_def lpp_helper_site_arguments_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_caller_endpoint_value}, @{thm lpp_helper_site_observations}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper prefix observations" else ();
\<close>
end
