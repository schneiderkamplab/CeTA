theory LP_Prolog_Helper_Call_Interface
  imports LP_Prolog_Helper_Return_Recipe LP_Prolog_Partial_Integer_Interface
begin

text \<open>Bind the checked helper recipe to actual arguments through the
existing partial-call interface. Integer observations concern actual values,
not expressions that could evaluate to them. The output is an actual caller
variable; the returned substitution acts on the whole caller continuation.\<close>

definition lpp_check_helper_call_interface where
  "lpp_check_helper_call_interface r positions output_position =
    (distinct (lpphr_head r) \<and>
     list_all (\<lambda>i. i<length (lpphr_head r)) positions \<and>
     map ((!) (lpphr_head r)) positions=lpphr_inputs r \<and>
     output_position<length (lpphr_head r) \<and>
     lpphr_head r!output_position=lpphr_output r)"

theorem lpp_helper_actual_call_return:
  assumes checked: "lpp_check_helper_return_recipe P r"
    and interface: "lpp_check_helper_call_interface r positions output_position"
    and numeric_length: "length (lpphr_head r)=length ns"
    and observed: "lpp_partial_observations positions ns actuals"
    and fresh: "actuals!output_position=LPIVar slot"
    and guards: "lpp_recurrence_guards (lpphr_prefix r)
      (lpp_recurrence_arguments (lpphr_head r) ns)"
  shows "\<exists>mark. (LPCGoals (LPCAtom (LPIFun (LPCUser (lpphr_predicate r)) actuals)#pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value (lpp_expression_value (lpphr_expression r)
          (lpp_recurrence_values (lpphr_prefix r) (lpp_recurrence_arguments (lpphr_head r) ns))))))) pending)#
        LPCBarrier mark#saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?H = "lpphr_head r"
  let ?eta = "lpp_partial_arguments ?H actuals"
  let ?rho = "lpp_recurrence_arguments ?H ns"
  have distinct: "distinct ?H" and inputs: "map ((!) ?H) positions=lpphr_inputs r"
    and bound: "output_position<length ?H" and output_name: "?H!output_position=lpphr_output r"
    using interface by (auto simp: lpp_check_helper_call_interface_def)
  have lengths: "length ?H=length actuals"
    using observed numeric_length by (simp add: lpp_partial_observations_def)
  have typed: "?eta y=lpp_integer_value (?rho y)" if "y\<in>set (lpphr_inputs r)" for y
    by (rule lpp_partial_observed_argument[OF numeric_length distinct observed])
      (use that inputs in simp)
  have target: "?eta (lpphr_output r)=LPIVar slot"
    using lpp_partial_arguments_nth[OF lengths distinct bound] output_name fresh by simp
  note run = lpp_helper_return_recipe_sound[OF checked typed target guards,
    where pending=pending and saved=saved]
  have exact: "map ?eta ?H=actuals" by (rule lpp_partial_arguments_exact[OF lengths distinct])
  show ?thesis using run by (simp add: map_map o_def exact)
qed

ML \<open>
val checked = [@{thm lpp_helper_actual_call_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper call interface dependency" else ();
\<close>
end
