theory LP_Prolog_Helper_Caller_Environment
  imports LP_Prolog_Helper_Call_Interface
begin

text \<open>The helper's actual return changes the active caller environment.
Its fresh renaming applies even to variables not observed numerically. Saved
alternatives are intentionally absent from this transformation.\<close>

definition lpp_helper_caller_environment where
  "lpp_helper_caller_environment eta slot n y =
    lp_isubst (eta y) (lpc_fresh_caller(slot:=lpp_integer_value n))"

lemma lpp_helper_caller_integer:
  "eta y=lpp_integer_value m \<Longrightarrow>
    lpp_helper_caller_environment eta slot n y=lpp_integer_value m"
  by (simp add: lpp_helper_caller_environment_def lpp_integer_value_def)

lemma lpp_helper_caller_output:
  "eta y=LPIVar slot \<Longrightarrow>
    lpp_helper_caller_environment eta slot n y=lpp_integer_value n"
  by (simp add: lpp_helper_caller_environment_def)

lemma lpp_helper_caller_fresh:
  "eta y=LPIVar other \<Longrightarrow> other\<noteq>slot \<Longrightarrow>
    lpp_helper_caller_environment eta slot n y=LPIVar (CHR ''0''#other)"
  by (simp add: lpp_helper_caller_environment_def lpc_fresh_caller_def)

lemma lpp_helper_caller_goals:
  "map (lp_cut_map (\<lambda>t. lp_isubst t (lpc_fresh_caller(slot:=lpp_integer_value n))))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
    map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_helper_caller_environment eta slot n))) gs"
  by (simp add: map_map lp_cut_map_comp lp_ieval_subst lpp_helper_caller_environment_def[abs_def] o_def)

theorem lpp_helper_caller_body_return:
  assumes checked: "lpp_check_helper_return_recipe P r"
    and interface: "lpp_check_helper_call_interface r positions output_position"
    and numeric_length: "length (lpphr_head r)=length ns"
    and observed: "lpp_partial_observations positions ns (map (\<lambda>t. lp_ieval t eta) call_terms)"
    and fresh: "(map (\<lambda>t. lp_ieval t eta) call_terms)!output_position=LPIVar slot"
    and guards: "lpp_recurrence_guards (lpphr_prefix r)
      (lpp_recurrence_arguments (lpphr_head r) ns)"
    and returned_value: "n=lpp_expression_value (lpphr_expression r)
      (lpp_recurrence_values (lpphr_prefix r) (lpp_recurrence_arguments (lpphr_head r) ns))"
  shows "\<exists>mark. (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
      (LPCAtom (Fun (LPCUser (lpphr_predicate r)) call_terms)#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_helper_caller_environment eta slot n))) rest @
        map (lp_cut_map (\<lambda>t. lp_isubst t (lpc_fresh_caller(slot:=lpp_integer_value n)))) pending)#
        LPCBarrier mark#saved)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  note run = lpp_helper_actual_call_return[OF checked interface numeric_length observed fresh guards,
    where pending="map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest @ pending" and saved=saved]
  show ?thesis using run by (simp add: returned_value map_map lp_cut_map_comp lp_ieval_subst
    lpp_helper_caller_environment_def[abs_def] o_def)
qed

ML \<open>
val checked = [@{thm lpp_helper_caller_integer}, @{thm lpp_helper_caller_output},
  @{thm lpp_helper_caller_fresh}, @{thm lpp_helper_caller_goals}, @{thm lpp_helper_caller_body_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted caller environment transport" else ();
\<close>
end
