theory LP_Prolog_Helper_Failure_Receipt
  imports LP_Prolog_Helper_Clause_Iteration
begin

record lpp_helper_failure =
  lpp_hf_clause :: nat
  lpp_hf_variables :: "string list"
  lpp_hf_prefix :: "lpp_helper_prefix_operation list"
  lpp_hf_predicate :: string
  lpp_hf_comparison :: lpp_integer_comparison
  lpp_hf_reversed :: bool
  lpp_hf_left :: "string lpp_integer_expression"
  lpp_hf_right :: "string lpp_integer_expression"

definition lpp_hf_operation where
  "lpp_hf_operation r = LPPRGuard (lpp_hf_predicate r) (lpp_hf_comparison r)
    (lpp_hf_reversed r) (lpp_hf_left r) (lpp_hf_right r)"

definition lpp_helper_failure_holds where
  "lpp_helper_failure_holds r ns =
    (let rho = lpp_recurrence_arguments (lpp_hf_variables r) ns;
         final = lpp_helper_prefix_values (lpp_hf_prefix r) rho
     in lpp_helper_prefix_guards (lpp_hf_prefix r) rho \<and>
       \<not>lpp_integer_compare (lpp_hf_comparison r)
         (lpp_expression_value (if lpp_hf_reversed r then lpp_hf_right r else lpp_hf_left r) final)
         (lpp_expression_value (if lpp_hf_reversed r then lpp_hf_left r else lpp_hf_right r) final))"

definition lpp_helper_failure_shape where
  "lpp_helper_failure_shape P f arity positions r =
    (lpp_hf_clause r<length P \<and>
     length (lpp_hf_variables r)=arity \<and> distinct (lpp_hf_variables r) \<and>
     list_all (\<lambda>i. i<arity) positions \<and>
     P!lpp_hf_clause r=(Fun (LPCUser f) (map Var (lpp_hf_variables r)),
       map lpp_helper_operation_goal (lpp_hf_prefix r) @
       lpp_recurrence_goal (lpp_hf_operation r)#
       drop (length (lpp_hf_prefix r)+1) (snd (P!lpp_hf_clause r))) \<and>
     lpp_check_helper_prefix P (lpp_hf_variables r)
       (map ((!) (lpp_hf_variables r)) positions) (lpp_hf_prefix r) \<and>
     lpp_partial_recurrence_check (lpp_hf_variables r)
       (lpp_helper_prefix_known (map ((!) (lpp_hf_variables r)) positions) (lpp_hf_prefix r))
       [lpp_hf_operation r])"

lemma lpp_checked_helper_failure_restores_stack:
  assumes shape: "lpp_helper_failure_shape P f (length ns) positions r"
    and fails: "lpp_helper_failure_holds r ns"
    and observations: "lpp_partial_observations positions ns actuals"
  shows "(LPCClause (LPCAtom (LPIFun (LPCUser f) actuals)#pending)
      (lpp_hf_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?H = "lpp_hf_variables r"
  let ?K = "map ((!) ?H) positions"
  let ?rho = "lpp_recurrence_arguments ?H ns"
  let ?eta = "lpp_partial_arguments ?H actuals"
  have lengths: "length ?H=length ns" and distinct: "distinct ?H"
    and bounds: "list_all (\<lambda>i. i<length ?H) positions"
    using shape by (auto simp: lpp_helper_failure_shape_def)
  have args_length: "length ?H=length actuals"
    using lengths observations by (simp add: lpp_partial_observations_def)
  have exact: "map ?eta ?H=actuals" by (rule lpp_partial_arguments_exact[OF args_length distinct])
  have head: "x\<in>set ?H" if "x\<in>set ?K" for x
    by (rule lpp_partial_observed_head[OF bounds that])
  have observed: "?eta x=lpp_integer_value (?rho x)" if "x\<in>set ?K" for x
    by (rule lpp_partial_observed_argument[OF lengths distinct observations that])
  have call_value: "lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta=LPIFun (LPCUser f) actuals"
    using exact by (simp add: map_map o_def)
  have step: "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending)
      (lpp_hf_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    by (rule lpp_helper_selected_clause_failure[
        where ops="lpp_hf_prefix r" and g="lpp_hf_predicate r"
          and c="lpp_hf_comparison r" and reversed="lpp_hf_reversed r"
          and a="lpp_hf_left r" and b="lpp_hf_right r" and K="?K" and rho="?rho"
          and rest="drop (length (lpp_hf_prefix r)+1) (snd (P!lpp_hf_clause r))"])
      (use shape fails head observed in \<open>auto simp: lpp_helper_failure_shape_def
        lpp_helper_failure_holds_def lpp_hf_operation_def lpp_partial_check_append Let_def\<close>)
  show ?thesis using step by (simp only: call_value)
qed

ML \<open>
val checked = [@{thm lpp_checked_helper_failure_restores_stack}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper clause failure receipt" else ();
\<close>
end
