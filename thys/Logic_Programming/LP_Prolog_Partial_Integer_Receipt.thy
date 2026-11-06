theory LP_Prolog_Partial_Integer_Receipt
  imports LP_Prolog_Partial_Integer_Interface
begin

definition lpp_partial_failure_shape where
  "lpp_partial_failure_shape P f arity positions r =
    (lpp_failure_clause r<length P \<and>
     length (lpp_failure_variables r)=arity \<and> distinct (lpp_failure_variables r) \<and>
     list_all (\<lambda>i. i<arity) positions \<and>
     P!lpp_failure_clause r=(Fun (LPCUser f) (map Var (lpp_failure_variables r)),
       map lpp_recurrence_goal (lpp_failure_prefix r) @
       lpp_recurrence_goal (lpp_failure_operation r)#
       drop (length (lpp_failure_prefix r)+1) (snd (P!lpp_failure_clause r))) \<and>
     lpp_partial_recurrence_check (lpp_failure_variables r)
       (map ((!) (lpp_failure_variables r)) positions)
       (lpp_failure_prefix r @ [lpp_failure_operation r]))"

lemma lpp_checked_partial_failure_restores_stack:
  assumes shape: "lpp_partial_failure_shape P f (length ns) positions r"
    and fails: "lpp_arithmetic_failure_holds r ns"
    and observations: "lpp_partial_observations positions ns actuals"
  shows "(LPCClause (LPCAtom (LPIFun (LPCUser f) actuals)#pending)
      (lpp_failure_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?H = "lpp_failure_variables r"
  let ?K = "map ((!) ?H) positions"
  let ?rho = "lpp_recurrence_arguments ?H ns"
  let ?eta = "lpp_partial_arguments ?H actuals"
  have lengths: "length ?H=length ns" and distinct: "distinct ?H"
    and bounds: "list_all (\<lambda>i. i<length ?H) positions"
    using shape by (auto simp: lpp_partial_failure_shape_def)
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
      (lpp_failure_clause r) mark#es,es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    by (rule lpp_partial_selected_clause_failure[
        where ops="lpp_failure_prefix r" and g="lpp_failure_predicate r"
          and c="lpp_failure_comparison r" and reversed="lpp_failure_reversed r"
          and a="lpp_failure_left r" and b="lpp_failure_right r" and K="?K" and rho="?rho"
          and rest="drop (length (lpp_failure_prefix r)+1) (snd (P!lpp_failure_clause r))"])
      (use shape fails head observed in \<open>auto simp: lpp_partial_failure_shape_def
        lpp_arithmetic_failure_holds_def lpp_failure_operation_def lpp_partial_check_append Let_def\<close>)
  show ?thesis using step by (simp only: call_value)
qed

ML \<open>
val checked = [@{thm lpp_checked_partial_failure_restores_stack}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial arithmetic failure receipt" else ();
\<close>
end
