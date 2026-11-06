theory LP_Prolog_Partial_Integer_Row
  imports LP_Prolog_Partial_Integer_Receipt LP_Prolog_Integer_Call_Row
begin

record lpp_partial_call = lpp_arithmetic_call +
  lpp_partial_inputs :: "nat list"
  lpp_partial_outputs :: "nat list"
  lpp_partial_terms :: "(string lp_cut_symbol,string) term list"
  lpp_partial_later :: "(string lp_cut_symbol,string) term lp_cut_goal list"

definition lpp_partial_call_shape where
  "lpp_partial_call_shape P f arity r =
    (length (lpp_call_variables r)=arity \<and> distinct (lpp_call_variables r) \<and>
     list_all (\<lambda>i. i<arity) (lpp_partial_inputs r) \<and>
     lpp_call_clause r<length P \<and> (f,arity)\<notin>lpp_builtin_signature \<and>
     P!lpp_call_clause r=(Fun (LPCUser f) (map Var (lpp_call_variables r)),
       map lpp_recurrence_goal (lpp_call_prefix r) @
       LPCAtom (Fun (LPCUser (lpp_call_target r)) (lpp_partial_terms r))#lpp_partial_later r) \<and>
     lp_cut_slice P (LPCUser f) arity =
       map lpp_failure_clause (lpp_call_failures r) @ lpp_call_clause r #
         drop (length (lpp_call_failures r)+1) (lp_cut_slice P (LPCUser f) arity) \<and>
     list_all (lpp_partial_failure_shape P f arity (lpp_partial_inputs r)) (lpp_call_failures r) \<and>
     lpp_partial_recurrence_check (lpp_call_variables r)
       (map ((!) (lpp_call_variables r)) (lpp_partial_inputs r)) (lpp_call_prefix r) \<and>
     length (lpp_partial_terms r)=length (lpp_call_outputs r) \<and>
     list_all (\<lambda>i. i<length (lpp_call_outputs r) \<and>
       lpp_partial_terms r!i=lpp_expression_term (lpp_call_outputs r!i)) (lpp_partial_outputs r) \<and>
     list_all (\<lambda>e. lpp_integer_endpoint e \<and>
       lpp_expression_check (lpp_recurrence_known
         (map ((!) (lpp_call_variables r)) (lpp_partial_inputs r)) (lpp_call_prefix r)) e)
       (lpp_call_outputs r))"

lemma lpp_partial_endpoint_value:
  assumes "lpp_integer_endpoint e" "lpp_expression_check K e"
  shows "lp_ieval (lpp_expression_term e) (lpp_partial_environment H K rho eta)=
    lpp_integer_value (lpp_expression_value e rho)"
  using assms by (cases e) (auto simp: lpp_partial_environment_def)

lemma lpp_checked_partial_call_steps:
  assumes shape: "lpp_partial_call_shape P f (length ns) r"
    and holds: "lpp_arithmetic_call_holds r ns"
    and observations: "lpp_partial_observations (lpp_partial_inputs r) ns actuals"
  shows "\<exists>returned next_pending saved.
    lpp_partial_observations (lpp_partial_outputs r) (lpp_arithmetic_call_outputs r ns) returned \<and>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) actuals)#pending)#es,
      LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_call_target r)) returned)#next_pending)#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?H = "lpp_call_variables r"
  let ?K = "map ((!) ?H) (lpp_partial_inputs r)"
  let ?ops = "lpp_call_prefix r"
  let ?rho = "lpp_recurrence_arguments ?H ns"
  let ?eta = "lpp_partial_arguments ?H actuals"
  let ?tail = "Fun (LPCUser (lpp_call_target r)) (lpp_partial_terms r)"
  let ?earlier = "map lpp_failure_clause (lpp_call_failures r)"
  let ?later = "drop (length (lpp_call_failures r)+1) (lp_cut_slice P (LPCUser f) (length ns))"
  let ?final = "lpp_partial_environment ?H (lpp_recurrence_known ?K ?ops) (lpp_recurrence_values ?ops ?rho) ?eta"
  have lengths: "length ?H=length ns" and distinct: "distinct ?H"
    and bounds: "list_all (\<lambda>i. i<length ?H) (lpp_partial_inputs r)"
    using shape by (auto simp: lpp_partial_call_shape_def)
  have actual_length: "length ?H=length actuals"
    using lengths observations by (simp add: lpp_partial_observations_def)
  have exact: "map ?eta ?H=actuals"
    by (rule lpp_partial_arguments_exact[OF actual_length distinct])
  have input_value: "lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta=LPIFun (LPCUser f) actuals"
    using exact by (simp add: map_map o_def)
  have head: "x\<in>set ?H" if "x\<in>set ?K" for x
    by (rule lpp_partial_observed_head[OF bounds that])
  have observed: "?eta x=lpp_integer_value (?rho x)" if "x\<in>set ?K" for x
    by (rule lpp_partial_observed_argument[OF lengths distinct observations that])
  have failed: "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    if member: "d\<in>set ?earlier" for d mark saved
  proof -
    obtain receipt where receipt: "receipt\<in>set (lpp_call_failures r)" and clause: "d=lpp_failure_clause receipt"
      using member by auto
    have checked: "lpp_partial_failure_shape P f (length ns) (lpp_partial_inputs r) receipt"
      and failure: "lpp_arithmetic_failure_holds receipt ns"
      using shape holds receipt by (auto simp: lpp_partial_call_shape_def lpp_arithmetic_call_holds_def list_all_iff)
    show ?thesis using lpp_checked_partial_failure_restores_stack[OF checked failure observations,
      where mark=mark and es=saved and pending=pending] by (simp only: input_value clause)
  qed
  obtain mark where iteration: "(LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending)#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?final)) (LPCAtom ?tail#lpp_partial_later r) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending) d mark) ?later @
        LPCBarrier mark#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    by (rule exE[OF lpp_partial_selected_source_iteration[where earlier="?earlier"
      and c="lpp_call_clause r" and cs="?later" and P=P and f=f and H="?H" and K="?K" and ops="?ops"
      and tail="?tail" and later_goals="lpp_partial_later r" and rho="?rho" and eta="?eta" and pending=pending and es=es]])
      (use shape holds failed head observed in \<open>auto simp: lpp_partial_call_shape_def lpp_arithmetic_call_holds_def lengths\<close>)
  have endpoint: "lp_ieval (lpp_expression_term e) ?final=
      lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ?ops ?rho))"
    if "e\<in>set (lpp_call_outputs r)" for e
    using shape that by (auto simp: lpp_partial_call_shape_def list_all_iff intro: lpp_partial_endpoint_value)
  have output_observations: "lpp_partial_observations (lpp_partial_outputs r) (lpp_arithmetic_call_outputs r ns)
      (map (\<lambda>t. lp_ieval t ?final) (lpp_partial_terms r))"
    using shape endpoint by (auto simp: lpp_partial_observations_def lpp_partial_call_shape_def
      lpp_arithmetic_call_outputs_def list_all_iff)
  show ?thesis using iteration output_observations by (auto simp: input_value o_def exact)
qed

ML \<open>
val checked = [@{thm lpp_checked_partial_call_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial arithmetic call row" else ();
\<close>
end
