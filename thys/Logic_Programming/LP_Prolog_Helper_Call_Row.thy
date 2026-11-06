theory LP_Prolog_Helper_Call_Row
  imports LP_Prolog_Helper_Failure_Receipt
begin

record lpp_helper_call =
  lpp_hc_clause :: nat
  lpp_hc_variables :: "string list"
  lpp_hc_prefix :: "lpp_helper_prefix_operation list"
  lpp_hc_target :: string
  lpp_hc_outputs :: "string lpp_integer_expression list"
  lpp_hc_failures :: "lpp_helper_failure list"
  lpp_hc_inputs :: "nat list"
  lpp_hc_observed_outputs :: "nat list"
  lpp_hc_terms :: "(string lp_cut_symbol,string) term list"
  lpp_hc_later :: "(string lp_cut_symbol,string) term lp_cut_goal list"

definition lpp_helper_call_shape where
  "lpp_helper_call_shape P f arity r =
    (length (lpp_hc_variables r)=arity \<and> distinct (lpp_hc_variables r) \<and>
     list_all (\<lambda>i. i<arity) (lpp_hc_inputs r) \<and>
     lpp_hc_clause r<length P \<and> (f,arity)\<notin>lpp_builtin_signature \<and>
     P!lpp_hc_clause r=(Fun (LPCUser f) (map Var (lpp_hc_variables r)),
       map lpp_helper_operation_goal (lpp_hc_prefix r) @
       LPCAtom (Fun (LPCUser (lpp_hc_target r)) (lpp_hc_terms r))#lpp_hc_later r) \<and>
     lp_cut_slice P (LPCUser f) arity =
       map lpp_hf_clause (lpp_hc_failures r) @ lpp_hc_clause r #
         drop (length (lpp_hc_failures r)+1) (lp_cut_slice P (LPCUser f) arity) \<and>
     list_all (lpp_helper_failure_shape P f arity (lpp_hc_inputs r)) (lpp_hc_failures r) \<and>
     lpp_check_helper_prefix P (lpp_hc_variables r)
       (map ((!) (lpp_hc_variables r)) (lpp_hc_inputs r)) (lpp_hc_prefix r) \<and>
     length (lpp_hc_terms r)=length (lpp_hc_outputs r) \<and>
     list_all (\<lambda>i. i<length (lpp_hc_outputs r) \<and>
       lpp_hc_terms r!i=lpp_expression_term (lpp_hc_outputs r!i)) (lpp_hc_observed_outputs r) \<and>
     list_all (\<lambda>e. lpp_integer_endpoint e \<and>
       lpp_expression_check (lpp_helper_prefix_known
         (map ((!) (lpp_hc_variables r)) (lpp_hc_inputs r)) (lpp_hc_prefix r)) e)
       (lpp_hc_outputs r))"

definition lpp_helper_call_holds where
  "lpp_helper_call_holds r ns =
    (lpp_helper_prefix_guards (lpp_hc_prefix r) (lpp_recurrence_arguments (lpp_hc_variables r) ns) \<and>
     list_all (\<lambda>failure. lpp_helper_failure_holds failure ns) (lpp_hc_failures r))"
definition lpp_helper_call_outputs where
  "lpp_helper_call_outputs r ns = map
    (\<lambda>e. lpp_expression_value e (lpp_helper_prefix_values (lpp_hc_prefix r)
      (lpp_recurrence_arguments (lpp_hc_variables r) ns))) (lpp_hc_outputs r)"

lemma lpp_checked_helper_call_steps:
  assumes shape: "lpp_helper_call_shape P f (length ns) r"
    and holds: "lpp_helper_call_holds r ns"
    and observations: "lpp_partial_observations (lpp_hc_inputs r) ns actuals"
  shows "\<exists>returned next_pending saved.
    lpp_partial_observations (lpp_hc_observed_outputs r) (lpp_helper_call_outputs r ns) returned \<and>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) actuals)#pending)#es,
      LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_hc_target r)) returned)#next_pending)#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?H = "lpp_hc_variables r"
  let ?K = "map ((!) ?H) (lpp_hc_inputs r)"
  let ?rho = "lpp_recurrence_arguments ?H ns"
  let ?eta = "lpp_partial_arguments ?H actuals"
  let ?tail = "Fun (LPCUser (lpp_hc_target r)) (lpp_hc_terms r)"
  let ?earlier = "map lpp_hf_clause (lpp_hc_failures r)"
  let ?later = "drop (length (lpp_hc_failures r)+1) (lp_cut_slice P (LPCUser f) (length ns))"
  have lengths: "length ?H=length ns" and distinct: "distinct ?H"
    and bounds: "list_all (\<lambda>i. i<length ?H) (lpp_hc_inputs r)"
    using shape by (auto simp: lpp_helper_call_shape_def)
  have actual_length: "length ?H=length actuals"
    using lengths observations by (simp add: lpp_partial_observations_def)
  have exact: "map ?eta ?H=actuals" by (rule lpp_partial_arguments_exact[OF actual_length distinct])
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
    obtain receipt where receipt: "receipt\<in>set (lpp_hc_failures r)" and clause: "d=lpp_hf_clause receipt"
      using member by auto
    have checked: "lpp_helper_failure_shape P f (length ns) (lpp_hc_inputs r) receipt"
      and failure: "lpp_helper_failure_holds receipt ns"
      using shape holds receipt by (auto simp: lpp_helper_call_shape_def lpp_helper_call_holds_def list_all_iff)
    show ?thesis using lpp_checked_helper_failure_restores_stack[OF checked failure observations,
      where mark=mark and es=saved and pending=pending] by (simp only: input_value clause)
  qed
  have selected: "lp_cut_slice P (LPCUser f) (length ?H)=?earlier@lpp_hc_clause r#?later"
    using shape lengths by (simp add: lpp_helper_call_shape_def)
  have index: "lpp_hc_clause r<length P"
    and clause: "P!lpp_hc_clause r=(Fun (LPCUser f) (map Var ?H),
      map lpp_helper_operation_goal (lpp_hc_prefix r) @ LPCAtom ?tail#lpp_hc_later r)"
    and ordinary: "(f,length ?H)\<notin>lpp_builtin_signature"
    and checked: "lpp_check_helper_prefix P ?H ?K (lpp_hc_prefix r)"
    and guards: "lpp_helper_prefix_guards (lpp_hc_prefix r) ?rho"
    using shape holds lengths by (auto simp: lpp_helper_call_shape_def lpp_helper_call_holds_def)
  obtain mark final_eta final_names next_pending bars where ctx:
      "lpp_caller_numeric_context ?H (lpp_helper_prefix_known ?K (lpp_hc_prefix r))
        (lpp_helper_prefix_values (lpp_hc_prefix r) ?rho) final_eta final_names"
    and barriers: "lp_cut_barriers bars"
    and iteration: "(LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending)#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t final_eta)) (LPCAtom ?tail#lpp_hc_later r) @ next_pending)#
        (bars @ map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?H)) ?eta)#pending) d mark) ?later @
          LPCBarrier mark#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_helper_selected_clause_iteration[OF selected index clause ordinary failed head observed checked guards,
      where saved=es] by blast
  let ?returned = "map (\<lambda>t. lp_ieval t final_eta) (lpp_hc_terms r)"
  have output_value: "lp_ieval (lpp_expression_term e) final_eta=
      lpp_integer_value (lpp_expression_value e (lpp_helper_prefix_values (lpp_hc_prefix r) ?rho))"
    if "e\<in>set (lpp_hc_outputs r)" for e
    using shape that by (auto simp: lpp_helper_call_shape_def list_all_iff intro: lpp_caller_endpoint_value[OF ctx])
  have outputs: "lpp_partial_observations (lpp_hc_observed_outputs r) (lpp_helper_call_outputs r ns) ?returned"
    using shape output_value
    by (auto simp: lpp_partial_observations_def lpp_helper_call_outputs_def lpp_helper_call_shape_def list_all_iff)
  show ?thesis
    apply (rule exI[of _ "?returned"])
    apply (rule exI[of _ "map (lp_cut_bind mark (\<lambda>t. lp_ieval t final_eta)) (lpp_hc_later r) @ next_pending"])
    apply (rule exI[of _ "bars @ map (\<lambda>d. LPCClause (LPCAtom (LPIFun (LPCUser f) actuals)#pending) d mark) ?later @ LPCBarrier mark#es"])
    using iteration[unfolded input_value, unfolded list.map lp_cut_bind.simps lp_cut_map.simps lp_ieval.simps append_Cons] outputs by blast
qed

ML \<open>
val checked = [@{thm lpp_checked_helper_call_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted helper call row assembly" else ();
\<close>
end
