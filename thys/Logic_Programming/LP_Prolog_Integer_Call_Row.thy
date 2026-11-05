theory LP_Prolog_Integer_Call_Row
  imports LP_Prolog_Integer_Recurrence_Failure LP_Prolog_Integer_Recurrence_Inverse
begin

record lpp_arithmetic_call =
  lpp_call_clause :: nat
  lpp_call_variables :: "string list"
  lpp_call_prefix :: "lpp_recurrence_operation list"
  lpp_call_target :: string
  lpp_call_outputs :: "string lpp_integer_expression list"
  lpp_call_failures :: "lpp_arithmetic_failure list"

definition lpp_arithmetic_call_shape where
  "lpp_arithmetic_call_shape P f arity r =
    (length (lpp_call_variables r)=arity \<and> distinct (lpp_call_variables r) \<and>
     lpp_call_clause r<length P \<and> (f,arity)\<notin>lpp_builtin_signature \<and>
     P!lpp_call_clause r=(Fun (LPCUser f) (map Var (lpp_call_variables r)),
       map lpp_recurrence_goal (lpp_call_prefix r) @
       [LPCAtom (Fun (LPCUser (lpp_call_target r)) (map lpp_expression_term (lpp_call_outputs r)))]) \<and>
     lp_cut_slice P (LPCUser f) arity =
       map lpp_failure_clause (lpp_call_failures r) @ lpp_call_clause r #
         drop (length (lpp_call_failures r)+1) (lp_cut_slice P (LPCUser f) arity) \<and>
     list_all (lpp_arithmetic_failure_shape P f arity) (lpp_call_failures r) \<and>
     lpp_recurrence_check (lpp_call_variables r) (lpp_call_prefix r) \<and>
     list_all (\<lambda>e. lpp_integer_endpoint e \<and>
       lpp_expression_check (lpp_recurrence_known (lpp_call_variables r) (lpp_call_prefix r)) e)
       (lpp_call_outputs r))"

definition lpp_arithmetic_call_holds where
  "lpp_arithmetic_call_holds r ns =
    (list_all (\<lambda>failed. lpp_arithmetic_failure_holds failed ns) (lpp_call_failures r) \<and>
     lpp_recurrence_guards (lpp_call_prefix r) (lpp_recurrence_arguments (lpp_call_variables r) ns))"

definition lpp_arithmetic_call_outputs where
  "lpp_arithmetic_call_outputs r ns = map (\<lambda>e. lpp_expression_value e
    (lpp_recurrence_values (lpp_call_prefix r) (lpp_recurrence_arguments (lpp_call_variables r) ns)))
    (lpp_call_outputs r)"

lemma lpp_checked_arithmetic_call_steps:
  assumes shape: "lpp_arithmetic_call_shape P f (length ns) r"
    and holds: "lpp_arithmetic_call_holds r ns"
  shows "\<exists>saved. (LPCGoals [LPCAtom (LPIFun (LPCUser f) (map lpp_integer_value ns))]#es,
    LPCGoals [LPCAtom (LPIFun (LPCUser (lpp_call_target r))
      (map lpp_integer_value (lpp_arithmetic_call_outputs r ns)))]#saved)
    \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?xs = "lpp_call_variables r"
  let ?ops = "lpp_call_prefix r"
  let ?rho = "lpp_recurrence_arguments ?xs ns"
  let ?eta = "lpp_recurrence_environment ?xs ?rho"
  let ?tail = "Fun (LPCUser (lpp_call_target r)) (map lpp_expression_term (lpp_call_outputs r))"
  let ?earlier = "map lpp_failure_clause (lpp_call_failures r)"
  let ?later = "drop (length (lpp_call_failures r)+1) (lp_cut_slice P (LPCUser f) (length ns))"
  have length: "length ?xs=length ns" and distinct: "distinct ?xs"
    using shape by (auto simp: lpp_arithmetic_call_shape_def)
  have exact: "map ?rho ?xs=ns" by (rule lpp_recurrence_arguments_exact[OF length distinct])
  have input_value: "lp_ieval (Fun (LPCUser f) (map Var ?xs)) ?eta=
      LPIFun (LPCUser f) (map lpp_integer_value ns)"
    using arg_cong[OF exact, of "map lpp_integer_value"]
    by (simp add: lpp_recurrence_environment_def map_map o_def cong: map_cong)
  have failed: "(LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?xs)) ?eta)] d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    if member: "d\<in>set ?earlier" for d mark saved
  proof -
    obtain receipt where receipt: "receipt\<in>set (lpp_call_failures r)" and clause: "d=lpp_failure_clause receipt"
      using member by auto
    have checked: "lpp_arithmetic_failure_shape P f (length ns) receipt"
      and failure: "lpp_arithmetic_failure_holds receipt ns"
      using shape holds receipt by (auto simp: lpp_arithmetic_call_shape_def lpp_arithmetic_call_holds_def list_all_iff)
    show ?thesis using lpp_checked_arithmetic_failure_restores_stack[OF checked failure, where mark=mark and es=saved]
      by (simp only: input_value clause)
  qed
  obtain mark where iteration: "(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?xs)) ?eta)]#es,
      LPCGoals [LPCAtom (lp_ieval ?tail
        (lpp_recurrence_environment (lpp_recurrence_known ?xs ?ops) (lpp_recurrence_values ?ops ?rho)))]#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var ?xs)) ?eta)] d mark) ?later @
        LPCBarrier mark#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    by (rule exE[OF lpp_recurrence_selected_source_iteration[where earlier="?earlier"
      and c="lpp_call_clause r" and cs="?later" and P=P and f=f and xs="?xs" and ops="?ops"
      and tail="?tail" and rho="?rho" and es=es]])
      (use shape holds failed in \<open>auto simp: lpp_arithmetic_call_shape_def lpp_arithmetic_call_holds_def length\<close>)
  have endpoint: "lp_ieval (lpp_expression_term e)
      (lpp_recurrence_environment (lpp_recurrence_known ?xs ?ops) (lpp_recurrence_values ?ops ?rho))=
      lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ?ops ?rho))"
    if "e\<in>set (lpp_call_outputs r)" for e
    using shape that by (auto simp: lpp_arithmetic_call_shape_def list_all_iff intro: lpp_recurrence_endpoint_value)
  have output_value: "lp_ieval ?tail
      (lpp_recurrence_environment (lpp_recurrence_known ?xs ?ops) (lpp_recurrence_values ?ops ?rho))=
      LPIFun (LPCUser (lpp_call_target r)) (map lpp_integer_value (lpp_arithmetic_call_outputs r ns))"
    by (simp add: lpp_arithmetic_call_outputs_def map_map o_def endpoint cong: map_cong)
  show ?thesis using iteration by (simp only: input_value output_value; blast)
qed

ML \<open>
val checked = [@{thm lpp_checked_arithmetic_call_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic call receipt dependency" else ();
\<close>
end
