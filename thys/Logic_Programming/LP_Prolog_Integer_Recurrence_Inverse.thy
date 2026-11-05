theory LP_Prolog_Integer_Recurrence_Inverse
  imports LP_Prolog_Integer_Recurrence_Relation
begin

lemma lpp_recurrence_endpoint_value:
  assumes "lpp_integer_endpoint e" "lpp_expression_check K e"
  shows "lp_ieval (lpp_expression_term e) (lpp_recurrence_environment K rho) =
    lpp_integer_value (lpp_expression_value e rho)"
  using assms by (cases e) (auto simp: lpp_recurrence_environment_def)

lemma lpp_recurrence_head_values:
  "lp_ieval (Fun (LPCUser f) (map Var xs)) (lpp_recurrence_environment xs rho) =
    LPIFun (LPCUser f) (map (lpp_integer_value o rho) xs)"
  by (simp add: map_map o_def lpp_recurrence_environment_def)

definition lpp_recurrence_integer_relation where
  "lpp_recurrence_integer_relation xs ops outputs =
    {(before,after). IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after (\<lambda>_. 0)))
      (lpp_recurrence_relation_formula xs ops outputs)}"

lemma lpp_recurrence_integer_relation_source_no:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),
      map lpp_recurrence_goal ops @
        [LPCAtom (Fun (LPCUser f) (map lpp_expression_term outputs))])"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
    and checked: "lpp_recurrence_check xs ops"
    and lengths: "length xs=length outputs"
    and endpoints: "list_all (\<lambda>e. lpp_integer_endpoint e \<and>
      lpp_expression_check (lpp_recurrence_known xs ops) e) outputs"
    and child: "\<not>SN_on (lpp_recurrence_integer_relation xs ops outputs) {rho}"
  shows "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
    {LPCGoals [LPCAtom (LPIFun (LPCUser f) (map (lpp_integer_value o rho) xs))]#es}"
proof -
  let ?S = "lpp_recurrence_integer_relation xs ops outputs"
  have guards: "lpp_recurrence_guards ops a" if "(a,b)\<in>?S" for a b
    using that lpp_recurrence_relation_formula_exact[OF lengths, of a b "\<lambda>_. 0" ops]
    by (simp add: lpp_recurrence_integer_relation_def)
  have call_values: "map b xs=map (\<lambda>e. lpp_expression_value e (lpp_recurrence_values ops a)) outputs"
    if "(a,b)\<in>?S" for a b
    using that lpp_recurrence_relation_formula_exact[OF lengths, of a b "\<lambda>_. 0" ops]
    by (simp add: lpp_recurrence_integer_relation_def)
  have tail_value: "lp_ieval (Fun (LPCUser f) (map lpp_expression_term outputs))
      (lpp_recurrence_environment (lpp_recurrence_known xs ops) (lpp_recurrence_values ops a)) =
      lp_ieval (Fun (LPCUser f) (map Var xs)) (lpp_recurrence_environment xs b)"
    if edge: "(a,b)\<in>?S" for a b
  proof -
    have endpoint: "lp_ieval (lpp_expression_term e)
        (lpp_recurrence_environment (lpp_recurrence_known xs ops) (lpp_recurrence_values ops a)) =
        lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ops a))"
      if "e\<in>set outputs" for e
      using endpoints that by (auto simp: list_all_iff intro: lpp_recurrence_endpoint_value)
    have mapped: "map ((lpp_integer_value :: int \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) o b) xs =
        map (\<lambda>e. lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ops a))) outputs"
      using arg_cong[OF call_values[OF edge], of "map lpp_integer_value"] by (simp add: map_map o_def)
    have evaluated: "map (\<lambda>e. lp_ieval (lpp_expression_term e)
        (lpp_recurrence_environment (lpp_recurrence_known xs ops) (lpp_recurrence_values ops a))) outputs =
        map (\<lambda>e. lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ops a))) outputs"
      by (rule map_cong) (auto intro: endpoint)
    have combined: "map (\<lambda>e. lp_ieval (lpp_expression_term e)
        (lpp_recurrence_environment (lpp_recurrence_known xs ops) (lpp_recurrence_values ops a))) outputs =
        map (lpp_integer_value o b) xs"
      by (rule HOL.trans[OF evaluated mapped[symmetric]])
    show ?thesis
      unfolding lpp_recurrence_head_values
      by (simp only: lp_ieval.simps map_map o_def combined[unfolded o_def])
  qed
  have no: "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
    {LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
      (lpp_recurrence_environment xs rho))]#es}"
    by (rule lpp_recurrence_source_nontermination[OF first index clause ordinary checked child guards tail_value])
  show ?thesis using no by (simp only: lpp_recurrence_head_values; blast)
qed

ML \<open>
val checked = [@{thm lpp_recurrence_integer_relation_source_no}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted inverse integer recurrence dependency" else ();
\<close>
end
