theory LP_Prolog_Triple_Answers
 imports LP_Prolog_Actual_Returns LP_Prolog_Return_Interface LP_Dependency_Triple_Models
begin

definition lpp_triple_answer_contract where
  "lpp_triple_answer_contract P ss Q ret =
    (SN_on (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)) {ss} \<and>
      (\<forall>eta. lp_actual_answer (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss eta \<longrightarrow>
        lp_answer_model Q (ret eta)))"

lemma lpp_triple_answer_contract_return_contract:
  "lpp_triple_answer_contract P ss Q ret \<longleftrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      ss ({} :: bool rel) False (\<lambda>eta. \<not>lp_answer_model Q (ret eta))"
  by (auto simp: lpp_triple_answer_contract_def lp_answer_contract_def
    lp_actual_answer_def lp_answers_covered_def)

lemma lpp_triple_answer_contract_SN:
  "lpp_triple_answer_contract P ss Q ret \<Longrightarrow>
    SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) {map fst ss}"
  by (rule lpp_domain_instrumentation_SN) (simp add: lpp_triple_answer_contract_def)

lemma lpp_triple_answer_contract_return:
  "lpp_triple_answer_contract P ss Q ret \<Longrightarrow>
    lp_actual_answer (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss eta \<Longrightarrow>
    lp_answer_model Q (ret eta)"
  by (simp add: lpp_triple_answer_contract_def)

theorem lpp_triple_answer_split:
  assumes program: "lp_cut_source_program P"
    and prefix: "lpp_triple_answer_contract P ss Q ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>eta.
      lp_actual_answer (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss eta \<Longrightarrow>
      lp_answer_model Q (ret eta) \<Longrightarrow>
      lpp_triple_answer_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] Q final"
  shows "lpp_triple_answer_contract P (lpc_attach_answers rest ss) Q final"
proof -
  have plain: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      ss ({} :: bool rel) False (\<lambda>_. False)"
    using prefix by (auto simp: lp_answer_contract_def lpp_triple_answer_contract_def lp_answers_covered_def)
  show ?thesis unfolding lpp_triple_answer_contract_return_contract
    by (rule lpp_domain_contract_compose_actual[OF program plain valid separated])
      (auto intro: continuation lpp_triple_answer_contract_return[OF prefix]
        simp: lpp_triple_answer_contract_return_contract[symmetric])
qed

theorem lpp_triple_answer_contract_modular:
  assumes descent: "SN_on D {a}"
    and represented: "rep ss a ret"
    and local: "\<And>us b out. rep us b out \<Longrightarrow>
      (\<And>vs c final. (b,c)\<in>D \<Longrightarrow> rep vs c final \<Longrightarrow>
        lpp_triple_answer_contract P vs Q final) \<Longrightarrow>
      lpp_triple_answer_contract P us Q out"
  shows "lpp_triple_answer_contract P ss Q ret"
proof -
  have all: "\<forall>us out. rep us b out \<longrightarrow> lpp_triple_answer_contract P us Q out"
    if sn: "SN_on D {b}" for b
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix b us out
    assume ih: "\<And>c. (b,c)\<in>D \<Longrightarrow>
      \<forall>vs final. rep vs c final \<longrightarrow> lpp_triple_answer_contract P vs Q final"
      and rep: "rep us b out"
    show "lpp_triple_answer_contract P us Q out"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF descent] represented by blast
qed

end
