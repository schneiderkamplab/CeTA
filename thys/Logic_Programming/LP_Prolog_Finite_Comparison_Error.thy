theory LP_Prolog_Finite_Comparison_Error
 imports LP_Prolog_Finite_Context_Length
begin

text \<open>A free root operand causes an instantiation error only when the
other operand cannot hide an infinite evaluation. Both operands below are
finite ground terms or free variables. No success fact is exported.\<close>

lemma lpp_finite_comparison_error_exact:
  assumes error: "lpp_finite_compare_error a b"
  shows "lpp_finite_compare_outcome comparison a b outcome \<longleftrightarrow> outcome=LPPBuiltinError"
  using error lpp_finite_compare_error_ground[of a b]
  by (auto simp: lpp_finite_compare_outcome_def)

lemma lpp_finite_comparison_error_symmetric:
  "lpp_finite_compare_error a b \<longleftrightarrow> lpp_finite_compare_error b a"
  by (auto simp: lpp_finite_compare_error_def)

lemma lpp_finite_comparison_error_step:
  assumes name: "lpp_comparison_descriptor f comparison reversed"
    and error: "lpp_finite_compare_error a b"
    and step: "lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and> tt=[]"
proof -
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''" and nl: "f\<noteq>''2:length''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name by (simp only: lpp_source_comparison_descriptor)
  have nd: "f\<noteq>lpp_disequality_predicate"
    using descriptor by (auto simp only: lpp_disequality_names)
  have np: "\<not>lpp_probe_name f"
  proof
    assume name: "lpp_probe_name f"
    have none: "lpp_source_comparison f=None"
      using name by (auto simp only: lpp_probe_name_def lpp_probe_legacy_flags(3,8,13))
    with descriptor show False by simp
  qed
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF name] by (simp add: numeral_2_eq_2)
  have domain: "lpp_finite_source_domain f [a,b]"
    using error
    by (simp only: lpp_finite_source_domain_def np ne nl nd if_False
        lpp_integer_source_domain.simps ni descriptor option.case; simp)
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
    using step domain by (auto simp: lpp_domain_answers_def)
  have outcome: "\<And>out. lpp_finite_source_builtin f [a,b] out \<longleftrightarrow> out=LPPBuiltinError"
    using error lpp_finite_comparison_error_symmetric[of a b]
    by (simp only: lpp_finite_source_legacy[OF ne nd nl np]
        lpp_integer_source_finite_comparison[OF name]; cases reversed;
        simp add: lpp_finite_comparison_error_exact)
  show ?thesis using actual selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def outcome)
qed

fun lpp_checked_free_operand where
  "lpp_checked_free_operand F (Var x) = (x\<in>set F)"
| "lpp_checked_free_operand F (Fun f ts) = False"

lemma lpp_checked_free_operand_sound:
  "lpp_checked_free_operand F a \<Longrightarrow> lpc_free_knowledge (set F) eta \<Longrightarrow>
    \<exists>x. lp_ieval a eta=LPIVar x"
  by (cases a) (auto simp: lpc_free_knowledge_def)

definition lpp_check_finite_comparison_error where
  "lpp_check_finite_comparison_error nd F ss source_context f comparison reversed a b gs active saved =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     lpp_comparison_descriptor f comparison reversed \<and>
     ((lpp_checked_free_operand F a \<and>
         (vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<or>
          lpp_checked_free_operand F b)) \<or>
      (lpp_checked_free_operand F b \<and>
         vars_term a \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context)))"

lemma lpp_finite_comparison_error_contract:
  assumes checked: "lpp_check_finite_comparison_error nd F ss source_context f comparison reversed a b gs active saved"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context eta"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  let ?T = "lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    using checked by (auto simp: lpp_check_finite_comparison_error_def)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    if "vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context" for e
    using known that lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
    by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
  have error: "lpp_finite_compare_error (lp_ieval a eta) (lp_ieval b eta)"
    using checked free lpp_checked_free_operand_sound[of F a eta]
      lpp_checked_free_operand_sound[of F b eta] ground
    by (auto simp: lpp_check_finite_comparison_error_def lpp_finite_compare_error_def)
  have empty: "lp_answer_contract ?T [] R t ret"
  proof (rule lp_answer_contract_intro)
    fix ev :: "(nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
    assume step: "?T [] ev us"
    have "([],map fst us)\<in>lpp_atomic_source P lpp_builtin_signature lpp_finite_source_builtin"
      using step by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
    then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
      by (simp add: lpp_atomic_source_empty)
  qed
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix ev us assume step: "?T (lpc_return_eval eta ss) ev us"
    have "ev=None \<and> us=[]"
      using lpp_finite_comparison_error_step[OF name error] step
      by (simp add: shape lpc_return_eval_def)
    then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
      using empty by simp
  qed
qed

ML \<open>
val checked = [@{thm lpp_finite_comparison_error_step}, @{thm lpp_finite_comparison_error_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite comparison error dependency" else ();
\<close>
end
