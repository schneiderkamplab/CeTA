theory LP_Prolog_Univ_Source
 imports LP_Prolog_Univ_Evaluation_Context LP_Prolog_Stable_Source
begin

text \<open>Extend the builtin interpretation of the shared source machine with
checked univ decomposition. The name map remains universally parameterized in
soundness statements: certificates cannot choose a favorable name encoding.
Connecting this interpretation to an original source still requires its symbol
correspondence. Construction from a known functor and variable input remains
outside the checked domain, not an assumed failure.\<close>

definition lpp_univ_source_builtin where
 "lpp_univ_source_builtin names operation f ts outcome =
  (if f=''2:=..'' then length ts=2 \<and> lpp_univ_view_outcome names (ts!0) (ts!1) outcome
   else lpp_stable_source_builtin operation f ts outcome)"

definition lpp_univ_source_domain where
 "lpp_univ_source_domain f ts =
  (if f=''2:=..'' then length ts=2 \<and> lpp_univ_view_domain (ts!0) (ts!1)
   else lpp_finite_source_domain f ts)"

lemma lpp_univ_source_other:
 "f\<noteq>''2:=..'' \<Longrightarrow>
  lpp_univ_source_builtin names operation f ts outcome=lpp_stable_source_builtin operation f ts outcome"
 "f\<noteq>''2:=..'' \<Longrightarrow>
  lpp_univ_source_domain f ts=lpp_finite_source_domain f ts"
 by (simp_all add: lpp_univ_source_builtin_def lpp_univ_source_domain_def)

lemma lpp_univ_source_domain_covered:
 "lpp_univ_view_domain a b \<Longrightarrow> lpp_univ_source_domain ''2:=..'' [a,b]"
 by (simp add: lpp_univ_source_domain_def)

lemma lpp_univ_source_outcome_covered:
 "lpp_univ_source_builtin names operation ''2:=..'' [a,b] outcome \<Longrightarrow>
  lpp_univ_view_outcome names a b outcome"
 by (simp add: lpp_univ_source_builtin_def)

lemma lpp_univ_source_selected:
 assumes "lpp_univ_source_builtin names operation f ts outcome"
 shows "(f,length ts)\<in>lpp_builtin_signature"
proof (cases "f=''2:=..''")
 case True
 then show ?thesis using assms
  by (simp add: lpp_univ_source_builtin_def lpp_builtin_signature_def)
next
 case False
 then have "lpp_stable_source_builtin operation f ts outcome" using assms
  by (simp add: lpp_univ_source_builtin_def)
 then show ?thesis by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite])
qed

lemma lpp_univ_legacy_domain_absent:
 "\<not> lpp_finite_source_domain ''2:=..'' ts"
 by (simp add: lpp_finite_source_domain_def lpp_probe_name_def
   lpp_disequality_predicate_def lpp_var_name_def lpp_identity_name_def; code_simp)

lemma lpp_univ_source_legacy_domain_agreement:
 assumes "lpp_finite_source_domain f ts"
 shows "lpp_univ_source_domain f ts"
 and "lpp_univ_source_builtin names operation f ts outcome=lpp_stable_source_builtin operation f ts outcome"
 using assms lpp_univ_legacy_domain_absent[of ts]
 by (auto simp: lpp_univ_source_domain_def lpp_univ_source_builtin_def)

lemma lpp_univ_source_wrong_arity_rejected:
 "length ts\<noteq>2 \<Longrightarrow> \<not>lpp_univ_source_domain ''2:=..'' ts"
 "length ts\<noteq>2 \<Longrightarrow> \<not>lpp_univ_source_builtin names operation ''2:=..'' ts outcome"
 by (simp_all add: lpp_univ_source_domain_def lpp_univ_source_builtin_def)

lemma lpp_univ_source_local_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes contract: "lpp_eval_integer_contract TYPE(string) E"
 and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and context_held: "lpp_evaluation_context_holds E SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and lower: "\<And>rho.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q \<Longrightarrow>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
    lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
    lpp_evaluation_context_holds E SP (contexts!lpcl_target middle) rho \<Longrightarrow>
    list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain) (lpc_return_eval eta ss) R t ret"
proof -
 have selected: "(''2:=..'',2)\<in>lpp_builtin_signature"
  by (simp add: lpp_builtin_signature_def)
 show ?thesis
  apply (rule lpp_univ_evaluation_context_contract[OF contract evaluation program checked known free context_held functors selected])
     apply assumption
    apply (rule lpp_univ_source_domain_covered, assumption)
   apply (rule lpp_univ_source_outcome_covered, assumption)
  by (rule lower; assumption)
qed

ML \<open>
val checked = @{thms lpp_univ_source_legacy_domain_agreement}
 @ [@{thm lpp_univ_source_outcome_covered}, @{thm lpp_univ_source_selected}, @{thm lpp_univ_source_local_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted univ source interpretation dependency" else ();
\<close>
end
