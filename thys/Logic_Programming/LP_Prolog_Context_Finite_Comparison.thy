theory LP_Prolog_Context_Finite_Comparison
 imports LP_Prolog_Context_Free_Link LP_Prolog_Context_Comparison LP_Prolog_Probe_Return_Domain
begin

lemma lpp_finite_comparison_outcome_kind:
  "lpp_finite_compare_outcome comparison a b outcome \<Longrightarrow>
    outcome=LPPBuiltinSuccess LPIVar \<or> outcome=LPPBuiltinFailure \<or> outcome=LPPBuiltinError"
  by (auto simp: lpp_finite_compare_outcome_def lpp_integer_compare_outcome_def split: if_splits)

lemma lpp_finite_comparison_success_identity:
  "lpp_finite_compare_outcome comparison a b (LPPBuiltinSuccess sigma) \<Longrightarrow> sigma=LPIVar"
  using lpp_finite_comparison_outcome_kind by blast

lemma lpp_finite_comparison_step:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs),eta)#saved) event tt"
  shows "event=None \<and>
    ((tt=(LPCGoals gs,eta)#saved \<and>
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar))
     \<or> tt=saved \<or> tt=[])"
proof -
  have selected: "(f,length [a,b])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF descriptor] by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. lpp_integer_source_builtin f [a,b] outcome =
      lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) outcome"
    by (rule lpp_integer_source_finite_comparison[OF descriptor])
  have identity: "\<And>sigma. lpp_integer_source_builtin f [a,b] (LPPBuiltinSuccess sigma) \<Longrightarrow> sigma=LPIVar"
    unfolding outcomes by (rule lpp_finite_comparison_success_identity)
  have success: "\<And>sigma. lpp_integer_source_builtin f [a,b] (LPPBuiltinSuccess sigma) \<Longrightarrow>
    sigma=LPIVar \<and> lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) (LPPBuiltinSuccess LPIVar)"
    using identity outcomes by metis
  show ?thesis using step selected
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def lpp_integer_source_no_probe lpp_integer_source_no_call lpp_integer_source_no_branch lpp_integer_source_no_choice simp del: lpp_integer_source_builtin.simps
        dest!: success)
qed

definition lpp_check_free_finite_comparison where
  "lpp_check_free_finite_comparison fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     lpp_comparison_descriptor f comparison reversed \<and>
     vars_term a \<union> vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_numeric_observation (LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)) source_context) yes \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd saved
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context no \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd []
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context error_edge)"

lemma lpp_free_finite_comparison_domain:
  assumes checked: "lpp_check_free_finite_comparison fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    and finite: "lp_seg_ground (lp_ieval a eta)" "lp_seg_ground (lp_ieval b eta)"
    using checked known lpp_source_context_ground_sound[OF observed]
    by (auto simp: lpp_check_free_finite_comparison_def lp_cut_knowledge_def lp_seg_ground_eval)
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name lpp_source_comparison_descriptor by blast
  show ?thesis using finite name
    by (cases comparison; cases reversed; simp add: shape lpc_return_eval_def)
qed

theorem lpp_free_finite_comparison_sound:
  assumes checked: "lpp_check_free_finite_comparison fuel Q nds states contexts Fs nd F ss source_context f comparison reversed a b gs active saved yes no error_edge"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?observation = "LPPOComparison comparison (if reversed then b else a) (if reversed then a else b)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    using checked by (auto simp: lpp_check_free_finite_comparison_def)
  have raw: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta,lp_ieval b eta]) #
       map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    using step by (simp add: shape lpc_return_eval_def)
  have actual: "event=None \<and>
    ((tt=lpc_return_eval eta ((LPCGoals gs,active)#saved) \<and> lpp_numeric_observation_holds eta ?observation)
      \<or> tt=lpc_return_eval eta saved \<or> tt=lpc_return_eval eta [])"
    using lpp_finite_comparison_step[OF name raw]
    by (auto simp: shape lpc_return_eval_def split: if_splits)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have yes_link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd ((LPCGoals gs,active)#saved)
    (lpcn_ground nd) (lpcn_guards nd) [] F (lpp_add_numeric_observation ?observation source_context) yes"
    and no_link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd saved
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context no"
    and error_link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd []
    (lpcn_ground nd) (lpcn_guards nd) [] F source_context error_edge"
    using checked by (auto simp: lpp_check_free_finite_comparison_def)
  have yes_step: "lpp_numeric_observation_holds eta ?observation \<Longrightarrow>
    \<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ((LPCGoals gs,active)#saved))) u"
    by (rule lpp_context_free_link_sound[OF yes_link equations refl known free])
      (rule lpp_add_numeric_observation_holds[OF observed])
  show ?thesis using actual yes_step lpp_context_free_link_sound[OF no_link equations refl known free observed]
    lpp_context_free_link_sound[OF error_link equations refl known free observed] by blast
qed

record lpp_finite_comparison_receipt =
  lppfc_predicate :: string
  lppfc_comparison :: lpp_integer_comparison
  lppfc_reversed :: bool
  lppfc_left :: "string lpc_term"
  lppfc_right :: "string lpc_term"
  lppfc_goals :: "string lpc_term lp_cut_goal list"
  lppfc_active :: "string lpc_term list"
  lppfc_saved :: "string lpc_return_state"
  lppfc_yes :: "string lpc_link"
  lppfc_no :: "string lpc_link"
  lppfc_error :: "string lpc_link"

definition lpp_check_free_finite_comparison_receipt where
  "lpp_check_free_finite_comparison_receipt fuel Q nds states contexts Fs nd F ss source_context evidence =
    lpp_check_free_finite_comparison fuel Q nds states contexts Fs nd F ss source_context
      (lppfc_predicate evidence) (lppfc_comparison evidence) (lppfc_reversed evidence)
      (lppfc_left evidence) (lppfc_right evidence) (lppfc_goals evidence) (lppfc_active evidence)
      (lppfc_saved evidence) (lppfc_yes evidence) (lppfc_no evidence) (lppfc_error evidence)"

lemma lpp_free_finite_receipt_domain:
  "lpp_check_free_finite_comparison_receipt fuel Q nds states contexts Fs nd F ss source_context evidence \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta \<Longrightarrow>
   lpp_source_context_holds SP source_context eta \<Longrightarrow>
   \<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
  unfolding lpp_check_free_finite_comparison_receipt_def by (rule lpp_free_finite_comparison_domain)

lemma lpp_free_finite_receipt_sound:
  "lpp_check_free_finite_comparison_receipt fuel Q nds states contexts Fs nd F ss source_context evidence \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta \<Longrightarrow>
   lpc_free_knowledge (set F) eta \<Longrightarrow>
   lpp_source_context_holds SP source_context eta \<Longrightarrow>
   lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt \<Longrightarrow>
   event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
  unfolding lpp_check_free_finite_comparison_receipt_def by (rule lpp_free_finite_comparison_sound)

definition lpp_check_finite_comparison_receipt where
  "lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence =
    lpp_check_free_finite_comparison_receipt fuel Q nds states contexts (replicate (length nds) []) nd [] ss source_context evidence"

lemma lpp_finite_receipt_domain:
  "lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta \<Longrightarrow>
   lpp_source_context_holds SP source_context eta \<Longrightarrow>
   \<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
  unfolding lpp_check_finite_comparison_receipt_def by (rule lpp_free_finite_receipt_domain)

lemma lpp_finite_receipt_sound:
  assumes checked: "lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have free: "lpc_free_knowledge (set []) eta" by (simp add: lpc_free_knowledge_def)
  have result: "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts (replicate (length nds) []) (lpc_return_scope_word swaps tt) u)"
    by (rule lpp_free_finite_receipt_sound[OF checked[unfolded lpp_check_finite_comparison_receipt_def] known free observed step])
  show ?thesis using result by (auto simp: lpp_context_free_rep_def lpp_context_return_rep_def)
qed


ML \<open>
val checked = [@{thm lpp_finite_comparison_step}, @{thm lpp_free_finite_comparison_domain},
  @{thm lpp_free_finite_comparison_sound}, @{thm lpp_finite_receipt_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite comparison dependency" else ();
\<close>
end
