theory LP_Prolog_Functor_Control_Contract
 imports LP_Prolog_Functor_Control_Check
begin

definition lpp_stable_functor_module_rep where
 "lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts ss t =
  (\<exists>swaps. lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpc_return_scope_word swaps ss) t)"

lemma lpp_stable_functor_module_intro:
 assumes bounds: "i<length nds" "i<length states" "i<length contexts" "i<length Fs" "i<length functor_contexts"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 shows "lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 unfolding lpp_stable_functor_module_rep_def
 by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
     unfold lpp_stable_functor_rep_def, rule exI[of _ i], rule exI[of _ eta])
   (use assms in auto)

lemma lpp_functor_link_bounds:
 "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e \<Longrightarrow>
  lpcl_target e<length nds \<and> lpcl_target e<length states \<and> lpcl_target e<length contexts \<and>
  lpcl_target e<length Fs \<and> lpcl_target e<length functor_contexts"
 by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def
   lpc_check_return_link_def lpc_check_link_def)

lemma lpp_univ_source_nonbuiltin_base:
 assumes clear: "lpp_no_builtin_frame ss"
 and step: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta ss) event tt"
 shows "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
 using step lpp_no_builtin_frame_sound[OF clear, of eta]
 by (cases rule: lpp_answer_transition.cases)
  (auto simp: lpp_builtin_active_def dest: lpp_univ_source_selected)

theorem lpp_functor_control_cut_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFCut action yes_facts no_facts)"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) ev ys \<Longrightarrow> J (lpc_return_eval eta ss) \<Longrightarrow> J ys"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases "action=LPCRInconsistent")
 case True
 have "lp_cut_check_inconsistent (lpcn_guards nd)"
  using checked by (simp add: True lpp_check_functor_source_action_def)
 then show ?thesis using lp_cut_checked_inconsistent[OF _ known] by blast
next
 case False
 have clear: "lpp_no_builtin_frame ss"
 and local_check: "lpp_check_functor_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   nd F ss source_context source_functors returned arity action"
  using checked False by (auto simp: lpp_check_functor_source_action_def)
 let ?U = "lpp_univ_source_builtin names operation"
 let ?T = "lpp_domain_answers P lpp_builtin_signature ?U lpp_univ_source_domain"
 let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix ev ys assume step: "?T (lpc_return_eval eta ss) ev ys"
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta ss))"
   by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
  have actual: "lpp_answer_transition P lpp_builtin_signature ?U (lpc_return_eval eta ss) ev ys"
   using step supported by (simp add: lpp_domain_answers_def)
  have base: "lpc_answer_transition P (lpc_return_eval eta ss) ev ys"
   by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
  obtain v swaps where strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
   and rep: "lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps ys) v"
   and emitted: "\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
   using lpp_stable_functor_cut_action_sound[OF compatible transfer local_check known free observed functors base] by blast
  have child: "lp_answer_contract ?T ys (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lower[OF strict _ stable[OF step invariant]])
    (use rep in \<open>auto simp: lpp_stable_functor_module_rep_def\<close>)
  have lifted: "lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  show "(\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   using emitted lifted by blast
 qed
qed

theorem lpp_functor_control_test_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and stable: "\<And>ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) ev ys \<Longrightarrow> J (lpc_return_eval eta ss) \<Longrightarrow> J ys"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts
   nd F ss source_context source_functors f a gs active saved yes no"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
 show ?thesis
 proof (rule lp_answer_contract_intro)
  fix ev ys assume step: "?T (lpc_return_eval eta ss) ev ys"
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta ss))"
   by (rule lpp_functor_term_test_domain[OF check])
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    (lpc_return_eval eta ss) ev ys"
   using step supported by (simp add: lpp_domain_answers_def)
  obtain v swaps where silent: "ev=None" and strict: "(?t,v)\<in>(lp_ild Q)\<^sup>+"
   and rep: "lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps ys) v"
   using lpp_stable_functor_term_test_sound[OF compatible transfer check known free observed functors actual] by blast
  have child: "lp_answer_contract ?T ys (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lower[OF strict _ stable[OF step invariant]])
    (use rep in \<open>auto simp: lpp_stable_functor_module_rep_def\<close>)
  have lifted: "lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  show "(\<forall>rho. ev=Some rho \<longrightarrow> (?t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*) \<and>
    lp_answer_contract ?T ys (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   using silent lifted by simp
 qed
qed

theorem lpp_functor_control_is_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFIs result_var middle facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and normalized: "\<And>f. J (lpc_return_eval eta ss) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_observed_functor_link T facts fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors a e gs active saved result_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
  by (rule lpp_functor_is_check_domain[OF checked[unfolded shape] known observed])
 have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
  using check by (auto simp: lpp_check_observed_functor_link_def lpp_check_evaluation_functor_link_def
    lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 show ?thesis
 proof (rule lpp_functor_observed_is_domain_contract[OF compatible transfer check domain known free observed functors invariant normalized])
  fix rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  let ?v = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  assume strict: "(?t,?v)\<in>(lp_ild Q)\<^sup>+"
   and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
  have rep: "lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpc_return_eval rho (states!lpcl_target middle)) ?v"
   by (rule lpp_stable_functor_module_intro[OF bounds child_known child_free child_observed child_functors])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep child_invariant]])
 qed
qed

theorem lpp_functor_control_univ_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss
   source_context source_functors returned arity (LPPFUniv value_var name_var args_var middle facts)"
 and shape: "ss=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),active)#saved)"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and invariant: "J (lpc_return_eval eta ss)"
 and normalized: "\<And>f ts. lp_ieval a eta=LPIFun f ts \<Longrightarrow> J (lpc_return_eval eta ss) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval b eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"
 and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<Longrightarrow> J vs \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 have check: "lpp_check_univ_evaluation_context T facts fuel Q nds states contexts functor_contexts Fs nd F ss
   source_context source_functors a b gs active saved value_var name_var args_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
  using check by (auto simp: lpp_check_univ_evaluation_context_def lpp_check_evaluation_functor_link_def
    lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
 show ?thesis
 proof (rule lpp_univ_stable_context_contract_invariant[OF compatible transfer check known free observed functors _ _ _ invariant normalized])
  show "(''2:=..'',2)\<in>lpp_builtin_signature" by (simp add: lpp_builtin_signature_def)
  show "\<And>x y. lpp_univ_view_domain x y \<Longrightarrow> lpp_univ_source_domain ''2:=..'' [x,y]"
   by (rule lpp_univ_source_domain_covered)
  show "\<And>x y out. lpp_univ_view_domain x y \<Longrightarrow>
    lpp_univ_source_builtin names operation ''2:=..'' [x,y] out \<Longrightarrow> lpp_univ_view_outcome names x y out"
   by (rule lpp_univ_source_outcome_covered)
 next
  fix rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  let ?v = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  assume edge: "(?t,?v)\<in>lp_ild Q"
   and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
  have strict: "(?t,?v)\<in>(lp_ild Q)\<^sup>+" by (rule r_into_trancl[OF edge])
  have rep: "lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpc_return_eval rho (states!lpcl_target middle)) ?v"
   by (rule lpp_stable_functor_module_intro[OF bounds child_known child_free child_observed child_functors])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) (lp_ild Q) ?t (\<lambda>rho. [(returned,map rho [0..<arity])])"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep child_invariant]])
 qed
qed

ML \<open>
val checked = [@{thm lpp_functor_control_cut_contract}, @{thm lpp_functor_control_test_contract}, @{thm lpp_functor_control_is_contract}, @{thm lpp_functor_control_univ_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor control contract dependency" else ();
\<close>
end
