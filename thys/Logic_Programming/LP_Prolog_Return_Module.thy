theory LP_Prolog_Return_Module
  imports LP_Prolog_Return_Modular LP_Cut_Return_Module
begin

datatype lpp_return_module_action = LPPMPrimitive lpp_return_action
  | LPPMTrim "string lpc_return_state" "string lpc_return_state" "string lpc_link"
  | LPPMParallel "string lpc_link list"
  | LPPMRefuted nat nat "(string * string lpc_term) list"

fun lpp_check_return_module_action where
  "lpp_check_return_module_action fuel P Q nds states nd ss returned arity (LPPMPrimitive action) =
    lpp_check_return_action fuel P Q nds states nd ss returned arity action"
| "lpp_check_return_module_action fuel P Q nds states nd ss returned arity (LPPMTrim successor barriers e) =
    (ss=successor@barriers \<and> lp_cut_barriers (map fst barriers) \<and>
      lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e)"

| "lpp_check_return_module_action fuel P Q nds states nd ss returned arity (LPPMParallel links) =
    (length links=length ss \<and> list_all (\<lambda>i.
      lpc_check_return_table_link fuel Q nds states nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] (links!i)) [0..<length ss])"

| "lpp_check_return_module_action fuel P Q nds states nd ss returned arity (LPPMRefuted i k bindings) =
    lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"

theorem lpp_return_module_action_sound:
  assumes checked: "lpp_check_return_module_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpc_return_module_rep nds states vs v \<Longrightarrow>
      lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
        vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
    (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPPMPrimitive primitive)
  have check: "lpp_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPPMPrimitive by simp
  show ?thesis
  proof (rule lp_answer_contract_primitive[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v"])
    fix vs v and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
      (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v"
    show "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin) vs (lp_ild Q) v out"
      using lower[OF strict] represented by auto
  next
    fix event tt
    assume step: "lpp_answer_transition P lpp_builtin_signature lpp_test_builtin (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
       lpc_return_module_rep nds states tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_return_action_sound[OF check known step] by (auto simp: lpc_return_module_rep_def)
  qed
next
  case (LPPMTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked LPPMTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpc_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpc_return_table_link_sound[OF link equations refl known] by blast
  have child: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
    (lpc_return_eval eta successor) (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: lpc_return_module_rep_def\<close>)
  have parent: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
    (lpc_return_eval eta successor) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  have old: "lpp_return_contract P lpp_builtin_signature lpp_test_builtin
    (lpc_return_eval eta successor) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using parent by (simp add: lpp_return_as_answer_contract)
  show ?thesis using lpp_return_contract_append_barriers[OF old suffix]
    by (simp add: lpp_return_as_answer_contract shape lpc_return_eval_def)
next
  case (LPPMParallel links)
  have contract: "lpp_return_contract P lpp_builtin_signature lpp_test_builtin
    (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
  proof (rule lpp_return_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpc_check_return_table_link fuel Q nds states nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] (links!i)"
      using checked LPPMParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpc_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpc_return_table_link_sound[OF link equations refl known] by blast
    have child: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
      (lpc_return_eval eta [ss!i]) (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
      by (rule lower[OF strict]) (use rep in \<open>auto simp: lpc_return_module_rep_def\<close>)
    show "lpp_return_contract P lpp_builtin_signature lpp_test_builtin [e] (lp_ild Q)
      [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
      unfolding e lpp_return_as_answer_contract
      by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  qed
  show ?thesis using contract by (simp add: lpp_return_as_answer_contract)
next
  case (LPPMRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPMRefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed

definition lpp_check_return_module where
  "lpp_check_return_module fuel P Q nds states returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpp_check_return_module_action fuel P Q nds states (nds!i) (states!i) returned arity (actions!i)) [0..<length nds])"

theorem lpp_check_return_module_contract:
  assumes checked: "lpp_check_return_module fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpp_return_contract P lpp_builtin_signature lpp_test_builtin (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  unfolding lpp_return_as_answer_contract
proof (rule lp_answer_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    lpc_return_module_rep nds states (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding lpc_return_module_rep_def lpc_return_rep_def
    using root known checked by (auto simp: lpp_check_return_module_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
    (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v \<Longrightarrow>
      lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin) vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpc_return_module_rep_def lpc_return_rep_def)
  have check: "lpp_check_return_module_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
    using checked bound by (auto simp: lpp_check_return_module_def list_all_iff)
  have canonical: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin)
    (lpc_return_eval nu (states!j)) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule lpp_return_module_action_sound[OF check knowledge]) (use lower t in blast)
  have old: "lpp_return_contract P lpp_builtin_signature lpp_test_builtin
    (lpc_return_eval nu (states!j)) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using canonical by (simp add: lpp_return_as_answer_contract)
  have restored: "lpp_return_contract P lpp_builtin_signature lpp_test_builtin
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_return_contract_scopes[OF program old])
  show "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_test_builtin) ss (lp_ild Q) t out"
    using restored represented by (simp add: lpp_return_as_answer_contract shape[symmetric] lpc_return_scope_word_inverse)
qed

end
