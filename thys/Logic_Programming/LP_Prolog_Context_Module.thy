theory LP_Prolog_Context_Module
  imports LP_Prolog_Context_Finite_Comparison LP_Prolog_Context_Graph LP_Prolog_Return_Modular LP_Cut_Return_Module
begin

datatype lpp_context_module_action = LPPCMPrimitive lpp_context_source_action
  | LPPCMTrim "string lpc_return_state" "string lpc_return_state" "string lpc_link"
  | LPPCMParallel "string lpc_link list"
  | LPPCMRefuted nat nat "(string * string lpc_term) list"
  | LPPCMFiniteComparison lpp_finite_comparison_receipt
  | LPPCMNormalizeIs "string list" "string lpp_integer_expression" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state" string "string lpc_link"
  | LPPCMNormalizeConstantIs "string lpp_integer_expression" "string lpc_term" "string lpc_term"
      "string lpc_term lp_cut_goal list" "string lpc_term list" "string lpc_return_state" "string lpc_link"

definition lpp_context_module_rep where
  "lpp_context_module_rep SP nds states contexts ss t =
    (\<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t)"
fun lpp_context_module_types where
  "lpp_context_module_types (LPPCMPrimitive action) = lpp_context_source_types action"
| "lpp_context_module_types (LPPCMNormalizeIs K evidence a e gs active saved result_var middle) = K"
| "lpp_context_module_types _ = []"

fun lpp_check_context_module_action where
  "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMPrimitive action) =
    lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity action"
| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMTrim successor barriers e) =
    (ss=successor@barriers \<and> lp_cut_barriers (map fst barriers) \<and>
      lpp_check_context_table_link fuel Q nds states contexts nd successor (lpcn_ground nd) (lpcn_guards nd) [] source_context e)"

| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMParallel links) =
    (length links=length ss \<and> list_all (\<lambda>i.
      lpp_check_context_table_link fuel Q nds states contexts nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] source_context (links!i)) [0..<length ss])"

| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMRefuted i k bindings) =
    lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"

| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMFiniteComparison evidence) =
    lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence"

| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMNormalizeIs K evidence a e gs active saved result_var middle) = False"
| "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity (LPPCMNormalizeConstantIs evidence a e gs active saved middle) = False"

theorem lpp_context_module_action_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_module_types action) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_context_module_rep SP nds states contexts vs v \<Longrightarrow>
      lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
        vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
    (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPPCMNormalizeIs K evidence a e gs active saved result_var middle)
  then show ?thesis using checked by simp
next
  case (LPPCMNormalizeConstantIs evidence a e gs active saved middle)
  then show ?thesis using checked by simp
next
  case (LPPCMPrimitive primitive)
  have check: "lpp_check_context_source_action fuel P Q nds states contexts nd ss source_context returned arity primitive"
    using checked LPPCMPrimitive by simp
  show ?thesis
  proof (rule lp_answer_contract_primitive[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts vs v"])
    fix vs v and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
      (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts vs v"
    show "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) vs (lp_ild Q) v out"
      using lower[OF strict] represented by auto
  next
    fix event tt
    assume step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
       lpp_context_module_rep SP nds states contexts tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_context_source_action_sound[OF check known observed _ step] integers LPPCMPrimitive by (auto simp: lpp_context_module_rep_def)
  qed
next
  case (LPPCMFiniteComparison evidence)
  have check: "lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence"
    using checked LPPCMFiniteComparison by simp
  show ?thesis
  proof (rule lp_answer_contract_primitive[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts vs v"])
    fix vs v and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
      (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts vs v"
    show "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) vs (lp_ild Q) v out"
      using lower[OF strict] represented by auto
  next
    fix event tt
    assume step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
       lpp_context_module_rep SP nds states contexts tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_finite_receipt_sound[OF check known observed step] by (auto simp: lpp_context_module_rep_def)
  qed
next
  case (LPPCMTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpp_check_context_table_link fuel Q nds states contexts nd successor (lpcn_ground nd) (lpcn_guards nd) [] source_context e"
    using checked LPPCMTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpp_context_table_link_sound[OF link equations refl known observed] by blast
  have child: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
    (lpc_return_eval eta successor) (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: lpp_context_module_rep_def\<close>)
  have parent: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
    (lpc_return_eval eta successor) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  have old: "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin
    (lpc_return_eval eta successor) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using parent by (simp add: lpp_return_as_answer_contract)
  show ?thesis using lpp_return_contract_append_barriers[OF old suffix]
    by (simp add: lpp_return_as_answer_contract shape lpc_return_eval_def)
next
  case (LPPCMParallel links)
  have contract: "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin
    (lpc_return_eval eta ss) (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
  proof (rule lpp_return_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] source_context (links!i)"
      using checked LPPCMParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpp_context_table_link_sound[OF link equations refl known observed] by blast
    have child: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
      (lpc_return_eval eta [ss!i]) (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
      by (rule lower[OF strict]) (use rep in \<open>auto simp: lpp_context_module_rep_def\<close>)
    show "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin [e] (lp_ild Q)
      [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
      unfolding e lpp_return_as_answer_contract
      by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] child])
  qed
  show ?thesis using contract by (simp add: lpp_return_as_answer_contract)
next
  case (LPPCMRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPCMRefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed

definition lpp_check_context_module where
  "lpp_check_context_module fuel P Q nds states contexts T typings returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     length nds=length contexts \<and> length nds=length typings \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types (actions!i)) \<and>
       lpp_check_context_module_action fuel P Q nds states contexts (nds!i) (states!i) (contexts!i) returned arity (actions!i)) [0..<length nds])"

theorem lpp_check_context_module_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_module fuel P Q nds states contexts T typings returned arity actions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  unfolding lpp_return_as_answer_contract
proof (rule lp_answer_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    lpp_context_module_rep SP nds states contexts (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding lpp_context_module_rep_def lpp_context_return_rep_def
    using root known checked observed by (auto simp: lpp_check_context_module_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
    (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpp_context_module_rep SP nds states contexts vs v \<Longrightarrow>
      lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and facts: "lpp_source_context_holds SP (contexts!j) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpp_context_module_rep_def lpp_context_return_rep_def)
  have check: "lpp_check_context_module_action fuel P Q nds states contexts (nds!j) (states!j) (contexts!j) returned arity (actions!j)"
    using checked bound by (auto simp: lpp_check_context_module_def list_all_iff)
  have typing: "lpp_check_context_typing T (contexts!j) (typings!j) (lpp_context_module_types (actions!j))"
    using checked bound by (auto simp: lpp_check_context_module_def list_all_iff)
  have integers: "lpp_integer_known (lpp_context_module_types (actions!j)) nu"
    by (rule lpp_context_typing_sound[OF transfer typing facts])
  have canonical: "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin)
    (lpc_return_eval nu (states!j)) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule lpp_context_module_action_sound[OF check knowledge facts integers]) (use lower t in blast)
  have old: "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin
    (lpc_return_eval nu (states!j)) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using canonical by (simp add: lpp_return_as_answer_contract)
  have restored: "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_return_contract_scopes[OF program old])
  show "lp_answer_contract (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) ss (lp_ild Q) t out"
    using restored represented by (simp add: lpp_return_as_answer_contract shape[symmetric] lpc_return_scope_word_inverse)
qed

end
