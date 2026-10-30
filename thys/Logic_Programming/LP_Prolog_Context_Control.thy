theory LP_Prolog_Context_Control
 imports LP_Prolog_Context_Module_Domain LP_Cut_SEG_Control
begin

theorem lpp_context_control_action:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_module_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_module_types action) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_context_module_rep SP nds states contexts vs v \<Longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret"
    and emit: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta ss) R t ret"
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
  have typed: "lpp_integer_known (lpp_context_source_types primitive) eta"
    using integers LPPCMPrimitive by simp
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt
    assume step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta ss) event tt"
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
      by (rule lpp_context_source_action_domain[OF check typed])
    have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
      using step supported by (simp add: lpp_domain_answers_def)
    have simulation: "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
        lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      by (rule lpp_context_source_action_sound[OF check known observed typed actual])
    have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using simulation lower by (auto simp: lpp_context_module_rep_def)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using child simulation emit by blast
  qed
next
  case (LPPCMFiniteComparison evidence)
  have check: "lpp_check_finite_comparison_receipt fuel Q nds states contexts nd ss source_context evidence"
    using checked LPPCMFiniteComparison by simp
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt
    assume step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta ss) event tt"
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
      by (rule lpp_finite_receipt_domain[OF check known observed])
    have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
      using step supported by (simp add: lpp_domain_answers_def)
    have simulation: "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
        lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_finite_receipt_sound[OF check known observed actual] by auto
    have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using simulation lower by (auto simp: lpp_context_module_rep_def)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using child simulation emit by blast
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
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta successor) R t ret"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: lpp_context_module_rep_def\<close>)
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using lpp_domain_contract_append_barriers[OF child suffix]
    by (simp add: shape lpc_return_eval_def)
next
  case (LPPCMParallel links)
  show ?thesis
  proof (rule lpp_domain_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpp_check_context_table_link fuel Q nds states contexts nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] source_context (links!i)"
      using checked LPPCMParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpp_context_table_link_sound[OF link equations refl known observed] by blast
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) [e] R t ret"
      unfolding e by (rule lower[OF strict]) (use rep in \<open>auto simp: lpp_context_module_rep_def\<close>)
  qed
next
  case (LPPCMRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPCMRefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed

definition lpp_check_context_control where
  "lpp_check_context_control fuel P Q nds states contexts T typings returned arity actions =
    (length nds=length states \<and> length nds=length contexts \<and> length nds=length typings \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
         lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action) \<and>
         lpp_check_context_module_action fuel P Q nds states contexts (nds!i) (states!i) (contexts!i) returned arity action)) [0..<length nds])"

theorem lpp_context_control_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_control fuel P Q nds states contexts T typings returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and represented: "lpp_context_module_rep SP nds states contexts ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_source_context_holds SP (contexts!i) eta \<Longrightarrow>
      (a,[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>rho. (a,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss R t ret"
proof -
  have sn: "SN (lp_ild Q)" by (rule lpc_seg_ranked_control_SN[OF ranked])
  have all: "\<forall>us. (a,b)\<in>(lp_ild Q)\<^sup>* \<longrightarrow>
      lpp_context_module_rep SP nds states contexts us b \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) us R t ret" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] UNIV_I], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>vs. (a,c)\<in>(lp_ild Q)\<^sup>* \<longrightarrow> lpp_context_module_rep SP nds states contexts vs c \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret"
      and reached: "(a,b)\<in>(lp_ild Q)\<^sup>*"
      and rep: "lpp_context_module_rep SP nds states contexts us b"
    obtain swaps i eta where index: "i<length nds"
      and shape: "lpc_return_scope_word swaps us=lpc_return_eval eta (states!i)"
      and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
      and observed: "lpp_source_context_holds SP (contexts!i) eta"
      and b: "b=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
      using rep by (auto simp: lpp_context_module_rep_def lpp_context_return_rep_def)
    have canonical: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known observed]) (use reached b in simp)
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action) \<and>
          lpp_check_context_module_action fuel P Q nds states contexts (nds!i) (states!i) (contexts!i) returned arity action"
        using checked member unfolding lpp_check_context_control_def list_all_iff by blast
      have check: "lpp_check_context_module_action fuel P Q nds states contexts (nds!i) (states!i) (contexts!i) returned arity action"
        using local Some by auto
      have typing: "lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action)"
        using local Some by auto
      have typed: "lpp_integer_known (lpp_context_module_types action) eta"
        by (rule lpp_context_typing_sound[OF transfer typing observed])
      show ?thesis
      proof (rule lpp_context_control_action[OF check known observed typed])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "lpp_context_module_rep SP nds states contexts vs c"
        have bc: "(b,c)\<in>(lp_ild Q)\<^sup>+" using edge b by simp
        have ac: "(a,c)\<in>(lp_ild Q)\<^sup>*" by (rule rtrancl_trans[OF reached trancl_into_rtrancl[OF bc]])
        show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret" using ih[OF bc] ac child by blast
      next
        fix rho assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
        have tail: "(b,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*" using edge b by simp
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF rtrancl_trans[OF reached tail]])
      qed
    qed
    have restored: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_scope_word (rev swaps) (lpc_return_eval eta (states!i))) R t ret"
      by (rule lpp_domain_contract_scopes[OF program canonical])
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) us R t ret" using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  qed
  show ?thesis using all[of a] represented by auto
qed


ML \<open>
val checked = [@{thm lpp_context_control_action}, @{thm lpp_context_control_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source control dependency" else ();
\<close>
end
