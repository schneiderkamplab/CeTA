theory LP_Cut_Domain_Return_Module
  imports LP_Cut_Domain_Return_Parallel LP_Cut_Domain_Return_Scope_Contracts
begin

context cut_runtime_domain
begin

definition precise_return_module_rep where
  "precise_return_module_rep nds states ss t =
    (\<exists>swaps. precise_return_rep nds states (lpc_return_scope_word swaps ss) t)"

theorem precise_return_module_action_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_module_action fuel P Q nds states nd ss returned arity action"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      precise_return_module_rep nds states vs v \<Longrightarrow>
      precise_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "precise_return_contract P (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPCRPrimitive primitive)
  have check: "lpc_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPCRPrimitive by simp
  show ?thesis
  proof (rule precise_return_primitive_lower[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"])
    fix vs v and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"
    show "precise_return_contract P vs (lp_ild Q) v out" using lower[OF strict] represented by auto
  next
    fix event tt assume step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
        ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
          precise_return_module_rep nds states tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using precise_return_action_sound[OF check known step] by (auto simp: precise_return_module_rep_def)
  qed
next
  case (LPCRTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked LPCRTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using precise_return_table_link_sound[OF link equations refl known] by blast
  have child: "precise_return_contract P (lpc_return_eval eta successor) (lp_ild Q) v
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
  have at_parent: "precise_return_contract P (lpc_return_eval eta successor) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF strict] child])
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using precise_return_contract_append_barriers[OF at_parent suffix]
    by (simp add: shape lpc_return_eval_def)
next
  case (LPCRParallel links)
  show ?thesis
  proof (rule precise_return_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpc_check_return_table_link fuel Q nds states nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] (links!i)"
      using checked LPCRParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using precise_return_table_link_sound[OF link equations refl known] by blast
    have child: "precise_return_contract P (lpc_return_eval eta [ss!i]) (lp_ild Q) v
      (\<lambda>rho. [(returned,map rho [0..<arity])])"
      by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
    show "precise_return_contract P [e] (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))]
      (\<lambda>rho. [(returned,map rho [0..<arity])])"
      unfolding e by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF strict] child])
  qed
next
  case (LPCRRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPCRRefuted by simp
  then show ?thesis using checked_refuted_guard[OF _ known] by blast
qed

theorem precise_check_return_module_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_module fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "precise_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (rule precise_return_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    precise_return_module_rep nds states (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding precise_return_module_rep_def precise_return_rep_def
    using root known checked by (auto simp: lpc_check_return_module_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v \<Longrightarrow>
      precise_return_contract P vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: precise_return_module_rep_def precise_return_rep_def)
  have check: "lpc_check_return_module_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
    using checked bound by (auto simp: lpc_check_return_module_def list_all_iff)
  have canonical: "precise_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule precise_return_module_action_sound[OF check knowledge]) (use lower t in blast)
  have restored: "precise_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule precise_return_contract_scopes[OF program canonical])
  show "precise_return_contract P ss (lp_ild Q) t out"
    using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
qed


end
end
