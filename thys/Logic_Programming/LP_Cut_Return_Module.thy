theory LP_Cut_Return_Module
  imports LP_Cut_Return_Check LP_Cut_Return_Barriers LP_Cut_Return_Scope_Contracts
begin

datatype 'f lpc_return_module_action =
    LPCRPrimitive "'f lpc_return_action"
  | LPCRTrim "'f lpc_return_state" "'f lpc_return_state" "'f lpc_link"

definition lpc_return_module_rep where
  "lpc_return_module_rep nds states ss t =
    (\<exists>swaps. lpc_return_rep nds states (lpc_return_scope_word swaps ss) t)"

fun lpc_check_return_module_action where
  "lpc_check_return_module_action fuel P Q nds states nd ss returned arity (LPCRPrimitive action) =
    lpc_check_return_action fuel P Q nds states nd ss returned arity action"
| "lpc_check_return_module_action fuel P Q nds states nd ss returned arity (LPCRTrim successor barriers e) =
    (ss=successor@barriers \<and> lp_cut_barriers (map fst barriers) \<and>
      lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e)"

theorem lpc_return_module_action_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_module_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpc_return_module_rep nds states vs v \<Longrightarrow>
      lpc_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "lpc_return_contract P (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPCRPrimitive primitive)
  have check: "lpc_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPCRPrimitive by simp
  show ?thesis
  proof (rule lpc_return_primitive_lower[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v"])
    fix vs v and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v"
    show "lpc_return_contract P vs (lp_ild Q) v out" using lower[OF strict] represented by auto
  next
    fix event tt assume step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
        ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
          lpc_return_module_rep nds states tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpc_return_action_sound[OF check known step] by (auto simp: lpc_return_module_rep_def)
  qed
next
  case (LPCRTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked LPCRTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpc_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpc_return_table_link_sound[OF link equations refl known] by blast
  have child: "lpc_return_contract P (lpc_return_eval eta successor) (lp_ild Q) v
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: lpc_return_module_rep_def\<close>)
  have at_parent: "lpc_return_contract P (lpc_return_eval eta successor) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpc_return_contract_start[OF trancl_into_rtrancl[OF strict] child])
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using lpc_return_contract_append_barriers[OF at_parent suffix]
    by (simp add: shape lpc_return_eval_def)
qed

definition lpc_check_return_module where
  "lpc_check_return_module fuel P Q nds states returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpc_check_return_module_action fuel P Q nds states (nds!i) (states!i) returned arity (actions!i)) [0..<length nds])"

theorem lpc_check_return_module_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_module fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpc_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (rule lpc_return_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    lpc_return_module_rep nds states (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding lpc_return_module_rep_def lpc_return_rep_def
    using root known checked by (auto simp: lpc_check_return_module_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> lpc_return_module_rep nds states vs v \<Longrightarrow>
      lpc_return_contract P vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpc_return_module_rep_def lpc_return_rep_def)
  have check: "lpc_check_return_module_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
    using checked bound by (auto simp: lpc_check_return_module_def list_all_iff)
  have canonical: "lpc_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule lpc_return_module_action_sound[OF check knowledge]) (use lower t in blast)
  have restored: "lpc_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpc_return_contract_scopes[OF program canonical])
  show "lpc_return_contract P ss (lp_ild Q) t out"
    using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
qed

end
