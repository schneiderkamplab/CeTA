theory LP_Cut_Domain_SEG_Control
 imports LP_Cut_Domain_SEG_Regions
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_control_action:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_module_action fuel P Q nds states nd ss returned arity action"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      precise_return_module_rep nds states vs v \<Longrightarrow> precise_return_contract P vs R t ret"
    and emit: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_return_eval eta ss) R t ret"
proof (cases action)
  case (LPCRPrimitive primitive)
  have check: "lpc_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPCRPrimitive by simp
  show ?thesis
  proof (rule precise_seg_primitive_contract)
    fix event tt assume step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
    obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
      and rep: "precise_return_rep nds states (lpc_return_scope_word swaps tt) u"
      using precise_return_action_sound[OF check known step] by blast
    show "precise_return_contract P tt R t ret"
      by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
  next
    fix rho tt assume step: "precise_answer_transition P (lpc_return_eval eta ss) (Some rho) tt"
    have edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
      using precise_return_action_sound[OF check known step] by blast
    show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF edge])
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
  have child: "precise_return_contract P (lpc_return_eval eta successor) R t ret"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using precise_return_contract_append_barriers[OF child suffix]
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
    show "precise_return_contract P [e] R t ret"
      unfolding e by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
  qed
next
  case (LPCRRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPCRRefuted by simp
  then show ?thesis using checked_refuted_guard[OF _ known] by blast
qed


theorem precise_seg_control_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_check_control fuel P Q nds states returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "precise_return_module_rep nds states ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      (a,[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      precise_return_contract P (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>rho. (a,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t ret"
proof -
  have sn: "SN (lp_ild Q)" by (rule lpc_seg_ranked_control_SN[OF ranked])
  have all: "\<forall>us. (a,b)\<in>(lp_ild Q)\<^sup>* \<longrightarrow>
      precise_return_module_rep nds states us b \<longrightarrow> precise_return_contract P us R t ret" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] UNIV_I], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>vs. (a,c)\<in>(lp_ild Q)\<^sup>* \<longrightarrow> precise_return_module_rep nds states vs c \<longrightarrow> precise_return_contract P vs R t ret"
      and reached: "(a,b)\<in>(lp_ild Q)\<^sup>*"
      and rep: "precise_return_module_rep nds states us b"
    obtain swaps i eta where index: "i<length nds"
      and shape: "lpc_return_scope_word swaps us=lpc_return_eval eta (states!i)"
      and known: "knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
      and b: "b=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
      using rep by (auto simp: precise_return_module_rep_def precise_return_rep_def)
    have canonical: "precise_return_contract P (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known]) (use reached b in simp)
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpc_check_return_module_action fuel P Q nds states (nds!i) (states!i) returned arity action"
        using checked member unfolding lpc_seg_check_control_def list_all_iff by blast
      have check: "lpc_check_return_module_action fuel P Q nds states (nds!i) (states!i) returned arity action"
        using local Some by simp
      show ?thesis
      proof (rule precise_seg_control_action[OF check known])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "precise_return_module_rep nds states vs c"
        have bc: "(b,c)\<in>(lp_ild Q)\<^sup>+" using edge b by simp
        have ac: "(a,c)\<in>(lp_ild Q)\<^sup>*" by (rule rtrancl_trans[OF reached trancl_into_rtrancl[OF bc]])
        show "precise_return_contract P vs R t ret" using ih[OF bc] ac child by blast
      next
        fix rho assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
        have tail: "(b,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*" using edge b by simp
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF rtrancl_trans[OF reached tail]])
      qed
    qed
    have restored: "precise_return_contract P (lpc_return_scope_word (rev swaps) (lpc_return_eval eta (states!i))) R t ret"
      by (rule precise_return_contract_scopes[OF program canonical])
    show "precise_return_contract P us R t ret" using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  qed
  show ?thesis using all[of a] represented by auto
qed


end
end
