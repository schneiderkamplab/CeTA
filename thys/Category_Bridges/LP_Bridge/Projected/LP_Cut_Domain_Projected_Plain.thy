theory LP_Cut_Domain_Projected_Plain
 imports LP_Cut_Domain_Projected_Module
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_projected_table_link_sound:
  assumes clauses: "lpc_check_projected_clauses filtering R Q"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and link: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "knowledge (set G) guards eta'"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  obtain u swaps where edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
    and rep: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
    using precise_return_table_link_sound[OF link equations old known] by blast
  have lifted: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
    by (rule lpc_projected_clause_strict_path[OF clauses edge initial])
  show ?thesis using lifted rep by blast
qed


lemma precise_projected_action_sound:
  assumes clauses: "lpc_check_projected_clauses filtering R Q"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and checked: "lpc_check_return_action fuel P Q nds states nd ss returned arity action"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
      precise_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lpc_projected_rel filtering (set R))\<^sup>*)"
proof -
  have source: "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      precise_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
    by (rule precise_return_action_sound[OF checked known step])
  show ?thesis
    using source lpc_projected_clause_strict_path[OF clauses _ initial]
      lpc_projected_clause_path[OF clauses _ initial] by blast
qed


theorem precise_projected_module_action_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes clauses: "lpc_check_projected_clauses filtering R Q"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and checked: "lpc_check_return_module_action fuel P Q nds states nd ss returned arity action"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<Longrightarrow>
      precise_return_module_rep nds states vs v \<Longrightarrow>
      precise_return_contract P vs (lpc_projected_rel filtering (set R)) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "precise_return_contract P (lpc_return_eval eta ss) (lpc_projected_rel filtering (set R))
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPCRPrimitive primitive)
  have check: "lpc_check_return_action fuel P Q nds states nd ss returned arity primitive"
    using checked LPCRPrimitive by simp
  show ?thesis
  proof (rule precise_return_primitive_lower[where rep="\<lambda>vs v out.
      out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"])
    fix vs v and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
    assume strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
      and represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> precise_return_module_rep nds states vs v"
    show "precise_return_contract P vs (lpc_projected_rel filtering (set R)) v out" using lower[OF strict] represented by auto
  next
    fix event tt assume step: "precise_answer_transition P (lpc_return_eval eta ss) event tt"
    show "(\<exists>u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<and>
        ((\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
          precise_return_module_rep nds states tt u)) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow>
        ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lpc_projected_rel filtering (set R))\<^sup>*)"
      using precise_projected_action_sound[OF clauses initial check known step] by (auto simp: precise_return_module_rep_def)
  qed
next
  case (LPCRTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpc_check_return_table_link fuel Q nds states nd successor (lpcn_ground nd) (lpcn_guards nd) [] e"
    using checked LPCRTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
    and rep: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using precise_projected_table_link_sound[OF clauses initial link equations refl known] by blast
  have child: "precise_return_contract P (lpc_return_eval eta successor) (lpc_projected_rel filtering (set R)) v
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
  have at_parent: "precise_return_contract P (lpc_return_eval eta successor) (lpc_projected_rel filtering (set R))
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
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+"
      and rep: "precise_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using precise_projected_table_link_sound[OF clauses initial link equations refl known] by blast
    have child: "precise_return_contract P (lpc_return_eval eta [ss!i]) (lpc_projected_rel filtering (set R)) v
      (\<lambda>rho. [(returned,map rho [0..<arity])])"
      by (rule lower[OF strict]) (use rep in \<open>auto simp: precise_return_module_rep_def\<close>)
    show "precise_return_contract P [e] (lpc_projected_rel filtering (set R)) [(lpcn_pred nd,map eta (lpcn_vars nd))]
      (\<lambda>rho. [(returned,map rho [0..<arity])])"
      unfolding e by (rule precise_return_contract_start[OF trancl_into_rtrancl[OF strict] child])
  qed
next
  case (LPCRRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPCRRefuted by simp
  then show ?thesis using checked_refuted_guard[OF _ known] by blast
qed


end
end
