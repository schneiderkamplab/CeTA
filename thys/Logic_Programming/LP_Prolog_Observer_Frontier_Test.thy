theory LP_Prolog_Observer_Frontier_Test
 imports LP_Prolog_Observer_Checked_Frontier_Block
begin

lemma lpp_frontier_general_continuation_accepted:
 "f\<noteq>''2:=..'' \<Longrightarrow> lpp_check_observer_univ_exit [y]
  [(LPCGoals [LPCAtom (Fun (LPCUser ''2:=..'') [Var x,Var y]), LPCAtom (Fun (LPCUser f) call_args)],payload)]"
 by simp

lemma lpp_frontier_missing_domain_rejected:
 "\<not>lpp_check_observer_univ_exit []
  [(LPCGoals [LPCAtom (Fun (LPCUser ''2:=..'') [Var x,Var y]), LPCAtom (Fun (LPCUser f) call_args)],payload)]"
 by simp

lemma lpp_frontier_pending_univ_rejected:
 "\<not>lpp_check_observer_univ_exit [y]
  [(LPCGoals [LPCAtom (Fun (LPCUser ''2:=..'') [Var x,Var y]), LPCAtom (Fun (LPCUser ''2:=..'') call_args)],payload)]"
 by simp

lemma lpp_frontier_saved_equality_rejected:
 "\<not>lpp_check_observer_univ_exit [y]
  [(LPCGoals [LPCAtom (Fun (LPCUser ''2:=..'') [Var x,Var y]), LPCAtom (Fun (LPCUser f) call_args)],payload),
   (LPCGoals [LPCUnify a b],saved_payload)]"
 by simp

lemma lpp_frontier_internal_rows_retained:
 "lpp_observer_frontier_conditions frontier_nodes base_conditions i eta \<Longrightarrow> base_conditions i eta"
 by (simp add: lpp_observer_frontier_conditions_def)

ML \<open>
val checked = @{thms lpp_frontier_general_continuation_accepted lpp_frontier_missing_domain_rejected
 lpp_frontier_pending_univ_rejected lpp_frontier_saved_equality_rejected lpp_frontier_internal_rows_retained};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted frontier controls" else ();
\<close>
end
