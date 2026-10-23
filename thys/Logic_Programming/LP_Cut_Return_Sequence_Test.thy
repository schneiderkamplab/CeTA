theory LP_Cut_Return_Sequence_Test
  imports LP_Cut_Return_Sequence
begin

lemma empty_interface_accepts_unused_binding:
  "lpc_mgu_unify (LPIFun f []) (LPIFun f []) [] (\<lambda>_. LPIFun f [])"
  by (simp add: lpc_mgu_unify_def)

lemma live_continuation_rejects_same_binding:
  fixes f :: 'f
  shows "\<not> lpc_mgu_unify (LPIFun f []) (LPIFun f []) [LPCAtom (LPIVar ''X'')]
    (\<lambda>_. LPIFun f [])"
proof
  assume mgu: "lpc_mgu_unify (LPIFun f []) (LPIFun f []) [LPCAtom (LPIVar ''X'')]
    (\<lambda>_. LPIFun f [])"
  have all: "\<forall>\<tau> :: string \<Rightarrow> ('f,string) lp_iterm.
    \<exists>\<delta>. lp_isubst (LPIFun f []) \<delta> = \<tau> ''X''"
    using mgu by (simp add: lpc_mgu_unify_def)
  have "\<exists>\<delta>. lp_isubst (LPIFun f []) \<delta> = LPIVar ''X''"
    by (rule spec[OF all, of LPIVar])
  then show False by simp
qed

lemma first_success_keeps_saved_prefix:
  "(LPCPrefix [(LPCGoals [],\<eta>),(LPCGoals [],\<nu>)],
    LPCContinue (start \<eta>) [(LPCGoals [],\<nu>)])\<in>lpc_return_sequence P C start finished"
  by (rule lpc_return_sequence.returned, rule lpc_answer_transition.success)

lemma completed_continuation_resumes_saved_prefix:
  "finished c \<Longrightarrow>
    (LPCContinue c [(LPCGoals [],\<nu>)],LPCPrefix [(LPCGoals [],\<nu>)])
      \<in>lpc_return_sequence P C start finished"
  by (rule lpc_return_sequence.resume)

lemma second_success_uses_saved_environment:
  "(LPCPrefix [(LPCGoals [],\<nu>)],LPCContinue (start \<nu>) [])
      \<in>lpc_return_sequence P C start finished"
  by (rule lpc_return_sequence.returned, rule lpc_answer_transition.success)

lemma failed_prefix_does_not_start_continuation:
  "\<not> (LPCPrefix ((LPCGoals [LPCFail],\<eta>)#es),LPCContinue c tt)
      \<in>lpc_return_sequence P C start finished"
  by (auto elim: lpc_return_sequence.cases dest: lpc_answer_event_is_success)

lemma unfinished_child_loop_is_not_hidden:
  assumes loop: "(c,c)\<in>C"
  shows "\<not> SN_on (lpc_return_sequence P C start finished) {LPCContinue c ss}"
proof
  assume sn: "SN_on (lpc_return_sequence P C start finished) {LPCContinue c ss}"
  have self: "(LPCContinue c ss,LPCContinue c ss)\<in>lpc_return_sequence P C start finished"
    by (rule lpc_return_sequence.child[OF loop])
  show False using SN_on_irrefl[OF sn] self by blast
qed

lemma scoped_cut_retains_caller_alternatives:
  "(LPCPrefix ((LPCGoals [LPCCut m],\<eta>)#(LPCGoals [],\<rho>)#(LPCBarrier m,\<nu>)#caller),
    LPCPrefix ((LPCGoals [],\<eta>)#(LPCBarrier m,\<nu>)#caller))
      \<in>lpc_return_sequence P C start finished"
  by (rule lpc_return_sequence.prefix)
    (use lpc_answer_transition.cut[of P m "[]" \<eta>
      "(LPCGoals [],\<rho>)#(LPCBarrier m,\<nu>)#caller"] in simp)

end
