theory LP_Prolog_Observer_Univ_Path
 imports LP_Prolog_Observer_Fresh_Univ_Product
begin

lemma lpp_observer_univ_actual_normalized_path:
 assumes domain: "lpp_univ_view_domain input_value requested"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested])#gs),env)#saved) event result"
 shows "event=None \<and> (result=[] \<or> (\<exists>f ts.
   input_value=LPIFun f ts \<and>
   lpc_answer_transition P
    ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
      LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) None
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) \<and>
   lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) None result))"
proof -
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [input_value,requested])#gs),env)#saved) event result"
  using step domain by (auto simp: lpp_domain_answers_def lpp_univ_source_domain_def)
 have selected: "(''2:=..'',2)\<in>lpp_builtin_signature"
  by (simp add: lpp_builtin_signature_def)
 show ?thesis
 proof (cases input_value)
  case (LPIVar x)
  have stopped: "event=None \<and> result=[]"
   apply (rule lpp_univ_variable_input_stops[OF selected _ actual[unfolded LPIVar]])
   using lpp_univ_source_outcome_covered by blast
  show ?thesis using stopped by simp
 next
  case (LPIFun f ts)
  have coverage: "lpp_univ_decompose_outcome names (LPIFun f ts) requested out"
   if "lpp_univ_source_builtin names operation ''2:=..'' [LPIFun f ts,requested] out" for out
   using lpp_univ_source_outcome_covered[OF that] by simp
  have equality: "event=None \<and> (result=[] \<or>
   lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) event result)"
   by (rule lpp_univ_uses_shared_equality[OF selected coverage actual[unfolded LPIFun]])
  have identity: "lpc_mgu_unify (LPIFun f ts) (LPIFun f ts)
   (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs) LPIVar"
   by (auto simp: lpc_mgu_unify_def)
  have first: "lpc_answer_transition P
    ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
      LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved) None
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#gs),env)#saved)"
   using lpc_answer_transition.unify[OF identity, of P env saved] by simp
  show ?thesis using equality first LPIFun by blast
 qed
qed

ML \<open>
val checked = @{thms lpp_observer_univ_actual_normalized_path};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual univ normalization path" else ();
\<close>
end
