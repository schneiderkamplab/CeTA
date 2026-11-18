theory LP_Prolog_Observer_Ordinary_Check
 imports LP_Prolog_Observer_Case_Node
begin

definition lpp_check_observer_target where
 "lpp_check_observer_target separation_contexts i e =
  (i<length separation_contexts \<and> lpcl_target e<length separation_contexts \<and>
   lpp_check_separation_transport (separation_contexts!i) (separation_contexts!lpcl_target e)
    (lp_cut_instance_subst (lpcl_bindings e)))"

fun lpp_check_observer_ordinary where
 "lpp_check_observer_ordinary separation_contexts i ss (LPPFCut control fs ns) =
  (case control of
    LPCRTerminal \<Rightarrow> ss=[]
  | LPCRInconsistent \<Rightarrow> True
  | LPCRAdmin event successor e \<Rightarrow> lpp_simple_control_frame ss \<and> lpc_prefix_active ss \<and> lpp_check_observer_target separation_contexts i e
  | LPCRCase m f ts gs payload saved e \<Rightarrow> lpp_simple_control_frame ss \<and> lpp_check_observer_target separation_contexts i e
  | _ \<Rightarrow> False)"
| "lpp_check_observer_ordinary separation_contexts i ss (LPPFTrim successor barriers e fs) =
   lpp_check_observer_target separation_contexts i e"
| "lpp_check_observer_ordinary separation_contexts i ss (LPPFParallel links factss) =
   (length links=length ss \<and> list_all (lpp_check_observer_target separation_contexts i) links)"
| "lpp_check_observer_ordinary separation_contexts i ss _ = False"

theorem lpp_observer_ordinary_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and scope_free: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_observer_ordinary separation_contexts i (states!i) action"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (lpp_observer_invariant A specs rest) rest observer_returned i"
proof (cases action)
 case (LPPFCut control fs ns)
 show ?thesis
 proof (cases control)
  case LPCRTerminal
  have "states!i=[]" using extra LPPFCut LPCRTerminal by simp
  then show ?thesis by (rule lpp_observer_empty_node_contract)
 next
  case LPCRInconsistent
  have inconsistent: "lp_cut_check_inconsistent (lpcn_guards (nds!i))"
   using checked LPPFCut LPCRInconsistent by (simp add: lpp_check_functor_source_action_def)
  show ?thesis unfolding lpp_observer_node_contract_def
   using lp_cut_checked_inconsistent[OF inconsistent] by blast
 next
  case (LPCRAdmin event successor e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and check: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity event successor e"
   using checked LPPFCut LPCRAdmin by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and transport: "lpp_check_separation_transport (separation_contexts!i) (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
   using extra LPPFCut LPCRAdmin by (auto simp: lpp_check_observer_target_def)
  have active: "lpc_prefix_active (states!i)" using extra LPPFCut LPCRAdmin by simp
  show ?thesis by (rule lpp_checked_observer_admin_node[OF program scope_free compatible transfer check bound transport simple clear active])
 next
  case (LPCRCase m f ts gs active saved e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
   and check: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (contexts!i) (functor_contexts!i) m f ts gs active saved e"
   using checked LPPFCut LPCRCase by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and transport: "lpp_check_separation_transport (separation_contexts!i) (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
   using extra LPPFCut LPCRCase by (auto simp: lpp_check_observer_target_def)
  show ?thesis by (rule lpp_checked_observer_case_node[OF program scope_free compatible transfer check bound transport simple clear shape])
 next
  case LPCRMeta then show ?thesis using extra LPPFCut by simp
 next
  case LPCREquality then show ?thesis using extra LPPFCut by simp
 next
  case LPCRResolution then show ?thesis using extra LPPFCut by simp
 qed
next
 case (LPPFTrim successor barriers e fs)
 show ?thesis
  apply (rule lpp_checked_observer_trim_node[OF program scope_free compatible transfer checked[unfolded LPPFTrim]])
  using extra LPPFTrim by (auto simp: lpp_check_observer_target_def)
next
 case (LPPFParallel links factss)
 show ?thesis
  apply (rule lpp_checked_observer_parallel_node[OF program scope_free compatible transfer checked[unfolded LPPFParallel]])
  using extra LPPFParallel by (auto simp: lpp_check_observer_target_def list_all_iff)
next
 case LPPFTest then show ?thesis using extra by simp
next
 case LPPFIs then show ?thesis using extra by simp
next
 case LPPFUniv then show ?thesis using extra by simp
qed

ML \<open>
val checked = @{thms lpp_observer_ordinary_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer ordinary checker" else ();
\<close>
end
