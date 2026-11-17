theory LP_Prolog_Separation_Ordinary_Check
 imports LP_Prolog_Separation_Finite_Control LP_Prolog_Separation_Simple_Contracts
begin

text \<open>Additional executable obligations for ordinary actions in a table
with local separation conditions. The existing action checker still checks the
source operation, every represented edge, contexts and return observations.
Resolution, equality, univ and module boundaries retain their separate rules.\<close>

definition lpp_empty_separation_target where
 "lpp_empty_separation_target separation_contexts e =
   (lpcl_target e<length separation_contexts \<and> separation_contexts!lpcl_target e=[])"

fun lpp_check_separation_ordinary where
 "lpp_check_separation_ordinary separation_contexts ss (LPPFCut control fs ns) =
  (case control of
    LPCRTerminal \<Rightarrow> ss=[]
  | LPCRInconsistent \<Rightarrow> True
  | LPCRAdmin event successor e \<Rightarrow> lpp_simple_control_frame ss \<and> lpp_empty_separation_target separation_contexts e
  | LPCRCase m f ts gs active saved e \<Rightarrow> lpp_simple_control_frame ss \<and> lpp_empty_separation_target separation_contexts e
  | _ \<Rightarrow> False)"
| "lpp_check_separation_ordinary separation_contexts ss (LPPFTest yes no fs ns) =
  (case ss of (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<Rightarrow>
   length ts=1 \<and> lpp_empty_separation_target separation_contexts yes \<and> lpp_empty_separation_target separation_contexts no
  | _ \<Rightarrow> False)"
| "lpp_check_separation_ordinary separation_contexts ss (LPPFIs result_var middle fs) =
  (case ss of (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<Rightarrow>
   length ts=2 \<and> f=''2:is'' \<and> lpp_empty_separation_target separation_contexts middle
  | _ \<Rightarrow> False)"
| "lpp_check_separation_ordinary separation_contexts ss (LPPFTrim successor barriers e fs) =
   lpp_empty_separation_target separation_contexts e"
| "lpp_check_separation_ordinary separation_contexts ss (LPPFParallel links factss) =
   (length links=length ss \<and> list_all (lpp_empty_separation_target separation_contexts) links)"
| "lpp_check_separation_ordinary separation_contexts ss (LPPFUniv v n a e fs) = False"

lemma lpp_separation_ordinary_test_shape:
 assumes "lpp_check_separation_ordinary separation_contexts ss (LPPFTest yes no fs ns)"
 obtains f a gs active saved where
  "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
  "lpp_empty_separation_target separation_contexts yes"
  "lpp_empty_separation_target separation_contexts no"
 using assms by (auto simp: length_Suc_conv numeral_2_eq_2 split!: list.splits prod.splits lp_cut_entry.splits lp_cut_goal.splits term.splits lp_cut_symbol.splits)

lemma lpp_separation_ordinary_is_shape:
 assumes "lpp_check_separation_ordinary separation_contexts ss (LPPFIs r middle fs)"
 obtains a e gs active saved where
  "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
  "lpp_empty_separation_target separation_contexts middle"
 using assms by (auto simp: length_Suc_conv numeral_2_eq_2 split!: list.splits prod.splits lp_cut_entry.splits lp_cut_goal.splits term.splits lp_cut_symbol.splits)

theorem lpp_separation_ordinary_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 and extra: "lpp_check_separation_ordinary separation_contexts (states!i) action"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (cases action)
 case (LPPFCut control fs ns)
 show ?thesis
 proof (cases control)
  case LPCRTerminal
  have "states!i=[]" using extra LPPFCut LPCRTerminal by simp
  then show ?thesis by (rule lpp_exhausted_premised_functor_node_contract)
 next
  case LPCRInconsistent
  have inconsistent: "lp_cut_check_inconsistent (lpcn_guards (nds!i))"
   using checked LPPFCut LPCRInconsistent by (simp add: lpp_check_functor_source_action_def)
  show ?thesis unfolding lpp_premised_functor_node_contract_def
   using lp_cut_checked_inconsistent[OF inconsistent] by blast
 next
  case (LPCRAdmin event successor e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and check: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity event successor e"
   using checked LPPFCut LPCRAdmin by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and empty: "separation_contexts!lpcl_target e=[]"
   using extra LPPFCut LPCRAdmin by (auto simp: lpp_empty_separation_target_def)
  show ?thesis by (rule lpp_finite_separation_admin_node_contract[OF compatible transfer check simple clear bound empty])
 next
  case (LPCRCase m f ts gs active saved e)
  have clear: "lpp_no_builtin_frame (states!i)"
   and shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
   and check: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (contexts!i) (functor_contexts!i) m f ts gs active saved e"
   using checked LPPFCut LPCRCase by (auto simp: lpp_check_functor_source_action_def)
  have simple: "lpp_simple_control_frame (states!i)"
   and bound: "lpcl_target e<length separation_contexts"
   and empty: "separation_contexts!lpcl_target e=[]"
   using extra LPPFCut LPCRCase by (auto simp: lpp_empty_separation_target_def)
  show ?thesis by (rule lpp_finite_separation_case_node_contract[OF compatible transfer check shape simple clear bound empty])
 next
  case LPCRMeta then show ?thesis using extra LPPFCut by simp
 next
  case LPCREquality then show ?thesis using extra LPPFCut by simp
 next
  case LPCRResolution then show ?thesis using extra LPPFCut by simp
 qed
next
 case (LPPFTest yes no fs ns)
 obtain f a gs active saved where
   shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
   and yes: "lpp_empty_separation_target separation_contexts yes"
   and no: "lpp_empty_separation_target separation_contexts no"
  using lpp_separation_ordinary_test_shape[OF extra[unfolded LPPFTest]] by blast
 show ?thesis
  apply (rule lpp_finite_separation_test_node_contract[OF compatible transfer checked[unfolded LPPFTest] shape])
  using yes no by (auto simp: lpp_empty_separation_target_def)
next
 case (LPPFIs r middle fs)
 obtain a e gs active saved where
   shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
   and target: "lpp_empty_separation_target separation_contexts middle"
  using lpp_separation_ordinary_is_shape[OF extra[unfolded LPPFIs]] by blast
 show ?thesis
  apply (rule lpp_finite_separation_is_node_contract[OF compatible transfer checked[unfolded LPPFIs] shape])
  using target by (auto simp: lpp_empty_separation_target_def)
next
 case LPPFUniv then show ?thesis using extra by simp
next
 case (LPPFTrim successor barriers e fs)
 show ?thesis
  apply (rule lpp_finite_separation_trim_node_contract[OF compatible transfer checked[unfolded LPPFTrim]])
  using extra LPPFTrim by (auto simp: lpp_empty_separation_target_def)
next
 case (LPPFParallel links factss)
 show ?thesis
  apply (rule lpp_finite_separation_parallel_node_contract[OF compatible transfer checked[unfolded LPPFParallel]])
  using extra LPPFParallel by (auto simp: lpp_empty_separation_target_def list_all_iff)
qed

ML \<open>
val checked = @{thms lpp_separation_ordinary_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ordinary separation checker" else ();
\<close>
end
