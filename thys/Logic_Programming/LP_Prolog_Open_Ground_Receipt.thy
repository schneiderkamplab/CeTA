theory LP_Prolog_Open_Ground_Receipt
 imports LP_Prolog_Open_Stable_Return LP_Prolog_Stable_Relational_Split
begin

fun lpp_open_user_head where
  "lpp_open_user_head (Fun (LPCUser f) ts) = True"
| "lpp_open_user_head _ = False"

lemma lpp_open_user_head_iff:
  "lpp_open_user_head h = (\<exists>f ts. h=Fun (LPCUser f) ts)"
proof (cases h)
  case (Var x)
  then show ?thesis by simp
next
  case (Fun f ts)
  then show ?thesis by (cases f) auto
qed

definition lpp_open_ground_receipt_check where
  "lpp_open_ground_receipt_check P incoming_context pre G H vs evidence =
    (list_all (\<lambda>cl. list_all lpc_model_safe_goal (snd cl) \<and> lpp_open_user_head (fst cl)) P \<and>
     (let model=lppsgr_model evidence; K=lppsgr_ground evidence in
     set K \<subseteq> set vs \<and> set H \<subseteq> set G \<union> set K \<and>
     lpp_inline_return_program_check P (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_open_builtin_check (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_check_transfer_contract (lppsir_summaries model) (lppsir_program model) (lppsir_proofs model) \<and>
     lpp_guarded_ground_check (lppsir_program model) (lppsgr_modes evidence) \<and>
     lpp_finite_ground_prefix_check (set (lppsir_predicates model)) (lppsgr_modes evidence)
       (set G \<union> lpp_source_context_ground incoming_context) K pre))"

lemma lpp_open_relational_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_open_ground_receipt_check P incoming_context pre G H vs evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and prefix: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
proof -
  let ?model = "lppsgr_model evidence"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes evidence"
  let ?K = "lppsgr_ground evidence"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  have selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using checked prefix by (auto simp: lpp_open_ground_receipt_check_def Let_def
      elim!: lpp_finite_ground_prefix_check.elims)
  have program: "lpp_inline_return_program_check P ?F ?SP"
    and builtin: "lpp_open_builtin_check ?F ?SP"
    and modes: "lpp_guarded_ground_check ?SP ?modes"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_open_ground_receipt_check_def Let_def)
  obtain theta where source: "lpp_stable_actual_return operation P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stable_seg_observed_actual[OF actual] by blast
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground lpp_stable_context_finite_envelope[OF compatible observed]] by (auto simp: lp_cut_knowledge_def)
  have safe: "list_all lpc_model_safe_goal (snd (P!c))" if "c<length P" for c
    using checked that by (auto simp: lpp_open_ground_receipt_check_def list_all_iff lpp_open_user_head_iff)
  have heads: "\<exists>g us. fst (P!c)=Fun (LPCUser g) us" if "c<length P" for c
    using checked that by (auto simp: lpp_open_ground_receipt_check_def list_all_iff lpp_open_user_head_iff)
  have source_call: "lpp_stable_actual_return operation P
    [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] theta"
    using source by (simp add: prefix)
  have success: "lpp_guarded_success ?SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) theta)"
    by (rule lpp_open_stable_relational_return[where eta=eta, OF program safe heads builtin selected ordinary source_call])
  have gr_after: "\<forall>x\<in>?G. lp_seg_ground (theta x)"
    using lpp_stable_seg_captured_term[OF source, of "Var _"] gr by fastforce
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_open_stable_ground_flow[OF compatible modes success gr_after])
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_stable_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  have relation: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) theta)"
    using success model_identity by simp
  have enriched: "lpp_stable_context_holds operation SP
      (lpp_context_add_success (lpp_context_add_ground incoming_context ?K) (f,ts)) theta"
    by (rule lpp_stable_add_success[OF next_context relation])
  show ?thesis using rho ground enriched by blast
qed


ML \<open>
val checked = [@{thm lpp_open_relational_ground_receipt_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open ground receipt" else ();
\<close>
end
