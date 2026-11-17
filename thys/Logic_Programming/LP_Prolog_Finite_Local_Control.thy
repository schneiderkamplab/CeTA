theory LP_Prolog_Finite_Local_Control
 imports LP_Prolog_Finite_Local_Invariant LP_Prolog_Finite_Direct_Control
begin

definition lpp_local_finite_ground where
 "lpp_local_finite_ground nd ctx =
   lpcn_ground nd @ filter (\<lambda>x. x\<in>lpp_source_context_ground ctx) (lpcn_vars nd)"

definition lpp_check_local_finite_states where
 "lpp_check_local_finite_states A P nds states contexts =
   (length nds=length states \<and> length nds=length contexts \<and>
    list_all (\<lambda>i.
      lpp_check_finite_resolution_state (lpp_local_finite_ground (nds!i) (contexts!i)) P (states!i) \<and>
      lpp_check_static_resolution_state A P (states!i)) [0..<length nds])"

lemma lpp_checked_local_finite_stable:
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_local_finite_states A P nds states contexts"
   and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
   and index: "i<length nds"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
   and state: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
   and step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation)
     lpp_finite_source_domain (lpc_return_eval eta (states!i)) event tt"
 shows "lpp_finite_direct_invariant A tt"
proof -
 have finite_check: "lpp_check_finite_resolution_state (lpp_local_finite_ground (nds!i) (contexts!i)) P (states!i)"
   and static_check: "lpp_check_static_resolution_state A P (states!i)"
   using checked index by (auto simp: lpp_check_local_finite_states_def list_all_iff)
 have ground: "lp_seg_ground (eta x)" if "x\<in>set (lpp_local_finite_ground (nds!i) (contexts!i))" for x
   using that known lpp_stable_context_ground_sound[OF observed]
   by (auto simp: lpp_local_finite_ground_def lp_cut_knowledge_def)
 have safe: "lpp_finite_direct_outcome result"
   if member: "(f,length ts)\<in>A" and result: "lpp_stable_source_builtin operation f ts result" for f ts result
 proof -
  have selected: "(f,length ts)\<in>lpp_builtin_signature"
    by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite[OF result]])
  show ?thesis by (rule lpp_direct_arithmetic_outcome[OF signature[OF member selected] result])
 qed
 show ?thesis
   by (rule lpp_local_invariant_domain_step[where eta=eta, OF finite_check static_check _ _ step state])
     (use ground safe in auto)
qed

theorem lpp_checked_finite_local_control_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_direct_control_contexts fuel P Q nds states contexts local_contexts Fs T returned arity actions"
    and enrich: "\<And>i eta. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "lpp_finite_direct_invariant A ss"
    and local_states: "lpp_check_local_finite_states A P nds states local_contexts"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) ss R t ret"
proof (rule lpp_finite_direct_control_local_contract_contexts[OF compatible checked enrich ranked transfer program invariant _ represented boundary emit]; (assumption)?)
 fix i eta ev ys
 assume index: "i<length nds"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (local_contexts!i) eta"
   and free: "lpc_free_knowledge (set (Fs!i)) eta"
   and current: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
   and step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation)
     lpp_finite_source_domain (lpc_return_eval eta (states!i)) ev ys"
 show "lpp_finite_direct_invariant A ys"
   by (rule lpp_checked_local_finite_stable[OF compatible local_states signature index known observed current step])
qed

ML \<open>
val checked = [@{thm lpp_checked_local_finite_stable}, @{thm lpp_checked_finite_local_control_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local control" else ();
\<close>
end
