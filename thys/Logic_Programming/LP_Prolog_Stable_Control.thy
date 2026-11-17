theory LP_Prolog_Stable_Control
 imports LP_Prolog_Stable_Control_Induction
begin

theorem lpp_stable_control_contract_contexts:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_evaluation_control_contexts fuel P Q nds states contexts local_contexts Fs T returned arity actions"
    and enrich: "\<And>i eta. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "J ss"
    and stable: "\<And>xs ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and scopes: "\<And>swaps xs. J (lpc_return_scope_word swaps xs)=J xs"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) ss R t ret"
proof (rule lpp_stable_control_local_contracts[where J=J, OF ranked program invariant scopes represented])
 fix i eta
 assume index: "i<length nds"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
   and free: "lpc_free_knowledge (set (Fs!i)) eta"
   and current: "J (lpc_return_eval eta (states!i))"
   and lower: "\<And>vs c. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
     lpp_stable_module_rep operation SP nds states contexts Fs vs c \<Longrightarrow> J vs \<Longrightarrow>
     lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
 show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known observed free current])
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using checked member unfolding lpp_check_evaluation_control_contexts_def list_all_iff by blast
      have check: "lpp_check_evaluation_module_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using local Some by auto
      have observed_local: "lpp_stable_context_holds operation SP (local_contexts!i) eta"
        by (rule enrich[OF index known observed])
      show ?thesis
      proof (rule lpp_stable_control_action[where J=J, OF compatible transfer check known free observed_local current stable frames subset])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "lpp_stable_module_rep operation SP nds states contexts Fs vs c"
          and inv_child: "J vs"
        show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
          by (rule lower[OF edge child inv_child])
      next
        fix rho tt assume event: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt"
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF index current known event])
      qed
    qed
qed

theorem lpp_stable_control_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_evaluation_control fuel P Q nds states contexts Fs T returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "J ss"
    and stable: "\<And>xs ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and scopes: "\<And>swaps xs. J (lpc_return_scope_word swaps xs)=J xs"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) ss R t ret"
proof -
  have control: "lpp_check_evaluation_control_contexts fuel P Q nds states contexts contexts Fs T returned arity actions"
    using checked by (simp add: lpp_check_evaluation_control_contexts_identity)
  have guarded_emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain
        (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
    by (rule emit) assumption+
  show ?thesis
    by (rule lpp_stable_control_contract_contexts[OF compatible control _ ranked transfer program invariant
      stable frames subset scopes represented boundary guarded_emit]) assumption
qed

ML \<open>
val checked = [@{thm lpp_stable_control_contract_contexts}, @{thm lpp_stable_control_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable control dependency" else ();
\<close>
end
