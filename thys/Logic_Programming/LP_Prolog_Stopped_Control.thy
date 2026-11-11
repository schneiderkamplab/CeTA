theory LP_Prolog_Stopped_Control
  imports LP_Prolog_Stopped_Action_Dispatch LP_Prolog_Stopped_Scopes
begin

definition lpp_check_stopped_control_contexts where
  "lpp_check_stopped_control_contexts fuel P Q nds states contexts local_contexts Fs T returned arity actions =
    (length nds=length Fs \<and> length nds=length states \<and> length nds=length contexts \<and>
     length nds=length local_contexts \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
         lpp_check_stopped_module_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action)) [0..<length nds])"

theorem lpp_stopped_control_contract_contexts:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stopped_control_contexts fuel P Q nds states contexts local_contexts Fs T returned arity actions"
    and enrich: "\<And>i eta. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "J ss"
    and stable: "\<And>xs ev ys. lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and scopes: "\<And>swaps xs. J (lpc_return_scope_word swaps xs)=J xs"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) ss R t ret"
proof -
  have sn: "SN (lp_ild Q)" by (rule lpc_seg_ranked_control_SN[OF ranked])
  have all: "\<forall>us. (a,b)\<in>(lp_ild Q)\<^sup>* \<longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs us b \<longrightarrow> J us \<longrightarrow> lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) us R t ret" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] UNIV_I], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>vs. (a,c)\<in>(lp_ild Q)\<^sup>* \<longrightarrow> lpp_stable_module_rep operation SP nds states contexts Fs vs c \<longrightarrow> J vs \<longrightarrow> lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) vs R t ret"
      and reached: "(a,b)\<in>(lp_ild Q)\<^sup>*"
      and rep: "lpp_stable_module_rep operation SP nds states contexts Fs us b"
      and inv: "J us"
    obtain swaps i eta where index: "i<length nds"
      and shape: "lpc_return_scope_word swaps us=lpc_return_eval eta (states!i)"
      and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
      and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
      and free: "lpc_free_knowledge (set (Fs!i)) eta"
      and b: "b=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
      using rep by (auto simp: lpp_stable_module_rep_def lpp_stable_rep_def)
    have current: "J (lpc_return_eval eta (states!i))" using inv shape scopes by metis
    have canonical: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known observed free current])
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpp_check_stopped_module_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using checked member unfolding lpp_check_stopped_control_contexts_def list_all_iff by blast
      have check: "lpp_check_stopped_module_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using local Some by auto
      have observed_local: "lpp_stable_context_holds operation SP (local_contexts!i) eta"
        by (rule enrich[OF index known observed])
      show ?thesis
      proof (rule lpp_stopped_module_action_contract[where J=J, OF compatible transfer check known free observed_local current stable frames subset])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "lpp_stable_module_rep operation SP nds states contexts Fs vs c"
          and inv_child: "J vs"
        have bc: "(b,c)\<in>(lp_ild Q)\<^sup>+" using edge b by simp
        have ac: "(a,c)\<in>(lp_ild Q)\<^sup>*" by (rule rtrancl_trans[OF reached trancl_into_rtrancl[OF bc]])
        show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) vs R t ret" using ih[OF bc] ac child inv_child by blast
      next
        fix rho tt assume event: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature) (lpc_return_eval eta (states!i)) (Some rho) tt"
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF index current known event])
      qed
    qed
    have restored: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) (lpc_return_scope_word (rev swaps) (lpc_return_eval eta (states!i))) R t ret"
      by (rule lpp_stopped_contract_scopes[OF program canonical])
    show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) us R t ret" using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  qed
  show ?thesis using all[of a] represented invariant by auto
qed

ML \<open>
val checked = [@{thm lpp_stopped_control_contract_contexts}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped control dependency" else ();
\<close>
end
