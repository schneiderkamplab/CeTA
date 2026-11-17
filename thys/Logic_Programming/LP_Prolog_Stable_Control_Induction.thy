theory LP_Prolog_Stable_Control_Induction
 imports LP_Prolog_Stable_Module_Action
begin

text \<open>One shared control induction over the established residual relation.
Local contracts carry their own invariant transport obligations; no closure
under arbitrary replacement of goal frames is required by the induction.\<close>

theorem lpp_stable_control_local_contracts:
 assumes ranked: "lpc_seg_ranked_control rank_of Q"
   and program: "lp_cut_source_program P"
   and invariant: "J ss"
   and scopes: "\<And>swaps xs. J (lpc_return_scope_word swaps xs)=J xs"
   and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss a"
   and local: "\<And>i eta. i<length nds \<Longrightarrow>
     lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
     lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
     lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
     J (lpc_return_eval eta (states!i)) \<Longrightarrow>
     (\<And>vs c. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
       lpp_stable_module_rep operation SP nds states contexts Fs vs c \<Longrightarrow> J vs \<Longrightarrow>
       lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret) \<Longrightarrow>
     lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
       (lpc_return_eval eta (states!i)) R t ret"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) ss R t ret"
proof -
  have sn: "SN (lp_ild Q)" by (rule lpc_seg_ranked_control_SN[OF ranked])
  have all: "\<forall>us. (a,b)\<in>(lp_ild Q)\<^sup>* \<longrightarrow>
      lpp_stable_module_rep operation SP nds states contexts Fs us b \<longrightarrow> J us \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) us R t ret" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] UNIV_I], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>vs. (a,c)\<in>(lp_ild Q)\<^sup>* \<longrightarrow> lpp_stable_module_rep operation SP nds states contexts Fs vs c \<longrightarrow> J vs \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
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
    have canonical: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
      by (rule local[OF index known observed free current])
        (use ih reached b in \<open>meson rtrancl_trans trancl_into_rtrancl\<close>)
    have restored: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_scope_word (rev swaps) (lpc_return_eval eta (states!i))) R t ret"
      by (rule lpp_domain_contract_scopes[OF program canonical])
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) us R t ret" using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  qed
  show ?thesis using all[of a] represented invariant by auto
qed
end
