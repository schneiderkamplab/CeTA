theory LP_Prolog_Finite_Direct_Control
 imports LP_Prolog_Finite_Direct_Action LP_Prolog_Stable_Control_Induction
begin

lemma lpp_finite_direct_subset:
 "set xs \<subseteq> set ys \<Longrightarrow> lpp_finite_direct_invariant A ys \<Longrightarrow>
   lpp_finite_direct_invariant A xs"
 by (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
   lpp_static_state_def list_all_iff)

lemma lpp_finite_direct_goal_scope[simp]:
 "lpp_finite_direct_goal (lp_cut_scope_goal r g)=lpp_finite_direct_goal g"
 by (cases g) auto

lemma lpp_static_goal_scope[simp]:
 "lpp_static_goal A (lp_cut_scope_goal r g)=lpp_static_goal A g"
 by (cases g) auto

lemma lpp_finite_direct_entry_scope[simp]:
 "lpp_finite_direct_entry (lp_cut_scope_entry r e)=lpp_finite_direct_entry e"
 by (cases e) (auto simp: list_all_iff)

lemma lpp_static_entry_scope[simp]:
 "lpp_static_entry A (lp_cut_scope_entry r e)=lpp_static_entry A e"
 by (cases e) (auto simp: list_all_iff)

lemma lpp_finite_direct_scope:
 "lpp_finite_direct_invariant A (lpc_return_scope r ss)=lpp_finite_direct_invariant A ss"
 by (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
   lpp_static_state_def list_all_iff)

lemma lpp_finite_direct_scopes:
 "lpp_finite_direct_invariant A (lpc_return_scope_word swaps ss)=lpp_finite_direct_invariant A ss"
 proof (induct swaps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons pair swaps)
 obtain a b where pair: "pair=(a,b)" by (cases pair) auto
 show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps lpp_finite_direct_scope)
qed

lemma lpp_finite_direct_arithmetic_stable:
 assumes program: "lpp_finite_direct_program P" "lpp_static_program A P"
   and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
   and step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys"
   and invariant: "lpp_finite_direct_invariant A xs"
 shows "lpp_finite_direct_invariant A ys"
proof (rule lpp_finite_direct_domain_step[OF program _ step invariant])
 fix f ts outcome
 assume member: "(f,length ts)\<in>A"
   and outcome: "lpp_stable_source_builtin operation f ts outcome"
 have selected: "(f,length ts)\<in>lpp_builtin_signature"
   by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite[OF outcome]])
 show "lpp_finite_direct_outcome outcome"
   by (rule lpp_direct_arithmetic_outcome[OF signature[OF member selected] outcome])
qed


definition lpp_check_finite_direct_control_contexts where
 "lpp_check_finite_direct_control_contexts fuel P Q nds states contexts local_contexts Fs T returned arity actions =
   (length nds=length Fs \<and> length nds=length states \<and> length nds=length contexts \<and>
    length nds=length local_contexts \<and> length nds=length actions \<and>
    list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
      (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
       lpp_check_finite_direct_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i)
         (local_contexts!i) returned arity action)) [0..<length nds])"

theorem lpp_finite_direct_control_local_contract_contexts:
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
    and stable: "\<And>i eta ev ys. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain
        (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow> lpp_finite_direct_invariant A ys"
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
proof (rule lpp_stable_control_local_contracts[where J="lpp_finite_direct_invariant A", OF ranked program invariant lpp_finite_direct_scopes represented])
 fix i eta
 assume index: "i<length nds"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
   and free: "lpc_free_knowledge (set (Fs!i)) eta"
   and current: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
   and lower: "\<And>vs c. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
     lpp_stable_module_rep operation SP nds states contexts Fs vs c \<Longrightarrow> lpp_finite_direct_invariant A vs \<Longrightarrow>
     lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
 show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known observed free current])
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpp_check_finite_direct_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using checked member unfolding lpp_check_finite_direct_control_contexts_def list_all_iff by blast
      have check: "lpp_check_finite_direct_action T fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (local_contexts!i) returned arity action"
        using local Some by auto
      have observed_local: "lpp_stable_context_holds operation SP (local_contexts!i) eta"
        by (rule enrich[OF index known observed])
      show ?thesis
      proof (rule lpp_finite_direct_control_action_local[OF compatible transfer check known free observed_local current
        stable[OF index known observed_local free current] lpp_finite_direct_subset])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "lpp_stable_module_rep operation SP nds states contexts Fs vs c"
          and inv_child: "lpp_finite_direct_invariant A vs"
        show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) vs R t ret"
          by (rule lower[OF edge child inv_child])
      next
        fix rho tt assume event: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt"
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF index current known event])
      qed
    qed
qed
theorem lpp_finite_direct_control_contract_contexts:
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
    and stable: "\<And>(xs::((string lp_cut_symbol,string) lp_iterm lp_cut_entry \<times> (nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list) ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain xs ev ys \<Longrightarrow> lpp_finite_direct_invariant A xs \<Longrightarrow> lpp_finite_direct_invariant A ys"
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
 by (rule lpp_finite_direct_control_local_contract_contexts[OF compatible checked enrich ranked transfer program invariant _ represented boundary emit];
   (assumption | (rule stable; assumption)))

ML \<open>
val checked = [@{thm lpp_finite_direct_control_local_contract_contexts},
 @{thm lpp_finite_direct_control_contract_contexts}, @{thm lpp_finite_direct_arithmetic_stable}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct control" else ();
\<close>
end
