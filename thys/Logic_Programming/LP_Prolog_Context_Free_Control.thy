theory LP_Prolog_Context_Free_Control
 imports LP_Prolog_Context_Free_Is_Constant_Normalized LP_Prolog_Context_Free_Source LP_Prolog_Context_Observed_Control
begin

definition lpp_context_free_module_rep where
  "lpp_context_free_module_rep SP nds states contexts Fs ss t =
    (\<exists>swaps. lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps ss) t)"
fun lpp_check_context_free_module_action where
  "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMPrimitive action) =
    lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMTrim successor barriers e) =
    (ss=successor@barriers \<and> lp_cut_barriers (map fst barriers) \<and>
      lpp_check_context_free_link fuel Q nds states contexts Fs nd successor (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMParallel links) =
    (length links=length ss \<and> list_all (\<lambda>i.
      lpp_check_context_free_link fuel Q nds states contexts Fs nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] F source_context (links!i)) [0..<length ss])"

| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMRefuted i k bindings) =
    lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"

| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMFiniteComparison evidence) =
    lpp_check_free_finite_comparison_receipt fuel Q nds states contexts Fs nd F ss source_context evidence"

| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMNormalizeIs K evidence a e gs active saved result_var middle) =
    lpp_check_context_free_is_normalized fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle"
| "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPPCMNormalizeConstantIs evidence a e gs active saved middle) =
    lpp_check_context_free_is_constant_normalized fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle"

definition lpp_check_context_free_control where
  "lpp_check_context_free_control fuel P Q nds states contexts Fs T typings returned arity actions =
    (length nds=length Fs \<and> length nds=length states \<and> length nds=length contexts \<and> length nds=length typings \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
         lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action) \<and>
         lpp_check_context_free_module_action fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (contexts!i) returned arity action)) [0..<length nds])"

theorem lpp_context_free_observed_control_action:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_free_module_action fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known (lpp_context_module_types action) eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and stable: "\<And>xs ev ys. lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_context_free_module_rep SP nds states contexts Fs vs v \<Longrightarrow> J vs \<Longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret"
    and emit: "\<And>rho tt. lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta ss) (Some rho) tt \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta ss) R t ret"
proof (cases action)
  case (LPPCMNormalizeIs K evidence a e gs active saved result_var middle)
  have check: "lpp_check_context_free_is_normalized fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle"
    using checked LPPCMNormalizeIs by simp
  have typed: "lpp_integer_known K eta" using integers LPPCMNormalizeIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_context_free_is_normalized_def lpp_check_context_free_link_def
      lpp_check_context_table_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_context_free_is_normalized_contract[where J=J, OF check known free observed typed invariant frames])
    fix rho
    assume edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
      and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
      and child_context: "lpp_source_context_holds SP (contexts!lpcl_target middle) rho"
      and inv: "J (lpc_return_eval rho (states!lpcl_target middle))"
    have represented: "lpp_context_free_module_rep SP nds states contexts Fs
      (lpc_return_eval rho (states!lpcl_target middle))
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
      unfolding lpp_context_free_module_rep_def lpp_context_free_rep_def
      by (rule exI[of _ "[]"], rule exI[of _ "lpcl_target middle"], rule exI[of _ rho])
        (use bounds knowledge child_free child_context in auto)
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
      by (rule lower[OF edge represented inv])
  qed
next
  case (LPPCMNormalizeConstantIs evidence a e gs active saved middle)
  have check: "lpp_check_context_free_is_constant_normalized fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle"
    using checked LPPCMNormalizeConstantIs by simp
  have bounds: "lpcl_target middle<length nds \<and> lpcl_target middle<length states \<and>
    lpcl_target middle<length contexts \<and> lpcl_target middle<length Fs"
    using check by (auto simp: lpp_check_context_free_is_constant_normalized_def lpp_check_context_free_link_def
      lpp_check_context_table_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  show ?thesis
  proof (rule lpp_context_free_is_constant_normalized_contract[where J=J, OF check known free observed invariant frames])
    fix rho
    assume edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
      and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
      and child_context: "lpp_source_context_holds SP (contexts!lpcl_target middle) rho"
      and inv: "J (lpc_return_eval rho (states!lpcl_target middle))"
    have represented: "lpp_context_free_module_rep SP nds states contexts Fs
      (lpc_return_eval rho (states!lpcl_target middle))
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
      unfolding lpp_context_free_module_rep_def lpp_context_free_rep_def
      by (rule exI[of _ "[]"], rule exI[of _ "lpcl_target middle"], rule exI[of _ rho])
        (use bounds knowledge child_free child_context in auto)
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
      by (rule lower[OF edge represented inv])
  qed
next
  case (LPPCMPrimitive primitive)
  have check: "lpp_check_context_free_source fuel P Q nds states contexts Fs nd F ss source_context returned arity primitive"
    using checked LPPCMPrimitive by simp
  have typed: "lpp_integer_known (lpp_context_source_types primitive) eta"
    using integers LPPCMPrimitive by simp
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt
    assume step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta ss) event tt"
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
      by (rule lpp_context_free_source_domain[OF check typed])
    have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
      using step supported by (simp add: lpp_domain_answers_def)
    obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
      using lpp_context_free_source_sound[OF check known free observed typed actual] by blast
    have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      by (rule lower[OF strict _ stable[OF step invariant]])
        (use rep in \<open>auto simp: lpp_context_free_module_rep_def\<close>)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using child step emit by blast
  qed
next
  case (LPPCMFiniteComparison evidence)
  have check: "lpp_check_free_finite_comparison_receipt fuel Q nds states contexts Fs nd F ss source_context evidence"
    using checked LPPCMFiniteComparison by simp
  show ?thesis
  proof (rule lp_answer_contract_intro)
    fix event tt
    assume step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta ss) event tt"
    have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst (lpc_return_eval eta ss))"
      by (rule lpp_free_finite_receipt_domain[OF check known observed])
    have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
      using step supported by (simp add: lpp_domain_answers_def)
    obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u"
      using lpp_free_finite_receipt_sound[OF check known free observed actual] by blast
    have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      by (rule lower[OF strict _ stable[OF step invariant]])
        (use rep in \<open>auto simp: lpp_context_free_module_rep_def\<close>)
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) tt R t ret"
      using child step emit by blast
  qed
next
  case (LPPCMTrim successor barriers e)
  have shape: "ss=successor@barriers" and barriers: "lp_cut_barriers (map fst barriers)"
    and link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd successor (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked LPPCMTrim by auto
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta successor)) v"
    using lpp_context_free_link_sound[OF link equations refl known free observed] by blast
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta successor) R t ret"
    by (rule lower[OF strict _ subset[OF _ invariant]])
      (use rep in \<open>auto simp: lpp_context_free_module_rep_def shape lpc_return_eval_def\<close>)
  have suffix: "lp_cut_barriers (map fst (lpc_return_eval eta barriers))"
    using barriers by (simp add: lpc_return_eval_erases lp_cut_state_map_def list_all_iff lp_cut_barrier_entry_map)
  show ?thesis using lpp_domain_contract_append_barriers[OF child suffix]
    by (simp add: shape lpc_return_eval_def)
next
  case (LPPCMParallel links)
  show ?thesis
  proof (rule lpp_domain_contract_singletons)
    fix e assume member: "e\<in>set (lpc_return_eval eta ss)"
    obtain i where index: "i<length ss" and e: "[e]=lpc_return_eval eta [ss!i]"
      using member by (auto simp: lpc_return_eval_def in_set_conv_nth)
    have link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd [ss!i] (lpcn_ground nd) (lpcn_guards nd) [] F source_context (links!i)"
      using checked LPPCMParallel index by (auto simp: list_all_iff)
    have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
    obtain v swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+"
      and rep: "lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta [ss!i])) v"
      using lpp_context_free_link_sound[OF link equations refl known free observed] by blast
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) [e] R t ret"
      unfolding e by (rule lower[OF strict _ subset[OF _ invariant]])
        (use rep member in \<open>auto simp: lpp_context_free_module_rep_def e[symmetric]\<close>)
  qed
next
  case (LPPCMRefuted i k bindings)
  have "lp_cut_check_refuted_guard fuel (lpcn_guards nd) i k bindings"
    using checked LPPCMRefuted by simp
  then show ?thesis using lp_cut_checked_refuted_guard[OF _ known] by blast
qed

theorem lpp_context_free_observed_control_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_free_control fuel P Q nds states contexts Fs T typings returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "J ss"
    and stable: "\<And>xs ev ys. lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain xs ev ys \<Longrightarrow> J xs \<Longrightarrow> J ys"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and subset: "\<And>xs ys. set xs\<subseteq> set ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and scopes: "\<And>swaps xs. J (lpc_return_scope_word swaps xs)=J xs"
    and represented: "lpp_context_free_module_rep SP nds states contexts Fs ss a"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_source_context_holds SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    and emit: "\<And>i eta rho tt. i<length nds \<Longrightarrow>
      J (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt \<Longrightarrow>
      (t,ret rho)\<in>R\<^sup>*"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) ss R t ret"
proof -
  have sn: "SN (lp_ild Q)" by (rule lpc_seg_ranked_control_SN[OF ranked])
  have all: "\<forall>us. (a,b)\<in>(lp_ild Q)\<^sup>* \<longrightarrow>
      lpp_context_free_module_rep SP nds states contexts Fs us b \<longrightarrow> J us \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) us R t ret" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] UNIV_I], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      \<forall>vs. (a,c)\<in>(lp_ild Q)\<^sup>* \<longrightarrow> lpp_context_free_module_rep SP nds states contexts Fs vs c \<longrightarrow> J vs \<longrightarrow> lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret"
      and reached: "(a,b)\<in>(lp_ild Q)\<^sup>*"
      and rep: "lpp_context_free_module_rep SP nds states contexts Fs us b"
      and inv: "J us"
    obtain swaps i eta where index: "i<length nds"
      and shape: "lpc_return_scope_word swaps us=lpc_return_eval eta (states!i)"
      and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
      and observed: "lpp_source_context_holds SP (contexts!i) eta"
      and free: "lpc_free_knowledge (set (Fs!i)) eta"
      and b: "b=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
      using rep by (auto simp: lpp_context_free_module_rep_def lpp_context_free_rep_def)
    have current: "J (lpc_return_eval eta (states!i))" using inv shape scopes by metis
    have canonical: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_eval eta (states!i)) R t ret"
    proof (cases "actions!i")
      case None show ?thesis by (rule boundary[OF index None known observed free current])
    next
      case (Some action)
      have member: "i\<in>set [0..<length nds]" using index by simp
      have local: "case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
          lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action) \<and>
          lpp_check_context_free_module_action fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (contexts!i) returned arity action"
        using checked member unfolding lpp_check_context_free_control_def list_all_iff by blast
      have check: "lpp_check_context_free_module_action fuel P Q nds states contexts Fs (nds!i) (Fs!i) (states!i) (contexts!i) returned arity action"
        using local Some by auto
      have typing: "lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_module_types action)"
        using local Some by auto
      have typed: "lpp_integer_known (lpp_context_module_types action) eta"
        by (rule lpp_context_typing_sound[OF transfer typing observed])
      show ?thesis
      proof (rule lpp_context_free_observed_control_action[where J=J, OF check known free observed typed current stable frames subset])
        fix vs c assume edge: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],c)\<in>(lp_ild Q)\<^sup>+"
          and child: "lpp_context_free_module_rep SP nds states contexts Fs vs c"
          and inv_child: "J vs"
        have bc: "(b,c)\<in>(lp_ild Q)\<^sup>+" using edge b by simp
        have ac: "(a,c)\<in>(lp_ild Q)\<^sup>*" by (rule rtrancl_trans[OF reached trancl_into_rtrancl[OF bc]])
        show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) vs R t ret" using ih[OF bc] ac child inv_child by blast
      next
        fix rho tt assume event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt"
        show "(t,ret rho)\<in>R\<^sup>*" by (rule emit[OF index current event])
      qed
    qed
    have restored: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lpc_return_scope_word (rev swaps) (lpc_return_eval eta (states!i))) R t ret"
      by (rule lpp_domain_contract_scopes[OF program canonical])
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) us R t ret" using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  qed
  show ?thesis using all[of a] represented invariant by auto
qed

ML \<open>
val checked = [@{thm lpp_context_free_observed_control_action}, @{thm lpp_context_free_observed_control_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual observed control dependency" else ();
\<close>
end
