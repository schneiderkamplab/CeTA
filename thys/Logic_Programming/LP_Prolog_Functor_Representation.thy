theory LP_Prolog_Functor_Representation
  imports LP_Prolog_Evaluation_Functor_Link LP_Prolog_Functor_Fork
begin

definition lpp_functor_rep where
  "lpp_functor_rep names E SP nds states contexts Fs functor_contexts ss t = (\<exists>i eta.
    i<length nds \<and> i<length states \<and> i<length contexts \<and> i<length Fs \<and> i<length functor_contexts \<and>
    ss=lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    lpp_evaluation_context_holds E SP (contexts!i) eta \<and>
    list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<and>
    t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

lemma lpp_evaluation_functor_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_evaluation_context_holds E SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j="lpcl_target e"
  obtain nu where same: "lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!?j))"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child_free: "lpc_free_knowledge (set (Fs!?j)) nu"
    and context_holds: "lpp_evaluation_context_holds E SP (contexts!?j) nu"
    and child_functors: "list_all (lpp_functor_fact_holds names nu) (functor_contexts!?j)"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_evaluation_functor_link_witness[OF contract evaluation program checked equations old known free observed functors] by blast
  have bounds: "?j<length nds" "?j<length states" "?j<length contexts" "?j<length Fs" "?j<length functor_contexts"
    using checked by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def
      lpc_check_return_link_def lpc_check_link_def)
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have rep: "lpp_functor_rep names E SP nds states contexts Fs functor_contexts
      (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
      [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_functor_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use bounds inverse knowledge child_free context_holds child_functors in auto)
  show ?thesis using edge rep by blast
qed


definition lpp_check_evaluation_functor_link_free_choices where
  "lpp_check_evaluation_functor_link_free_choices T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F H source_context source_functors e =
    (lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e \<or>
     lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e)"

lemma lpp_evaluation_functor_link_free_choices_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link_free_choices T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F H source_context source_functors e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and saved_free: "lpc_free_knowledge (set H) eta'"
    and observed: "lpp_evaluation_context_holds E SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_functor_rep names E SP nds states contexts Fs functor_contexts (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
 have alternatives:
   "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e \<or>
    lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  using checked by (simp add: lpp_check_evaluation_functor_link_free_choices_def)
 from alternatives show ?thesis
 proof
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
  show ?thesis by (rule lpp_evaluation_functor_link_sound[OF contract _ program link equations old known free observed functors]) (rule evaluation)
 next
  assume link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs H source_context source_functors e"
  show ?thesis by (rule lpp_evaluation_functor_link_sound[OF contract _ program link equations old known saved_free observed functors]) (rule evaluation)
 qed
qed

ML \<open>
val checked = [@{thm lpp_evaluation_functor_link_sound}, @{thm lpp_evaluation_functor_link_free_choices_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor representation dependency" else ();
\<close>
end
