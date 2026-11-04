theory LP_Prolog_Equation_Initialization
 imports LP_Prolog_Evaluation_Link
begin

fun lpp_context_with_equations where
  "lpp_context_with_equations (facts,guards,observations) eqs =
    (facts,guards,observations @ map (\<lambda>(a,b). LPPOEquation a b) eqs)"

lemma lpp_context_with_equations_empty[simp]:
  "lpp_context_with_equations source_context []=source_context"
  by (cases source_context) simp

lemma lpp_context_with_equations_sound:
  assumes "lpp_evaluation_context_holds E SP source_context eta"
    "lp_equations eqs eta"
  shows "lpp_evaluation_context_holds E SP (lpp_context_with_equations source_context eqs) eta"
  using assms
  by (cases source_context)
    (auto simp: lpp_evaluation_context_holds_def lp_equations_def list_all_iff)

lemma lpp_equation_initialized_link_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F
      (lpp_context_with_equations source_context eqs) e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_evaluation_context_holds E SP source_context eta'"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_evaluation_context_holds E SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
  by (rule lpp_evaluation_link_witness[OF contract evaluation program checked equations old known free
        lpp_context_with_equations_sound[OF observed equations]])

ML \<open>
val checked = [@{thm lpp_context_with_equations_sound}, @{thm lpp_equation_initialized_link_witness}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted equation initialization dependency" else ();
\<close>
end
