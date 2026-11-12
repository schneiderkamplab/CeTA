theory LP_Prolog_Evaluation_Link
  imports LP_Prolog_Evaluation_Context
begin

text \<open>The evaluation interpretation is additional checked context on the
same shared return link, equations, free knowledge and scope swaps.\<close>

fun lpp_evaluation_context_transport where
  "lpp_evaluation_context_transport T fs (facts,guards,observations)
      (child_facts,child_guards,child_observations) bindings =
    lpp_check_evaluation_context_transport T facts guards observations fs
      child_facts child_guards child_observations bindings"

fun lpp_equation_link_ground where
  "lpp_equation_link_ground (facts,guards,observations) G eqs =
    lpp_observations_equation_ground (observations @ map (\<lambda>x. LPPOGround (Var x)) G @
      map (\<lambda>(a,b). LPPOEquation a b) eqs)"

lemma lpp_equation_link_ground_sound:
  assumes evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and known: "lp_cut_knowledge (set G) K eta"
    and equations: "lp_equations eqs eta"
  shows "\<forall>x\<in>lpp_equation_link_ground source_context G eqs. lp_seg_ground (eta x)"
proof -
  obtain facts guards observations where shape: "source_context=(facts,guards,observations)"
    by (cases source_context) auto
  let ?obs = "observations @ map (\<lambda>x. LPPOGround (Var x)) G @ map (\<lambda>(a,b). LPPOEquation a b) eqs"
  have holds: "list_all (lpp_evaluation_observation_holds E eta) ?obs"
    using observed known equations
    by (auto simp: shape lpp_evaluation_context_holds_def lp_cut_knowledge_def lp_equations_def list_all_iff)
  have each: "\<forall>x\<in>lpp_observation_ground_vars ob. lp_seg_ground (eta x)"
    if "ob\<in>set ?obs" for ob
    by (rule lpp_evaluation_observation_ground[where E=E, OF evaluation])
      (use holds that in \<open>auto simp: list_all_iff\<close>)
  have initial: "\<forall>x\<in>lpp_observations_ground ?obs. lp_seg_ground (eta x)"
    using each known by (auto simp: lpp_observations_ground_def lp_cut_knowledge_def)
  have equalities: "\<forall>(a,b)\<in>set (concat (map lpp_observation_equations ?obs)). lp_ieval a eta=lp_ieval b eta"
    using holds by (fastforce simp: list_all_iff dest: lpp_evaluation_observation_equations)
  show ?thesis unfolding shape lpp_equation_link_ground.simps lpp_observations_equation_ground_def
    by (rule lp_ground_equation_closure_sound[OF equalities initial])
qed

definition lpp_check_evaluation_link where
  "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e =
    ((lpc_check_return_table_link fuel Q nds states nd ss G K eqs e \<or>
      lpc_check_return_table_link fuel Q nds states nd ss
        (G @ filter (\<lambda>x. x\<in>lpp_source_context_ground source_context) (lpcn_vars nd)) K eqs e \<or>
      lpc_check_return_table_link fuel Q nds states nd ss
        (G @ filter (\<lambda>x. x\<in>lpp_equation_link_ground source_context G eqs)
          (lpcn_vars nd @ concat (map (sorted_list_of_set \<circ> vars_term \<circ> snd) (lpcl_bindings e)))) K eqs e) \<and>
     lpcl_target e<length contexts \<and> lpcl_target e<length Fs \<and>
     lpc_check_link_free_normalized fuel eqs F (Fs!lpcl_target e) (lpcl_bindings e) \<and>
     lpp_evaluation_context_transport T fs
       (lpp_source_context_subst (lpp_context_add_ground source_context G) (lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))))
       (contexts!lpcl_target e) (lpcl_bindings e))"

lemma lpp_evaluation_link_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F source_context e"
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
proof -
  let ?j = "lpcl_target e"
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  have context_ground: "\<forall>x\<in>lpp_source_context_ground source_context. lp_seg_ground (eta' x)"
    by (rule lpp_evaluation_context_ground_sound[OF evaluation observed])
  have enriched_known: "lp_cut_knowledge
      (set (G @ filter (\<lambda>x. x\<in>lpp_source_context_ground source_context) (lpcn_vars nd))) K eta'"
    using known context_ground by (auto simp: lp_cut_knowledge_def)
  have equation_ground: "\<forall>x\<in>lpp_equation_link_ground source_context G eqs. lp_seg_ground (eta' x)"
    by (rule lpp_equation_link_ground_sound[OF evaluation observed known equations])
  have equation_known: "lp_cut_knowledge
      (set (G @ filter (\<lambda>x. x\<in>lpp_equation_link_ground source_context G eqs)
        (lpcn_vars nd @ concat (map (sorted_list_of_set \<circ> vars_term \<circ> snd) (lpcl_bindings e))))) K eta'"
    using known equation_ground by (auto simp: lp_cut_knowledge_def)
  obtain grounded where base: "lpc_check_return_table_link fuel Q nds states nd ss grounded K eqs e"
    and grounded_known: "lp_cut_knowledge (set grounded) K eta'"
    using checked known enriched_known equation_known unfolding lpp_check_evaluation_link_def by blast
  have free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!?j) (lpcl_bindings e)"
    and free_bound: "?j<length Fs"
    using checked by (auto simp: lpp_check_evaluation_link_def)
  have link: "lpc_check_return_link fuel Q nds nd ss grounded K eqs (states!?j) e"
    and state_bound: "?j<length states"
    using base by (auto simp: lpc_check_return_table_link_def)
  have node_bound: "?j<length nds"
    using link by (auto simp: lpc_check_return_link_def lpc_check_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval ?nu (states!?j))"
    and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map ?nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpc_return_link_sound[OF link equations old grounded_known] by blast+
  have child_free: "lpc_free_knowledge (set (Fs!?j)) ?nu"
    by (rule lpc_checked_link_free_normalized_sound[OF free_check equations free])
  let ?norm = "lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))"
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcl_vars e)) =
      Some (Some (map LPCAtom (lpcl_terms e)))"
    using base by (auto simp: lpc_check_return_table_link_def lpc_check_return_link_def
      lpc_check_link_def lp_cut_check_interface_def)
  have unchanged: "lp_ieval (?norm x) eta'=eta' x" for x
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have enriched: "lpp_evaluation_context_holds E SP (lpp_context_add_ground source_context G) eta'"
    using observed known by (cases source_context)
      (auto simp: lpp_evaluation_context_holds_def lp_cut_knowledge_def list_all_iff)
  have normalized: "lpp_evaluation_context_holds E SP (lpp_source_context_subst (lpp_context_add_ground source_context G) ?norm) eta'"
    using enriched by (simp add: lpp_evaluation_context_substitute unchanged)
  have transport: "lpp_evaluation_context_transport T fs (lpp_source_context_subst (lpp_context_add_ground source_context G) ?norm)
      (contexts!?j) (lpcl_bindings e)"
    and context_bound: "?j<length contexts"
    using checked by (auto simp: lpp_check_evaluation_link_def)
  have child_context: "lpp_evaluation_context_holds E SP (contexts!?j) ?nu"
    using lpp_evaluation_context_transport_sound[OF contract evaluation program] transport normalized
    by (cases "lpp_source_context_subst (lpp_context_add_ground source_context G) ?norm"; cases "contexts!?j") auto
  show ?thesis using same child_known child_free child_context edge by blast
qed

ML \<open>
val checked = [@{thm lpp_evaluation_link_witness}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted evaluation-link dependency" else ();
\<close>
end
