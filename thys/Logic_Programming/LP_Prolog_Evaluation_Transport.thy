theory LP_Prolog_Evaluation_Transport
 imports LP_Prolog_Evaluation_Refresh
begin

lemma lpp_evaluation_transport_sound:
  fixes SP :: "'v lpp_success_clause list"
    and incoming outgoing :: "'v lpp_source_context"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_evaluation_context_transport T fs incoming outgoing bindings"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming eta"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result SP outgoing
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  obtain facts guards observations where incoming: "incoming=(facts,guards,observations)"
    by (cases incoming) auto
  obtain child_facts child_guards child_observations where outgoing: "outgoing=(child_facts,child_guards,child_observations)"
    by (cases outgoing) auto
  have check: "lpp_check_evaluation_context_transport T facts guards observations fs
    child_facts child_guards child_observations bindings"
    using checked by (simp add: incoming outgoing)
  have source: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (facts,guards,observations) eta"
    using observed by (simp add: incoming)
  show ?thesis unfolding outgoing
    by (rule lpp_evaluation_context_transport_sound[OF lpp_finite_evaluation_integer_contract
      _ transfer check source]) (auto dest: lpp_finite_evaluation_ground)
qed

lemma lpp_evaluation_add_ground_sound:
  "lpp_evaluation_context_holds E SP incoming eta \<Longrightarrow>
   (\<forall>x\<in>set G. lp_seg_ground (eta x)) \<Longrightarrow>
   lpp_evaluation_context_holds E SP (lpp_context_add_ground incoming G) eta"
  by (cases incoming) (auto simp: lpp_evaluation_context_holds_def list_all_iff)

end
