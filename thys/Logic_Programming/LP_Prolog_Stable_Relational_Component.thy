theory LP_Prolog_Stable_Relational_Component
 imports LP_Prolog_Control_Shape_Check LP_Prolog_Stable_Relational_Check LP_Prolog_Stable_Guarded_Graph
begin
hide_const (open) Tree_Automata_Containment.entry

datatype lpp_stable_relational_component =
    LPPSExisting lpp_finite_triple_component lpp_finite_guarded_descent
  | LPPSRelational lpp_link_types lpp_link_types "string lpc_triple_split"
      lpp_source_ground_receipt "string * string lpc_term list"
      lpp_guarded_call_receipt lpp_guarded_call_receipt
  | LPPSControlShape lpp_link_types lpp_link_types "string lpc_triple_split"
      lpp_source_shape_receipt "string * string lpc_term list"
      lpp_guarded_call_receipt lpp_guarded_call_receipt

fun lpp_check_stable_relational_component where
  "lpp_check_stable_relational_component fuel P SP D Q T roots contexts incoming entry OD
      (LPPSExisting component descent) =
    (lpp_finite_triple_check_component fuel P D Q T roots contexts incoming entry component \<and>
      lpp_check_finite_component_descent OD roots incoming entry component descent)"
| "lpp_check_stable_relational_component fuel P SP D Q T roots contexts incoming entry OD
      (LPPSRelational ft st receipt evidence atom first_call second_call) =
    lpp_check_stable_relational_split T ft st fuel P SP D Q roots contexts incoming entry receipt evidence
      atom OD first_call second_call"
| "lpp_check_stable_relational_component fuel P SP D Q T roots contexts incoming entry OD
      (LPPSControlShape ft st receipt evidence atom first_call second_call) =
    lpp_check_control_shape_split T ft st fuel P SP D Q roots contexts incoming entry receipt evidence
      atom OD first_call second_call"

theorem lpp_stable_relational_component_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_relational_component fuel P SP D Q T roots contexts incoming entry OD component"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>
        inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof (cases component)
  case (LPPSExisting old descent)
  have local: "lpp_finite_triple_check_component fuel P D Q T roots contexts incoming entry old"
    and calls: "lpp_check_finite_component_descent OD roots incoming entry old descent"
    using checked by (simp_all add: LPPSExisting)
  show ?thesis by (rule lpp_stable_guarded_component_checked_lower[OF compatible local calls program
    transfer observed known free lower])
next
  case (LPPSRelational ft st receipt evidence atom first_call second_call)
  obtain f ts where atom: "atom=(f,ts)" by (cases atom) auto
  have local: "lpp_check_stable_relational_split T ft st fuel P SP D Q roots contexts incoming entry
    receipt evidence (f,ts) OD first_call second_call"
    using checked by (simp add: LPPSRelational atom)
  show ?thesis by (rule lpp_checked_stable_relational_split_sound[OF compatible transfer local program
    known observed free lower])
next
  case (LPPSControlShape ft st receipt evidence atom first_call second_call)
  obtain f ts where atom: "atom=(f,ts)" by (cases atom) auto
  have local: "lpp_check_control_shape_split T ft st fuel P SP D Q roots contexts incoming entry
    receipt evidence (f,ts) OD first_call second_call"
    using checked by (simp add: LPPSControlShape atom)
  show ?thesis by (rule lpp_checked_control_shape_split_sound[OF compatible transfer local program
    known observed free lower])
qed

ML \<open>
val checked = [@{thm lpp_stable_relational_component_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable relational component" else ();
\<close>
end
