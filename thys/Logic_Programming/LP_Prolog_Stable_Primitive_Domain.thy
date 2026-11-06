theory LP_Prolog_Stable_Primitive_Domain
 imports LP_Prolog_Stable_Legacy_Context
begin

lemma lpp_stable_primitive_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_primitive T fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
  by (rule lpp_evaluation_primitive_domain[OF program checked known
    lpp_stable_context_finite_envelope[OF compatible observed]])

ML \<open>
val checked = [@{thm lpp_stable_primitive_domain}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable primitive domain dependency" else ();
\<close>
end
