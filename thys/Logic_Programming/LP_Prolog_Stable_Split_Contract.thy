theory LP_Prolog_Stable_Split_Contract
 imports LP_Prolog_Stable_Link LP_Prolog_Domain_Composition
begin

text \<open>Use the shared scoped composition theorem with actual answers and
initialized context evidence. Termination of the prefix does not manufacture
return observations. The same source builtin interpretation governs both parts.\<close>

lemma lpp_stable_split_contract:
  assumes program: "lp_cut_source_program P"
    and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and initialized: "list_all (\<lambda>frame. lpp_stable_context_holds operation SP ctx (snd frame)) ss"
    and continuation: "\<And>eta. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
      lpp_stable_context_holds operation SP ctx eta \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P B U D)
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_attach_answers rest ss) R t final"
proof (rule lpp_domain_contract_compose_actual[OF program prefix valid separated])
  fix eta assume actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
  have observed: "lpp_stable_context_holds operation SP ctx eta"
    by (rule lpp_stable_actual_return_preserves_context[OF actual initialized])
  show "lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
    by (rule continuation[OF actual observed])
qed

ML \<open>
val checked = [@{thm lpp_stable_split_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable Split dependency" else ();
\<close>
end
