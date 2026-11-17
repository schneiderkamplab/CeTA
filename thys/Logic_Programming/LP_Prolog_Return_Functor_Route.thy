theory LP_Prolog_Return_Functor_Route
 imports LP_Prolog_Functor_Split_Contract LP_Cut_Return_Routing
begin

fun lpp_return_functor_route where
 "lpp_return_functor_route bindings (LPPFunctorFact t n ats) =
  LPPFunctorFact (map_term id (lpc_return_route bindings) t)
    (map_term id (lpc_return_route bindings) n)
    (map_term id (lpc_return_route bindings) ats)"

definition lpp_check_return_functor_route where
 "lpp_check_return_functor_route bindings interface observations =
  (lpc_check_return_route bindings interface \<and>
   list_all (\<lambda>ob. list_all (\<lambda>t. vars_term t \<subseteq> dom (map_of bindings))
     (lpp_functor_fact_terms ob)) observations)"

lemma lpp_return_functor_route_holds:
 assumes checked: "lpp_check_return_functor_route bindings interface observations"
 and known: "list_all (lpp_functor_fact_holds names eta) observations"
 shows "list_all (lpp_functor_fact_holds names (lpc_return_env interface eta))
   (map (lpp_return_functor_route bindings) observations)"
proof -
 have route: "lpc_check_return_route bindings interface"
  using checked by (simp add: lpp_check_return_functor_route_def)
 have eq: "lp_ieval (map_term id (lpc_return_route bindings) t) (lpc_return_env interface eta) = lp_ieval t eta"
  if "ob\<in>set observations" "t\<in>set (lpp_functor_fact_terms ob)" for ob t
  by (rule lpc_return_route_term[OF route])
    (use checked that in \<open>auto simp: lpp_check_return_functor_route_def list_all_iff\<close>)
 have held: "lpp_functor_fact_holds names (lpc_return_env interface eta)
    (lpp_return_functor_route bindings ob)" if member: "ob\<in>set observations" for ob
 proof (cases ob)
  case (LPPFunctorFact t n ats)
  have equalities:
   "lp_ieval (map_term id (lpc_return_route bindings) t) (lpc_return_env interface eta)=lp_ieval t eta"
   "lp_ieval (map_term id (lpc_return_route bindings) n) (lpc_return_env interface eta)=lp_ieval n eta"
   "lp_ieval (map_term id (lpc_return_route bindings) ats) (lpc_return_env interface eta)=lp_ieval ats eta"
   using eq[OF member] by (simp_all add: LPPFunctorFact)
  have prior: "lpp_functor_fact_holds names eta ob"
   using known member by (simp add: list_all_iff)
  show ?thesis using prior by (simp add: LPPFunctorFact equalities)
 qed
 show ?thesis using held by (simp add: list_all_iff)
qed

theorem lpp_actual_return_routed_functors:
 assumes checked: "list_all (\<lambda>frame. lpp_check_return_functor_route bindings (snd frame) observations) ss"
 and known: "list_all (lpp_functor_fact_holds names eta) observations"
 and actual: "lp_actual_answer (lpp_domain_answers P B U D) (lpc_return_eval eta ss) rho"
 shows "list_all (lpp_functor_fact_holds names rho) (map (lpp_return_functor_route bindings) observations)"
proof (rule lpp_actual_return_preserves_functors[OF actual])
 show "list_all (\<lambda>frame. list_all (lpp_functor_fact_holds names (snd frame))
   (map (lpp_return_functor_route bindings) observations)) (lpc_return_eval eta ss)"
  using checked lpp_return_functor_route_holds[OF _ known]
  by (auto simp: lpc_return_eval_def list_all_iff)
qed

ML \<open>
val checked = @{thms lpp_return_functor_route_holds lpp_actual_return_routed_functors};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted return functor route" else ();
\<close>
end
