theory LP_Prolog_Acquired_Univ_Resolution
 imports LP_Prolog_Acquired_Univ_Link
begin

text \<open>Extract the actual resolution unifier and complete acquired state.
Checked return-value transport updates the active payload and preserves each
saved frame in its old namespace. Matching excludes the resolution-failure
branch; it does not assert that the subsequent extraction succeeds.\<close>

lemma lpp_actual_acquired_univ_resolution:
 assumes resolve: "lp_cut_check_resolution P fuel k l G A guards a gs c mark (map fst saved) next anchors"
 and known: "lp_cut_knowledge (set G) guards eta"
 and payload: "lpc_check_return_values fuel k G
   (lp_cut_resolution_equations k l G a (fst (P!c))) active (concat (map snd saved)) outputs"
 and short: "lpc_return_short k saved"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and acquired: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and step: "lpp_domain_answers P B U D
   (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c mark,active)#saved)) event result"
 shows "event=None \<and> (\<exists>sigma rho body_tail.
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho \<and>
   snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
     [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail \<and>
   result=lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,outputs)#saved) \<and>
   result=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'')
     [rho x,LPIFun (LPCUser ''2:prolog_data_2e'') [rho y,rho z]])#
     (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)),
      \<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)#lpc_return_eval eta saved)"
proof -
 have possible: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  by (rule lp_cut_check_match_sound[OF matching])
 have base: "lpc_answer_transition P
   ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c mark,
     lpc_return_env active eta)#lpc_return_eval eta saved) event result"
  using step by (auto simp: lpc_return_eval_def intro: lpp_observer_clause_base)
 obtain sigma rho where mgu: "lpc_mgu_resolve (lp_ieval a eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho"
 and silent: "event=None"
 and actual: "result=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)),
   \<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)#lpc_return_eval eta saved"
  using base possible by (cases rule: lpc_answer_transition.cases) auto
 obtain body_tail where body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
  using acquired by (auto simp: lpp_check_fresh_univ_clause_def)
 have unifier: "lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have evaluated: "result=lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,outputs)#saved)"
  using actual lpc_return_resolution_success[OF resolve known unifier payload short]
  by (simp add: map_map lp_cut_map_comp o_def)
 show ?thesis unfolding silent
  apply (intro conjI)
  apply simp
  apply (rule exI[of _ sigma], rule exI[of _ rho], rule exI[of _ body_tail])
  using mgu body evaluated actual by (simp add: map_map lp_cut_map_comp o_def)
qed

ML \<open>
val checked = @{thms lpp_actual_acquired_univ_resolution};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual acquired resolution" else ();
val _ = writeln "ACTUAL_ACQUIRED_UNIV_RESOLUTION_KERNEL_CHECKED";
\<close>
end
