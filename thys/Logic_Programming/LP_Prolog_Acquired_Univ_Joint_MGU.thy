theory LP_Prolog_Acquired_Univ_Joint_MGU
 imports LP_Prolog_Acquired_Univ_Row
begin

text \<open>Choose the unifier from the actual caller-attached resolution and
project that very unifier to the helper prefix. The reverse projection is not
used: the suspended caller may share live variables with the helper.\<close>

lemma lpp_attached_resolution_common_mgu:
 fixes combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes possible: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst a sigma=lp_ieval (fst (P!c)) rho"
 and step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot))
     ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved))) event result"
 shows "event=None \<and> (\<exists>sigma rho joint_result.
   lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
     (fst (P!c)) (snd (P!c)) sigma rho \<and>
   lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho \<and>
   joint_result=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
     \<lambda>slot. lp_isubst (combined_env slot) sigma)#saved \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   lpp_domain_answers P B U D
     (lpc_reinterface (\<lambda>env slot. env (Inl slot)) ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)) None
     (lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result))"
proof -
 let ?L = "\<lambda>env slot. env (Inl slot)"
 let ?R = "\<lambda>env slot. env (Inr slot)"
 have base: "lpc_answer_transition P
   ((LPCClause (LPCAtom a#(gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)) c mark,
     ?R combined_env)#lpc_attach_answers rest (lpc_reinterface ?R saved)) event result"
  using step by (auto simp: lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 obtain sigma rho where bound: "c<length P" and silent: "event=None"
 and full_mgu: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)
    (fst (P!c)) (snd (P!c)) sigma rho"
 and actual: "result=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma))
    (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)),
    \<lambda>slot. lp_isubst (combined_env (Inr slot)) sigma)#lpc_attach_answers rest (lpc_reinterface ?R saved)"
  using base possible by (cases rule: lpc_answer_transition.cases) auto
 have prefix_mgu: "lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) sigma rho"
  by (rule lpc_mgu_resolve_prefix_projection[OF full_mgu])
 let ?joint = "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
     \<lambda>slot. lp_isubst (combined_env slot) sigma)#saved"
 have attached: "result=lpc_attach_answers rest (lpc_reinterface ?R ?joint)"
  using actual by (simp add: lpc_reinterface_def lpc_attach_answers_def map_map lp_cut_map_comp lp_ieval_subst o_def)
 have helper_base: "lpc_answer_transition P
   (lpc_reinterface ?L ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)) None
   (lpc_reinterface ?L ?joint)"
  by (simp add: lpc_reinterface_def; rule lpc_answer_transition.resolve[OF bound prefix_mgu])
 have helper_step: "lpp_domain_answers P B U D
   (lpc_reinterface ?L ((LPCClause (LPCAtom a#gs) c mark,combined_env)#saved)) None
   (lpc_reinterface ?L ?joint)"
  using helper_base by (auto simp: lpp_domain_answers_def lpc_reinterface_def lpp_builtin_active_def intro: lpp_answer_transition.base)
 show ?thesis unfolding silent
  apply (intro conjI)
  apply simp
  apply (rule exI[of _ sigma], rule exI[of _ rho], rule exI[of _ ?joint])
  using full_mgu prefix_mgu attached helper_step by blast
qed

ML \<open>
val checked = @{thms lpp_attached_resolution_common_mgu};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached common MGU" else ();
val _ = writeln "ATTACHED_COMMON_MGU_KERNEL_CHECKED";
\<close>
end
