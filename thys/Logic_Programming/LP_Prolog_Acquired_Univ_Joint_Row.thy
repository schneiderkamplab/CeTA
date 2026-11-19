theory LP_Prolog_Acquired_Univ_Joint_Row
 imports LP_Prolog_Acquired_Univ_Joint_MGU
begin

text \<open>Use the caller-attached step's MGU in the checked helper row.
The helper interface identities are explicit; no second existential helper MGU
is substituted for the actual attached witness.\<close>

lemma lpp_checked_attached_acquired_row:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functors
   nd F a gs c mark active saved k l A next anchors bindings mode outputs source_context source_functors yes no"
 and matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and acquired: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functor_facts: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and helper_payload: "(\<lambda>slot. combined_env (Inl slot))=lpc_return_env active eta"
 and helper_saved: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_saved=lpc_return_eval eta saved"
 and step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot))
    ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c mark,combined_env)#joint_saved))) event result"
 and swaps: "lpcl_swaps yes=[]"
 and target_shape: "states!lpcl_target yes=
   (LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
     [input_template,Fun (LPCUser ''2:prolog_data_2e'') [Var output_name,Var output_args]])#source_goals),source_active)#source_saved"
 shows "event=None \<and> (\<exists>sigma rho joint_result body_tail nu.
   lpc_mgu_resolve (lp_ieval a eta)
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
     map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
    (fst (P!c)) (snd (P!c)) sigma rho \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result) \<and>
   joint_result=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)),
     \<lambda>slot. lp_isubst (combined_env slot) sigma)#joint_saved \<and>
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
     (fst (P!c)) (snd (P!c)) sigma rho \<and>
   lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result=lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,outputs)#saved) \<and>
   snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
     [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target yes))) (lpcn_guards (nds!lpcl_target yes)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target yes)) nu \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target yes) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target yes) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target yes),map nu (lpcn_vars (nds!lpcl_target yes)))])\<in>lp_ild Q \<and>
   lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z \<and>
   (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals \<and>
   (\<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)=lpc_return_env source_active nu \<and> lpc_return_eval eta saved=lpc_return_eval nu source_saved)"
proof -
 let ?G = "lpcn_ground nd"
 let ?K = "lpcn_guards nd"
 have base: "lpc_return_free_resolution_base fuel P Q nds Fs nd F a gs c mark (map fst saved) k l A next anchors bindings mode yes no"
  using checked by (simp add: lpp_check_functor_resolution_node_def)
 have coverage: "lp_cut_check_coverage fuel k a (fst (P!c)) bindings mode \<or>
   (mode=LPCAlwaysSuccess \<and> (lpc_check_free_call F a (fst (P!c)) \<or>
     lpc_check_mixed_free_call fuel k ?G F a (fst (P!c))))"
  using base by (simp add: lpc_return_free_resolution_base_def)
 have unifiable: "\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. \<exists>rho.
   lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  by (rule lp_cut_check_match_sound[OF matching])
 have possible: "mode\<noteq>LPCAlwaysFailure"
  using coverage unifiable lp_cut_coverage_failure[of fuel k a "fst (P!c)" bindings mode] by auto
    have resolve: "lp_cut_check_resolution P fuel k l ?G A ?K a gs c mark (map fst saved) next anchors"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_return_free_resolution_base_def)
    have payload: "lpc_check_return_values fuel k ?G (lp_cut_resolution_equations k l ?G a (fst (P!c)))
      active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpp_check_evaluation_functor_link_free_choices T yes_facts fuel Q nds states contexts Fs functors nd ((LPCGoals next,outputs)#saved)
        (?G@sorted_list_of_set (lp_cut_anchor_vars anchors))
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCHeadGuard a (fst (P!c)) True])
        (lp_cut_resolution_equations k l ?G a (fst (P!c)))
        (lpc_return_resolution_free fuel F ?G a gs (fst (P!c)) (snd (P!c)) k l) (lpp_saved_free k F) (lpp_evaluation_fork_context source_context k (set (lpcn_ground nd))) (lpp_functor_fork_context source_functors k (set ?G)) yes"
      using checked possible by (auto simp: lpp_check_functor_resolution_node_def)

 have context_short: "lpp_context_short k source_context"
 and functor_short: "lpp_functor_context_short k source_functors"
  using checked possible by (auto simp: lpp_check_functor_resolution_node_def)
 obtain sigma rho joint_result where silent: "event=None"
 and full_mgu: "lpc_mgu_resolve (lp_ieval a eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
     map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>slot. combined_env (Inr slot)))) rest)
     (fst (P!c)) (snd (P!c)) sigma rho"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
     (fst (P!c)) (snd (P!c)) sigma rho"
 and joint_shape: "joint_result=(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) (snd (P!c)) @
   map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)),
    \<lambda>slot. lp_isubst (combined_env slot) sigma)#joint_saved"
 and actual_caller: "result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) joint_result)"
  using lpp_attached_resolution_common_mgu[OF unifiable step] by blast
 obtain body_tail where body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
     [Var x,Fun (LPCUser ''2:prolog_data_2e'') [Var y,Var z]])#body_tail"
  using acquired by (auto simp: lpp_check_fresh_univ_clause_def)
 have unifier: "lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have helper_slot: "combined_env (Inl slot)=lpc_return_env active eta slot" for slot
  using fun_cong[OF helper_payload, of slot] by simp
 have actual: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) joint_result=
   lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ((LPCGoals next,outputs)#saved)"
  using lpc_return_resolution_success[OF resolve known unifier payload short] helper_payload helper_saved
  by (simp add: joint_shape lpc_reinterface_def map_map lp_cut_map_comp o_def helper_slot)
 have transported: "\<exists>nu.
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target yes))) (lpcn_guards (nds!lpcl_target yes)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target yes)) nu \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target yes) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target yes) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target yes),map nu (lpcn_vars (nds!lpcl_target yes)))])\<in>lp_ild Q \<and>
   lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z \<and>
   (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals \<and>
   (\<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)=lpc_return_env source_active nu \<and> lpc_return_eval eta saved=lpc_return_eval nu source_saved"
  by (rule lpp_acquired_univ_resolution_link[where rho=rho and sigma=sigma and x=x and y=y and z=z,
    OF compatible program resolve known free observed functor_facts parent context_short functor_short
      mgu payload short body link swaps target_shape])
 show ?thesis unfolding silent
  apply (intro conjI)
  apply simp
  apply (rule exI[of _ sigma], rule exI[of _ rho], rule exI[of _ joint_result], rule exI[of _ body_tail])
  using full_mgu actual_caller joint_shape mgu body actual transported by blast
qed

ML \<open>
val checked = @{thms lpp_checked_attached_acquired_row};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired row witness" else ();
val _ = writeln "ATTACHED_ACQUIRED_ROW_KERNEL_CHECKED";
\<close>
end
