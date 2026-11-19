theory LP_Prolog_Acquired_Univ_Resolution_Link
 imports LP_Prolog_Acquired_Univ_Resolution
begin

text \<open>Discharge link knowledge, equations, free alternatives and forked
contexts for the supplied resolution MGU. Every target coordinate uses that
same unifier. Static resolution/link components remain checked premises.\<close>

lemma lpp_acquired_univ_resolution_link:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and resolve: "lp_cut_check_resolution P fuel k l G A guards a gs c mark (map fst saved) next anchors"
 and known: "lp_cut_knowledge (set G) guards eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functor_facts: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and parent: "\<forall>v\<in>set (lpcn_vars nd). length v<k"
 and context_short: "lpp_context_short k source_context"
 and functor_short: "lpp_functor_context_short k source_functors"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and payload: "lpc_check_return_values fuel k G
   (lp_cut_resolution_equations k l G a (fst (P!c))) active (concat (map snd saved)) outputs"
 and short: "lpc_return_short k saved"
 and body: "snd (P!c)=LPCAtom (Fun (LPCUser ''2:=..'')
   [Var x,Fun pair_symbol [Var y,Var z]])#body_tail"
 and checked: "lpp_check_evaluation_functor_link_free_choices T fs fuel Q nds states contexts Fs functors
   nd ((LPCGoals next,outputs)#saved) (G@sorted_list_of_set (lp_cut_anchor_vars anchors))
   (guards@lpc_negative_guards k (set G) guards@[LPCHeadGuard a (fst (P!c)) True])
   (lp_cut_resolution_equations k l G a (fst (P!c)))
   (lpc_return_resolution_free fuel F G a gs (fst (P!c)) (snd (P!c)) k l)
   (lpp_saved_free k F) (lpp_evaluation_fork_context source_context k (set G))
   (lpp_functor_fork_context source_functors k (set G)) link"
 and swaps: "lpcl_swaps link=[]"
 and target_shape: "states!lpcl_target link=
   (LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'')
     [input_template,Fun pair_symbol [Var output_name,Var output_args]])#source_goals),source_active)#source_saved"
 shows "\<exists>nu.
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target link)) nu \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target link) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functors!lpcl_target link) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q \<and>
   lp_ieval input_template nu=rho x \<and> nu output_name=rho y \<and> nu output_args=rho z \<and>
   (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)=map (lp_cut_map (\<lambda>t. lp_ieval t nu)) source_goals \<and>
   (\<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)=lpc_return_env source_active nu \<and> lpc_return_eval eta saved=lpc_return_eval nu source_saved"
proof -
 let ?env = "lp_cut_resolution_env k l eta sigma rho"
 let ?G = "G@sorted_list_of_set (lp_cut_anchor_vars anchors)"
 let ?K = "guards@lpc_negative_guards k (set G) guards@[LPCHeadGuard a (fst (P!c)) True]"
 let ?eqs = "lp_cut_resolution_equations k l G a (fst (P!c))"
 have unifier: "lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
  using mgu by (simp add: lpc_mgu_resolve_def)
 have equations: "lp_equations ?eqs ?env"
  by (rule lp_cut_checked_resolution_equations[OF resolve known unifier])
 have bounds: "2 * k \<le> l" using resolve by (simp add: lp_cut_check_resolution_def)
 have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
  by (rule lp_cut_resolution_parent_interface[OF _ parent]) (use bounds in arith)
 have prior: "lp_cut_knowledge (set ?G) (guards@[LPCHeadGuard a (fst (P!c)) True]) ?env"
  using lp_cut_check_resolution_success(2)[OF resolve known unifier]
  by (simp add: lp_cut_anchor_vars_def)
 have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set G) guards)"
  by (rule lpc_negative_guards_sound[OF _ _ known])
    (use resolve in \<open>auto simp: lp_cut_check_resolution_def\<close>)
 have knowledge: "lp_cut_knowledge (set ?G) ?K ?env"
  using prior negative by (simp add: lp_cut_knowledge_def)
 have ground: "\<forall>v\<in>set G. lp_seg_ground (eta v)"
  using known by (simp add: lp_cut_knowledge_def)
 have body_free: "lpc_free_knowledge
   (set (lpc_return_resolution_free fuel F G a gs (fst (P!c)) (snd (P!c)) k l)) ?env"
  by (rule lpc_return_resolution_free_sound[OF mgu free ground bounds])
 have saved_free: "lpc_free_knowledge (set (lpp_saved_free k F)) ?env"
  by (rule lpp_saved_free_sound[OF free]) (use bounds in arith)
 have forked: "list_all (lpp_functor_fact_holds names ?env)
   (lpp_functor_fork_context source_functors k (set G))"
  by (rule lpp_functor_context_fork_sound[OF functor_facts functor_short bounds ground])
 have facts: "lpp_stable_context_holds operation SP (lpp_evaluation_fork_context source_context k (set G)) ?env"
  by (rule lpp_stable_context_fork_sound[OF observed context_short bounds ground])
 obtain chosen_free where link: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functors
   nd ((LPCGoals next,outputs)#saved) ?G ?K ?eqs chosen_free
   (lpp_evaluation_fork_context source_context k (set G))
   (lpp_functor_fork_context source_functors k (set G)) link"
 and chosen: "lpc_free_knowledge (set chosen_free) ?env"
  using checked body_free saved_free by (auto simp: lpp_check_evaluation_functor_link_free_choices_def)
 have source_shape: "lpc_return_eval ?env ((LPCGoals next,outputs)#saved)=
   (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [rho x,LPIFun pair_symbol [rho y,rho z]])#
    (map (lp_cut_bind mark (\<lambda>t. lp_ieval t rho)) body_tail @
     map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma)) gs)),
     \<lambda>slot. lp_isubst (lpc_return_env active eta slot) sigma)#lpc_return_eval eta saved"
  using lpc_return_resolution_success[OF resolve known unifier payload short] by (simp add: body)
 show ?thesis
  by (rule lpp_acquired_univ_link_correspondence[where rho=rho and x=x and y=y and z=z, OF compatible program link equations old knowledge
    chosen facts forked swaps source_shape target_shape])
qed

ML \<open>
val checked = @{thms lpp_acquired_univ_resolution_link};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted resolution link" else ();
val _ = writeln "ACQUIRED_RESOLUTION_LINK_KERNEL_CHECKED";
\<close>
end
