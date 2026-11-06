theory LP_Prolog_Stable_Length
 imports LP_Prolog_Stable_Constant LP_Prolog_Finite_Context_Length
begin

lemma lpp_stable_length_normalized_contract:
  fixes P :: "(string,string) lp_cut_program"
    and a e :: "(string lp_cut_symbol,string) lp_iterm"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and ret :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) \<Rightarrow> 'r"
    and R :: "'r rel" and t :: "'r"
  assumes ground: "lp_seg_ground e"
    and contracts: "\<And>f. lpp_length_result e (LPIFun (LPCUser f) []) \<Longrightarrow>
      lp_answer_contract
        (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) R t ret"
  shows "lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:length'') [e,a])#gs),eta)#saved) R t ret"
proof (rule lp_answer_contract_intro)
  let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain"
  fix event tt
  assume step: "?T ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:length'') [e,a])#gs),eta)#saved) event tt"
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_stable_source_builtin operation)
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:length'') [e,a])#gs),eta)#saved) event tt"
    using step ground by (auto simp: lpp_domain_answers_def lpp_finite_source_domain_def)
  have no_answer: "event=None" and cover: "tt=[] \<or> (\<exists>f.
    lpp_length_result e (LPIFun (LPCUser f) []) \<and>
    lpc_answer_transition P
      ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt)"
    using lpp_finite_length_uses_shared_equality[OF lpp_stable_answer_transition_refines[OF actual]] by auto
  have child: "lp_answer_contract ?T tt R t ret"
  proof (cases "tt=[]")
    case True
    have empty: "lp_answer_contract ?T [] R t ret"
    proof (rule lp_answer_contract_intro)
      fix ev :: "('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm) option" and us
      assume "?T [] ev us"
      then have "([],map fst us)\<in>lpp_atomic_source P lpp_builtin_signature (lpp_stable_source_builtin operation)"
        by (auto simp: lpp_domain_answers_def dest: lpp_answer_transition_erases)
      then show "(\<forall>rho. ev=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T us R t ret"
        by (simp add: lpp_atomic_source_empty)
    qed
    show ?thesis using empty True by simp
  next
    case False
    obtain f where result_value: "lpp_length_result e (LPIFun (LPCUser f) [])"
      and equality: "lpc_answer_transition P
        ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      using cover False by blast
    have normalized: "?T ((LPCGoals (LPCUnify a (LPIFun (LPCUser f) [])#gs),eta)#saved) event tt"
      unfolding lpp_domain_answers_def by (intro disjI1 lpp_answer_transition.base[OF _ equality])
        (simp add: lpp_builtin_active_def)
    show ?thesis by (rule lp_answer_contract_child[OF contracts[OF result_value] normalized])
  qed
  show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and> lp_answer_contract ?T tt R t ret"
    using child no_answer by simp
qed

theorem lpp_stable_context_length_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_context_length T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:length'') [e,a])#gs),active)#saved"
    and expr_ground: "vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
    and result_var: "lpp_fresh_return result_var ss"
    and context_fresh: "lpp_context_fresh result_var source_context"
    and free_fresh: "result_var\<notin>set F"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
      (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
      source_context middle"
    using checked by (auto simp: lpp_check_finite_context_length_def)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    using known expr_ground lpp_stable_context_ground_sound[OF observed]
    by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
  have contracts: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if evaluated: "lpp_length_result (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
  proof -
  let ?nu = "eta(result_var:=(LPIFun (LPCUser f) []))"
  let ?synthetic = "((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)"
  have fa: "result_var\<notin>vars_term a" and fe: "result_var\<notin>vars_term e"
    and rest: "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ?synthetic =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "LPIFun (LPCUser f) []"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (result_var#lpcn_ground nd)) (lpcn_guards nd) ?nu"
    using known guards lpp_fresh_guard_eval[of result_var _ eta "LPIFun (LPCUser f) []"]
      by (auto simp: lp_cut_knowledge_def list_all_iff intro: lp_seg_ground.intros)
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  have old_context: "lpp_stable_context_holds operation SP source_context ?nu"
    using lpp_stable_context_fresh_eval[OF context_fresh, of operation SP eta "LPIFun (LPCUser f) []"] observed by simp
  have extended_free: "lpc_free_knowledge (set F) ?nu"
    using free free_fresh by (auto simp: lpc_free_knowledge_def inj_on_def)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_stable_link_witness[OF compatible program link equations parent extended extended_free old_context] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval ?nu ?synthetic)=map snd (lpc_return_eval eta ss)"
    using arg_cong[OF unchanged, of "map snd"]
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using child same represented by simp
  qed
  show ?thesis using lpp_stable_length_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_stable_length_normalized_contract}, @{thm lpp_stable_context_length_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable length dependency" else ();
\<close>
end
