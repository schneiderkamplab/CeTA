theory LP_Prolog_Finite_Direct_Root
 imports LP_Prolog_Finite_Reachable_Program LP_Cut_Root
begin

definition lpp_check_finite_direct_root where
 "lpp_check_finite_direct_root fuel P Q nds states contexts Fs T returned arity actions ranks signatures q modes =
   (lpp_check_finite_direct_control_contexts fuel P Q nds states contexts contexts Fs T returned arity actions \<and>
    lpc_seg_ranked_control ranks Q \<and> lp_cut_source_program P \<and>
    lpp_check_finite_reachable_signature P signatures \<and>
    list_all (\<lambda>x. x\<noteq>None) actions \<and> nds\<noteq>[] \<and>
    (q,length modes)\<in>set signatures \<and>
    lp_cut_check_root q modes (lpcn_vars (nds!0)) (lpcn_state (nds!0))
      (lpcn_ground (nds!0)) (lpcn_guards (nds!0)) \<and>
    states!0=[(LPCGoals [LPCAtom (Fun (LPCUser q) (map Var (lpcn_vars (nds!0))))],map Var (lpcn_vars (nds!0)))] \<and>
    contexts!0=([],[],[]) \<and> Fs!0=[])"

theorem lpp_finite_direct_root_sound:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_finite_direct_root fuel P Q nds states contexts Fs T returned arity actions ranks signatures q modes"
   and transfer: "lpp_check_transfer_program T SP receipts"
   and len: "length ts=length modes"
   and finite: "list_all lpp_finite_term ts"
   and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
 shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
   {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
 let ?nd = "nds!0"
 let ?vs = "lpcn_vars ?nd"
 let ?eta = "lp_cut_query_env ?vs ts"
 let ?ss = "lpc_return_eval ?eta (states!0)"
 have control: "lpp_check_finite_direct_control_contexts fuel P Q nds states contexts contexts Fs T returned arity actions"
   and ranked: "lpc_seg_ranked_control ranks Q" and source: "lp_cut_source_program P"
   and program: "lpp_check_finite_reachable_signature P signatures"
   and closed: "list_all (\<lambda>x. x\<noteq>None) actions" and nonempty: "nds\<noteq>[]"
   and signature: "(q,length modes)\<in>set signatures"
   and root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
   and state: "states!0=[(LPCGoals [LPCAtom (Fun (LPCUser q) (map Var ?vs))],map Var ?vs)]"
   and initial_context: "contexts!0=([],[],[])" and free: "Fs!0=[]"
   using checked by (auto simp: lpp_check_finite_direct_root_def)
 have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
   using root len by (auto simp: lp_cut_check_root_def)
 have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
 have initial: "lpp_finite_direct_invariant (set signatures) ?ss"
   using finite signature len
   by (simp add: state lpc_return_eval_def map_map o_def vals
     lpp_finite_direct_invariant_def lpp_finite_direct_state_def lpp_static_state_def)
 have grounded: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
   using ground by (simp only: vals)
 have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
   using root grounded by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
 have bounds: "0<length nds" "0<length states" "0<length contexts" "0<length Fs"
   using nonempty control by (auto simp: lpp_check_finite_direct_control_contexts_def)
 have rep: "lpp_stable_module_rep operation SP nds states contexts Fs ?ss [(lpcn_pred ?nd,ts)]"
   unfolding lpp_stable_module_rep_def lpp_stable_rep_def
   by (rule exI[of _ "[]"], rule exI[of _ 0], rule exI[of _ ?eta])
      (use bounds known in \<open>simp add: vals free initial_context lpc_free_knowledge_def
        lpp_stable_context_holds_def lpp_evaluation_context_holds_def\<close>)
 have sn: "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) {map fst ?ss}"
   by (rule lpp_finite_reachable_closed_control_SN[OF compatible control ranked transfer source program initial rep closed])
 show ?thesis using sn by (simp add: state lpc_return_eval_def map_map o_def vals)
qed

ML \<open>
val checked = [@{thm lpp_finite_direct_root_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct root" else ();
\<close>
end
