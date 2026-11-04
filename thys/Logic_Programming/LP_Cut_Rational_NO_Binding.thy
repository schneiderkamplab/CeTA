theory LP_Cut_Rational_NO_Binding
  imports LP_Cut_Rational_NO_Trace LP_Cut_NO_Certificate
begin

lemma lpc_rational_binding_call_step:
  assumes binding: "lpc_check_rational_binding fuel G anchors x binding_term r"
    and call: "lp_rational_match fuel G [(x,r)] a i"
  shows "(lp_cut_state_eval (LPCGoals [LPCUnify (Var x) binding_term,LPCAtom a]#before) LPIVar,
    lpc_rational_state G [LPCGoals [LPCAtom i]] @ lp_cut_state_eval before LPIVar)
    \<in> lp_cut_mgu_source P"
proof -
  have actual: "lpc_mgu_unify (LPIVar x) (lp_ieval binding_term LPIVar)
    [LPCAtom (lp_ieval a LPIVar)] (lpc_graph_binding G x r)"
    by (rule lpc_checked_rational_binding_mgu[OF binding])
  have evaluated: "lp_isubst (lp_ieval a LPIVar) (lpc_graph_binding G x r)=
    lp_rational_graph_value G LPIVar i"
    using lp_rational_match_sound[OF call, of LPIVar]
    by (simp add: lp_ieval_subst lpc_graph_binding_environment)
  show ?thesis using lp_cut_mgu_source.unify[OF actual, of "lp_cut_state_eval before LPIVar" P]
    by (simp add: lp_cut_state_map_def evaluated)
qed

definition lpc_rational_check_source where
  "lpc_rational_check_source fuel G anchors P q modes argv x binding_term r a i before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     lpc_no_trace fuel P [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       (LPCGoals [LPCUnify (Var x) binding_term,LPCAtom a]#before) \<and>
     lpc_check_rational_binding fuel G anchors x binding_term r \<and>
     lp_rational_match fuel G [(x,r)] a i \<and>
     steps\<noteq>[] \<and> list_all (\<lambda>x. lpc_no_suffix_safe (snd x)) steps \<and>
     lpc_rational_trace fuel G P [LPCGoals [LPCAtom i]] steps
       ([LPCGoals [LPCAtom i]]@after))"

theorem lpc_rational_check_source_sound:
  assumes checked: "lpc_rational_check_source fuel G anchors P q modes argv x binding_term r a i before after initial_steps steps"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_cut_mgu_source P)
      {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
proof -
  let ?start = "lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar"
  let ?bound = "lp_cut_state_eval (LPCGoals [LPCUnify (Var x) binding_term,LPCAtom a]#before) LPIVar"
  let ?loop = "lpc_rational_state G [LPCGoals [LPCAtom i]]@lp_cut_state_eval before LPIVar"
  have initial_steps: "(?start,?bound)\<in>(lp_cut_mgu_source P)\<^sup>*"
    by (rule lpc_no_trace_sound[where fuel=fuel and steps=initial_steps])
      (use checked in \<open>simp add: lpc_rational_check_source_def\<close>)
  have bind: "(?bound,?loop)\<in>lp_cut_mgu_source P"
    by (rule lpc_rational_binding_call_step)
      (use checked in \<open>auto simp: lpc_rational_check_source_def\<close>)
  have reach: "(?start,?loop)\<in>(lp_cut_mgu_source P)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF initial_steps bind])
  have pump: "\<not>SN_on (lp_cut_mgu_source P) {?loop}"
    by (rule lpc_rational_trace_pump)
      (use checked in \<open>auto simp: lpc_rational_check_source_def\<close>)
  have no: "\<not>SN_on (lp_cut_mgu_source P) {?start}"
  proof
    assume sn: "SN_on (lp_cut_mgu_source P) {?start}"
    have included: "{?loop}\<subseteq>(lp_cut_mgu_source P)\<^sup>* `` {?start}"
      using reach by auto
    show False using SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]] pump by contradiction
  qed
  show ?thesis using checked no by (simp add: lpc_rational_check_source_def)
qed

ML \<open>
val checked = [@{thm lpc_rational_check_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational NO source dependency" else ();
\<close>
end
