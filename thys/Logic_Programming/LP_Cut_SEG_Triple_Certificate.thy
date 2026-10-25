theory LP_Cut_SEG_Triple_Certificate
  imports LP_Cut_SEG_Triple_Graph LP_Dependency_Triple_Checker LP_Cut_Return_Module_Certificate
begin

definition check_lpc_seg_triples where
  "check_lpc_seg_triples I J fuel P D Q roots blocks q modes chain_pred predicates constructors
      D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs =
    (lpc_triple_check_graph fuel P D Q roots blocks q modes chain_pred \<and>
      (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
        D'=lp_roles_triples p d D \<and> Q'=lp_roles_program p d Q \<and>
        q' = p chain_pred \<and> n=length modes \<and> positions=lpc_positions modes \<and>
        check_lp_triple_pidp I J D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs))"

theorem check_lpc_seg_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lpc_seg_triples I J fuel P D Q roots blocks q modes chain_pred predicates constructors
      D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?p = "lpc_lookup fallback predicates"
  let ?d = "lpc_lookup fallback constructors"
  let ?us = "map (map_term ?d id) ts"
  let ?runtime = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  have graph: "lpc_triple_check_graph fuel P D Q roots blocks q modes chain_pred"
    and child: "check_lp_triple_pidp I J D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs"
    and triples: "D'=lp_roles_triples ?p ?d D"
    and support: "Q'=lp_roles_program ?p ?d Q"
    and query: "q'=?p chain_pred" "n=length modes" "positions=lpc_positions modes"
    using checked by (auto simp: check_lpc_seg_triples_def Let_def)
  have length: "length ?us=n" using len query by simp
  have finite: "ground (?us!i)" if "i\<in>set positions" "i<n" for i
    using ground[of i] that len query by simp
  have sn: "SN_on (lp_triple_calls (set D') Q')
      {(q',map (\<lambda>t. lp_ieval t LPIVar) ?us)}"
    by (rule check_lp_triple_pidp_sound[OF I J child length finite])
  have eval: "map_lp_iterm ?d id (lp_ieval t LPIVar)=lp_ieval (map_term ?d id t) LPIVar" for t
    by (simp add: lp_signature_eval)
  have mapped: "lp_roles_iatom ?p ?d (chain_pred,?runtime)=
      (q',map (\<lambda>t. lp_ieval t LPIVar) ?us)"
    by (simp add: lp_roles_iatom_def query eval map_map o_def)
  have source_calls: "SN_on (lp_triple_calls (set D) Q) {(chain_pred,?runtime)}"
    by (rule lp_roles_triple_termination_reflect[where p="?p" and d="?d"])
      (use sn in \<open>simp only: triples support mapped\<close>)
  show ?thesis
  proof (rule lpc_triple_graph_root_sound[OF graph source_calls])
    show "length ?runtime=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip ?runtime modes). b \<longrightarrow> lp_seg_ground t"
      using ground len
      by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  qed
qed

end
