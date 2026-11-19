theory LP_Cut_Domain_SEG_Triple_Certificate
 imports LP_Cut_Domain_SEG_Triple_Graph
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem precise_check_lpc_seg_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lpc_seg_triples I J fuel P triples Q roots blocks q modes chain_pred predicates constructors
      triples' Q' outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?p = "lpc_lookup fallback predicates"
  let ?d = "lpc_lookup fallback constructors"
  let ?us = "map (map_term ?d id) ts"
  let ?runtime = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  have graph: "lpc_triple_check_graph fuel P triples Q roots blocks q modes chain_pred"
    and child: "check_lp_triple_pidp I J triples' Q' outs fallback dnames pnames marks filters q' n positions labs proofs"
    and triples: "triples'=lp_roles_triples ?p ?d triples"
    and support: "Q'=lp_roles_program ?p ?d Q"
    and query: "q'=?p chain_pred" "n=length modes" "positions=lpc_positions modes"
    using checked by (auto simp: check_lpc_seg_triples_def Let_def)
  have length: "length ?us=n" using len query by simp
  have finite: "ground (?us!i)" if "i\<in>set positions" "i<n" for i
    using ground[of i] that len query by simp
  have sn: "SN_on (lp_triple_calls (set triples') Q')
      {(q',map (\<lambda>t. lp_ieval t LPIVar) ?us)}"
    by (rule check_lp_triple_pidp_sound[OF I J child length finite])
  have eval: "map_lp_iterm ?d id (lp_ieval t LPIVar)=lp_ieval (map_term ?d id t) LPIVar" for t
    by (simp add: lp_signature_eval)
  have mapped: "lp_roles_iatom ?p ?d (chain_pred,?runtime)=
      (q',map (\<lambda>t. lp_ieval t LPIVar) ?us)"
    by (simp add: lp_roles_iatom_def query eval map_map o_def)
  have source_calls: "SN_on (lp_triple_calls (set triples) Q) {(chain_pred,?runtime)}"
    by (rule lp_roles_triple_termination_reflect[where p="?p" and d="?d"])
      (use sn in \<open>simp only: triples support mapped\<close>)
  show ?thesis
  proof (rule precise_triple_graph_root_sound[OF graph source_calls])
    show "length ?runtime=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip ?runtime modes). b \<longrightarrow> lp_seg_ground t"
      using ground len
      by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
    show "list_all D ?runtime"
      by (auto simp: list_all_iff intro: valuation_domain variables)
  qed
qed


end
end
