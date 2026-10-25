theory LP_Cut_Return_Triples
  imports LP_Cut_Return_Certificate LP_Dependency_Triple_Chains
begin

text \<open>A checked source graph exposes its residual program and triples.
  The source and query are checked by the existing return-table extraction;
  the child obligation is the successful-prefix triple-call relation, not
  ordinary termination of the underlying TRS. Predicate and data encodings
  remain separate, and the original query groundness is not strengthened.\<close>

theorem lpc_return_root_triples_sound:
  fixes ts :: "('a lp_cut_symbol,string) term list"
    and p d :: "'a lp_cut_symbol \<Rightarrow> 'b"
  assumes checked: "lpc_return_check_root fuel P Q nds states returned arity acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_triple_calls (set (lp_dependency_triples (lp_roles_program p d Q)))
        (lp_roles_program p d Q))
        {(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpc_return_root_sound[where p=p and d=d, OF checked len ground])
  fix us :: "('b,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  show "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule lp_triple_calls_imply_source_termination[OF child[OF length gr]])
qed

end
