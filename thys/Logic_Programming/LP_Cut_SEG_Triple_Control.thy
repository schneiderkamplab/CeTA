theory LP_Cut_SEG_Triple_Control
  imports LP_Cut_SEG_Triple_Contracts LP_Cut_SEG_Free_Control
begin

text \<open>The finite source-control table is checked independently of the
recursive triples. Its open boundaries must have a genuine triple-call edge
and a represented child. Internal administrative transitions are justified by
the finite control rank, not by pretending that they are strict DP steps.
Free-variable knowledge and cut-scope renaming are retained by the existing
source-control theorem.\<close>

theorem lpc_seg_triple_control_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_free_check_control fuel P C nds states Fs returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and program: "lp_cut_source_program P"
    and represented: "lpc_return_free_module_rep nds states Fs ss control"
    and lower: "\<And>vs b v out. (a,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      rep vs b v out \<Longrightarrow> lpc_return_contract P vs S v out"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      (control,[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild C)\<^sup>* \<Longrightarrow>
      \<exists>b v. (a,b)\<in>lp_triple_calls (set D) Q \<and> (t,v)\<in>S\<^sup>* \<and>
        rep (lpc_return_eval eta (states!i)) b v ret"
    and emit: "\<And>rho. (control,[(returned,map rho [0..<arity])])\<in>(lp_ild C)\<^sup>*
      \<Longrightarrow> (t,ret rho)\<in>S\<^sup>*"
  shows "lpc_return_contract P ss S t ret"
proof (rule lpc_seg_free_control_contract[OF checked ranked program represented _ emit])
  fix i eta
  assume index: "i<length nds" and boundary_node: "actions!i=None"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and path: "(control,[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild C)\<^sup>*"
  obtain b v where edge: "(a,b)\<in>lp_triple_calls (set D) Q"
    and bridge: "(t,v)\<in>S\<^sup>*"
    and rep: "rep (lpc_return_eval eta (states!i)) b v ret"
    using boundary[OF index boundary_node known free path] by blast
  have child: "lpc_return_contract P (lpc_return_eval eta (states!i)) S v ret"
    by (rule lower[OF edge rep])
  show "lpc_return_contract P (lpc_return_eval eta (states!i)) S t ret"
    by (rule lpc_return_contract_start[OF bridge child])
qed

end
