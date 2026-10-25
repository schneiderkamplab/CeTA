theory LP_Cut_SEG_Triple_Contracts
  imports LP_Cut_Return_Actual LP_Cut_Return_Modular LP_Dependency_Triple_Checker
begin

text \<open>Recursive call descent and successful answer coverage are different
relations. In particular, termination of the supporting success program is
not a premise. The local obligations below still have to be discharged by
checked source operations; this is not an executable source checker.\<close>

theorem lpc_return_contract_separate_descent:
  assumes descent: "SN_on D {a}"
    and represented: "rep ss a t ret"
    and local: "\<And>us b u out. rep us b u out \<Longrightarrow>
      (\<And>vs c v final. (b,c)\<in>D \<Longrightarrow> rep vs c v final \<Longrightarrow>
        lpc_return_contract P vs S v final) \<Longrightarrow>
      lpc_return_contract P us S u out"
  shows "lpc_return_contract P ss S t ret"
proof -
  have all: "\<forall>us u out. rep us b u out \<longrightarrow> lpc_return_contract P us S u out"
    if sn: "SN_on D {b}" for b
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix b us u out
    assume ih: "\<And>c. (b,c)\<in>D \<Longrightarrow>
      \<forall>vs v final. rep vs c v final \<longrightarrow> lpc_return_contract P vs S v final"
      and rep: "rep us b u out"
    show "lpc_return_contract P us S u out"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF descent] represented by blast
qed

text \<open>Both recursive Split children descend from the same parent call.
The continuation edge is required only for actual successful prefix answers,
and uses that very answer environment. A prefix that diverges is covered by
the first child, never by an invented success clause.\<close>

theorem lpc_return_split_separate_descent:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs c v out. (a,c)\<in>D \<Longrightarrow> rep vs c v out \<Longrightarrow>
      lpc_return_contract P vs S v out"
    and prefix_edge: "(a,b)\<in>D"
    and prefix_rep: "rep ss b t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      (t,ret eta)\<in>S\<^sup>* \<Longrightarrow> \<exists>c v.
      (a,c)\<in>D \<and> (ret eta,v)\<in>S\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] c v final"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) S t final"
proof -
  have prefix: "lpc_return_contract P ss S t ret"
    by (rule lower[OF prefix_edge prefix_rep])
  show ?thesis
  proof (rule lpc_return_contract_compose_actual[OF program prefix valid separated])
    fix eta assume actual: "lpc_actual_return P ss eta"
    have success: "(t,ret eta)\<in>S\<^sup>*"
      by (rule lpc_actual_return_residual[OF prefix actual])
    obtain c v where edge: "(a,c)\<in>D" and bridge: "(ret eta,v)\<in>S\<^sup>*"
      and rep: "rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] c v final"
      using continuation[OF actual success] by blast
    have child: "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] S v final"
      by (rule lower[OF edge rep])
    show "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] S (ret eta) final"
      by (rule lpc_return_contract_start[OF bridge child])
  qed
qed

lemma lpc_checked_triple_prefix_edge:
  assumes triple: "(h,ps,b)\<in>set D"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval h rho"
    and prefix: "((map (\<lambda>g. lp_atom_eval g rho) ps,rho),([],eta))
      \<in>(lp_seg_answer_step Q)\<^sup>*"
  shows "(a,lp_atom_eval b eta)\<in>lp_triple_calls (set D) Q"
  using assms unfolding lp_triple_calls_def by blast

theorem lpc_triples_source_contract:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lp_triple_pidp I J D Q outs fallback dnames pnames marks filters q n positions labs proofs"
    and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
    and represented: "rep ss (q,map (\<lambda>t. lp_ieval t LPIVar) ts) t ret"
    and local: "\<And>us a u out. rep us a u out \<Longrightarrow>
      (\<And>vs b v final. (a,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
        rep vs b v final \<Longrightarrow> lpc_return_contract P vs S v final) \<Longrightarrow>
      lpc_return_contract P us S u out"
  shows "lpc_return_contract P ss S t ret"
proof (rule lpc_return_contract_separate_descent[where D="lp_triple_calls (set D) Q"
    and rep=rep, OF _ represented])
  show "SN_on (lp_triple_calls (set D) Q) {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
    by (rule check_lp_triple_pidp_sound[OF I J checked len ground])
next
  fix us a u out
  assume rep: "rep us a u out"
    and lower: "\<And>vs b v final. (a,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      rep vs b v final \<Longrightarrow> lpc_return_contract P vs S v final"
  show "lpc_return_contract P us S u out" by (rule local[OF rep lower])
qed

end
