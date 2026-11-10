theory LP_Cut_Domain_SEG_Triple_Contracts
 imports Category_LP_Cut_Projected_Segment_Bridge.LP_Cut_Domain_SEG_Projected_Checker
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs Tree_Automata_Containment.entry

context cut_runtime_domain
begin

theorem precise_return_contract_separate_descent:
  assumes descent: "SN_on triples {a}"
    and represented: "rep ss a t ret"
    and local: "\<And>us b u out. rep us b u out \<Longrightarrow>
      (\<And>vs c v final. (b,c)\<in>triples \<Longrightarrow> rep vs c v final \<Longrightarrow>
        precise_return_contract P vs S v final) \<Longrightarrow>
      precise_return_contract P us S u out"
  shows "precise_return_contract P ss S t ret"
proof -
  have all: "\<forall>us u out. rep us b u out \<longrightarrow> precise_return_contract P us S u out"
    if sn: "SN_on triples {b}" for b
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix b us u out
    assume ih: "\<And>c. (b,c)\<in>triples \<Longrightarrow>
      \<forall>vs v final. rep vs c v final \<longrightarrow> precise_return_contract P vs S v final"
      and rep: "rep us b u out"
    show "precise_return_contract P us S u out"
      by (rule local[OF rep]) (use ih in blast)
  qed
  show ?thesis using all[OF descent] represented by blast
qed


theorem precise_return_split_separate_descent:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and lower: "\<And>vs c v out. (a,c)\<in>triples \<Longrightarrow> rep vs c v out \<Longrightarrow>
      precise_return_contract P vs S v out"
    and prefix_edge: "(a,b)\<in>triples"
    and prefix_rep: "rep ss b t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. precise_actual_return P ss eta \<Longrightarrow>
      (t,ret eta)\<in>S\<^sup>* \<Longrightarrow> \<exists>c v.
      (a,c)\<in>triples \<and> (ret eta,v)\<in>S\<^sup>* \<and>
      rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] c v final"
  shows "precise_return_contract P (lpc_attach_answers rest ss) S t final"
proof -
  have prefix: "precise_return_contract P ss S t ret"
    by (rule lower[OF prefix_edge prefix_rep])
  show ?thesis
  proof (rule precise_return_contract_compose_actual[OF program prefix valid separated])
    fix eta assume actual: "precise_actual_return P ss eta"
    have success: "(t,ret eta)\<in>S\<^sup>*"
      by (rule precise_actual_return_residual[OF prefix actual])
    obtain c v where edge: "(a,c)\<in>triples" and bridge: "(ret eta,v)\<in>S\<^sup>*"
      and rep: "rep [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] c v final"
      using continuation[OF actual success] by blast
    have child: "precise_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] S v final"
      by (rule lower[OF edge rep])
    show "precise_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] S (ret eta) final"
      by (rule precise_return_contract_start[OF bridge child])
  qed
qed


lemma precise_checked_triple_prefix_edge:
  assumes triple: "(h,ps,b)\<in>set triples"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval h rho"
    and prefix: "((map (\<lambda>g. lp_atom_eval g rho) ps,rho),([],eta))
      \<in>(lp_seg_answer_step Q)\<^sup>*"
  shows "(a,lp_atom_eval b eta)\<in>lp_triple_calls (set triples) Q"
  using assms unfolding lp_triple_calls_def by blast


theorem precise_triples_source_contract:
  fixes ts :: "(('g::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lp_triple_pidp I J triples Q outs fallback dnames pnames marks filters q n positions labs proofs"
    and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
    and represented: "rep ss (q,map (\<lambda>t. lp_ieval t LPIVar) ts) t ret"
    and local: "\<And>us a u out. rep us a u out \<Longrightarrow>
      (\<And>vs b v final. (a,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
        rep vs b v final \<Longrightarrow> precise_return_contract P vs S v final) \<Longrightarrow>
      precise_return_contract P us S u out"
  shows "precise_return_contract P ss S t ret"
proof (rule precise_return_contract_separate_descent[where triples="lp_triple_calls (set triples) Q"
    and rep=rep, OF _ represented])
  show "SN_on (lp_triple_calls (set triples) Q) {(q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
    by (rule check_lp_triple_pidp_sound[OF I J checked len ground])
next
  fix us a u out
  assume rep: "rep us a u out"
    and lower: "\<And>vs b v final. (a,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      rep vs b v final \<Longrightarrow> precise_return_contract P vs S v final"
  show "precise_return_contract P us S u out" by (rule local[OF rep lower])
qed


end
end
