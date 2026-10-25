theory LP_Cut_SEG_Regions
  imports LP_Cut_SEG_Rules LP_Cut_Return_Check
begin

text \<open>The virtual LP is only a finite local control-flow witness. Its
rank_of is checked directly; it is not the extracted termination obligation.
This allows the existing verified local source operations to be reused without
requiring a generated TRS rewrite for every administrative source transition.\<close>

definition lpc_seg_control_weight where
  "lpc_seg_control_weight rank_of gs = sum_list (map (\<lambda>a. Suc (rank_of (fst a))) gs)"

definition lpc_seg_ranked_control where
  "lpc_seg_ranked_control rank_of Q = list_all (\<lambda>(h,bs).
    lpc_seg_control_weight rank_of bs < Suc (rank_of (fst h))) Q"

lemma lpc_seg_control_subst[simp]:
  "lpc_seg_control_weight rank_of (map (\<lambda>a. lp_iatom_subst a sigma) gs) = lpc_seg_control_weight rank_of gs"
  by (simp add: lpc_seg_control_weight_def lp_iatom_subst_def map_map o_def split_def)

lemma lpc_seg_control_eval[simp]:
  "lpc_seg_control_weight rank_of (map (\<lambda>a. lp_atom_eval a eta) gs) = lpc_seg_control_weight rank_of gs"
  by (simp add: lpc_seg_control_weight_def lp_atom_eval_def map_map o_def split_def)

lemma lpc_seg_ranked_control_SN:
  assumes checked: "lpc_seg_ranked_control rank_of Q"
  shows "SN (lp_ild Q)"
proof -
  have decrease: "lpc_seg_control_weight rank_of ys < lpc_seg_control_weight rank_of xs"
    if step: "(xs,ys)\<in>lp_ild Q" for xs ys
    using step checked
    by (cases rule: lp_ild.cases)
      (auto simp: lpc_seg_ranked_control_def list_all_iff lpc_seg_control_weight_def
        lp_atom_eval_def lp_iatom_subst_def map_map o_def split_def)
  have subset: "lp_ild Q \<subseteq> (measure (lpc_seg_control_weight rank_of))\<inverse>"
    using decrease by auto
  have sn: "SN ((measure (lpc_seg_control_weight rank_of))\<inverse>)"
    by (simp add: SN_iff_wf)
  show ?thesis by (rule SN_subset[OF sn subset])
qed

theorem lpc_seg_auxiliary_contract:
  assumes finite: "SN_on L {a}"
    and represented: "rep ss a"
    and local: "\<And>us b. rep us b \<Longrightarrow>
      lpc_return_contract P us R t ret \<or>
      ((\<forall>event vs. lpc_answer_transition P us event vs \<longrightarrow>
         (\<exists>c. (b,c)\<in>L\<^sup>+ \<and> rep vs c)) \<and>
       (\<forall>rho vs. lpc_answer_transition P us (Some rho) vs \<longrightarrow> (t,ret rho)\<in>R\<^sup>*))"
  shows "lpc_return_contract P ss R t ret"
proof -
  have all: "\<forall>us. rep us b \<longrightarrow> lpc_return_contract P us R t ret"
    if sn: "SN_on L {b}" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>L\<^sup>+ \<Longrightarrow> \<forall>vs. rep vs c \<longrightarrow> lpc_return_contract P vs R t ret"
      and rep: "rep us b"
    show "lpc_return_contract P us R t ret"
    proof (cases "lpc_return_contract P us R t ret")
      case True then show ?thesis .
    next
      case False
      have edges: "\<And>event vs. lpc_answer_transition P us event vs \<Longrightarrow>
        \<exists>c. (b,c)\<in>L\<^sup>+ \<and> rep vs c"
        and answers: "\<And>rho vs. lpc_answer_transition P us (Some rho) vs \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
        using local[OF rep] False by blast+
      show ?thesis by (rule lpc_seg_primitive_contract) (use ih edges answers in blast)+
    qed
  qed
  show ?thesis using all[OF finite] represented by blast
qed

text \<open>Every local control node carries a finite template for the entry
measure. Templates use positional arguments, not source variable names. The
following check ensures that unification along a virtual control edge cannot
change an already ground entry measure. This check concerns control edges only;
return clauses are checked separately against extracted connection rules.\<close>

definition lpc_seg_template_value where
  "lpc_seg_template_value templates a = lp_ieval (templates (fst a))
    (\<lambda>i. if i<length (snd a) then snd a!i else LPIFun LPCTruth [])"

definition lpc_seg_template_term where
  "lpc_seg_template_term templates a = templates (fst a)\<cdot>
    (\<lambda>i. if i<length (snd a) then snd a!i else Fun LPCTruth [])"

lemma lpc_seg_template_eval:
  "lpc_seg_template_value templates (lp_atom_eval a eta) =
    lp_ieval (lpc_seg_template_term templates a) eta"
  by (simp add: lpc_seg_template_value_def lpc_seg_template_term_def
    lp_atom_eval_def lp_ieval_finite_subst; rule lp_ieval_cong; simp)

lemma lpc_seg_template_subst:
  "lpc_seg_template_value templates (lp_iatom_subst a sigma) =
    lp_isubst (lpc_seg_template_value templates a) sigma"
  by (simp add: lpc_seg_template_value_def lp_iatom_subst_def lp_ieval_subst;
    rule lp_ieval_cong; simp)

definition lpc_seg_template_edge where
  "lpc_seg_template_edge templates h b =
    (lpc_seg_template_term templates h = lpc_seg_template_term templates b)"

lemma lpc_seg_template_edge_preserves:
  assumes checked: "lpc_seg_template_edge templates h b"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval h eta"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
  shows "lpc_seg_template_value templates (lp_atom_eval b eta) =
    lpc_seg_template_value templates a"
proof -
  have same: "lpc_seg_template_value templates (lp_atom_eval b eta) =
      lpc_seg_template_value templates (lp_atom_eval h eta)"
    using checked by (simp add: lpc_seg_template_edge_def lpc_seg_template_eval)
  have unchanged: "lpc_seg_template_value templates (lp_atom_eval h eta) =
      lpc_seg_template_value templates a"
    unfolding unified[symmetric] lpc_seg_template_subst
    by (rule lp_seg_ground_subst[OF ground])
  show ?thesis using same unchanged by simp
qed

definition lpc_seg_template_program where
  "lpc_seg_template_program templates Q = list_all (\<lambda>(h,bs).
    length bs=1 \<and> lpc_seg_template_edge templates h (hd bs)) Q"

lemma lpc_seg_template_step:
  assumes checked: "lpc_seg_template_program templates Q"
    and step: "([a],gs)\<in>lp_ild Q"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
  shows "\<exists>b. gs=[b] \<and> lpc_seg_template_value templates b = lpc_seg_template_value templates a"
proof -
  obtain c eta sigma where c: "c<length Q"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval (fst (Q!c)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!c))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!c))=1"
    and edge: "lpc_seg_template_edge templates (fst (Q!c)) (hd (snd (Q!c)))"
    using checked c by (auto simp: lpc_seg_template_program_def list_all_iff split_def)
  obtain b where body: "snd (Q!c)=[b]" using len by (cases "snd (Q!c)") auto
  have same: "lpc_seg_template_value templates (lp_atom_eval b eta) = lpc_seg_template_value templates a"
    by (rule lpc_seg_template_edge_preserves[OF _ unified ground]) (use edge body in simp)
  show ?thesis using gs body same by auto
qed

lemma lpc_seg_template_path:
  assumes checked: "lpc_seg_template_program templates Q"
    and path: "([a],gs)\<in>(lp_ild Q)\<^sup>*"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
  shows "\<exists>b. gs=[b] \<and> lpc_seg_template_value templates b = lpc_seg_template_value templates a"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step ys zs)
  obtain b where ys: "ys=[b]" and same: "lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using step.hyps by blast
  have known: "lp_seg_ground (lpc_seg_template_value templates b)" using ground same by simp
  have edge: "([b],zs)\<in>lp_ild Q" using step.hyps(2) ys by simp
  obtain c where zs: "zs=[c]" and equal: "lpc_seg_template_value templates c = lpc_seg_template_value templates b"
    using lpc_seg_template_step[OF checked edge known] by blast
  show ?case using zs equal same by auto
qed

end
