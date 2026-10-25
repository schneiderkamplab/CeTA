theory LP_Cut_SEG_Projected_Control
  imports LP_Cut_SEG_Projected_Connection LP_Cut_SEG_Free_Context_Region
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

lemma lpc_seg_role_one:
  "lpc_seg_role_value 1 is_cont c d (LPIFun f ts) = LPIFun (c f) (map (map_lp_iterm d id) ts)"
proof -
  have one: "(1::nat)=Suc 0" by simp
  have mapped: "map (\<lambda>i. map_lp_iterm d id (ts!i)) [0..<length ts] = map (map_lp_iterm d id) ts"
    by (rule nth_equalityI) simp_all
  show ?thesis by (simp add: one mapped)
qed

lemma lpc_seg_role_projection_subst:
  fixes filtering :: "'g afs" and m :: "('g,string) term"
  assumes pr: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d v) m"
  shows "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lp_isubst v sigma)) m"
proof (cases v)
  case (LPIVar x)
  then show ?thesis using pr by (auto elim: lp_iproject.cases)
next
  case (LPIFun f ts)
  have commutes: "lpc_seg_role_value 1 is_cont c d (lp_isubst v sigma) =
    lp_isubst (lpc_seg_role_value 1 is_cont c d v) (\<lambda>x. map_lp_iterm d id (sigma x))"
    by (simp add: LPIFun lpc_seg_role_one map_map o_def lp_data_map_subst)
  show ?thesis unfolding commutes by (rule lp_iproject_subst[OF pr])
qed

lemma lpc_seg_template_predicate_step:
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and step: "([a],gs)\<in>lp_ild Q"
    and stable: "\<And>v sigma. J v \<Longrightarrow> J (lp_isubst v sigma)"
  shows "fst a\<in>active \<and> (\<exists>b. gs=[b] \<and>
    (fst b\<in>active \<longrightarrow> J (lpc_seg_template_value templates a) \<longrightarrow>
      J (lpc_seg_template_value templates b)))"
proof -
  obtain k eta sigma where k: "k<length Q"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval (fst (Q!k)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!k))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!k))=1" and active: "fst (fst (Q!k))\<in>active"
    and edge: "fst (hd (snd (Q!k)))\<in>active \<longrightarrow>
      lpc_seg_template_edge templates (fst (Q!k)) (hd (snd (Q!k)))"
    using checked k by (auto simp: lpc_seg_template_program_on_def list_all_iff split_def)
  obtain b where body: "snd (Q!k)=[b]" using len by (cases "snd (Q!k)") auto
  have source: "fst a\<in>active"
    using active unified by (simp add: lp_iatom_subst_def lp_atom_eval_def prod_eq_iff)
  have equal: "lpc_seg_template_value templates (lp_atom_eval b eta) =
    lp_isubst (lpc_seg_template_value templates a) sigma" if "fst b\<in>active"
  proof -
    have eq: "lpc_seg_template_term templates b=lpc_seg_template_term templates (fst (Q!k))"
      using edge body that by (simp add: lpc_seg_template_edge_def)
    show ?thesis by (simp only: lpc_seg_template_eval eq
      lpc_seg_template_eval[symmetric] unified[symmetric] lpc_seg_template_subst)
  qed
  show ?thesis using source gs body equal stable by (auto simp: lp_atom_eval_def)
qed

lemma lpc_seg_template_predicate_path:
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and path: "([a],gs)\<in>(lp_ild Q)\<^sup>*"
    and initial: "J (lpc_seg_template_value templates a)"
    and stable: "\<And>v sigma. J v \<Longrightarrow> J (lp_isubst v sigma)"
  shows "\<exists>b. gs=[b] \<and> (fst b\<in>active \<longrightarrow> J (lpc_seg_template_value templates b))"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case using initial by auto
next
  case (step ys zs)
  obtain b where ys: "ys=[b]" and known: "fst b\<in>active \<longrightarrow> J (lpc_seg_template_value templates b)"
    using step.hyps by blast
  have edge: "([b],zs)\<in>lp_ild Q" using step.hyps(2) ys by simp
  show ?case using lpc_seg_template_predicate_step[where J=J, OF checked edge stable] known by blast
qed

end
