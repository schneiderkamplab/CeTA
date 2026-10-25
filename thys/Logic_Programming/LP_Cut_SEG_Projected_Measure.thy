theory LP_Cut_SEG_Projected_Measure
  imports LP_Cut_SEG_Projected_Captured LP_Cut_SEG_Measure
begin

text \<open>The existing structural template check also preserves finite
observations. Groundness of the unfiltered interface is not required.\<close>

lemma lpc_seg_projected_template_edge:
  fixes pi :: "'f lp_cut_symbol afs" and measure :: "('f lp_cut_symbol,'w) term"
  assumes checked: "lpc_seg_template_edge templates h b"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval h eta"
    and observed: "lp_iproject pi (lpc_seg_template_value templates a) measure"
  shows "lp_iproject pi (lpc_seg_template_value templates (lp_atom_eval b eta)) measure"
proof -
  have same: "lpc_seg_template_value templates (lp_atom_eval b eta) =
      lpc_seg_template_value templates (lp_atom_eval h eta)"
    using checked by (simp add: lpc_seg_template_edge_def lpc_seg_template_eval)
  show ?thesis unfolding same unified[symmetric] lpc_seg_template_subst
    by (rule lp_iproject_subst[OF observed])
qed

lemma lpc_seg_projected_template_step:
  fixes pi :: "'f lp_cut_symbol afs" and measure :: "('f lp_cut_symbol,'w) term"
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and step: "([a],gs)\<in>lp_ild Q"
  shows "fst a\<in>active \<and> (\<exists>b. gs=[b] \<and>
    (fst b\<in>active \<longrightarrow> lp_iproject pi (lpc_seg_template_value templates a) measure \<longrightarrow>
      lp_iproject pi (lpc_seg_template_value templates b) measure))"
proof -
  obtain c eta sigma where c: "c<length Q"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval (fst (Q!c)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!c))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!c))=1" and active: "fst (fst (Q!c))\<in>active"
    and edge: "fst (hd (snd (Q!c)))\<in>active \<longrightarrow>
      lpc_seg_template_edge templates (fst (Q!c)) (hd (snd (Q!c)))"
    using checked c by (auto simp: lpc_seg_template_program_on_def list_all_iff split_def)
  obtain b where body: "snd (Q!c)=[b]" using len by (cases "snd (Q!c)") auto
  have source: "fst a\<in>active"
    using active unified by (simp add: lp_iatom_subst_def lp_atom_eval_def prod_eq_iff)
  have retained: "lp_iproject pi (lpc_seg_template_value templates (lp_atom_eval b eta)) measure"
    if target: "fst b\<in>active" and pr: "lp_iproject pi (lpc_seg_template_value templates a) measure"
    by (rule lpc_seg_projected_template_edge[OF _ unified pr]) (use edge body target in simp)
  show ?thesis using source gs body retained by (auto simp: lp_atom_eval_def)
qed

lemma lpc_seg_projected_template_path:
  fixes pi :: "'f lp_cut_symbol afs" and measure :: "('f lp_cut_symbol,'w) term"
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and path: "([a],gs)\<in>(lp_ild Q)\<^sup>*"
    and observed: "lp_iproject pi (lpc_seg_template_value templates a) measure"
  shows "\<exists>b. gs=[b] \<and> (fst b\<in>active \<longrightarrow>
    lp_iproject pi (lpc_seg_template_value templates b) measure)"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case using observed by auto
next
  case (step ys zs)
  obtain b where ys: "ys=[b]" and known: "fst b\<in>active \<longrightarrow>
    lp_iproject pi (lpc_seg_template_value templates b) measure"
    using step.hyps by blast
  have edge: "([b],zs)\<in>lp_ild Q" using step.hyps(2) ys by simp
  show ?case using lpc_seg_projected_template_step[OF checked edge] known by blast
qed

end
