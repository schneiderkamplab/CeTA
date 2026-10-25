theory LP_Cut_SEG_Projected_Templates
  imports LP_Cut_SEG_Projected_Control
begin

definition lpc_seg_projected_template_edge where
  "lpc_seg_projected_template_edge filtering is_cont c d templates h b =
    (let l=lpc_seg_template_term templates h; r=lpc_seg_template_term templates b in
      lpc_seg_role_shape 1 is_cont l \<and> lpc_seg_role_shape 1 is_cont r \<and>
      af_term filtering (lpc_seg_role_term 1 is_cont c d l) =
      af_term filtering (lpc_seg_role_term 1 is_cont c d r))"

definition lpc_seg_projected_template_program where
  "lpc_seg_projected_template_program filtering is_cont c d active templates Q =
    list_all (\<lambda>(h,bs). fst h\<in>active \<and> length bs=1 \<and>
      (fst (hd bs)\<in>active \<longrightarrow> lpc_seg_projected_template_edge filtering is_cont c d templates h (hd bs))) Q"

definition lpc_seg_check_projected_templates where
  "lpc_seg_check_projected_templates filtering is_cont c d entries Q =
    (distinct (map fst entries) \<and>
      list_all (\<lambda>(f,vs,t). distinct vs \<and> vars_term t\<subseteq> set vs) entries \<and>
      lpc_seg_projected_template_program filtering is_cont c d (set (map fst entries)) (lpc_seg_templates entries) Q)"

lemma lpc_seg_projected_template_lookup_valid:
  assumes checked: "lpc_seg_check_projected_templates filtering is_cont c d entries Q"
    and lookup: "map_of entries f=Some (vs,t)"
  shows "distinct vs \<and> vars_term t\<subseteq> set vs"
  using checked map_of_SomeD[OF lookup]
  by (auto simp: lpc_seg_check_projected_templates_def list_all_iff)

lemma lpc_seg_projected_equal_eval:
  fixes m :: "('g,string) term"
  assumes pr: "lp_iproject filtering (lp_ieval l eta) m"
    and eq: "af_term filtering l=af_term filtering r"
  shows "lp_iproject filtering (lp_ieval r eta) m"
proof -
  have each: "lp_iproject filtering (eta x) (lp_projection filtering (eta x)::('g,string) term)"
    if "x\<in>vars_term (af_term filtering r)" for x
  proof -
    have member: "x\<in>vars_term (af_term filtering l)" using that eq by simp
    obtain n :: "('g,string) term" where n: "lp_iproject filtering (eta x) n"
      using lp_iproject_ieval_variables[OF pr member] by blast
    show ?thesis using n lp_projection_eq[OF n] by simp
  qed
  show ?thesis using lp_iproject_ieval_forward[OF each] lp_iproject_ieval_inverse[OF pr] eq by simp
qed

lemma lpc_seg_projected_template_step:
  fixes m :: "('g,string) term"
  assumes checked: "lpc_seg_projected_template_program filtering is_cont c d active templates Q"
    and step: "([a],gs)\<in>lp_ild Q"
  shows "fst a\<in>active \<and> (\<exists>b. gs=[b] \<and>
    (fst b\<in>active \<longrightarrow>
      lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)) m \<longrightarrow>
      lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates b)) m))"
proof -
  obtain k eta sigma where k: "k<length Q"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval (fst (Q!k)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!k))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!k))=1" and active: "fst (fst (Q!k))\<in>active"
    and edge: "fst (hd (snd (Q!k)))\<in>active \<longrightarrow>
      lpc_seg_projected_template_edge filtering is_cont c d templates (fst (Q!k)) (hd (snd (Q!k)))"
    using checked k by (auto simp: lpc_seg_projected_template_program_def list_all_iff split_def)
  obtain b where body: "snd (Q!k)=[b]" using len by (cases "snd (Q!k)") auto
  have source: "fst a\<in>active"
    using active unified by (simp add: lp_iatom_subst_def lp_atom_eval_def prod_eq_iff)
  have target: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates (lp_atom_eval b eta))) m"
    if act: "fst b\<in>active"
      and pr: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)) m"
  proof -
    let ?l="lpc_seg_template_term templates (fst (Q!k))"
    let ?r="lpc_seg_template_term templates b"
    have ls: "lpc_seg_role_shape 1 is_cont ?l" and rs: "lpc_seg_role_shape 1 is_cont ?r"
      and eq: "af_term filtering (lpc_seg_role_term 1 is_cont c d ?l)=af_term filtering (lpc_seg_role_term 1 is_cont c d ?r)"
      using edge body act by (auto simp: lpc_seg_projected_template_edge_def Let_def)
    have raw: "lp_ieval ?l eta=lp_isubst (lpc_seg_template_value templates a) sigma"
      by (simp only: lpc_seg_template_eval[symmetric] unified[symmetric] lpc_seg_template_subst)
    have left: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lp_ieval ?l eta)) m"
      unfolding raw by (rule lpc_seg_role_projection_subst[OF pr])
    have right: "lp_iproject filtering (lp_ieval (lpc_seg_role_term 1 is_cont c d ?r) (\<lambda>x. map_lp_iterm d id (eta x))) m"
      by (rule lpc_seg_projected_equal_eval[OF left[unfolded lpc_seg_role_eval[OF ls]] eq])
    show ?thesis by (simp only: lpc_seg_template_eval lpc_seg_role_eval[OF rs]) (rule right)
  qed
  show ?thesis using source gs body target by (auto simp: lp_atom_eval_def)
qed

lemma lpc_seg_projected_template_path:
  fixes m :: "('g,string) term"
  assumes checked: "lpc_seg_projected_template_program filtering is_cont c d active templates Q"
    and path: "([a],gs)\<in>(lp_ild Q)\<^sup>*"
    and initial: "lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)) m"
  shows "\<exists>b. gs=[b] \<and> (fst b\<in>active \<longrightarrow>
    lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates b)) m)"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case using initial by auto
next
  case (step ys zs)
  obtain b where ys: "ys=[b]" and known: "fst b\<in>active \<longrightarrow>
    lp_iproject filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates b)) m"
    using step.hyps by blast
  have edge: "([b],zs)\<in>lp_ild Q" using step.hyps(2) ys by simp
  show ?case using lpc_seg_projected_template_step[OF checked edge] known by blast
qed

end
