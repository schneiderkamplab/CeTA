theory LP_Cut_SEG_Emit
  imports LP_Cut_SEG_Finite
begin

definition lpc_seg_check_emits where
  "lpc_seg_check_emits templates returned outp R Q = list_all (\<lambda>(h,bs).
    length bs=1 \<and> (fst (hd bs)=returned \<longrightarrow>
      (let l=lpc_seg_template_term templates h;
           r=lpc_seg_template_term (\<lambda>_. outp) (hd bs) in
        (l,r)\<in>R \<and> vars_term r \<subseteq> vars_term l))) Q"

theorem lpc_seg_emit_path:
  fixes templates :: "'f lp_cut_symbol \<Rightarrow> ('f lp_cut_symbol,nat) term"
    and a :: "('f lp_cut_symbol,string) lp_iatom"
  assumes preserved: "lpc_seg_template_program_on active templates Q"
    and emits: "lpc_seg_check_emits templates returned outp R Q"
    and not_returned: "fst a\<noteq>returned"
    and path: "([a],[(returned,outputs)])\<in>(lp_ild Q)\<^sup>*"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
    and normal: "\<forall>s\<lhd>lpc_seg_finite_value (lpc_seg_template_value templates a). s\<in>NF_terms N"
  shows "(lpc_seg_finite_value (lpc_seg_template_value templates a),
    lpc_seg_finite_value (lpc_seg_template_value (\<lambda>_. outp) (returned,outputs)))\<in>qrstep False N R"
proof -
  obtain ys where prefix: "([a],ys)\<in>(lp_ild Q)\<^sup>*"
    and last: "(ys,[(returned,outputs)])\<in>lp_ild Q"
    using path not_returned by (cases rule: rtrancl.cases) auto
  obtain b where ys: "ys=[b]" and same: "fst b\<in>active \<longrightarrow>
    lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using lpc_seg_template_path_on[OF preserved prefix ground] by blast
  have edge: "([b],[(returned,outputs)])\<in>lp_ild Q" using last ys by simp
  have source_active: "fst b\<in>active" using lpc_seg_template_step_on[OF preserved edge] by blast
  have same': "lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using same source_active by simp
  have b_ground: "lp_seg_ground (lpc_seg_template_value templates b)" using ground same' by simp
  obtain c eta sigma where c: "c<length Q"
    and unified: "lp_iatom_subst b sigma = lp_atom_eval (fst (Q!c)) eta"
    and out_shape: "[(returned,outputs)]=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!c))"
    using edge by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!c))=1"
    using emits c by (auto simp: lpc_seg_check_emits_def list_all_iff split_def)
  obtain rhs where body: "snd (Q!c)=[rhs]" using len by (cases "snd (Q!c)") auto
  have target: "lp_atom_eval rhs eta=(returned,outputs)" using out_shape body by simp
  have name: "fst rhs=returned" using target by (simp add: lp_atom_eval_def prod_eq_iff)
  let ?l = "lpc_seg_template_term templates (fst (Q!c))"
  let ?r = "lpc_seg_template_term (\<lambda>_. outp) rhs"
  have local: "length (snd (Q!c))=1 \<and> (fst (hd (snd (Q!c)))=returned \<longrightarrow>
    (let l=lpc_seg_template_term templates (fst (Q!c));
         r=lpc_seg_template_term (\<lambda>_. outp) (hd (snd (Q!c))) in
      (l,r)\<in>R \<and> vars_term r \<subseteq> vars_term l))"
    using emits nth_mem[OF c] unfolding lpc_seg_check_emits_def list_all_iff split_def by blast
  have rule: "(?l,?r)\<in>R" and vars: "vars_term ?r \<subseteq> vars_term ?l"
    using local name body by (auto simp: Let_def)
  have left: "lp_ieval ?l eta = lpc_seg_template_value templates a"
  proof -
    have "lp_ieval ?l eta = lpc_seg_template_value templates (lp_atom_eval (fst (Q!c)) eta)"
      by (simp only: lpc_seg_template_eval)
    also have "... = lp_isubst (lpc_seg_template_value templates b) sigma"
      by (simp only: unified[symmetric] lpc_seg_template_subst)
    also have "... = lpc_seg_template_value templates b" by (rule lp_seg_ground_subst[OF b_ground])
    finally show ?thesis by (simp only: same')
  qed
  have right: "lp_ieval ?r eta = lpc_seg_template_value (\<lambda>_. outp) (returned,outputs)"
    by (simp only: lpc_seg_template_eval[symmetric] target)
  have finite: "lp_seg_ground (lp_ieval ?l eta)" using ground left by simp
  have proper: "\<forall>s\<lhd>lpc_seg_finite_value (lp_ieval ?l eta). s\<in>NF_terms N" using normal left by simp
  show ?thesis using lpc_seg_finite_root_values[OF rule vars finite proper] by (simp only: left right)
qed

end
