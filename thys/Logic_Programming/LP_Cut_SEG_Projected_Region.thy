theory LP_Cut_SEG_Projected_Region
  imports LP_Cut_SEG_Projected_Templates
begin

definition lpc_seg_check_projected_emits where
  "lpc_seg_check_projected_emits filtering templates returned outp is_cont c d R Q =
    list_all (\<lambda>(h,bs). length bs=1 \<and> (fst (hd bs)=returned \<longrightarrow>
      lpc_seg_check_projected_pair filtering 1 1 is_cont c d R
        (lpc_seg_template_term templates h)
        (lpc_seg_template_term (\<lambda>_. outp) (hd bs)))) Q"

theorem lpc_seg_projected_emit_path:
  fixes filtering :: "'g afs"
  assumes preserved: "lpc_seg_projected_template_program filtering is_cont c d active templates Q"
    and emits: "lpc_seg_check_projected_emits filtering templates returned outp is_cont c d R Q"
    and not_returned: "fst a\<noteq>returned"
    and path: "([a],[(returned,outputs)])\<in>(lp_ild Q)\<^sup>*"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))"
  shows "(lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a),
    lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value (\<lambda>_. outp) (returned,outputs)))
      \<in>lpc_seg_projected_rel filtering R"
proof -
  let ?J = "\<lambda>v m. lp_iproject filtering (lpc_seg_role_value 1 is_cont c d v) m"
  obtain m :: "('g,string) term" where initial: "?J (lpc_seg_template_value templates a) m"
    using observed by (auto simp: lpc_seg_has_projection_def)
  obtain ys where prefix: "([a],ys)\<in>(lp_ild Q)\<^sup>*"
    and last: "(ys,[(returned,outputs)])\<in>lp_ild Q"
    using path not_returned by (cases rule: rtrancl.cases) auto
  obtain b where ys: "ys=[b]" and known: "fst b\<in>active \<longrightarrow> ?J (lpc_seg_template_value templates b) m"
    using lpc_seg_projected_template_path[OF preserved prefix initial] by blast
  have edge: "([b],[(returned,outputs)])\<in>lp_ild Q" using last ys by simp
  have active: "fst b\<in>active" using lpc_seg_projected_template_step[OF preserved edge] by blast
  have pr: "?J (lpc_seg_template_value templates b) m" using known active by simp
  obtain k eta sigma where k: "k<length Q"
    and unified: "lp_iatom_subst b sigma = lp_atom_eval (fst (Q!k)) eta"
    and out_shape: "[(returned,outputs)]=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!k))"
    using edge by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!k))=1"
    using emits k by (auto simp: lpc_seg_check_projected_emits_def list_all_iff split_def)
  obtain rhs where body: "snd (Q!k)=[rhs]" using len by (cases "snd (Q!k)") auto
  have target: "lp_atom_eval rhs eta=(returned,outputs)" using out_shape body by simp
  have name: "fst rhs=returned" using target by (simp add: lp_atom_eval_def prod_eq_iff)
  let ?l = "lpc_seg_template_term templates (fst (Q!k))"
  let ?r = "lpc_seg_template_term (\<lambda>_. outp) rhs"
  have checked: "lpc_seg_check_projected_pair filtering 1 1 is_cont c d R ?l ?r"
    using emits nth_mem[OF k] name body
    by (auto simp: lpc_seg_check_projected_emits_def list_all_iff split_def)
  have lhs: "lp_ieval ?l eta = lp_isubst (lpc_seg_template_value templates b) sigma"
    by (simp only: lpc_seg_template_eval[symmetric] unified[symmetric] lpc_seg_template_subst)
  have left: "?J (lp_ieval ?l eta) m"
    unfolding lhs by (rule lpc_seg_role_projection_subst[OF pr])
  obtain n where right: "?J (lp_ieval ?r eta) n"
    and progress: "(m,n)\<in>rstep (af_rule filtering ` R)"
    by (rule lpc_seg_checked_projected_pair[OF checked left]) blast
  have rhs: "lp_ieval ?r eta=lpc_seg_template_value (\<lambda>_. outp) (returned,outputs)"
    by (simp only: lpc_seg_template_eval[symmetric] target)
  show ?thesis using initial right progress by (auto simp: lpc_seg_projected_rel_def rhs)
qed

theorem lpc_seg_projected_control_contract:
  assumes checked: "lpc_seg_free_check_control fuel P Q nds states Fs returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "lpc_return_free_module_rep nds states Fs ss [a]"
    and preserved: "lpc_seg_projected_template_program filtering is_cont c d active templates Q"
    and emits: "lpc_seg_check_projected_emits filtering templates returned outp is_cont c d R Q"
    and not_returned: "fst a\<noteq>returned"
    and observed: "lpc_seg_has_projection filtering (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a))"
    and out_vars: "vars_term outp \<subseteq> set [0..<arity]"
    and ambient: "lpc_seg_projection_context filtering A"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      ([a],[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      lpc_return_contract P (lpc_return_eval eta (states!i)) (lpc_seg_projected_rel filtering R)
        (A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
        (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
  shows "lpc_return_contract P ss (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
proof (rule lpc_seg_free_control_contract[OF checked ranked program represented boundary])
  fix rho assume path: "([a],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  have edge: "(lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a),
    lpc_seg_runtime_value is_cont c d outp rho)\<in>lpc_seg_projected_rel filtering R"
    using lpc_seg_projected_emit_path[OF preserved emits not_returned path observed]
    by (simp only: lpc_seg_output_template[OF out_vars] lpc_seg_runtime_value_def)
  show "(A (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)),
    A (lpc_seg_runtime_value is_cont c d outp rho))\<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
    by (rule r_into_rtrancl[OF lpc_seg_projection_context_step[OF ambient edge]])
qed

end
