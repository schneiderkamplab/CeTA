theory LP_Cut_SEG_Encoded_Emit
  imports LP_Cut_SEG_Roles LP_Cut_SEG_Control
begin

definition lpc_seg_check_encoded_emits where
  "lpc_seg_check_encoded_emits templates returned outp is_cont c d C R Q =
    list_all (\<lambda>(h,bs). length bs=1 \<and> (fst (hd bs)=returned \<longrightarrow>
      lpc_seg_check_encoded_pair 1 1 is_cont c d C R
        (lpc_seg_template_term templates h)
        (lpc_seg_template_term (\<lambda>_. outp) (hd bs)))) Q"

theorem lpc_seg_encoded_emit_path:
  fixes templates :: "'f lp_cut_symbol \<Rightarrow> ('f lp_cut_symbol,nat) term"
    and a :: "('f lp_cut_symbol,string) lp_iatom"
  assumes preserved: "lpc_seg_template_program_on active templates Q"
    and emits: "lpc_seg_check_encoded_emits templates returned outp is_cont c d C R Q"
    and not_returned: "fst a\<noteq>returned"
    and path: "([a],[(returned,outputs)])\<in>(lp_ild Q)\<^sup>*"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "(lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)),
    lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d
      (lpc_seg_template_value (\<lambda>_. outp) (returned,outputs))))\<in>qrstep False N R"
proof -
  obtain ys where prefix: "([a],ys)\<in>(lp_ild Q)\<^sup>*"
    and last: "(ys,[(returned,outputs)])\<in>lp_ild Q"
    using path not_returned by (cases rule: rtrancl.cases) auto
  obtain b where ys: "ys=[b]" and same: "fst b\<in>active \<longrightarrow>
    lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using lpc_seg_template_path_on[OF preserved prefix ground] by blast
  have edge: "([b],[(returned,outputs)])\<in>lp_ild Q" using last ys by simp
  have active: "fst b\<in>active" using lpc_seg_template_step_on[OF preserved edge] by blast
  have equal: "lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using same active by simp
  have finite: "lp_seg_ground (lpc_seg_template_value templates b)" using ground equal by simp
  obtain k eta sigma where k: "k<length Q"
    and unified: "lp_iatom_subst b sigma = lp_atom_eval (fst (Q!k)) eta"
    and out_shape: "[(returned,outputs)]=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!k))"
    using edge by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!k))=1"
    using emits k by (auto simp: lpc_seg_check_encoded_emits_def list_all_iff split_def)
  obtain rhs where body: "snd (Q!k)=[rhs]" using len by (cases "snd (Q!k)") auto
  have target: "lp_atom_eval rhs eta=(returned,outputs)" using out_shape body by simp
  have name: "fst rhs=returned" using target by (simp add: lp_atom_eval_def prod_eq_iff)
  let ?l = "lpc_seg_template_term templates (fst (Q!k))"
  let ?r = "lpc_seg_template_term (\<lambda>_. outp) rhs"
  have checked: "lpc_seg_check_encoded_pair 1 1 is_cont c d C R ?l ?r"
    using emits nth_mem[OF k] name body
    by (auto simp: lpc_seg_check_encoded_emits_def list_all_iff split_def)
  have lhs: "lp_ieval ?l eta = lpc_seg_template_value templates a"
  proof -
    have "lp_ieval ?l eta = lpc_seg_template_value templates (lp_atom_eval (fst (Q!k)) eta)"
      by (simp only: lpc_seg_template_eval)
    also have "... = lp_isubst (lpc_seg_template_value templates b) sigma"
      by (simp only: unified[symmetric] lpc_seg_template_subst)
    also have "... = lpc_seg_template_value templates b" by (rule lp_seg_ground_subst[OF finite])
    finally show ?thesis by (simp only: equal)
  qed
  have rhs: "lp_ieval ?r eta = lpc_seg_template_value (\<lambda>_. outp) (returned,outputs)"
    by (simp only: lpc_seg_template_eval[symmetric] target)
  have measured: "lp_seg_ground (lp_ieval ?l eta)" using ground lhs by simp
  show ?thesis using lpc_seg_checked_encoded_pair[OF checked measured range roots]
    by (simp only: lhs rhs)
qed

theorem lpc_seg_encoded_region_contract:
  fixes P :: "('f,string) lp_cut_program"
    and a :: "('f lp_cut_symbol,string) lp_iatom"
  assumes checked: "lpc_seg_check_control fuel P Q nds states returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and program: "lp_cut_source_program P"
    and represented: "lpc_return_module_rep nds states ss [a]"
    and preserved: "lpc_seg_template_program_on active templates Q"
    and emits: "lpc_seg_check_encoded_emits templates returned outp is_cont c d C R Q"
    and not_returned: "fst a\<noteq>returned"
    and finite: "lp_seg_ground (lpc_seg_template_value templates a)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      ([a],[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])\<in>(lp_ild Q)\<^sup>* \<Longrightarrow>
      lpc_return_contract P (lpc_return_eval eta (states!i)) (qrstep False N R)
        (lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
        (\<lambda>rho. lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d
          (lpc_seg_template_value (\<lambda>_. outp) (returned,map rho [0..<arity]))))"
  shows "lpc_return_contract P ss (qrstep False N R)
    (lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)))
    (\<lambda>rho. lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d
      (lpc_seg_template_value (\<lambda>_. outp) (returned,map rho [0..<arity]))))"
proof (rule lpc_seg_control_contract[OF checked ranked program represented boundary])
  fix rho
  assume path: "([a],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
  show "(lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value templates a)),
    lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d
      (lpc_seg_template_value (\<lambda>_. outp) (returned,map rho [0..<arity]))))\<in>(qrstep False N R)\<^sup>*"
    by (rule r_into_rtrancl[OF lpc_seg_encoded_emit_path[OF preserved emits not_returned path finite range roots]])
qed

end
