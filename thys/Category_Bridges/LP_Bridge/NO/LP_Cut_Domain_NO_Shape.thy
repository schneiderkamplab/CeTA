theory LP_Cut_Domain_NO_Shape
  imports LP_Cut_Domain_NO_Source LP_Cut_Back_Representation
begin

definition cut_program_shape :: "('f,'v) lp_cut_program \<Rightarrow> bool" where
  "cut_program_shape P \<longleftrightarrow> (\<forall>(h,bs)\<in>set P.
    cut_fatom_shape h \<and> list_all (cut_goal_shape cut_fatom_shape) bs)"
lemma cut_encoded_head_shape[simp]: "cut_fatom_shape (cut_head h)"
  by (cases h) simp
lemma cut_encoded_program_shape:
  "cut_program_shape (cut_program P)"
  by (auto simp: cut_program_shape_def cut_program_def list_all_iff split: logic_atom.splits)
lemma cut_program_shape_nth:
  "cut_program_shape P \<Longrightarrow> c<length P \<Longrightarrow>
    cut_fatom_shape (fst (P!c)) \<and> list_all (cut_goal_shape cut_fatom_shape) (snd (P!c))"
  by (auto simp: cut_program_shape_def case_prod_unfold dest: nth_mem)
lemma cut_back_program_length[simp]: "length (cut_program_back P) = length P"
  by (simp add: cut_program_back_def)
lemma cut_back_program_nth:
  "c<length P \<Longrightarrow> cut_program_back P!c =
    (cut_fatom_back (fst (P!c)),map cut_fgoal_back (snd (P!c)))"
  by (simp add: cut_program_back_def split: prod.splits)
lemma cut_program_forward_back:
  "cut_program_shape P \<Longrightarrow> cut_program (cut_program_back P) = P"
  unfolding cut_program_shape_def cut_program_back_def cut_program_def
  by (auto simp: map_map o_def list_all_iff split_def
      intro!: map_idI intro: cut_fatom_forward_back cut_fgoal_forward_back;
      fastforce intro: cut_fatom_forward_back cut_fgoal_forward_back)
lemma cut_back_slice:
  "cut_program_shape P \<Longrightarrow>
    logic_slice (cut_program_back P) f n = lp_cut_slice P (LPCUser f) n"
  using cut_slice[of "cut_program_back P" f n] cut_program_forward_back by metis

context cut_runtime_domain
begin

lemma no_step_shape:
  assumes program: "cut_program_shape P"
    and shape: "list_all (cut_choice_shape cut_iatom_shape) s"
    and step: "(s,t)\<in>mgu_source P"
  shows "list_all (cut_choice_shape cut_iatom_shape) t"
proof -
  have body: "cut_goal_shape cut_fatom_shape g"
    if "c<length P" "g\<in>set (snd (P!c))" for c g
    using cut_program_shape_nth[OF program that(1)] that(2) by (simp add: list_all_iff)
  show ?thesis using step shape
    by (cases rule: mgu_source.cases)
      (auto simp: list_all_iff intro: cut_goal_eval_bind_shape cut_goal_subst_shape body
        dest: cut_admin_shape[unfolded list_all_iff] cut_lower_shape[unfolded list_all_iff])
qed

lemma no_run_shape:
  fixes sequence :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes program: "cut_program_shape P"
    and start: "list_all (cut_choice_shape cut_iatom_shape) (sequence 0)"
    and steps: "\<And>n. (sequence n,sequence (Suc n))\<in>mgu_source P"
  shows "list_all (cut_choice_shape cut_iatom_shape) (sequence n)"
  by (induct n) (rule start, rule no_step_shape[OF program _ steps], assumption)

end
end
