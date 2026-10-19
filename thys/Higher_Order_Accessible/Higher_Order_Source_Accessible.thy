theory Higher_Order_Source_Accessible
  imports Higher_Order_Candidate_Neutral
begin

definition ho_accessible_arguments where
  "ho_accessible_arguments rank S V B t = (case ho_typeof S V B t of
    Some (HBase b) \<Rightarrow> (case ho_application_head t of HConst c \<Rightarrow>
      {(T,v). v\<in>set (ho_spine_arguments t) \<and> ho_typeof S V B v=Some T \<and>
        ho_positive_type rank (rank b) T}
      | _ \<Rightarrow> {})
    | _ \<Rightarrow> {})"

locale ho_source_accessible_reducibility = ho_source_neutral_reducibility S V R B
  for S V :: "ho_type list" and R :: "ho_rule list" and B :: "ho_type list" +
  fixes rank :: "nat \<Rightarrow> nat"
begin

sublocale access: ho_accessible_reducibility "ho_step S V R B" HApp
    "\<lambda>A t. ho_typeof S V B t=Some A" rank "ho_accessible_arguments rank S V B"
proof unfold_locales
  fix b t T v assume ty: "ho_typeof S V B t=Some (HBase b)"
    and av: "(T,v)\<in>ho_accessible_arguments rank S V B t"
  show "ho_positive_type rank (rank b) T"
    using av by (auto simp: ho_accessible_arguments_def ty split: ho_term.splits)
qed

abbreviation source_candidate where
  "source_candidate \<equiv> source.candidate_computable access.accessible_candidates"

lemma source_candidate_closed:
  "access.accessible_candidates b t \<Longrightarrow> ho_step S V R B t u \<Longrightarrow>
    access.accessible_candidates b u"
  by (rule access.accessible_candidates_reduction)

lemma source_candidate_base_neutral:
  assumes ty: "ho_typeof S V B t=Some (HBase b)" and neu: "ho_source_neutral t"
    and reducts: "\<And>u. ho_step S V R B t u \<Longrightarrow> access.accessible_candidates b u"
  shows "access.accessible_candidates b t"
proof (rule access.accessible_candidates_neutral[OF ty _ reducts])
  show "ho_accessible_arguments rank S V B t={}"
    using neu by (auto simp: ho_accessible_arguments_def ho_source_neutral_def split: option.splits ho_type.splits ho_term.splits)
qed

lemma source_candidate_neutral:
  "ho_typeof S V B t=Some A \<Longrightarrow> ho_source_neutral t \<Longrightarrow>
    (\<And>u. ho_step S V R B t u \<Longrightarrow> source_candidate A u) \<Longrightarrow> source_candidate A t"
  by (rule source_neutral.candidate_neutral_computable[OF source_candidate_closed source_candidate_base_neutral])

lemma source_candidate_reduction:
  "source_candidate A t \<Longrightarrow> ho_step S V R B t u \<Longrightarrow> source_candidate A u"
  by (rule source.candidate_reduction[OF source_candidate_closed])

lemma source_candidate_reductions:
  "(ho_step S V R B)\<^sup>*\<^sup>* t u \<Longrightarrow> source_candidate A t \<Longrightarrow> source_candidate A u"
  by (rule source.candidate_reductions[OF source_candidate_closed])

lemma source_candidate_free:
  "ho_lookup V n=Some A \<Longrightarrow> source_candidate A (HFree n)"
  by (rule source_candidate_neutral)
     (auto simp: ho_source_neutral_def source_free_irreducible)

lemma source_candidate_bound:
  "ho_lookup B n=Some A \<Longrightarrow> source_candidate A (HBound n)"
  by (rule source_candidate_neutral)
     (auto simp: ho_source_neutral_def source_bound_irreducible)

lemma source_candidate_accessible:
  assumes ct: "source_candidate (HBase b) t"
    and av: "(T,v)\<in>ho_accessible_arguments rank S V B t"
  shows "source_candidate T v"
proof -
  have "access.accessible_candidates b t" using ct by simp
  then show ?thesis by (rule access.accessible_candidates_accessible[OF _ av])
qed

end

end
