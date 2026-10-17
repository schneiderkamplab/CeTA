theory Relative_ADP_Bridge
  imports Relative_ADP_Lift_Dev.Relative_ADP_Lift
begin

lemma adp_defined_position_root_subterm:
  assumes q: "q \<in> adp_defined_positions D s"
  shows "[] \<in> adp_defined_positions D (s |_ q)"
proof -
  from q obtain f ts where q_poss: "q \<in> poss s"
    and at: "s |_ q = Fun f ts" and fD: "f \<in> D"
    unfolding adp_defined_positions_def by blast
  show ?thesis unfolding adp_defined_positions_def at using fD by simp
qed

lemma adp_defined_position_replace_below:
  assumes q: "q \<in> poss s"
    and c: "c \<in> adp_defined_positions D u"
  shows "q @ c \<in> adp_defined_positions D (replace_at s q u)"
proof -
  from c obtain f ts where c_poss: "c \<in> poss u"
    and at: "u |_ c = Fun f ts" and fD: "f \<in> D"
    unfolding adp_defined_positions_def by blast
  have q_after: "q \<in> poss (replace_at s q u)"
    by (rule replace_at_below_poss[OF q]) simp
  have qc_poss: "q @ c \<in> poss (replace_at s q u)"
    using q_after c_poss replace_at_subt_at[OF q] by simp
  have qc_at: "replace_at s q u |_ (q @ c) = Fun f ts"
    using subt_at_append[OF q_after] replace_at_subt_at[OF q] at by simp
  show ?thesis unfolding adp_defined_positions_def
    using qc_poss qc_at fD by blast
qed

lemma relative_root_origin_productive_imp_productive:
  assumes root: "relative_root_origin_productive R B D"
  shows "relative_origin_productive R B D"
  unfolding relative_origin_productive_def
proof (intro allI impI)
  fix s q
  assume q_defined: "q \<in> adp_defined_positions D s"
    and minimal: "s |_ q \<in> Tinf (relstep R B)"
  have q_poss: "q \<in> poss s"
    using q_defined unfolding adp_defined_positions_def by blast
  have local_root: "[] \<in> adp_defined_positions D (s |_ q)"
    by (rule adp_defined_position_root_subterm[OF q_defined])
  obtain u c where local_block:
      "relative_origin_block R B D (s |_ q) u [] [] c"
    and c_defined: "c \<in> adp_defined_positions D u"
    and c_minimal: "u |_ c \<in> Tinf (relstep R B)"
    by (rule relative_root_origin_productive_block[
          OF root minimal local_root])
  let ?t = "replace_at s q u"
  have local_at: "s |_ q = s |_ q" by simp
  have block: "relative_origin_block R B D s ?t q q (q @ c)"
    using relative_origin_block_context[OF local_block q_poss local_at] by simp
  have target_defined: "q @ c \<in> adp_defined_positions D ?t"
    by (rule adp_defined_position_replace_below[OF q_poss c_defined])
  have q_after: "q \<in> poss ?t"
    by (rule replace_at_below_poss[OF q_poss]) simp
  have target_minimal: "?t |_ (q @ c) \<in> Tinf (relstep R B)"
    using subt_at_append[OF q_after] replace_at_subt_at[OF q_poss] c_minimal
    by simp
  show "\<exists>u q'. relative_origin_block R B D s u q q q' \<and>
      q' \<in> adp_defined_positions D u \<and>
      u |_ q' \<in> Tinf (relstep R B)"
    by (rule exI[of _ ?t], rule exI[of _ "q @ c"])
       (rule conjI[OF block], rule conjI[OF target_defined target_minimal])
qed

theorem relative_root_origin_chain_criterion:
  assumes wf: "wf_trs (R \<union> B)"
    and root: "relative_root_origin_productive R B
      (adp_defined_symbols (R \<union> B))"
    and not_sn: "\<not> SN_rel (rstep R) (rstep B)"
  shows "\<not> adp_problem_SN (canonical_relative_adp_problem R B)"
  by (rule relative_origin_productive_chain_criterion[
        OF wf relative_root_origin_productive_imp_productive[OF root] not_sn])

end
