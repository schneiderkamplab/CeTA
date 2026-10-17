theory Relative_ADP_Root_Base_Carrier
  imports Relative_ADP_Concrete_Refinement_Dev.Relative_ADP_Concrete_Refinement
begin

lemma relative_root_base_carrier_transition:
  assumes state: "relative_context_origin_state R B D s t C holes"
    and cover: "carrier_cover holes owners locations carriers"
    and rule: "(l, r) \<in> B"
    and nondup: "vars_term_ms r \<subseteq># vars_term_ms l"
    and p_context: "p \<in> poss_mctxt C"
    and p_defined: "p \<in> adp_defined_positions D t"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
  defines "C' \<equiv> mreplace_at C p (rhs_origin_mctxt l r p C)"
    and "t' \<equiv> replace_at t p (r \<cdot> sigma)"
    and "holes' \<equiv> unfill_holes
      (mreplace_at C p (rhs_origin_mctxt l r p C))
      (replace_at t p (r \<cdot> sigma))"
  shows "\<exists>parents tails.
    relative_context_origin_state R B D s t' C' holes' \<and>
    carrier_refinement holes' parents tails holes \<and>
    carrier_cover holes'
      (refined_carrier_owners owners parents)
      (refined_carrier_locations locations parents tails) carriers"
proof -
  have origin': "relative_context_origin_state R B D s t' C' holes'"
    unfolding C'_def t'_def holes'_def
    by (rule relative_context_origin_state_root_base[
          OF state rule nondup p_context p_defined p_fun redex])
  from state have length: "num_holes C = length holes"
    and source: "fill_holes C holes = t"
    unfolding relative_context_origin_state_def by blast+
  obtain parents tails where refinement:
    "carrier_refinement holes' parents tails holes"
    unfolding C'_def t'_def holes'_def
    using concrete_carrier_refinement_exists[
      OF nondup length source p_context redex] by blast
  have cover': "carrier_cover holes'
      (refined_carrier_owners owners parents)
      (refined_carrier_locations locations parents tails) carriers"
    by (rule carrier_cover_refinement[OF cover refinement])
  show ?thesis using origin' refinement cover' by blast
qed

end
