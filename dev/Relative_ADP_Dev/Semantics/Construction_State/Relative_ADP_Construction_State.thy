theory Relative_ADP_Construction_State
  imports Relative_ADP_Root_Base_Carrier_Dev.Relative_ADP_Root_Base_Carrier
begin

definition relative_carrier_origin_state ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    ('f, 'v) mctxt \<Rightarrow> ('f, 'v) term list \<Rightarrow>
    nat list \<Rightarrow> pos list \<Rightarrow> ('f, 'v) term list \<Rightarrow> bool" where
  "relative_carrier_origin_state R B D s t C holes owners locations carriers
    \<longleftrightarrow>
    relative_context_origin_state R B D s t C holes \<and>
    carrier_cover holes owners locations carriers"

lemma initial_relative_carrier_origin_state:
  assumes fun_term: "is_Fun s"
    and defined: "[] \<in> adp_defined_positions D s"
  shows "relative_carrier_origin_state R B D s s
    (root_hole_mctxt s) (root_hole_terms s)
    (initial_carrier_owners (root_hole_terms s))
    (initial_carrier_locations (root_hole_terms s))
    (root_hole_terms s)"
  unfolding relative_carrier_origin_state_def
  using initial_relative_context_origin_state[OF fun_term defined]
    initial_carrier_cover by blast

lemma relative_carrier_origin_state_root_base:
  assumes state: "relative_carrier_origin_state R B D s t C holes
      owners locations carriers"
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
    relative_carrier_origin_state R B D s t' C' holes'
      (refined_carrier_owners owners parents)
      (refined_carrier_locations locations parents tails) carriers \<and>
    carrier_refinement holes' parents tails holes"
proof -
  from state have origin: "relative_context_origin_state R B D s t C holes"
    and cover: "carrier_cover holes owners locations carriers"
    unfolding relative_carrier_origin_state_def by blast+
  obtain parents tails where origin':
      "relative_context_origin_state R B D s t' C' holes'"
    and refinement: "carrier_refinement holes' parents tails holes"
    and cover': "carrier_cover holes'
      (refined_carrier_owners owners parents)
      (refined_carrier_locations locations parents tails) carriers"
    unfolding C'_def t'_def holes'_def
    using relative_root_base_carrier_transition[
      OF origin cover rule nondup p_context p_defined p_fun redex] by blast
  show ?thesis
    unfolding relative_carrier_origin_state_def
    using origin' refinement cover' by blast
qed

end
