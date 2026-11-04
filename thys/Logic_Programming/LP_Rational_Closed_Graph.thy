theory LP_Rational_Closed_Graph
  imports LP_Rational_Graph_Equations LP_Equation_Congruence
begin

text \<open>A closed rational graph has no runtime variables. This is distinct
from finite groundness: its unfolding can have an infinite constructor spine.
Closure permits exact NO-side matching without treating graph size as a norm.\<close>
definition lp_rational_graph_closed where
  "lp_rational_graph_closed G = (lp_rational_graph_valid G \<and>
    (\<forall>n\<in>set G. \<not>lpr_is_external n))"

lemma lp_rational_closed_model_environment:
  assumes closed: "lp_rational_graph_closed G"
    and model: "lp_rational_graph_model G rho eta"
  shows "lp_rational_graph_model G theta eta"
  using assms by (auto simp: lp_rational_graph_closed_def lp_rational_graph_model_def
    dest!: nth_mem split: lp_rational_node.splits)

lemma lp_rational_closed_value_environment:
  assumes "lp_rational_graph_closed G" "i<length G"
  shows "lp_rational_graph_value G rho i=lp_rational_graph_value G theta i"
  by (rule lp_rational_graph_model_unique[where rho=theta,
      OF _ lp_rational_closed_model_environment[OF assms(1) lp_rational_graph_value_model]
        lp_rational_graph_value_model assms(2)])
    (use assms in \<open>simp add: lp_rational_graph_closed_def\<close>)

lemma lp_rational_closed_value_subst:
  assumes "lp_rational_graph_closed G" "i<length G"
  shows "lp_isubst (lp_rational_graph_value G rho i) sigma=lp_rational_graph_value G rho i"
proof -
  have valid: "lp_rational_graph_valid G" using assms(1)
    by (simp add: lp_rational_graph_closed_def)
  show ?thesis
    by (simp only: lp_rational_graph_value_subst[OF valid assms(2)]
      lp_rational_closed_value_environment[OF assms])
qed

lemma lp_rational_closed_not_finite:
  "lp_rational_graph_closed [LPRBranch f [0]] \<and>
    \<not>lp_seg_ground (lp_rational_graph_value [LPRBranch f [0]] rho 0)"
  by (simp add: lp_rational_graph_closed_def lp_rational_graph_valid_def
      lp_rational_graph_self_cycle_not_finite)

ML \<open>
val checked = [@{thm lp_rational_closed_value_subst}, @{thm lp_rational_closed_not_finite}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm lp_rational_graph_model_unique}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn name => not (member (op =) inherited name)) (oracles checked)
  then error "Untrusted closed rational graph dependency" else ();
\<close>
end
