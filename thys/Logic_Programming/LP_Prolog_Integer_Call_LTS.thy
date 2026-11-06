theory LP_Prolog_Integer_Call_LTS
  imports LP_Prolog_Integer_Call_Formula LP_Prolog_Integer_Recurrence_LTS
begin

fun lpp_call_edge_shape where
  "lpp_call_edge_shape P views (from_loc,to_loc,recipe) =
    (lpp_arithmetic_call_shape P (fst (views from_loc)) (length (snd (views from_loc))) recipe \<and>
     fst (views to_loc)=lpp_call_target recipe \<and>
     length (snd (views to_loc))=length (lpp_call_outputs recipe))"

fun lpp_call_edge_transition where
  "lpp_call_edge_transition views (from_loc,to_loc,recipe) = Transition from_loc to_loc
    (lpp_call_formula recipe (snd (views from_loc)) (snd (views to_loc)))"

fun lpp_call_edge_recipe where
  "lpp_call_edge_recipe views (from_loc,to_loc,recipe) = (fst (views from_loc),recipe)"

definition lpp_call_state where
  "lpp_call_state views s = (fst (views (LTS.location s)),
    map (lpp_recurrence_state_values s) (snd (views (LTS.location s))))"

lemma lpp_call_lts_step:
  assumes rules: "transition_rules system=set (map (lpp_call_edge_transition views) call_edges)"
    and checked: "list_all (lpp_call_edge_shape P views) call_edges"
    and edge: "(s,t)\<in>LPPIntegerLTS.transition system"
  shows "(lpp_call_state views s,lpp_call_state views t)\<in>
    lpp_arithmetic_call_relation P (map (lpp_call_edge_recipe views) call_edges)"
proof -
  obtain phi gamma where rule: "Transition (LTS.location s) (LTS.location t) phi\<in>transition_rules system"
    and source: "IA4.assignment (valuation s)" and target: "IA4.assignment (valuation t)"
    and local_typed: "IA4.assignment gamma"
    and satisfies: "IA4.satisfies (LPPIntegerLTS.pre_post_inter (valuation s) (valuation t) gamma) phi"
    using edge by (auto elim!: LPPIntegerLTS.mem_transitionE)
  obtain from_loc to_loc recipe where member: "(from_loc,to_loc,recipe)\<in>set call_edges"
    and source_loc: "LTS.location s=from_loc" and target_loc: "LTS.location t=to_loc"
    and formula: "phi=lpp_call_formula recipe (snd (views from_loc)) (snd (views to_loc))"
    using rule rules by (auto split: prod.splits)
  have shape: "lpp_arithmetic_call_shape P (fst (views from_loc)) (length (snd (views from_loc))) recipe"
    and target_predicate: "fst (views to_loc)=lpp_call_target recipe"
    and lengths: "length (snd (views to_loc))=length (lpp_call_outputs recipe)"
    using checked member by (auto simp: list_all_iff)
  let ?delta = "LPPIntegerLTS.pre_post_inter (valuation s) (valuation t) gamma"
  have typed: "IA4.assignment ?delta" using source target local_typed by simp
  have project: "(\<lambda>x. IA.to_int (?delta (x,IA.IntT))) =
      lpp_trans_integer (lpp_recurrence_state_values s) (lpp_recurrence_state_values t)
        (\<lambda>x. IA.to_int (gamma (x,IA.IntT)))"
    by (rule ext, rename_tac x, case_tac x) (simp_all add: lpp_recurrence_state_values_def)
  have observed: "IA4.satisfies (lpp_integer_assignment
      (lpp_trans_integer (lpp_recurrence_state_values s) (lpp_recurrence_state_values t)
        (\<lambda>x. IA.to_int (gamma (x,IA.IntT)))))
      (lpp_call_formula recipe (snd (views from_loc)) (snd (views to_loc)))"
    using satisfies formula lpp_call_formula_arbitrary_valuation[OF typed,
      where r=recipe and input_coordinates="snd (views from_loc)" and output_coordinates="snd (views to_loc)"]
    by (simp only: project)
  have holds: "lpp_arithmetic_call_holds recipe (map (lpp_recurrence_state_values s) (snd (views from_loc)))"
    and output_values: "map (lpp_recurrence_state_values t) (snd (views to_loc))=
      lpp_arithmetic_call_outputs recipe (map (lpp_recurrence_state_values s) (snd (views from_loc)))"
    using observed lpp_call_formula_exact[OF lengths, where before="lpp_recurrence_state_values s"
      and after="lpp_recurrence_state_values t" and middle="\<lambda>x. IA.to_int (gamma (x,IA.IntT))"
      and input_coordinates="snd (views from_loc)"] by blast+
  have recipe_member: "(fst (views from_loc),recipe)\<in>set (map (lpp_call_edge_recipe views) call_edges)"
    using member by force
  show ?thesis using shape target_predicate holds output_values recipe_member
    by (auto simp: lpp_call_state_def lpp_arithmetic_call_relation_def source_loc target_loc
      intro!: exI[of _ recipe])
qed

lemma lpp_call_lts_initial_nontermination:
  assumes rules: "transition_rules system=set (map (lpp_call_edge_transition views) call_edges)"
    and checked: "list_all (lpp_call_edge_shape P views) call_edges"
    and child: "\<not>LPPIntegerLTS.lts_termination system"
  shows "\<exists>s\<in>LPPIntegerLTS.initial_states system.
    \<not>SN_on (lpp_arithmetic_call_relation P (map (lpp_call_edge_recipe views) call_edges))
      {lpp_call_state views s}"
proof -
  obtain s where initial: "s\<in>LPPIntegerLTS.initial_states system"
    and no: "\<not>SN_on (LPPIntegerLTS.transition system) {s}"
    using child unfolding SN_on_def by blast
  let ?R = "lpp_arithmetic_call_relation P (map (lpp_call_edge_recipe views) call_edges)"
  let ?rep = "\<lambda>s q. q=lpp_call_state views s"
  have simulate: "\<exists>v. ?rep b v \<and> (u,v)\<in>?R\<^sup>+"
    if "(a,b)\<in>LPPIntegerLTS.transition system" "?rep a u" for a b u
    using lpp_call_lts_step[OF rules checked that(1)] that(2) by (auto intro: r_into_trancl)
  have projected: "\<not>SN_on ?R {lpp_call_state views s}"
    by (rule lp_source_nontermination_simulation[where rep="?rep", OF no _ simulate]) simp
  show ?thesis using initial projected by blast
qed

ML \<open>
val checked = [@{thm lpp_call_lts_step}, @{thm lpp_call_lts_initial_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic call LTS dependency" else ();
\<close>
end
