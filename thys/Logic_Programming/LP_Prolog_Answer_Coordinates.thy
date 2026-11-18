theory LP_Prolog_Answer_Coordinates
 imports LP_Prolog_Domain_Invariant_Composition LP_Cut_Return_Preserved_Ground
begin

definition lpc_answer_coordinates where
 "lpc_answer_coordinates coordinates ss =
  list_all (\<lambda>row. list_all (\<lambda>(a,b). snd row a=snd row b) coordinates) ss"

lemma lpc_answer_coordinates_prune:
 "lpc_answer_coordinates coordinates ss \<Longrightarrow> lpc_answer_coordinates coordinates (lpc_answer_prune m ss)"
 by (induction ss) (auto simp: lpc_answer_coordinates_def split: prod.splits lp_cut_entry.splits)

lemma lpc_answer_coordinates_step:
 assumes step: "lpc_answer_transition P ss event tt"
 and invariant: "lpc_answer_coordinates coordinates ss"
 shows "lpc_answer_coordinates coordinates tt"
 using step invariant
 by (cases rule: lpc_answer_transition.cases)
  (auto simp: lpc_answer_coordinates_def list_all_iff
   dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpp_answer_coordinates_step:
 assumes step: "lpp_domain_answers P B U D ss event tt"
 and invariant: "lpc_answer_coordinates coordinates ss"
 shows "lpc_answer_coordinates coordinates tt"
proof -
 have base: "lpc_answer_transition P ss event tt \<Longrightarrow> lpc_answer_coordinates coordinates tt"
  by (rule lpc_answer_coordinates_step[OF _ invariant])
 have atomic: "lpc_answer_coordinates coordinates tt"
  if "lpp_answer_transition P B U ss event tt"
  using that invariant base
  by (cases rule: lpp_answer_transition.cases)
   (auto simp: lpc_answer_coordinates_def list_all_iff
    dest: lpc_answer_coordinates_step[unfolded lpc_answer_coordinates_def list_all_iff])
 show ?thesis using step invariant atomic by (auto simp: lpp_domain_answers_def)
qed

lemma lpp_answer_coordinates_reachable:
 assumes path: "(ss,tt)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
 and initial: "lpc_answer_coordinates coordinates ss"
 shows "lpc_answer_coordinates coordinates tt"
 using path initial
 by (induction rule: rtrancl_induct)
  (auto simp: lp_answer_steps_def intro: lpp_answer_coordinates_step)

lemma lpp_actual_answer_coordinates:
 assumes initial: "lpc_answer_coordinates coordinates ss"
 and actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
 shows "list_all (\<lambda>(a,b). rho a=rho b) coordinates"
proof -
 obtain us vs where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>*"
 and event: "lpp_domain_answers P B U D us (Some rho) vs"
  using actual by (auto simp: lp_actual_answer_def)
 have invariant: "lpc_answer_coordinates coordinates us"
  by (rule lpp_answer_coordinates_reachable[OF path initial])
 have shape: "us=(LPCGoals [],rho)#vs"
  using event by (auto simp: lpp_domain_answers_def dest: lpc_answer_event_is_success elim: lpp_answer_transition.cases)
 show ?thesis using invariant by (simp add: shape lpc_answer_coordinates_def)
qed

end
