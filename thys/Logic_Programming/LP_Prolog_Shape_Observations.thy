theory LP_Prolog_Shape_Observations
  imports LP_Prolog_Inline_Shape_Return LP_Prolog_Evaluation_Comparison
begin

fun lpp_shape_observation_fact where
  "lpp_shape_observation_fact G shape x (LPPOShape H s t) =
    (G=H \<and> (case lp_return_shape_facts 16 G s t of None \<Rightarrow> False
      | Some facts \<Rightarrow> (shape,x)\<in>set facts))"
| "lpp_shape_observation_fact G shape x _ = False"

lemma lpp_shape_observation_fact_sound:
  assumes checked: "lpp_shape_observation_fact G shape x observation"
    and observed: "lpp_evaluation_observation_holds E eta observation"
  shows "lp_return_shape_holds G shape (eta x)"
proof (cases observation)
  case (LPPOShape H s t)
  have same: "G=H" and held: "lp_return_shape_holds G s (lp_ieval t eta)"
    using checked observed LPPOShape by auto
  have valid: "lp_return_facts_valid G eta (lp_return_shape_facts 16 G s t)"
    by (rule lp_return_shape_facts_sound[OF held])
  show ?thesis using checked valid LPPOShape
    by (auto simp: lp_return_facts_valid_def lp_return_shape_known_def split: option.splits)
qed (use checked in auto)

fun lpp_shape_seed_check where
  "lpp_shape_seed_check G ground_vars (facts,guards,observations) seeds =
    list_all (\<lambda>(shape,x). shape=LPReturnAny \<or>
      (shape=LPReturnGround \<and> x\<in>set ground_vars \<union> lpp_observations_ground observations) \<or>
      list_ex (lpp_shape_observation_fact G shape x) observations) seeds"

lemma lpp_shape_seed_check_sound:
  assumes checked: "lpp_shape_seed_check G ground_vars context seeds"
    and known: "\<forall>x\<in>set ground_vars. lp_seg_ground (eta x)"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP context eta"
  shows "lp_return_shape_known G seeds eta"
proof -
  obtain facts guards observations where ctx: "context=(facts,guards,observations)"
    by (cases "context") auto
  have finite: "\<forall>x\<in>lpp_observations_ground observations. lp_seg_ground (eta x)"
    using lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
    by (simp add: ctx)
  have observations: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) observations"
    using observed by (simp add: ctx lpp_evaluation_context_holds_def)
  have each: "lp_return_shape_holds G shape (eta x)"
    if member: "(shape,x)\<in>set seeds" for shape x
  proof -
    have alternatives: "shape=LPReturnAny \<or>
      (shape=LPReturnGround \<and> x\<in>set ground_vars \<union> lpp_observations_ground observations) \<or>
      (\<exists>observation\<in>set observations. lpp_shape_observation_fact G shape x observation)"
      using checked member by (fastforce simp: ctx list_all_iff list_ex_iff)
    show ?thesis using alternatives known finite observations
      by (auto simp: lp_return_ground_exact list_all_iff
        intro: lp_return_shape_holds.any dest: lpp_shape_observation_fact_sound)
  qed
  show ?thesis using each by (auto simp: lp_return_shape_known_def)

qed

fun lpp_context_add_shapes where
  "lpp_context_add_shapes (facts,guards,observations) G outputs =
    (facts,guards,observations @ map (\<lambda>(shape,x). LPPOShape G shape (Var x)) outputs)"

lemma lpp_evaluation_add_shapes_sound:
  assumes observed: "lpp_evaluation_context_holds E SP context eta"
    and known: "lp_return_shape_known G outputs eta"
  shows "lpp_evaluation_context_holds E SP (lpp_context_add_shapes context G outputs) eta"
  using observed known by (cases "context")
    (auto simp: lpp_evaluation_context_holds_def list_all_iff lp_return_shape_known_def)

end
