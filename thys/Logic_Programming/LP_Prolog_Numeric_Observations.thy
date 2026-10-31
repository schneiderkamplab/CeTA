theory LP_Prolog_Numeric_Observations
  imports LP_Ground_Equations LP_Return_Shape_Facts LP_Prolog_Finite_Comparison LP_Prolog_Numeric_Guards LP_Prolog_Integer_Test_Check LP_Cut_SEG_Triple_Prefix
begin

text \<open>Numeric observations travel with the shared active return frame.
These facts describe successful operations; they do not justify evaluating a
future operation or erase its finite-domain obligation. Their substitution
closure permits ordinary shared unification and helper return transport.\<close>

datatype 'v lpp_numeric_observation =
    LPPOGround "(string lp_cut_symbol,'v) term"
  | LPPOEquation "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPOShape "string lp_cut_symbol lp_return_grammar" lp_return_shape "(string lp_cut_symbol,'v) term"
  | LPPOInteger "(string lp_cut_symbol,'v) term"
  | LPPOEvaluation "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPOComparison lpp_integer_comparison "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

fun lpp_numeric_observation_holds where
  "lpp_numeric_observation_holds eta (LPPOGround t) = lp_seg_ground (lp_ieval t eta)"
| "lpp_numeric_observation_holds eta (LPPOEquation a b) = (lp_ieval a eta=lp_ieval b eta)"
| "lpp_numeric_observation_holds eta (LPPOShape G shape t) = lp_return_shape_holds G shape (lp_ieval t eta)"
| "lpp_numeric_observation_holds eta (LPPOInteger t) = lpp_is_integer (lp_ieval t eta)"
| "lpp_numeric_observation_holds eta (LPPOEvaluation e t) = lpp_integer_result (lp_ieval e eta) (lp_ieval t eta)"
| "lpp_numeric_observation_holds eta (LPPOComparison comparison a b) =
    lpp_finite_compare_outcome comparison (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar)"

lemma lpp_integer_result_subst:
  fixes e t :: "(string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  shows "lpp_integer_result e t \<Longrightarrow> lpp_integer_result (lp_isubst e sigma) (lp_isubst t sigma)"
proof -
  assume result: "lpp_integer_result e t"
  obtain n where evaluated: "lpp_integer_evaluation e n" and result_value: "t=lpp_integer_value n"
    using result by (auto simp: lpp_integer_result_def)
  have stable: "lp_isubst e sigma=e" by (rule lpp_integer_evaluation_subst[OF evaluated])
  show ?thesis using result by (simp add: stable result_value lpp_integer_result_def)
qed

lemma lpp_integer_comparison_success_subst:
  fixes a b :: "(string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes success: "lpp_integer_compare_outcome comparison a b (LPPBuiltinSuccess LPIVar)"
  shows "lpp_integer_compare_outcome comparison (lp_isubst a sigma) (lp_isubst b sigma) (LPPBuiltinSuccess LPIVar)"
proof -
  obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
    using success by (auto simp: lpp_integer_compare_outcome_def)
  show ?thesis using success by (simp only: lpp_integer_evaluation_subst[OF left]
    lpp_integer_evaluation_subst[OF right])
qed

lemma lpp_numeric_observation_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  shows "lpp_numeric_observation_holds eta observation \<Longrightarrow>
    lpp_numeric_observation_holds (\<lambda>x. lp_isubst (eta x) sigma) observation"
  by (cases observation) (auto simp: lp_ieval_subst[symmetric] lp_seg_ground_subst intro: lpp_is_integer_subst
    lpp_integer_result_subst lpp_finite_comparison_subst lp_seg_ground_subst lp_return_shape_subst)

lemma lpp_numeric_observations_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  shows "list_all (lpp_numeric_observation_holds eta) observations \<Longrightarrow>
    list_all (lpp_numeric_observation_holds (\<lambda>x. lp_isubst (eta x) sigma)) observations"
  by (auto simp: list_all_iff intro: lpp_numeric_observation_subst)

lemma lpp_integer_test_emits:
  "lpp_integer_test_outcome a (LPPBuiltinSuccess LPIVar) \<Longrightarrow> lpp_is_integer a"
  by (auto simp: lpp_integer_test_outcome_def split: if_splits)

lemma lpp_integer_is_emits:
  "lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) (LPPBuiltinSuccess sigma) \<Longrightarrow>
    lpp_numeric_observation_holds (\<lambda>x. lp_isubst (eta x) sigma) (LPPOEvaluation e a)"
  by (auto simp: lp_ieval_subst[symmetric] dest: lpp_integer_is_success_evidence)

lemma lpp_integer_comparison_emits:
  "lpp_integer_compare_outcome comparison (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess LPIVar) \<Longrightarrow>
    lpp_numeric_observation_holds eta (LPPOComparison comparison a b)"
  by (auto intro: lpp_integer_comparison_finite)

text \<open>Reuse the shared saved-answer transport theorem for ordinary LP
steps; builtin success updates only the active environment, while failure and
uncaught error retain no new fact in the saved alternatives.\<close>

lemma lpp_answer_substitution_property:
  assumes stable: "\<And>eta sigma. F eta \<Longrightarrow> F (\<lambda>x. lp_isubst (eta x) sigma)"
    and step: "lpp_answer_transition P B U ss event us"
    and known: "list_all (\<lambda>e. F (snd e)) ss"
  shows "list_all (\<lambda>e. F (snd e)) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> F eta)"
  using step
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis by (rule lpc_answer_substitution_property[where F=F, OF stable base(2) known])
qed (use known in \<open>auto simp: list_all_iff intro: stable\<close>)+

lemma lpp_numeric_return_observations:
  fixes ss :: "((string lp_cut_symbol,string) lp_iterm lp_cut_entry *
    ('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list"
  assumes step: "lpp_answer_transition P B U ss event us"
    and known: "list_all (\<lambda>frame. list_all (lpp_numeric_observation_holds (snd frame)) observations) ss"
  shows "list_all (\<lambda>frame. list_all (lpp_numeric_observation_holds (snd frame)) observations) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> list_all (lpp_numeric_observation_holds eta) observations)"
  by (rule lpp_answer_substitution_property[OF lpp_numeric_observations_subst step known])

ML \<open>
val checked = [@{thm lpp_numeric_observations_subst}, @{thm lpp_integer_test_emits},
  @{thm lpp_integer_is_emits}, @{thm lpp_integer_comparison_emits},
  @{thm lpp_numeric_return_observations}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric observation dependency" else ();
\<close>
end
