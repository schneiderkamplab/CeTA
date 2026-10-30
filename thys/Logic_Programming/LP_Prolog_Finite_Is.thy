theory LP_Prolog_Finite_Is
 imports LP_Prolog_Finite_Evaluation
begin

text \<open>Scalar unification uses the same most-general unifier contract as
the shared cut-aware equality step. Inspecting a scalar does not traverse a
possibly rational left-hand term.\<close>
fun lpp_scalar_unifier where
  "lpp_scalar_unifier (LPIVar x) f = Some (LPIVar(x:=LPIFun (LPCUser f) []))"
| "lpp_scalar_unifier (LPIFun g ts) f =
    (if g=LPCUser f \<and> ts=[] then Some LPIVar else None)"

lemma lpp_scalar_unifier_sound:
  "lpp_scalar_unifier a f=Some mu \<Longrightarrow> lp_isubst a mu=LPIFun (LPCUser f) []"
  by (cases a) (auto split: if_splits)

lemma lpp_scalar_unifier_complete:
  "lpp_scalar_unifier a f=None \<longleftrightarrow> \<not>(\<exists>sigma. lp_isubst a sigma=LPIFun (LPCUser f) [])"
  by (cases a) (auto split: if_splits)

lemma lpp_scalar_unifier_most_general:
  assumes chosen: "lpp_scalar_unifier a f=Some mu"
    and unifies: "lp_isubst a sigma=LPIFun (LPCUser f) []"
  shows "lp_isubst (mu x) sigma=sigma x"
  using chosen unifies by (cases a) (auto split: if_splits)

lemma lpp_scalar_unifier_mgu:
  assumes chosen: "lpp_scalar_unifier a f=Some mu"
  shows "lpc_mgu_unify a (LPIFun (LPCUser f) []) gs mu"
proof (unfold lpc_mgu_unify_def, intro conjI allI impI)
  show "lp_isubst a mu=lp_isubst (LPIFun (LPCUser f) []) mu"
    using lpp_scalar_unifier_sound[OF chosen] by simp
next
  fix tau assume unified: "lp_isubst a tau=lp_isubst (LPIFun (LPCUser f) []) tau"
  have solution: "lp_isubst a tau=LPIFun (LPCUser f) []" using unified by simp
  have factor: "(\<lambda>x. lp_isubst (mu x) tau)=tau"
    by (rule ext, rule lpp_scalar_unifier_most_general[OF chosen solution])
  show "\<exists>delta. lp_isubst (lp_isubst a mu) delta=lp_isubst a tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t mu) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
    by (rule exI[of _ tau]) (simp add: lpc_isubst_comp factor)
qed

definition lpp_finite_is_outcome where
  "lpp_finite_is_outcome a e outcome =
    (if \<exists>n. lpp_integer_evaluation e n then lpp_integer_is_outcome a e outcome
     else lp_seg_ground e \<and> (outcome=LPPBuiltinError \<or>
       (\<exists>f. outcome=(case lpp_scalar_unifier a f of None \<Rightarrow> LPPBuiltinFailure
          | Some mu \<Rightarrow> LPPBuiltinSuccess mu))))"

lemma lpp_finite_is_integer:
  "lpp_integer_evaluation e n \<Longrightarrow>
    lpp_finite_is_outcome a e outcome = lpp_integer_is_outcome a e outcome"
  by (auto simp: lpp_finite_is_outcome_def)

lemma lpp_finite_is_total:
  "lp_seg_ground e \<Longrightarrow> \<exists>outcome. lpp_finite_is_outcome a e outcome"
proof -
  assume ground: "lp_seg_ground e"
  show ?thesis
  proof (cases "\<exists>n. lpp_integer_evaluation e n")
    case True
    then obtain n where evaluated: "lpp_integer_evaluation e n" by blast
    have "lpp_integer_is_outcome a e (case lpp_integer_unifier a n of
      None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu)"
      by (simp only: lpp_integer_is_outcome_exact[OF evaluated])
    then show ?thesis by (simp only: lpp_finite_is_integer[OF evaluated]; blast)
  next
    case False
    have "lpp_finite_is_outcome a e LPPBuiltinError"
      by (simp add: lpp_finite_is_outcome_def False ground)
    then show ?thesis by blast
  qed
qed

lemma lpp_finite_is_success_evidence:
  fixes a e :: "(string lp_cut_symbol,'v) lp_iterm"
  assumes outcome: "lpp_finite_is_outcome a e (LPPBuiltinSuccess mu)"
  shows "lpp_finite_evaluation_result e (lp_isubst a mu) \<and> lp_isubst e mu=e"
proof (cases "\<exists>n. lpp_integer_evaluation e n")
  case True
  then obtain n where evaluated: "lpp_integer_evaluation e n" by blast
  have old: "lpp_integer_is_outcome a e (LPPBuiltinSuccess mu)"
    using outcome by (simp only: lpp_finite_is_integer[OF evaluated])
  show ?thesis using lpp_integer_is_success_evidence[OF old]
    by (simp only: lpp_finite_evaluation_integer[OF evaluated])
next
  case False
  obtain f where ground: "lp_seg_ground e" and chosen: "lpp_scalar_unifier a f=Some mu"
    using outcome False by (auto simp: lpp_finite_is_outcome_def split: option.splits)
  show ?thesis using lpp_scalar_unifier_sound[OF chosen]
    by (simp add: lpp_finite_evaluation_result_def False lp_seg_ground_subst[OF ground] ground)
qed

end
