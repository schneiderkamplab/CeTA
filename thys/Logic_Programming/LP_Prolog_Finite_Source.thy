theory LP_Prolog_Finite_Source
 imports LP_Prolog_Finite_Is LP_Prolog_Ground_Disequality
begin

text \<open>This is an interpretation of the existing parameterized source
transition, with a larger evaluation domain. It agrees exactly with the previous
interpretation on its checked domain. It does not define a second execution
relation or a replacement evaluation graph.\<close>

definition lpp_finite_source_builtin where
  "lpp_finite_source_builtin f ts outcome =
    (if f=''2:is'' then length ts=2 \<and> lpp_finite_is_outcome (ts!0) (ts!1) outcome
     else if f=lpp_disequality_predicate then length ts=2 \<and> lpp_ground_disequality_outcome (ts!0) (ts!1) outcome
     else lpp_integer_source_builtin f ts outcome)"

definition lpp_finite_source_domain where
  "lpp_finite_source_domain f ts =
    (if f=''2:is'' then length ts=2 \<and> lp_seg_ground (ts!1)
     else if f=lpp_disequality_predicate then length ts=2 \<and> lp_seg_ground (ts!0) \<and> lp_seg_ground (ts!1)
     else lpp_integer_source_domain f ts)"

lemma lpp_finite_source_legacy:
  "f\<noteq>''2:is'' \<Longrightarrow> f\<noteq>lpp_disequality_predicate \<Longrightarrow> lpp_finite_source_builtin f ts outcome=lpp_integer_source_builtin f ts outcome"
  by (simp add: lpp_finite_source_builtin_def)

lemma lpp_finite_source_integer_domain:
  assumes domain: "lpp_integer_source_domain f ts"
  shows "lpp_finite_source_builtin f ts outcome=lpp_integer_source_builtin f ts outcome"
proof (cases "f=''2:is''")
  case True
  obtain n where length: "length ts=2" and evaluated: "lpp_integer_evaluation (ts!1) n"
    using domain by (auto simp: True)
  have exact: "lpp_finite_is_outcome (ts!0) (ts!1) outcome = lpp_integer_is_outcome (ts!0) (ts!1) outcome"
    by (rule lpp_finite_is_integer[OF evaluated])
  show ?thesis by (simp only: lpp_finite_source_builtin_def True if_True exact; simp add: length)
next
  case False
  have different: "f\<noteq>lpp_disequality_predicate" using domain lpp_disequality_outside_legacy_domain[of ts] by blast
  show ?thesis by (rule lpp_finite_source_legacy[OF False different])
qed

lemma lpp_finite_source_domain_extends:
  assumes domain: "lpp_integer_source_domain f ts"
  shows "lpp_finite_source_domain f ts"
proof -
  have different: "f\<noteq>lpp_disequality_predicate"
    using domain lpp_disequality_outside_legacy_domain[of ts] by blast
  show ?thesis using domain
    by (cases "f=''2:is''")
      (auto simp: lpp_finite_source_domain_def different dest: lpp_integer_evaluation_ground)
qed

lemma lpp_finite_source_selected:
  assumes outcome: "lpp_finite_source_builtin f ts outcome"
  shows "(f,length ts)\<in>lpp_builtin_signature"
proof (cases "f=''2:is''")
  case True
  have "length ts=2" using outcome
    by (simp only: lpp_finite_source_builtin_def True if_True; blast)
  then show ?thesis by (simp add: True lpp_builtin_signature_def)
next
  case False
  show ?thesis
  proof (cases "f=lpp_disequality_predicate")
    case True
    have "length ts=2" using outcome
      by (simp add: lpp_finite_source_builtin_def True)
    then show ?thesis by (simp add: True)
  next
    case different: False
    have "lpp_integer_source_builtin f ts outcome"
      using outcome by (simp only: lpp_finite_source_legacy[OF False different])
    then show ?thesis by (rule lpp_integer_source_selected)
  qed
qed

lemma lpp_finite_source_total_on_domain:
  assumes domain: "lpp_finite_source_domain f ts"
  shows "\<exists>outcome. lpp_finite_source_builtin f ts outcome"
proof (cases "f=''2:is''")
  case True
  have length: "length ts=2" and ground: "lp_seg_ground (ts!1)"
    using domain by (auto simp: True lpp_finite_source_domain_def)
  show ?thesis using lpp_finite_is_total[OF ground, of "ts!0"]
    by (simp add: lpp_finite_source_builtin_def True length)
next
  case False
  show ?thesis
  proof (cases "f=lpp_disequality_predicate")
    case True
    show ?thesis using domain
      by (auto simp: lpp_finite_source_domain_def lpp_finite_source_builtin_def
        lpp_ground_disequality_outcome_def True)
  next
    case different: False
    have old: "lpp_integer_source_domain f ts"
      using domain by (simp add: lpp_finite_source_domain_def False different)
    show ?thesis using lpp_integer_source_total_on_domain[OF old]
      by (simp add: lpp_finite_source_builtin_def False different)
  qed
qed

lemma lpp_finite_source_checked_step:
  assumes domain: "lpp_integer_source_domain f ts"
    and selected: "(f,length ts)\<in>lpp_builtin_signature"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt =
    lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt"
  by (rule lpp_selected_builtin_cong[OF selected])
    (rule lpp_finite_source_integer_domain[OF domain])

end
