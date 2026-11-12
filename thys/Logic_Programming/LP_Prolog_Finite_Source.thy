theory LP_Prolog_Finite_Source
 imports LP_Prolog_List_Observation LP_Prolog_Branch_Scope LP_Prolog_Finite_Length LP_Prolog_Ground_Disequality LP_Prolog_Probe_Builtin
begin

lemma lpp_nonprobe_names [simp]:
  "lpp_probe_name ''1:is_list'' = False"
  "lpp_probe_name ''2:is'' = False"
  "lpp_probe_name ''2:length'' = False"
  "lpp_probe_name ''3:subtract'' = False"
  "lpp_probe_name ''2:;'' = False"
  "lpp_probe_name ''1:integer'' = False"
  "lpp_probe_name ''1:var'' = False"
  "lpp_probe_name ''1:nonvar'' = False"
  "lpp_probe_name ''1:compound'' = False"
  "lpp_probe_name ''1:atomic'' = False"
  "lpp_probe_name ''2:=='' = False"
  "lpp_probe_name (map char_of_nat [50,58,92,61,61]) = False"
  "lpp_probe_name ''2:<'' = False"
  "lpp_probe_name ''2:>'' = False"
  "lpp_probe_name ''2:=<'' = False"
  "lpp_probe_name ''2:>='' = False"
  "lpp_probe_name ''2:=:='' = False"
  "lpp_probe_name (map char_of_nat [50,58,61,92,61]) = False"
  "lpp_probe_name lpp_disequality_predicate = False"
  by code_simp+

lemma lpp_length_disequality_names[simp]:
  "''2:length''\<noteq>lpp_disequality_predicate"
  "lpp_disequality_predicate\<noteq>''2:length''"
  by code_simp+

text \<open>This is an interpretation of the existing parameterized source
transition, with a larger evaluation domain. It agrees exactly with the previous
interpretation on its checked domain. It does not define a second execution
relation or a replacement evaluation graph.\<close>

text \<open>Library delegation keeps the caller's answer environment and saved
alternatives. Its body is executed by the shared LP machine; no termination or
successful-return fact is assumed at this step. The source compiler includes
the fixed library clauses in the complete program.\<close>
definition lpp_subtract_library :: string where
  "lpp_subtract_library = ''3:prolog_data_0070726f6c6f672e6c6962726172793a73756274726163745f6c697374''"

definition lpp_finite_source_builtin where
  "lpp_finite_source_builtin f ts outcome =
    (if lpp_probe_name f then lpp_probe_outcome f ts outcome
     else if f=''2:is'' then length ts=2 \<and> lpp_finite_is_outcome (ts!0) (ts!1) outcome
     else if f=lpp_disequality_predicate then length ts=2 \<and> lpp_rational_disequality_outcome (ts!0) (ts!1) outcome
     else if f=''2:length'' then length ts=2 \<and> lpp_finite_length_outcome (ts!0) (ts!1) outcome
     else if f=''3:subtract'' then length ts=3 \<and> (outcome=LPPBuiltinCall (LPIFun (LPCUser lpp_subtract_library) ts) \<or> outcome=LPPBuiltinError)
     else if f=''2:;'' then lpp_branch_outcome ts outcome
     else if f=''1:is_list'' then length ts=1 \<and> lpp_is_list_outcome (ts!0) outcome
     else lpp_integer_source_builtin f ts outcome)"

definition lpp_finite_source_domain where
  "lpp_finite_source_domain f ts =
    (if lpp_probe_name f then lpp_probe_domain f ts
     else if f=''2:is'' then length ts=2 \<and>
       (lp_seg_ground (ts!1) \<or> lpp_finite_instantiation_error (ts!1))
     else if f=lpp_disequality_predicate then length ts=2
     else if f=''2:length'' then length ts=2 \<and> lp_seg_ground (ts!0)
     else if f=''3:subtract'' then length ts=3
     else if f=''2:;'' then lpp_branch_domain ts
     else if f=''1:is_list'' then length ts=1
     else lpp_integer_source_domain f ts)"

lemma lpp_length_outside_legacy_domain[simp]:
  "\<not> lpp_integer_source_domain ''2:length'' ts"
  by (simp add: lpp_var_name_def lpp_identity_name_def)

lemma lpp_finite_length_source_success:
  "lpp_finite_source_builtin ''2:length'' [t,a] (LPPBuiltinSuccess mu) \<Longrightarrow>
    lpp_is_integer (lp_isubst a mu)"
  by (simp add: lpp_finite_source_builtin_def lpp_disequality_predicate_def;
      rule lpp_finite_length_success_integer)

lemma lpp_finite_source_legacy:
  "f\<noteq>''2:is'' \<Longrightarrow> f\<noteq>lpp_disequality_predicate \<Longrightarrow> f\<noteq>''2:length'' \<Longrightarrow> \<not>lpp_probe_name f \<Longrightarrow> f\<noteq>''3:subtract'' \<Longrightarrow> f\<noteq>''2:;'' \<Longrightarrow> f\<noteq>''1:is_list'' \<Longrightarrow> lpp_finite_source_builtin f ts outcome=lpp_integer_source_builtin f ts outcome"
  by (simp add: lpp_finite_source_builtin_def)

lemma lpp_probe_legacy_domain [simp]:
  "lpp_integer_source_domain f ts \<Longrightarrow> \<not>lpp_probe_name f"
  using lpp_probe_not_integer_domain by blast

lemma lpp_finite_source_integer_domain:
  assumes domain: "lpp_integer_source_domain f ts"
  shows "lpp_finite_source_builtin f ts outcome=lpp_integer_source_builtin f ts outcome"
proof (cases "f=''2:is''")
  case True
  obtain n where length: "length ts=2" and evaluated: "lpp_integer_evaluation (ts!1) n"
    using domain by (auto simp: True)
  have exact: "lpp_finite_is_outcome (ts!0) (ts!1) outcome = lpp_integer_is_outcome (ts!0) (ts!1) outcome"
    by (rule lpp_finite_is_integer[OF evaluated])
  show ?thesis by (simp only: lpp_finite_source_builtin_def lpp_probe_legacy_domain[OF domain] if_False True if_True exact; simp add: length)
next
  case False
  have different: "f\<noteq>lpp_disequality_predicate" using domain lpp_disequality_outside_legacy_domain[of ts] by blast
  have nonlength: "f\<noteq>''2:length''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonsubtract: "f\<noteq>''3:subtract''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonlist: "f\<noteq>''1:is_list''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonbranch: "f\<noteq>''2:;''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  show ?thesis by (rule lpp_finite_source_legacy[OF False different nonlength lpp_probe_legacy_domain[OF domain] nonsubtract nonbranch nonlist])
qed

lemma lpp_finite_source_domain_extends:
  assumes domain: "lpp_integer_source_domain f ts"
  shows "lpp_finite_source_domain f ts"
proof -
  have different: "f\<noteq>lpp_disequality_predicate"
    using domain lpp_disequality_outside_legacy_domain[of ts] by blast
  have nonlength: "f\<noteq>''2:length''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonsubtract: "f\<noteq>''3:subtract''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonlist: "f\<noteq>''1:is_list''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nonbranch: "f\<noteq>''2:;''" using domain by (auto simp: lpp_var_name_def lpp_identity_name_def)
  show ?thesis using domain
    by (cases "f=''2:is''")
      (auto simp: lpp_finite_source_domain_def different nonlength nonsubtract nonbranch nonlist lpp_probe_legacy_domain[OF domain] dest: lpp_integer_evaluation_ground)
qed

lemma lpp_finite_source_selected:
  assumes outcome: "lpp_finite_source_builtin f ts outcome"
  shows "(f,length ts)\<in>lpp_builtin_signature"
proof (cases "lpp_probe_name f")
  case True
  then have "lpp_probe_domain f ts" using outcome
    by (simp add: lpp_finite_source_builtin_def lpp_probe_outcome_def)
  then show ?thesis by (rule lpp_probe_selected)
next
  case nonprobe: False
  show ?thesis
  proof (cases "f=''2:is''")
  case True
  have "length ts=2" using outcome
    by (auto simp: lpp_finite_source_builtin_def nonprobe True)
  then show ?thesis by (simp add: True lpp_builtin_signature_def)
next
  case False
  show ?thesis
  proof (cases "f=lpp_disequality_predicate")
    case True
    have "length ts=2" using outcome
      by (simp add: lpp_finite_source_builtin_def nonprobe True)
    then show ?thesis by (simp add: True)
  next
    case different: False
    show ?thesis
    proof (cases "f=''2:length''")
      case True
      have "length ts=2" using outcome
        by (simp add: lpp_finite_source_builtin_def nonprobe True)
      then show ?thesis by (simp add: True lpp_builtin_signature_def)
    next
      case nonlength: False
      show ?thesis
      proof (cases "f=''3:subtract''")
        case True
        have "length ts=3" using outcome
          by (simp add: lpp_finite_source_builtin_def nonprobe True lpp_disequality_predicate_def)
        then show ?thesis by (simp add: True lpp_builtin_signature_def)
      next
        case nonsubtract: False
        show ?thesis
        proof (cases "f=''2:;''")
          case True
          have "lpp_branch_outcome ts outcome" using outcome
            by (simp add: lpp_finite_source_builtin_def nonprobe True lpp_disequality_predicate_def)
          then show ?thesis using lpp_branch_outcome_arity
            by (auto simp: True lpp_builtin_signature_def)
        next
          case nonbranch: False
          show ?thesis
          proof (cases "f=''1:is_list''")
            case True
            then show ?thesis using outcome
              by (auto simp: lpp_finite_source_builtin_def nonprobe False different nonlength nonsubtract nonbranch lpp_builtin_signature_def lpp_disequality_predicate_def)
          next
            case nonlist: False
            have "lpp_integer_source_builtin f ts outcome"
              using outcome by (simp only: lpp_finite_source_legacy[OF False different nonlength nonprobe nonsubtract nonbranch nonlist])
            then show ?thesis by (rule lpp_integer_source_selected)
          qed
        qed
      qed
    qed
  qed
qed
qed

lemma lpp_finite_source_total_on_domain:
  assumes domain: "lpp_finite_source_domain f ts"
  shows "\<exists>outcome. lpp_finite_source_builtin f ts outcome"
proof (cases "lpp_probe_name f")
  case True
  then show ?thesis using domain lpp_probe_total[of f ts]
    by (simp add: lpp_finite_source_domain_def lpp_finite_source_builtin_def)
next
  case nonprobe: False
  show ?thesis
  proof (cases "f=''2:is''")
  case True
  have length: "length ts=2" and cases: "lp_seg_ground (ts!1) \<or> lpp_finite_instantiation_error (ts!1)"
    using domain by (auto simp: True lpp_finite_source_domain_def nonprobe)
  have "\<exists>outcome. lpp_finite_is_outcome (ts!0) (ts!1) outcome"
    using cases lpp_finite_is_total[of "ts!1" "ts!0"]
      lpp_finite_is_instantiation_error[of "ts!1" "ts!0"] by blast
  then show ?thesis by (simp add: lpp_finite_source_builtin_def nonprobe True length)
next
  case False
  show ?thesis
  proof (cases "f=lpp_disequality_predicate")
    case True
    show ?thesis using domain
      by (auto simp: lpp_finite_source_domain_def nonprobe lpp_finite_source_builtin_def nonprobe
        lpp_rational_disequality_outcome_def True)
  next
    case different: False
    show ?thesis
    proof (cases "f=''2:length''")
      case True
      have arity: "length ts=2" using domain
        by (simp add: lpp_finite_source_domain_def nonprobe True)
      show ?thesis by (rule exI[of _ LPPBuiltinError])
        (simp add: lpp_finite_source_builtin_def nonprobe True arity lpp_finite_length_outcome_def)
    next
      case nonlength: False
      show ?thesis
      proof (cases "f=''3:subtract''")
        case True
        have "length ts=3" using domain
          by (simp add: lpp_finite_source_domain_def nonprobe True lpp_disequality_predicate_def)
        then show ?thesis by (rule_tac x=LPPBuiltinError in exI)
          (simp add: lpp_finite_source_builtin_def nonprobe True lpp_disequality_predicate_def)
      next
        case nonsubtract: False
        show ?thesis
        proof (cases "f=''2:;''")
          case True
          then show ?thesis using domain
            by (simp add: lpp_finite_source_domain_def lpp_finite_source_builtin_def nonprobe lpp_disequality_predicate_def lpp_branch_domain_def)
        next
          case nonbranch: False
          show ?thesis
          proof (cases "f=''1:is_list''")
            case True
            then show ?thesis using domain
              by (auto simp: lpp_finite_source_domain_def lpp_finite_source_builtin_def
                nonprobe False different nonlength nonsubtract nonbranch lpp_is_list_outcome_def lpp_disequality_predicate_def)
          next
            case nonlist: False
            have old: "lpp_integer_source_domain f ts"
              using domain by (simp add: lpp_finite_source_domain_def nonprobe False different nonlength nonsubtract nonbranch nonlist)
            show ?thesis using lpp_integer_source_total_on_domain[OF old]
              by (simp add: lpp_finite_source_builtin_def nonprobe False different nonlength nonsubtract nonbranch nonlist)
          qed
        qed
      qed
    qed
  qed
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
