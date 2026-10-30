theory LP_Prolog_Integer_Source
  imports LP_Prolog_Finite_Comparison LP_Prolog_Identity_Test
begin

text \<open>A single interpreted operation relation extends the existing term
tests with integer tests, evaluation and comparison. Its domain is explicit:
unsupported arithmetic has no certified source-node rule and is protected by
the domain envelope. The relation is not a claim of completeness for Prolog
floating point evaluation or cyclic arithmetic expressions. Finite ground comparisons additionally use a conservative finite-outcome envelope.\<close>

fun lpp_source_comparison where
  "lpp_source_comparison f =
    (if f=''2:<'' then Some (LPPIntLess,False)
     else if f=''2:>'' then Some (LPPIntLess,True)
     else if f=''2:=<'' then Some (LPPIntLessEqual,False)
     else if f=''2:>='' then Some (LPPIntLessEqual,True)
     else if f=''2:=:='' then Some (LPPIntEqual,False)
     else if f=map char_of_nat [50,58,61,92,61] then Some (LPPIntNotEqual,False)
     else None)"

lemma lpp_source_comparison_descriptor:
  "lpp_source_comparison f=Some (comparison,reversed) \<longleftrightarrow>
    lpp_comparison_descriptor f comparison reversed"
  by (cases comparison; cases reversed) (auto simp: char_of_nat_def)

fun lpp_integer_source_builtin where
  "lpp_integer_source_builtin f ts outcome =
    (if f=''1:integer'' then (length ts=1 \<and> lpp_integer_test_outcome (ts!0) outcome)
     else if f=''2:is'' then (length ts=2 \<and> lpp_integer_is_outcome (ts!0) (ts!1) outcome)
     else (case lpp_source_comparison f of
       Some (comparison,reversed) \<Rightarrow> (length ts=2 \<and>
         lpp_finite_compare_outcome comparison (if reversed then ts!1 else ts!0) (if reversed then ts!0 else ts!1) outcome)
       | None \<Rightarrow> lpp_test_builtin f ts outcome))"

fun lpp_integer_source_domain where
  "lpp_integer_source_domain f ts =
    (if f=''1:integer'' then length ts=1
     else if f=''2:is'' then (length ts=2 \<and> (\<exists>n. lpp_integer_evaluation (ts!1) n))
     else (case lpp_source_comparison f of
       Some pair \<Rightarrow> (length ts=2 \<and>
         lp_seg_ground (ts!0) \<and> lp_seg_ground (ts!1))
       | None \<Rightarrow> ((lpp_var_name f \<and> length ts=1) \<or> (lpp_identity_name f \<and> length ts=2))))"

lemma lpp_integer_source_test[simp]:
  "lpp_integer_source_builtin ''1:integer'' [a] outcome = lpp_integer_test_outcome a outcome"
  by simp

lemma lpp_integer_source_is[simp]:
  "lpp_integer_source_builtin ''2:is'' [a,e] outcome = lpp_integer_is_outcome a e outcome"
  by simp

lemma lpp_integer_source_finite_comparison:
  assumes name: "lpp_comparison_descriptor f comparison reversed"
  shows "lpp_integer_source_builtin f [a,b] outcome =
    lpp_finite_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) outcome"
proof -
  have names: "f\<noteq>''1:integer''" "f\<noteq>''2:is''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name lpp_source_comparison_descriptor by blast
  show ?thesis by (simp only: lpp_integer_source_builtin.simps names if_False descriptor option.case prod.case; simp)
qed

lemma lpp_integer_source_comparison:
  assumes name: "lpp_comparison_descriptor f comparison reversed"
    and left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
  shows "lpp_integer_source_builtin f [a,b] outcome =
    lpp_integer_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) outcome"
proof -
  have names: "f\<noteq>''1:integer''" "f\<noteq>''2:is''"
    using name by (cases comparison; cases reversed; auto)+
  have descriptor: "lpp_source_comparison f=Some (comparison,reversed)"
    using name lpp_source_comparison_descriptor by blast
  show ?thesis by (simp only: lpp_integer_source_builtin.simps names if_False descriptor
    option.case prod.case; cases reversed; simp add: lpp_finite_comparison_integer[OF left right] lpp_finite_comparison_integer[OF right left])
qed

lemma lpp_integer_source_selected:
  assumes outcome: "lpp_integer_source_builtin f ts outcome"
  shows "(f,length ts)\<in>lpp_builtin_signature"
proof (cases "f=''1:integer''")
  case True
  have "length ts=1" using outcome by (simp only: lpp_integer_source_builtin.simps True if_True HOL.simp_thms; blast)
  then show ?thesis by (simp add: True lpp_builtin_signature_def)
next
  case ni: False
  show ?thesis
  proof (cases "f=''2:is''")
    case True
    have "length ts=2" using outcome by (auto simp: True)
    then show ?thesis by (simp add: True lpp_builtin_signature_def)
  next
    case ne: False
    show ?thesis
    proof (cases "lpp_source_comparison f")
      case None
      have "lpp_test_builtin f ts outcome" using outcome
        by (simp only: lpp_integer_source_builtin.simps ni ne if_False None option.case)
      then show ?thesis by (rule lpp_test_builtin_selected)
    next
      case (Some pair)
      obtain comparison reversed where pair: "pair=(comparison,reversed)" by (cases pair) auto
      have name: "lpp_comparison_descriptor f comparison reversed"
        using Some pair lpp_source_comparison_descriptor by blast
      have "length ts=2" using outcome
        by (simp only: lpp_integer_source_builtin.simps ni ne if_False Some pair option.case prod.case; blast)
      then show ?thesis using lpp_comparison_selected[OF name] by simp
    qed
  qed
qed

lemma lpp_integer_source_total_on_domain:
  assumes domain: "lpp_integer_source_domain f ts"
  shows "\<exists>outcome. lpp_integer_source_builtin f ts outcome"
proof (cases "f=''1:integer''")
  case True
  show ?thesis using domain by (auto simp: True lpp_integer_test_outcome_def)
next
  case ni: False
  show ?thesis
  proof (cases "f=''2:is''")
    case True
    obtain n where len: "length ts=2" and ev: "lpp_integer_evaluation (ts!1) n"
      using domain by (auto simp: True)
    have "\<exists>outcome. lpp_integer_is_outcome (ts!0) (ts!1) outcome"
      by (simp only: lpp_integer_is_outcome_exact[OF ev]; blast)
    then show ?thesis by (simp add: True len)
  next
    case ne: False
    show ?thesis
    proof (cases "lpp_source_comparison f")
      case None
      have d: "(lpp_var_name f \<and> length ts=1) \<or> (lpp_identity_name f \<and> length ts=2)"
        using domain by (simp only: lpp_integer_source_domain.simps ni ne if_False None option.case)
      have "\<exists>outcome. lpp_test_builtin f ts outcome" using d
        by (cases ts; auto simp: lpp_test_builtin_def lpp_var_builtin_def length_Suc_conv)
      then show ?thesis by (simp only: lpp_integer_source_builtin.simps ni ne if_False None option.case)
    next
      case (Some pair)
      obtain comparison reversed where pair: "pair=(comparison,reversed)" by (cases pair) auto
      have len: "length ts=2" and left: "lp_seg_ground (ts!0)" and right: "lp_seg_ground (ts!1)"
        using domain by (simp only: lpp_integer_source_domain.simps ni ne if_False Some option.case; blast)+
      have ev: "\<exists>outcome. lpp_finite_compare_outcome comparison
        (if reversed then ts!1 else ts!0) (if reversed then ts!0 else ts!1) outcome"
        by (cases reversed) (use lpp_finite_comparison_total[OF left right]
          lpp_finite_comparison_total[OF right left] in simp_all)
      show ?thesis using ev by (simp only: lpp_integer_source_builtin.simps ni ne if_False Some pair option.case prod.case len HOL.simp_thms)
    qed
  qed
qed

lemma lpp_source_comparison_legacy_names:
  "lpp_source_comparison ''1:var''=None"
  "lpp_source_comparison ''1:nonvar''=None"
  "lpp_source_comparison ''1:compound''=None"
  "lpp_source_comparison ''1:atomic''=None"
  "lpp_source_comparison ''2:==''=None"
  "lpp_source_comparison (map char_of_nat [50,58,92,61,61])=None"
  by code_simp+

lemma lpp_integer_source_legacy:
  assumes name: "lpp_var_name f \<or> lpp_identity_name f"
  shows "lpp_integer_source_builtin f ts outcome = lpp_test_builtin f ts outcome"
proof -
  have ni: "f\<noteq>''1:integer''" and ne: "f\<noteq>''2:is''"
    using name by (auto simp: lpp_var_name_def lpp_identity_name_def)
  have nc: "lpp_source_comparison f=None"
    using name by (auto simp only: lpp_var_name_def lpp_identity_name_def lpp_source_comparison_legacy_names)
  show ?thesis by (simp only: lpp_integer_source_builtin.simps ni ne if_False nc option.case)
qed

lemma lpp_integer_source_nonbuiltin_base:
  assumes clear: "lpp_no_builtin_frame ss"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin
      (lpc_return_eval eta ss) event tt"
  shows "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  using step lpp_no_builtin_frame_sound[OF clear, of eta]
  by (cases rule: lpp_answer_transition.cases)
    (auto simp: lpp_builtin_active_def simp del: lpp_integer_source_builtin.simps dest: lpp_integer_source_selected)

ML \<open>
val checked = [@{thm lpp_integer_source_comparison}, @{thm lpp_integer_source_selected},
  @{thm lpp_integer_source_total_on_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer source dispatch dependency" else ();
\<close>
end
