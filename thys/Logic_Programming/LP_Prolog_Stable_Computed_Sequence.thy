theory LP_Prolog_Stable_Computed_Sequence
  imports LP_Prolog_Stable_Computed_Projection
begin

text \<open>A finite sequence of the existing checked argument expansions can
observe nested expressions. Each stage retains every original argument,
helper premise and observation. Later stages may refer to coordinates added
by earlier stages; every index is checked against that stage's actual arity.\<close>

fun lpp_expand_observed_sequence where
  "lpp_expand_observed_sequence [] D = D"
| "lpp_expand_observed_sequence (stage # stages) D =
    lpp_expand_observed_sequence stages (map (lpp_expand_observed_triple stage) D)"

fun lpp_check_expansion_sequence where
  "lpp_check_expansion_sequence [] D = True"
| "lpp_check_expansion_sequence (stage # stages) D =
    (list_all (\<lambda>((h,ps,b,gs),os). lpp_check_argument_expansion stage h \<and>
      lpp_check_argument_expansion stage b) D \<and>
      lpp_check_expansion_sequence stages (map (lpp_expand_observed_triple stage) D))"

theorem lpp_stable_expanded_sequence_SN:
  assumes sn: "SN (lpp_stable_observed_calls operation
    (set (lpp_expand_observed_sequence stages D)) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: 'w lpp_success_iatom rel)"
  using sn
proof (induction stages arbitrary: D)
  case Nil
  then show ?case by simp
next
  case (Cons stage stages)
  have expanded: "SN (lpp_stable_observed_calls operation
      (lpp_expand_observed_triple stage ` set D) P)"
    using Cons.IH[of "map (lpp_expand_observed_triple stage) D"] Cons.prems by simp
  show ?case by (rule lpp_stable_expanded_calls_SN[OF expanded])
qed

definition lpp_check_computed_sequence_component where
  "lpp_check_computed_sequence_component T stages positions coordinates modes locations system D row_receipts child =
    (lpp_check_expansion_sequence stages D \<and>
      lpp_check_stable_projected_numeric_component T positions coordinates modes locations system
        (lpp_expand_observed_sequence stages D) row_receipts child)"

theorem lpp_check_computed_sequence_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_stable_numeric_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_computed_sequence_component T stages positions coordinates modes locations system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof -
  have component: "lpp_check_stable_projected_numeric_component T positions coordinates modes locations system
      (lpp_expand_observed_sequence stages D) row_receipts child"
    using checked by (simp add: lpp_check_computed_sequence_component_def)
  have expanded: "SN (lpp_stable_observed_calls operation
      (set (lpp_expand_observed_sequence stages D)) P)"
    by (rule lpp_check_stable_projected_numeric_component_sound[OF compatible component transfer])
  show ?thesis by (rule lpp_stable_expanded_sequence_SN[OF expanded])
qed

ML \<open>
val checked = [@{thm lpp_stable_expanded_sequence_SN}, @{thm lpp_check_computed_sequence_component_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted computed sequence dependency" else ();
\<close>
end
