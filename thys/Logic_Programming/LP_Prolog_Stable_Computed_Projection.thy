theory LP_Prolog_Stable_Computed_Projection
 imports LP_Prolog_Stable_Numeric_Component
begin

text \<open>Additional call arguments observe fixed source expressions. The
original arguments, successful helper premises, observations and edges remain
present. Only a later checked projection may omit unused coordinates.\<close>

definition lpp_expand_call where
  "lpp_expand_call C expressions a = (fst a, snd a @
    map (\<lambda>(f,indices). C f (lpp_select_arguments indices (snd a))) (expressions (fst a)))"

lemma lpp_expand_call_eval:
  "lpp_success_atom_eval (lpp_expand_call Fun expressions a) eta =
    lpp_expand_call LPIFun expressions (lpp_success_atom_eval a eta)"
  by (auto simp: lpp_expand_call_def lpp_success_atom_eval_def lpp_select_arguments_map map_map split_def)

lemma lpp_expand_call_subst:
  "lpp_success_iatom_subst (lpp_expand_call LPIFun expressions a) sigma =
    lpp_expand_call LPIFun expressions (lpp_success_iatom_subst a sigma)"
  by (auto simp: lpp_expand_call_def lpp_success_iatom_subst_def lpp_select_arguments_map map_map split_def)

fun lpp_expand_observed_triple where
  "lpp_expand_observed_triple expressions ((h,ps,b,gs),observations) =
    ((lpp_expand_call Fun expressions h,ps,lpp_expand_call Fun expressions b,gs),observations)"

lemma lpp_stable_observed_call_expansion:
  assumes edge: "(a,b)\<in>lpp_stable_observed_calls operation D P"
  shows "(lpp_expand_call LPIFun expressions a,lpp_expand_call LPIFun expressions b)\<in>
    lpp_stable_observed_calls operation (lpp_expand_observed_triple expressions ` D) P"
proof -
  obtain h ps target gs observations sigma eta where
    member: "((h,ps,target,gs),observations)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) observations"
    and facts: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  have projected: "((lpp_expand_call Fun expressions h,ps,lpp_expand_call Fun expressions target,gs),observations)
      \<in>lpp_expand_observed_triple expressions ` D"
    using imageI[OF member, of "lpp_expand_observed_triple expressions"] by simp
  have match: "lpp_success_iatom_subst (lpp_expand_call LPIFun expressions a) sigma =
      lpp_success_atom_eval (lpp_expand_call Fun expressions h) eta"
    by (simp only: lpp_expand_call_subst matching lpp_expand_call_eval)
  show ?thesis unfolding lpp_stable_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ "lpp_expand_call LPIFun expressions a"], rule exI[of _ "lpp_expand_call Fun expressions h"],
      rule exI[of _ ps], rule exI[of _ "lpp_expand_call Fun expressions target"],
      rule exI[of _ gs], rule exI[of _ observations], rule exI[of _ sigma], rule exI[of _ eta])
    using projected match guards observations facts target by (simp add: lpp_expand_call_eval)
qed

theorem lpp_stable_expanded_calls_SN:
  assumes sn: "SN (lpp_stable_observed_calls operation (lpp_expand_observed_triple expressions ` D) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation D P :: 'w lpp_success_iatom rel)"
  by (rule lpp_typed_successor_simulation_SN[where T="\<lambda>_. True" and
      project="lpp_expand_call LPIFun expressions", OF sn])
    (auto intro: lpp_stable_observed_call_expansion)

definition lpp_check_argument_expansion where
  "lpp_check_argument_expansion expressions a = list_all (\<lambda>(f,indices).
    list_all (\<lambda>i. i<length (snd a)) indices) (expressions (fst a))"

definition lpp_check_stable_computed_numeric_component where
  "lpp_check_stable_computed_numeric_component T expressions positions coordinates modes locations system D row_receipts child =
    (list_all (\<lambda>((h,ps,b,gs),os). lpp_check_argument_expansion expressions h \<and>
      lpp_check_argument_expansion expressions b) D \<and>
      lpp_check_stable_projected_numeric_component T positions coordinates modes locations system
        (map (lpp_expand_observed_triple expressions) D) row_receipts child)"

theorem lpp_check_stable_computed_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_stable_numeric_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_computed_numeric_component T expressions positions coordinates modes locations system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof -
  have component: "lpp_check_stable_projected_numeric_component T positions coordinates modes locations system
      (map (lpp_expand_observed_triple expressions) D) row_receipts child"
    using checked by (simp add: lpp_check_stable_computed_numeric_component_def)
  have expanded: "SN (lpp_stable_observed_calls operation (lpp_expand_observed_triple expressions ` set D) P)"
    using lpp_check_stable_projected_numeric_component_sound[OF compatible component transfer] by simp
  show ?thesis by (rule lpp_stable_expanded_calls_SN[OF expanded])
qed

ML \<open>
val checked = [@{thm lpp_stable_expanded_calls_SN}, @{thm lpp_check_stable_computed_numeric_component_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted computed numeric projection dependency" else ();
\<close>
end
