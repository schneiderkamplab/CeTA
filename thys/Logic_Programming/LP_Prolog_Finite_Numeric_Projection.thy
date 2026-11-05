theory LP_Prolog_Finite_Numeric_Projection
 imports LP_Prolog_Finite_Numeric_Calls
begin

text \<open>Projection changes only call arguments. Guards, observations and
successful helper premises remain identical. Every original call must simulate
one projected call, including when no arguments are selected. In particular an
empty projection cannot remove a recursive edge.\<close>

definition lpp_select_arguments :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "lpp_select_arguments positions xs = map ((!) xs) (filter (\<lambda>i. i<length xs) positions)"

lemma lpp_select_arguments_map:
  "lpp_select_arguments positions (map f xs) = map f (lpp_select_arguments positions xs)"
  by (auto simp: lpp_select_arguments_def map_map intro!: map_cong)

definition lpp_project_call where
  "lpp_project_call positions a = (fst a,lpp_select_arguments (positions (fst a)) (snd a))"

lemma lpp_project_call_eval:
  "lpp_success_atom_eval (lpp_project_call positions a) eta =
    lpp_project_call positions (lpp_success_atom_eval a eta)"
  by (simp add: lpp_project_call_def lpp_success_atom_eval_def lpp_select_arguments_map)

lemma lpp_project_call_subst:
  "lpp_success_iatom_subst (lpp_project_call positions a) sigma =
    lpp_project_call positions (lpp_success_iatom_subst a sigma)"
  by (simp add: lpp_project_call_def lpp_success_iatom_subst_def lpp_select_arguments_map)

fun lpp_project_observed_triple where
  "lpp_project_observed_triple positions ((h,ps,b,gs),observations) =
    ((lpp_project_call positions h,ps,lpp_project_call positions b,gs),observations)"

lemma lpp_finite_observed_call_projection:
  assumes edge: "(a,b)\<in>lpp_finite_observed_calls D P"
  shows "(lpp_project_call positions a,lpp_project_call positions b)\<in>
    lpp_finite_observed_calls (lpp_project_observed_triple positions ` D) P"
proof -
  obtain h ps target gs observations sigma eta where
    member: "((h,ps,target,gs),observations)\<in>D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) gs"
    and observations: "list_all (lpp_evaluation_observation_holds lpp_finite_evaluation_result eta) observations"
    and facts: "list_all (lpp_guarded_success P lpp_finite_evaluation_result)
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "b=lpp_success_atom_eval target eta"
    using edge by (auto simp: lpp_finite_observed_calls_def)
  have projected: "((lpp_project_call positions h,ps,lpp_project_call positions target,gs),observations)
      \<in>lpp_project_observed_triple positions ` D"
    using imageI[OF member, of "lpp_project_observed_triple positions"] by simp
  have match: "lpp_success_iatom_subst (lpp_project_call positions a) sigma =
      lpp_success_atom_eval (lpp_project_call positions h) eta"
    by (simp only: lpp_project_call_subst matching lpp_project_call_eval)
  show ?thesis unfolding lpp_finite_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ "lpp_project_call positions a"], rule exI[of _ "lpp_project_call positions h"],
      rule exI[of _ ps], rule exI[of _ "lpp_project_call positions target"],
      rule exI[of _ gs], rule exI[of _ observations], rule exI[of _ sigma], rule exI[of _ eta])
    using projected match guards observations facts target
    by (simp add: lpp_project_call_eval)
qed

theorem lpp_finite_projected_calls_SN:
  assumes sn: "SN (lpp_finite_observed_calls (lpp_project_observed_triple positions ` D) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_finite_observed_calls D P :: 'w lpp_success_iatom rel)"
  by (rule lpp_typed_successor_simulation_SN[where T="\<lambda>_. True" and
      project="lpp_project_call positions", OF sn])
    (auto intro: lpp_finite_observed_call_projection)


definition lpp_check_call_projection where
  "lpp_check_call_projection positions a =
    (distinct (positions (fst a)) \<and> list_all (\<lambda>i. i<length (snd a)) (positions (fst a)))"

definition lpp_check_finite_projected_numeric_component where
  "lpp_check_finite_projected_numeric_component T positions coordinates locations system D row_receipts child =
    (list_all (\<lambda>((h,ps,b,gs),os). lpp_check_call_projection positions h \<and>
      lpp_check_call_projection positions b) D \<and>
      lpp_check_numeric_component T coordinates locations system
        (map (lpp_project_observed_triple positions) D) row_receipts child)"

theorem lpp_check_finite_projected_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_finite_projected_numeric_component T positions coordinates locations system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_finite_observed_calls (set D) P)"
proof (rule lpp_finite_projected_calls_SN)
  have component: "lpp_check_numeric_component T coordinates locations system
      (map (lpp_project_observed_triple positions) D) row_receipts child"
    using checked by (simp add: lpp_check_finite_projected_numeric_component_def)
  show "SN (lpp_finite_observed_calls (lpp_project_observed_triple positions ` set D) P)"
    using lpp_check_finite_numeric_component_sound[OF component transfer] by simp
qed

end
