theory LP_Prolog_Stable_Routing_Coverage
 imports LP_Prolog_Stable_Structural_Components
begin

definition lpp_check_stable_finite_routing where
  "lpp_check_stable_finite_routing route_rank component_count D =
    (lpp_check_stable_routing route_rank D \<and>
      list_all (\<lambda>((h,ps,b,gs),os). route_rank (fst h)<component_count) D)"

lemma lpp_stable_outside_routing_empty:
  assumes checked: "lpp_check_stable_finite_routing route_rank component_count D"
    and outside: "component_count\<le>n"
  shows "lpp_stable_rank_rows route_rank n (set D) = {}"
  using checked outside
  by (auto simp: lpp_check_stable_finite_routing_def lpp_stable_rank_rows_def list_all_iff split: prod.splits)

theorem lpp_stable_finite_routed_calls_SN:
  assumes checked: "lpp_check_stable_finite_routing route_rank component_count D"
    and components: "\<And>n. n<component_count \<Longrightarrow>
      SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P :: 'w lpp_success_iatom rel)"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: 'w lpp_success_iatom rel)"
proof (rule lpp_stable_routed_calls_SN)
  show "lpp_check_stable_routing route_rank D"
    using checked by (simp add: lpp_check_stable_finite_routing_def)
next
  fix n
  show "SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P :: 'w lpp_success_iatom rel)"
  proof (cases "n<component_count")
    case True then show ?thesis by (rule components)
  next
    case False
    have empty: "lpp_stable_rank_rows route_rank n (set D) = {}"
      by (rule lpp_stable_outside_routing_empty[OF checked]) (use False in arith)
    show ?thesis by (simp add: empty lpp_stable_observed_calls_def)
  qed
qed

ML \<open>
val checked = [@{thm lpp_stable_finite_routed_calls_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted finite routing coverage dependency" else ();
\<close>
end
