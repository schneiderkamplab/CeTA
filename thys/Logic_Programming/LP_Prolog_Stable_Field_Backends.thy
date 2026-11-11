theory LP_Prolog_Stable_Field_Backends
 imports LP_Prolog_Stable_Backend_Routing LP_Prolog_Observed_Endpoint_Rewrite
begin

fun lpp_field_backend_rows where
  "lpp_field_backend_rows None D = D"
| "lpp_field_backend_rows (Some (fuel,field_plan)) D =
    map (lpp_field_observed_triple field_plan) (map (lpp_rewrite_endpoints fuel) D)"

fun lpp_check_field_backend where
  "lpp_check_field_backend I J T P D (None,child) = lpp_check_stable_backend I J T P D child"
| "lpp_check_field_backend I J T P D (Some (fuel,field_plan),child) =
    (lpp_check_field_projection field_plan (map (lpp_rewrite_endpoints fuel) D) \<and>
      lpp_check_stable_backend I J T P (lpp_field_backend_rows (Some (fuel,field_plan)) D) child)"

theorem lpp_check_field_backend_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_field_backend I J T P D backend"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof -
  obtain meta child where backend: "backend=(meta,child)" by (cases backend) auto
  show ?thesis
  proof (cases meta)
    case None
    have base: "lpp_check_stable_backend I J T P D child"
      using checked by (simp add: backend None)
    show ?thesis by (rule lpp_check_stable_backend_sound[OF I J compatible base transfer])
  next
    case (Some data)
    obtain fuel field_plan where data: "data=(fuel,field_plan)" by (cases data) auto
    have fields: "lpp_check_field_projection field_plan (map (lpp_rewrite_endpoints fuel) D)"
      and base: "lpp_check_stable_backend I J T P
        (map (lpp_field_observed_triple field_plan) (map (lpp_rewrite_endpoints fuel) D)) child"
      using checked by (auto simp: backend Some data)
    have child_sn: "SN (lpp_stable_observed_calls operation
        (set (map (lpp_field_observed_triple field_plan) (map (lpp_rewrite_endpoints fuel) D))) P :: string lpp_success_iatom rel)"
      by (rule lpp_check_stable_backend_sound[OF I J compatible base transfer])
    have rewritten_sn: "SN (lpp_stable_observed_calls operation
        (set (map (lpp_rewrite_endpoints fuel) D)) P :: string lpp_success_iatom rel)"
      by (rule lpp_checked_field_projection_SN[OF fields child_sn])
    show ?thesis by (rule SN_subset[OF rewritten_sn lpp_rewrite_endpoints_sound])
  qed
qed

definition lpp_check_field_backend_routing where
  "lpp_check_field_backend_routing I J T P route_rank D backends =
    (lpp_check_stable_finite_routing route_rank (length backends) D \<and>
      list_all (\<lambda>n. lpp_check_field_backend I J T P
        (lpp_stable_rank_row_list route_rank n D) (backends!n)) [0..<length backends])"

theorem lpp_check_field_backend_routing_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_field_backend_routing I J T P route_rank D backends"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (rule lpp_stable_finite_routed_calls_SN[where component_count="length backends"])
  show "lpp_check_stable_finite_routing route_rank (length backends) D"
    using checked by (simp add: lpp_check_field_backend_routing_def)
next
  fix n assume index: "n<length backends"
  have child: "lpp_check_field_backend I J T P (lpp_stable_rank_row_list route_rank n D) (backends!n)"
    using checked index by (auto simp: lpp_check_field_backend_routing_def list_all_iff)
  have sn: "SN (lpp_stable_observed_calls operation (set (lpp_stable_rank_row_list route_rank n D)) P :: string lpp_success_iatom rel)"
    by (rule lpp_check_field_backend_sound[OF I J compatible child transfer])
  show "SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P :: string lpp_success_iatom rel)"
    using sn by (simp only: lpp_stable_rank_row_list_set)
qed

ML \<open>
val checked = [@{thm lpp_check_field_backend_sound}, @{thm lpp_check_field_backend_routing_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted field backend dependency" else ();
\<close>
end
