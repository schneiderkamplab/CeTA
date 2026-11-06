theory LP_Prolog_Stable_Backend_Routing
 imports LP_Prolog_Stable_Backends
begin

definition lpp_stable_rank_row_list where
  "lpp_stable_rank_row_list route_rank n D =
    filter (\<lambda>((h,ps,b,gs),os). route_rank (fst h)=n \<and> route_rank (fst b)=n) D"

lemma lpp_stable_rank_row_list_set:
  "set (lpp_stable_rank_row_list route_rank n D)=lpp_stable_rank_rows route_rank n (set D)"
  by (auto simp: lpp_stable_rank_row_list_def lpp_stable_rank_rows_def split: prod.splits)

definition lpp_check_stable_backend_routing where
  "lpp_check_stable_backend_routing I J T P route_rank D backends =
    (lpp_check_stable_finite_routing route_rank (length backends) D \<and>
      list_all (\<lambda>n. lpp_check_stable_backend I J T P
        (lpp_stable_rank_row_list route_rank n D) (backends!n)) [0..<length backends])"

theorem lpp_check_stable_backend_routing_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_backend_routing I J T P route_rank D backends"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (rule lpp_stable_finite_routed_calls_SN[where component_count="length backends"])
  show "lpp_check_stable_finite_routing route_rank (length backends) D"
    using checked by (simp add: lpp_check_stable_backend_routing_def)
next
  fix n assume index: "n<length backends"
  have all_children: "\<forall>i\<in>set [0..<length backends]. lpp_check_stable_backend I J T P
    (lpp_stable_rank_row_list route_rank i D) (backends!i)"
    using checked by (auto simp: lpp_check_stable_backend_routing_def list_all_iff)
  have child: "lpp_check_stable_backend I J T P (lpp_stable_rank_row_list route_rank n D) (backends!n)"
    by (rule bspec[OF all_children]) (use index in simp)
  have sn: "SN (lpp_stable_observed_calls operation (set (lpp_stable_rank_row_list route_rank n D)) P :: string lpp_success_iatom rel)"
    by (rule lpp_check_stable_backend_sound[OF I J compatible child transfer])
  show "SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P :: string lpp_success_iatom rel)"
    using sn by (simp only: lpp_stable_rank_row_list_set)
qed

ML \<open>
val checked = [@{thm lpp_check_stable_backend_routing_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted stable backend routing" else ();
\<close>
end
