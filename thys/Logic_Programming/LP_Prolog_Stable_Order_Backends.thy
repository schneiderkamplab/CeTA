theory LP_Prolog_Stable_Order_Backends
  imports LP_Prolog_Stable_Field_Backends LP_Prolog_Success_Order_Rows
begin

fun lpp_check_order_backend where
  "lpp_check_order_backend I J T P D (None,child) = lpp_check_field_backend I J T P D child"
| "lpp_check_order_backend I J T P D (Some (summaries,receipts,selections),child) =
    (lpp_check_order_program summaries P receipts \<and> length selections=length D \<and>
      list_all (\<lambda>i. case D!i of ((h,ps,b,gs),os) \<Rightarrow>
        list_all (\<lambda>u. lpp_order_use summaries ps u\<noteq>None) (snd (selections!i)) \<and> (case fst (selections!i) of None \<Rightarrow> True | Some n \<Rightarrow> n\<le>length os)) [0..<length D] \<and>
      lpp_check_field_backend I J T P (lpp_enrich_order_rows summaries selections D) child)"

theorem lpp_check_order_backend_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_backend I J T P D backend"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof -
  obtain meta child where backend: "backend=(meta,child)" by (cases backend) auto
  show ?thesis
  proof (cases meta)
    case None
    have child: "lpp_check_field_backend I J T P D child" using checked by (simp add: backend None)
    show ?thesis by (rule lpp_check_field_backend_sound[OF I J compatible child transfer])
  next
    case (Some data)
    obtain summaries proofs selections where data: "data=(summaries,proofs,selections)" by (cases data) auto
    have program: "lpp_check_order_program summaries P proofs" and count: "length selections=length D"
      and child: "lpp_check_field_backend I J T P (lpp_enrich_order_rows summaries selections D) child"
      using checked by (auto simp: backend Some data)
    have child_sn: "SN (lpp_stable_observed_calls operation (set (lpp_enrich_order_rows summaries selections D)) P :: string lpp_success_iatom rel)"
      by (rule lpp_check_field_backend_sound[OF I J compatible child transfer])
    show ?thesis by (rule lpp_enriched_order_calls_SN[OF compatible program count child_sn])
  qed
qed

definition lpp_check_order_backend_routing where
  "lpp_check_order_backend_routing I J T P route_rank D backends =
    (lpp_check_stable_finite_routing route_rank (length backends) D \<and>
      list_all (\<lambda>n. lpp_check_order_backend I J T P
        (lpp_stable_rank_row_list route_rank n D) (backends!n)) [0..<length backends])"

theorem lpp_check_order_backend_routing_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_order_backend_routing I J T P route_rank D backends"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (rule lpp_stable_finite_routed_calls_SN[where component_count="length backends"])
  show "lpp_check_stable_finite_routing route_rank (length backends) D"
    using checked by (simp add: lpp_check_order_backend_routing_def)
next
  fix n assume index: "n<length backends"
  have child: "lpp_check_order_backend I J T P (lpp_stable_rank_row_list route_rank n D) (backends!n)"
    using checked index by (auto simp: lpp_check_order_backend_routing_def list_all_iff)
  have sn: "SN (lpp_stable_observed_calls operation (set (lpp_stable_rank_row_list route_rank n D)) P :: string lpp_success_iatom rel)"
    by (rule lpp_check_order_backend_sound[OF I J compatible child transfer])
  show "SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set D)) P :: string lpp_success_iatom rel)"
    using sn by (simp only: lpp_stable_rank_row_list_set)
qed


ML \<open>
val checked = [@{thm lpp_check_order_backend_sound}, @{thm lpp_check_order_backend_routing_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted actual-return backend dependency" else ();
\<close>
end
