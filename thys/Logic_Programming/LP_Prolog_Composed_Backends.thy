theory LP_Prolog_Composed_Backends
 imports LP_Prolog_Stable_Backend_Routing LP_Prolog_Stable_Row_Composition
begin

fun lpp_composition_rows where
 "lpp_composition_rows [] D = D"
| "lpp_composition_rows (k#ks) D = lpp_composition_rows ks (lpp_compose_observed_rows k D)"

fun lpp_check_composition where
 "lpp_check_composition [] D = True"
| "lpp_check_composition (k#ks) D =
   (list_all (lpp_observed_row_short k) D \<and>
    lpp_check_composition ks (lpp_compose_observed_rows k D))"

lemma lpp_composition_rows_SN:
 assumes checked: "lpp_check_composition ks D"
 and sn: "SN (lpp_stable_observed_calls operation (set (lpp_composition_rows ks D)) P)"
 shows "SN (lpp_stable_observed_calls operation (set D) P)"
 using checked sn
proof (induction ks arbitrary: D)
 case Nil then show ?case by simp
next
 case (Cons k ks)
 have short: "list_all (lpp_observed_row_short k) D"
  and rest: "lpp_check_composition ks (lpp_compose_observed_rows k D)"
  using Cons.prems(1) by auto
 have child: "SN (lpp_stable_observed_calls operation
    (set (lpp_composition_rows ks (lpp_compose_observed_rows k D))) P)"
  using Cons.prems(2) by simp
 have sn: "SN (lpp_stable_observed_calls operation (set (lpp_compose_observed_rows k D)) P)"
  by (rule Cons.IH[OF rest child])
 show ?case by (rule lpp_compose_observed_rows_SN[OF short sn])
qed

fun lpp_same_observed_row where
 "lpp_same_observed_row ((h,ps,b,gs),os) ((h2,ps2,b2,gs2),os2) =
  (h=h2 \<and> b=b2 \<and> set ps=set ps2 \<and> set gs=set gs2 \<and> set os=set os2)"

lemma lpp_same_observed_row_calls:
 assumes same: "lpp_same_observed_row r s"
 shows "lpp_stable_observed_calls operation {r} P = lpp_stable_observed_calls operation {s} P"
proof -
 obtain h ps b gs os where r: "r=((h,ps,b,gs),os)" by (cases r) auto
 obtain h2 ps2 b2 gs2 os2 where s: "s=((h2,ps2,b2,gs2),os2)" by (cases s) auto
 have eq: "h=h2" "b=b2" "set ps=set ps2" "set gs=set gs2" "set os=set os2"
  using same by (auto simp: r s)
 show ?thesis unfolding r s lpp_stable_observed_calls_def
  by (simp add: list_all_iff eq)
qed

lemma lpp_same_observed_rows_calls:
 assumes same: "list_all2 lpp_same_observed_row D E"
 shows "lpp_stable_observed_calls operation (set D) P = lpp_stable_observed_calls operation (set E) P"
 using same
proof induction
 case Nil show ?case by simp
next
 case (Cons r s D E)
 have union: "lpp_stable_observed_calls operation (insert r (set D)) P =
  lpp_stable_observed_calls operation {r} P \<union> lpp_stable_observed_calls operation (set D) P" for r D
  unfolding lpp_stable_observed_calls_def by blast
 show ?case using Cons.IH lpp_same_observed_row_calls[OF Cons.hyps(1), of operation P] by (simp add: union; blast)
qed

definition lpp_check_composed_backend where
 "lpp_check_composed_backend I J T P D data = (case data of (ks,child_rows,child) \<Rightarrow>
  lpp_check_composition ks D \<and>
  list_all2 lpp_same_observed_row (lpp_composition_rows ks D) child_rows \<and>
  lpp_check_stable_backend I J T P child_rows child)"

theorem lpp_check_composed_backend_sound:
 fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
 assumes I: "tp_spec I" and J: "dpp_spec J"
 and compatible: "lpp_stable_integer_operations operation"
 and checked: "lpp_check_composed_backend I J T P D data"
 and transfer: "lpp_check_transfer_program T P receipts"
 shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof -
 obtain ks child_rows child where data: "data=(ks,child_rows,child)" by (cases data) auto
 have stages: "lpp_check_composition ks D"
 and same: "list_all2 lpp_same_observed_row (lpp_composition_rows ks D) child_rows"
 and backend: "lpp_check_stable_backend I J T P child_rows child"
  using checked by (auto simp: lpp_check_composed_backend_def data)
 have sn: "SN (lpp_stable_observed_calls operation (set (lpp_composition_rows ks D)) P :: string lpp_success_iatom rel)"
  using lpp_check_stable_backend_sound[OF I J compatible backend transfer]
   lpp_same_observed_rows_calls[OF same, of operation P] by metis
 show ?thesis by (rule lpp_composition_rows_SN[OF stages sn])
qed

definition lpp_check_composed_backend_routing where
 "lpp_check_composed_backend_routing I J T P ranks D backends =
  (lpp_check_stable_finite_routing ranks (length backends) D \<and>
   list_all (\<lambda>n. lpp_check_composed_backend I J T P
    (lpp_stable_rank_row_list ranks n D) (backends!n)) [0..<length backends])"

theorem lpp_check_composed_backend_routing_sound:
 fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
 assumes I: "tp_spec I" and J: "dpp_spec J"
 and compatible: "lpp_stable_integer_operations operation"
 and checked: "lpp_check_composed_backend_routing I J T P ranks D backends"
 and transfer: "lpp_check_transfer_program T P receipts"
 shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (rule lpp_stable_finite_routed_calls_SN[where component_count="length backends"])
 show "lpp_check_stable_finite_routing ranks (length backends) D"
  using checked by (simp add: lpp_check_composed_backend_routing_def)
next
 fix n assume n: "n<length backends"
 have child: "lpp_check_composed_backend I J T P (lpp_stable_rank_row_list ranks n D) (backends!n)"
  using checked n by (auto simp: lpp_check_composed_backend_routing_def list_all_iff)
 have sn: "SN (lpp_stable_observed_calls operation (set (lpp_stable_rank_row_list ranks n D)) P :: string lpp_success_iatom rel)"
  by (rule lpp_check_composed_backend_sound[OF I J compatible child transfer])
 show "SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows ranks n (set D)) P :: string lpp_success_iatom rel)"
  using sn by (simp only: lpp_stable_rank_row_list_set)
qed

ML \<open>
val checked = [@{thm lpp_composition_rows_SN}, @{thm lpp_check_composed_backend_routing_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
 then error "Untrusted composed backend" else ();
\<close>
end
