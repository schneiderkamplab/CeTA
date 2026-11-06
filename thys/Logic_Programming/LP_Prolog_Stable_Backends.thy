theory LP_Prolog_Stable_Backends
 imports LP_Prolog_Stable_Structural_Child LP_Prolog_Stable_Numeric_Component
   LP_Prolog_Stable_Relational_Routing
begin

definition lpp_check_stable_backend where
  "lpp_check_stable_backend I J T P D backend =
    (case backend of
      Inl (entries,evidence,child_rows,predicates,constructors,outs,fallback,dnames,pnames,marks,filters,labs,proofs) \<Rightarrow>
        lpp_check_structural_entry_coverage T entries D evidence \<and>
        set child_rows=lpp_erase_triples (fst ` set D) \<and>
        lpp_check_structural_pidp_entries I J child_rows (lpp_erase_success P) entries
          (lpc_lookup fallback predicates) (lpc_lookup fallback constructors)
          outs (fallback :: (string,nat list) lab) dnames pnames marks filters labs proofs
    | Inr (positions,coordinates,modes,locations,system,row_receipts,child) \<Rightarrow>
        lpp_check_stable_projected_numeric_component T positions coordinates modes locations system D row_receipts child)"

theorem lpp_check_stable_backend_sound:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_backend I J T P D backend"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (cases backend)
  case (Inl structural)
  obtain entries evidence child_rows predicates constructors outs fallback dnames pnames marks filters labs proofs
    where shape: "structural=(entries,evidence,child_rows,predicates,constructors,outs,fallback,dnames,pnames,marks,filters,labs,proofs)"
    by (cases structural) auto
  have coverage: "lpp_check_structural_entry_coverage T entries D evidence"
    and subject: "set child_rows=lpp_erase_triples (fst ` set D)"
    and children: "lpp_check_structural_pidp_entries I J child_rows (lpp_erase_success P) entries
      (lpc_lookup fallback predicates) (lpc_lookup fallback constructors)
      outs fallback dnames pnames marks filters labs proofs"
    using checked by (simp_all add: lpp_check_stable_backend_def Inl shape)
  show ?thesis by (rule lpp_checked_structural_pidp_component[OF I J compatible coverage transfer subject children])
next
  case (Inr numeric)
  obtain positions coordinates modes locations system row_receipts child
    where shape: "numeric=(positions,coordinates,modes,locations,system,row_receipts,child)"
    by (cases numeric) auto
  have component: "lpp_check_stable_projected_numeric_component T positions coordinates modes locations system D row_receipts child"
    using checked by (simp add: lpp_check_stable_backend_def Inr shape)
  show ?thesis by (rule lpp_check_stable_projected_numeric_component_sound[OF compatible component transfer])
qed

ML \<open>
val checked = [@{thm lpp_check_stable_backend_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted stable backend selection" else ();
\<close>
end
