theory LP_Prolog_Recursive_Entry_Link
 imports LP_Prolog_Recursive_Entry LP_Prolog_Parameter_Coordinate_Link
begin

text \<open>Transport the entry fragment in the very valuation representing the
checked target. Neither a coordinate map nor this rule proves a Split contract.\<close>

definition lpp_check_recursive_entry_transport where
 "lpp_check_recursive_entry_transport i p h t c i' p' h' t' c' bindings =
  (lpp_check_parameter_coordinate (Var i) (Var i') bindings \<and>
   lpp_check_parameter_coordinate (Var p) (Var p') bindings \<and>
   lpp_check_parameter_coordinate (Var h) (Var h') bindings \<and>
   lpp_check_parameter_coordinate (Var t) (Var t') bindings \<and>
   lpp_check_parameter_coordinate (Var c) (Var c') bindings)"

lemma lpp_checked_recursive_entry_transport:
 assumes checked: "lpp_check_recursive_entry_transport i p h t c i' p' h' t' c' bindings"
 and entry: "lpp_recursive_entry initial_parameter i p h t c eta"
 shows "lpp_recursive_entry initial_parameter i' p' h' t' c'
   (\<lambda>x. lp_ieval (bindings x) eta)"
 using checked entry
 by (simp add: lpp_check_recursive_entry_transport_def lpp_check_parameter_coordinate_def
   lpp_recursive_entry_def)

lemma lpp_stable_functor_link_with_recursive_entry:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and coordinates: "lpp_check_recursive_entry_transport i p h t c i' p' h' t' c'
   (lp_cut_instance_subst (lpcl_bindings e))"
 and entry: "lpp_recursive_entry initial_parameter i p h t c eta'"
 shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target e) nu \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q \<and>
   list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e) \<and>
   lpp_recursive_entry initial_parameter i' p' h' t' c' nu"
 by (rule lpp_stable_functor_link_with_parameter_facts[OF compatible program checked equations old known free observed functors])
    (rule lpp_checked_recursive_entry_transport[OF coordinates entry])

ML \<open>
val checked = @{thms lpp_checked_recursive_entry_transport lpp_stable_functor_link_with_recursive_entry};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive entry link" else ();
\<close>
end
