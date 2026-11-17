theory LP_Prolog_Functor_Free_Link
 imports LP_Prolog_Functor_Link LP_Prolog_Context_Free_Link
begin

definition lpp_check_free_functor_link where
 "lpp_check_free_functor_link fuel Q nds states contexts functor_contexts Fs
   nd ss G guards eqs F source_context source_functors link =
  (lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
    nd ss G guards eqs source_context source_functors link \<and>
   lpcl_target link<length Fs \<and>
   lpc_check_link_free_normalized fuel eqs F (Fs!lpcl_target link) (lpcl_bindings link))"

lemma lpp_free_functor_link_sound:
 assumes checked: "lpp_check_free_functor_link fuel Q nds states contexts functor_contexts Fs
   nd ss G guards eqs F source_context source_functors link"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) guards eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and source: "lpp_source_context_holds P source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 shows "\<exists>nu. lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss) =
   lpc_return_eval nu (states!lpcl_target link) \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
   lpc_free_knowledge (set (Fs!lpcl_target link)) nu \<and>
   lpp_source_context_holds P (contexts!lpcl_target link) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target link) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
proof -
 have base: "lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
    nd ss G guards eqs source_context source_functors link"
 and free_check: "lpc_check_link_free_normalized fuel eqs F (Fs!lpcl_target link) (lpcl_bindings link)"
  using checked by (auto simp: lpp_check_free_functor_link_def)
 have child_free: "lpc_free_knowledge (set (Fs!lpcl_target link))
   (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings link) x) eta')"
  by (rule lpc_checked_link_free_normalized_sound[OF free_check equations free])
 show ?thesis using lpp_return_functor_link_sound[OF base equations old known source functors]
  child_free by blast
qed

lemma lpp_free_functor_link_missing_free_table_rejected:
 "\<not> lpp_check_free_functor_link fuel Q nds states contexts functor_contexts []
   nd ss G guards eqs F source_context source_functors link"
 by (simp add: lpp_check_free_functor_link_def)

ML \<open>
val checked = [@{thm lpp_free_functor_link_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted free functor link dependency" else ();
\<close>
end
