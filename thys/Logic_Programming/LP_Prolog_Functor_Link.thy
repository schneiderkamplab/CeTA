theory LP_Prolog_Functor_Link
 imports LP_Prolog_Functor_Context
begin

text \<open>Extend the shared return-table link with explicit functor relations.
Both old source facts and new relations use exactly the link's checked instance
substitution. Target evidence is selected by the same target index as the state;
no caller may substitute a different successful context for a saved alternative.\<close>

definition lpp_check_return_functor_link where
 "lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
   nd ss G guards eqs source_context source_functors link =
  (lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link \<and>
   lpcl_target link<length contexts \<and> lpcl_target link<length functor_contexts \<and>
   lpp_source_context_transport source_context (contexts!lpcl_target link) (lpcl_bindings link) \<and>
   lpp_check_functor_transport source_functors (functor_contexts!lpcl_target link)
     (lp_cut_instance_subst (lpcl_bindings link)))"

lemma lpp_source_context_transport_holds:
 "lpp_source_context_transport source_context target_context bindings \<Longrightarrow>
  lpp_source_context_holds P source_context eta \<Longrightarrow>
  lpp_source_context_holds P target_context (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
 by (cases source_context; cases target_context)
  (auto dest: lpp_context_transport_sound)

lemma lpp_return_functor_link_sound:
 assumes checked: "lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
   nd ss G guards eqs source_context source_functors link"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) guards eta'"
 and source: "lpp_source_context_holds P source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 shows "\<exists>nu. lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss) =
   lpc_return_eval nu (states!lpcl_target link) \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
   lpp_source_context_holds P (contexts!lpcl_target link) nu \<and>
   list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target link) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
proof -
 let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings link) x) eta'"
 have base: "lpc_check_return_link fuel Q nds nd ss G guards eqs (states!lpcl_target link) link"
  using checked by (simp add: lpp_check_return_functor_link_def lpc_check_return_table_link_def)
 have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps link)
    (lpc_return_eval ?nu (states!lpcl_target link))"
 and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) ?nu"
 and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
    [(lpcn_pred (nds!lpcl_target link),map ?nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
  using lpc_return_link_sound[OF base equations old known] by blast+
 have child: "lpp_source_context_holds P (contexts!lpcl_target link) ?nu"
  by (rule lpp_source_context_transport_holds[OF _ source])
   (use checked in \<open>simp add: lpp_check_return_functor_link_def\<close>)
 have child_functors: "list_all (lpp_functor_fact_holds names ?nu) (functor_contexts!lpcl_target link)"
  by (rule lpp_check_functor_transport_sound[OF _ functors])
   (use checked in \<open>simp add: lpp_check_return_functor_link_def\<close>)
 show ?thesis by (rule exI[of _ ?nu])
  (use same child_known edge child child_functors in \<open>simp add: lpc_return_scope_word_inverse\<close>)
qed

lemma lpp_functor_link_missing_context_rejected:
 "\<not> lpp_check_return_functor_link fuel Q nds states contexts []
   nd ss G guards eqs source_context source_functors link"
 by (simp add: lpp_check_return_functor_link_def)

lemma lpp_functor_link_target_out_of_bounds_rejected:
 "length functor_contexts\<le>lpcl_target link \<Longrightarrow>
  \<not> lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
    nd ss G guards eqs source_context source_functors link"
 by (auto simp: lpp_check_return_functor_link_def)

lemma lpp_functor_link_missing_fact_rejected:
 "functor_contexts!lpcl_target link=[observation] \<Longrightarrow>
  \<not> lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
    nd ss G guards eqs source_context [] link"
 by (simp add: lpp_check_return_functor_link_def lpp_check_functor_transport_def)

lemma lpp_functor_link_changed_arguments_rejected:
 "functor_contexts!lpcl_target link=[LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''B'')] \<Longrightarrow>
  lp_cut_instance_subst (lpcl_bindings link)=Var \<Longrightarrow>
  \<not> lpp_check_return_functor_link fuel Q nds states contexts functor_contexts
    nd ss G guards eqs source_context [LPPFunctorFact (Var ''V'') (Var ''N'') (Var ''A'')] link"
 by (simp add: lpp_check_return_functor_link_def lpp_check_functor_transport_def)

lemma lpp_functor_link_empty_extension:
 "lpp_check_return_functor_link fuel Q nds states contexts (replicate (length states) [])
    nd ss G guards eqs source_context [] link =
  (lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link \<and>
   lpcl_target link<length contexts \<and> lpcl_target link<length states \<and>
   lpp_source_context_transport source_context (contexts!lpcl_target link) (lpcl_bindings link))"
 by (auto simp: lpp_check_return_functor_link_def lpp_check_functor_transport_def)

ML \<open>
val checked = [@{thm lpp_return_functor_link_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted functor return link dependency" else ();
\<close>
end
