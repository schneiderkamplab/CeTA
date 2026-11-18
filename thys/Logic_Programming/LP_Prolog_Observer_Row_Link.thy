theory LP_Prolog_Observer_Row_Link
 imports LP_Prolog_Attached_Observer_Product
begin

text \<open>Recombine the helper's checked row representation with the actual
caller observation, frame by frame. The caller environment is not reconstructed
from helper bindings. Equal source frames are required before combining two
independent observation stacks; zip truncation cannot erase an alternative.\<close>

definition lpp_observer_join where
 "lpp_observer_join helper caller = map
  (\<lambda>((entry,h),(_,c)). (entry,case_sum h c)) (zip helper caller)"

lemma lpp_observer_join_projections:
 assumes aligned: "map fst helper=map fst caller"
 shows "lpc_reinterface (\<lambda>eta x. eta (Inl x)) (lpp_observer_join helper caller)=helper"
 and "lpc_reinterface (\<lambda>eta x. eta (Inr x)) (lpp_observer_join helper caller)=caller"
 using aligned
 by (induct helper arbitrary: caller)
  (auto simp: lpp_observer_join_def lpc_reinterface_def split: list.splits prod.splits)

lemma lpp_observer_join_reconstruct:
 "lpp_observer_join (lpc_reinterface (\<lambda>eta x. eta (Inl x)) ss)
   (lpc_reinterface (\<lambda>eta x. eta (Inr x)) ss)=ss"
proof -
 have both: "case_sum (\<lambda>x. eta (Inl x)) (\<lambda>x. eta (Inr x))=eta" for eta
  by (rule ext) (case_tac x; simp)
 show ?thesis by (induct ss)
  (auto simp: lpp_observer_join_def lpc_reinterface_def both split: prod.splits)
qed

lemma lpp_observer_join_leaf:
 assumes aligned: "map fst helper=map fst caller"
 shows "lpp_leaf_stack_invariant A (map (\<lambda>(slot,shape). (Inr slot,shape)) specs)
   (lpp_observer_join helper caller) = lpp_leaf_stack_invariant A specs caller"
 using lpp_observer_reindex_leaf[where route_index=Inr and ss="lpp_observer_join helper caller"]
  lpp_observer_join_projections(2)[OF aligned] by simp

lemma lpp_observer_join_missing_frame:
 "length helper\<noteq>length caller \<Longrightarrow> map fst helper\<noteq>map fst caller"
 by (metis length_map)

lemma lpp_observer_join_stale_saved:
 assumes aligned: "map fst helper=map fst ((active_frame,active_env)#(saved_frame,saved_env)#saved)"
 and member: "(slot,shape)\<in>set specs"
 and stale: "\<not>lpp_runtime_leaf_effect A shape (saved_env slot)"
 shows "\<not>lpp_leaf_stack_invariant A (map (\<lambda>(slot,shape). (Inr slot,shape)) specs)
   (lpp_observer_join helper ((active_frame,active_env)#(saved_frame,saved_env)#saved))"
 using lpp_observer_join_leaf[OF aligned] lpp_leaf_stack_rejects_stale_saved[where A=A and specs=specs and slot=slot and shape=shape and saved_env=saved_env and active_frame=active_frame and active_env=active_env and saved_frame=saved_frame and ss=saved, OF member stale] by simp

lemma lpp_checked_observer_row_link:
 assumes checked: "lpc_check_return_link fuel Q nds nd source_rows G guards eqs child checked_link"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) guards eta'"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta' source_rows"
 defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings checked_link) x) eta'"
 shows "runtime=lpp_observer_join
   (lpc_return_scope_word (lpcl_swaps checked_link) (lpc_return_eval nu child))
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target checked_link)))
   (lpcn_guards (nds!lpcl_target checked_link)) nu"
 and "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target checked_link),map nu (lpcn_vars (nds!lpcl_target checked_link)))])\<in>lp_ild Q"
proof -
 have same: "lpc_return_eval eta' source_rows =
   lpc_return_scope_word (lpcl_swaps checked_link) (lpc_return_eval nu child)"
 and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target checked_link)))
   (lpcn_guards (nds!lpcl_target checked_link)) nu"
 and residual: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target checked_link),map nu (lpcn_vars (nds!lpcl_target checked_link)))])\<in>lp_ild Q"
  using lpc_return_link_sound[OF checked equations old known] unfolding nu_def by blast+
 show "runtime=lpp_observer_join
   (lpc_return_scope_word (lpcl_swaps checked_link) (lpc_return_eval nu child))
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
  using lpp_observer_join_reconstruct[of runtime] by (simp only: represented same)
 show "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target checked_link)))
   (lpcn_guards (nds!lpcl_target checked_link)) nu" by (rule child_known)
 show "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target checked_link),map nu (lpcn_vars (nds!lpcl_target checked_link)))])\<in>lp_ild Q"
  by (rule residual)
qed


lemma lpp_observer_reinterface_scopes:
 "lpc_reinterface F (lpc_return_scope_word swaps ss) =
  lpc_return_scope_word swaps (lpc_reinterface F ss)"
 by (induct swaps arbitrary: ss)
  (auto simp: lpc_reinterface_def map_map o_def map_prod_def split_def split: prod.splits)

lemma lpp_checked_observer_context_link:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd source_rows G K eqs F source_context source_functors e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
    and separation: "list_all (lpp_separation_holds eta') source_separation"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta' source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u \<and>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime))"
proof -
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and represented_child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (lpc_return_scope_word swaps (lpc_return_eval eta' source_rows)) u"
  using lpp_separation_functor_link_sound[OF compatible program checked separation_bound
   separation_check separation equations old known free observed functors] by blast
 show ?thesis by (rule exI[of _ u], rule exI[of _ swaps])
  (use strict represented_child invariant in
   \<open>simp add: lpp_observer_reinterface_scopes represented lpp_leaf_stack_scopes\<close>)
qed

ML \<open>
val checked = @{thms lpp_observer_join_projections lpp_observer_join_reconstruct
 lpp_observer_join_leaf lpp_checked_observer_row_link
 lpp_observer_reinterface_scopes lpp_checked_observer_context_link
 lpp_observer_join_missing_frame lpp_observer_join_stale_saved};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer row link" else ();
\<close>
end
