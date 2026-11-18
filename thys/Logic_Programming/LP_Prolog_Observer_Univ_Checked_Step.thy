theory LP_Prolog_Observer_Univ_Checked_Step
 imports LP_Prolog_Observer_Fresh_Simulation
begin

theorem lpp_checked_separation_univ_source_step:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts)"
 and extra: "lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and source_program: "lp_cut_source_program P"
 and coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_return_eval eta (states!i)) event result"
 shows "event=None \<and> (result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) result u))"
proof -
 obtain a gs active saved where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,Fun pair_symbol [output_name,output_args]])#gs),active)#saved"
  and incoming: "set [LPPSeparate a output_name,LPPSeparate a output_args]\<subseteq> set (separation_contexts!i)"
  and bound: "lpcl_target middle<length separation_contexts"
  and transport: "lpp_check_separation_transport
    [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]
    (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
  using lpp_checked_separation_univ_shape[OF extra] by blast
 have init: "lpp_check_univ_initialization value_var name_var args_var a (states!i) (contexts!i) (functor_contexts!i)"
   using checked by (auto simp: shape lpp_check_functor_source_action_def lpp_check_univ_evaluation_context_def)
 have separated: "list_all (lpp_separation_holds eta) [LPPSeparate a output_name,LPPSeparate a output_args]"
   using incoming conditions unfolding lpp_separation_node_conditions_def list_all_iff by blast
 have initialized: "list_all (lpp_separation_holds
     (eta(value_var:=LPIFun f ts,name_var:=LPIFun (names f) [],args_var:=lpp_argument_list ts)))
     [LPPSeparate (Fun pair_symbol [output_name,output_args]) (Fun pair_symbol [Var name_var,Var args_var])]"
   if input: "lp_ieval a eta=LPIFun f ts" for f ts
   using lpp_univ_initializes_pair_separation[OF init[unfolded shape] input observed functors separated] by simp
 have check: "lpp_check_univ_evaluation_context T facts fuel Q nds states contexts functor_contexts Fs
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i)
   a (Fun pair_symbol [output_name,output_args]) gs active saved value_var name_var args_var middle"
  using checked by (simp add: shape lpp_check_functor_source_action_def)
 have dom_check: "lpp_check_univ_view_domain (Fs!i) a (Fun pair_symbol [output_name,output_args])"
  using check by (simp add: lpp_check_univ_evaluation_context_def)
 have domain: "lpp_univ_view_domain (lp_ieval a eta) (lp_ieval (Fun pair_symbol [output_name,output_args]) eta)"
  by (rule lpp_check_univ_view_domain_sound[OF dom_check free])
 show ?thesis
  apply (rule lpp_checked_univ_module_block[OF compatible transfer check bound transport _
    known free observed functors domain finite step source_program])
  subgoal for f ts by (rule initialized[of f ts]) assumption
  subgoal for j nu by (rule coverage[of j nu]) assumption+
  done
qed

ML \<open>
val checked = @{thms lpp_checked_separation_univ_source_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked univ source step" else ();
\<close>
end
