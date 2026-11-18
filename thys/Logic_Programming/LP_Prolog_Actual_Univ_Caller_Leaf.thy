theory LP_Prolog_Actual_Univ_Caller_Leaf
 imports LP_Prolog_Checked_Univ_Caller_Path
begin

text \<open>The existing builtin interpretation requires its successful unifier
to be most general in every continuation. Instantiate that requirement with an
observer goal for the caller value. This is a proof context, not a new source
goal or an altered SEG.\<close>

lemma lpp_actual_univ_success_caller_leaf:
 assumes outcome: "lpp_univ_view_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) (LPPBuiltinSuccess sigma)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and known: "lpp_runtime_leaf_effect A shape caller_value"
 and protected: "{x,y}\<inter>set2_lp_iterm caller_value={}"
 shows "lpp_runtime_leaf_effect A shape (lp_isubst caller_value sigma)"
proof -
 have mgu: "lpc_mgu_unify
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y])
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIFun (names f) [],lpp_argument_list ts])
   [LPCAtom caller_value] sigma"
  using outcome by (simp add: lpp_univ_decompose_outcome_def)
 have finite_args: "lpp_finite_term (lpp_argument_list ts)"
  using finite by (simp add: lpp_argument_list_finite)
 show ?thesis
  apply (rule lpp_runtime_leaf_effect_separated_pair[OF known mgu _ finite_args distinct _ protected,
    where g="LPCAtom caller_value"])
  using fresh by (auto simp: lpp_argument_list_support)
qed

lemma lpp_actual_univ_leaf_stack_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,
     LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]])#gs),eta)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant A specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,
     LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]])#gs),eta)#saved)"
 and finite: "list_all lpp_finite_term ts"
 and distinct: "x\<noteq>y"
 and fresh: "x\<notin>set2_lp_iterm (LPIFun f ts)" "y\<notin>set2_lp_iterm (LPIFun f ts)"
 and protected: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   {x,y}\<inter>set2_lp_iterm (eta slot)={}"
 shows "lpp_leaf_stack_invariant A specs tt"
proof (rule lpp_leaf_stack_domain_step[OF step invariant])
 fix event tt
 assume base: "lpc_answer_transition P
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,
     LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]])#gs),eta)#saved) event tt"
 show "lpp_leaf_stack_invariant A specs tt"
  by (rule lpp_leaf_stack_base_step[OF base invariant]) auto
next
 fix builtin arguments rest rho es sigma
 assume frame: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,
     LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]])#gs),eta)#saved)=
    (LPCGoals (LPCAtom (LPIFun (LPCUser builtin) arguments)#rest),rho)#es"
 and success: "lpp_univ_source_builtin names operation builtin arguments (LPPBuiltinSuccess sigma)"
 have outcome: "lpp_univ_view_outcome names (LPIFun f ts)
   (LPIFun (LPCUser ''2:prolog_data_2e'') [LPIVar x,LPIVar y]) (LPPBuiltinSuccess sigma)"
 and same: "rho=eta"
  using frame success by (auto simp: lpp_univ_source_builtin_def)
 show "lpp_leaf_environment_transport A specs rho sigma"
  unfolding same lpp_leaf_environment_transport_def
  by (auto intro: lpp_actual_univ_success_caller_leaf[OF outcome finite distinct fresh _ protected])
qed

lemma lpp_actual_variable_univ_leaf_stack_step:
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar v,requested])#gs),eta)#saved) event tt"
 and invariant: "lpp_leaf_stack_invariant A specs
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar v,requested])#gs),eta)#saved)"
 shows "lpp_leaf_stack_invariant A specs tt"
proof (rule lpp_leaf_stack_domain_step[OF step invariant])
 fix event tt
 assume base: "lpc_answer_transition P
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar v,requested])#gs),eta)#saved) event tt"
 show "lpp_leaf_stack_invariant A specs tt"
  by (rule lpp_leaf_stack_base_step[OF base invariant]) auto
next
 fix builtin arguments rest rho es sigma
 assume frame: "((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIVar v,requested])#gs),eta)#saved)=
    (LPCGoals (LPCAtom (LPIFun (LPCUser builtin) arguments)#rest),rho)#es"
 and success: "lpp_univ_source_builtin names operation builtin arguments (LPPBuiltinSuccess sigma)"
 show "lpp_leaf_environment_transport A specs rho sigma"
  using frame success by (auto simp: lpp_univ_source_builtin_def)
qed

ML \<open>
val checked = @{thms lpp_actual_univ_success_caller_leaf lpp_actual_univ_leaf_stack_step
 lpp_actual_variable_univ_leaf_stack_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual univ caller preservation" else ();
\<close>
end
