theory LP_Prolog_Univ_Stable_Initialization
 imports LP_Prolog_Univ_Initialization LP_Prolog_Stable_Fresh_Context
begin

lemma lpp_univ_stable_initialization_sound:
 fixes names :: "string lp_cut_symbol \<Rightarrow> string lp_cut_symbol"
 assumes checked: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template ss source_context source_functors"
 and input: "lp_ieval input_template eta=LPIFun f ts"
 and known_context: "lpp_stable_context_holds operation P source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
    name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lpc_return_eval extended ss=lpc_return_eval eta ss"
 and "lpp_stable_context_holds operation P source_context extended"
 and "list_all (lpp_functor_fact_holds names extended)
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors)"
 and "lp_ieval input_template extended=lp_ieval (Var value_variable) extended"
proof -
 have empty_checked: "lpp_check_univ_initialization value_variable name_variable arguments_variable
   input_template ss ([],[],[]) source_functors"
  using checked by (auto simp: lpp_check_univ_initialization_def lpp_context_fresh_def)
 have empty_context: "lpp_source_context_holds P ([],[],[]) eta"
  by (simp add: lpp_path_context_holds_def)
 have base:
  "lpc_return_eval extended ss=lpc_return_eval eta ss"
  "list_all (lpp_functor_fact_holds names extended)
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors)"
  "lp_ieval input_template extended=lp_ieval (Var value_variable) extended"
  using lpp_univ_initialization_sound[OF empty_checked input empty_context functors]
  unfolding extended_def by auto
 show "lpc_return_eval extended ss=lpc_return_eval eta ss" by (rule base(1))
 show "list_all (lpp_functor_fact_holds names extended)
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable)#source_functors)"
  by (rule base(2))
 show "lp_ieval input_template extended=lp_ieval (Var value_variable) extended" by (rule base(3))
 have fresh: "lpp_context_fresh value_variable source_context"
   "lpp_context_fresh name_variable source_context" "lpp_context_fresh arguments_variable source_context"
  using checked by (auto simp: lpp_check_univ_initialization_def)
 show "lpp_stable_context_holds operation P source_context extended"
  using known_context unfolding extended_def
  by (simp add: lpp_stable_context_fresh_eval[OF fresh(1)]
    lpp_stable_context_fresh_eval[OF fresh(2)] lpp_stable_context_fresh_eval[OF fresh(3)])
qed

ML \<open>
val checked = @{thms lpp_univ_stable_initialization_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ evaluation initialization dependency" else ();
\<close>
end
