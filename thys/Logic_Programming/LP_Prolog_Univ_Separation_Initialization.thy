theory LP_Prolog_Univ_Separation_Initialization
 imports LP_Prolog_Univ_Separation_Context LP_Prolog_Separation_Univ_Transport
begin

lemma lpp_univ_initializes_pair_separation:
 fixes names :: "string lp_cut_symbol\<Rightarrow>string lp_cut_symbol"
 and eta :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 and active :: "(string lp_cut_symbol,string) term list"
 and saved :: "((string lp_cut_symbol,string) term lp_cut_entry\<times>(string lp_cut_symbol,string) term list) list"
 assumes checked: "lpp_check_univ_initialization value_variable name_variable arguments_variable input_template
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,Fun pair_symbol [output_name,output_args]])#gs),active)#saved)
   source_context source_functors"
 and input: "lp_ieval input_template eta=LPIFun f ts"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and separated: "list_all (lpp_separation_holds eta)
   [LPPSeparate input_template output_name,LPPSeparate input_template output_args]"
 defines "extended \<equiv> eta(value_variable:=LPIFun f ts,
   name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)"
 shows "lpp_separation_holds extended
   (LPPSeparate (Fun pair_symbol [output_name,output_args])
     (Fun pair_symbol [Var name_variable,Var arguments_variable]))"
proof -
 have same: "lpc_return_eval extended
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,Fun pair_symbol [output_name,output_args]])#gs),active)#saved) =
   lpc_return_eval eta
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,Fun pair_symbol [output_name,output_args]])#gs),active)#saved)"
   unfolding extended_def by (rule lpp_univ_stable_initialization_sound(1)[OF checked input context_held functors])
 have retained: "lp_ieval input_template extended=lp_ieval input_template eta"
   "lp_ieval output_name extended=lp_ieval output_name eta"
   "lp_ieval output_args extended=lp_ieval output_args eta"
   using same by (auto simp: lpc_return_eval_def)
 have kept: "list_all (lpp_separation_holds extended)
   [LPPSeparate input_template output_name,LPPSeparate input_template output_args]"
   using separated by (simp add: retained)
 have observation: "lpp_functor_fact_holds names extended
   (LPPFunctorFact (Var value_variable) (Var name_variable) (Var arguments_variable))"
   using lpp_univ_stable_initialization_sound(3)[OF checked input context_held functors]
   by (simp add: extended_def)
 have equation: "lp_ieval input_template extended=lp_ieval (Var value_variable) extended"
   unfolding extended_def by (rule lpp_univ_stable_initialization_sound(4)[OF checked input context_held functors])
 show ?thesis by (rule lpp_initialized_univ_pair_separation[OF observation equation kept])
qed

ML \<open>
val checked = @{thms lpp_univ_initializes_pair_separation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted univ pair separation initialization" else ();
\<close>
end
