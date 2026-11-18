theory LP_Prolog_Leaf_Spine_Head
 imports LP_Prolog_Leaf_Stack_Steps LP_Prolog_Finite_List_Head
begin

text \<open>A successful linear list-head resolution on an observed proper
spine is actual matching, even when the symbolic call argument is a variable.
This supplies caller-effect preservation without assuming finite elements from
spine length alone.\<close>

lemma lpp_spine_head_matching_witness:
 assumes spine: "lpp_list_length arg n"
 and mgu: "lpc_mgu_resolve (LPIFun f (arg#actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) bs sigma rho"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 shows "\<exists>nu. lp_ieval (Fun f
   (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) nu =
   LPIFun f (arg#actuals)"
proof -
 obtain a b where shape: "arg=LPIFun (LPCUser ''2:prolog_data_2e'') [a,b]"
  using lpp_list_head_success_shape[OF spine mgu] by blast
 let ?nu = "lpp_partial_arguments (x#y#H) (a#b#actuals)"
 have exact: "map ?nu (x#y#H)=a#b#actuals"
  by (rule lpp_partial_arguments_exact[OF _ distinct]) (simp add: lengths)
 show ?thesis by (rule exI[of _ "?nu"])
  (use exact in \<open>simp add: shape map_map o_def\<close>)
qed

lemma lpp_leaf_environment_spine_head:
 fixes eta sigma rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) bs sigma rho"
 and call_shape: "lp_ieval call eta=LPIFun f (arg#actuals)"
 and spine: "lpp_list_length arg n"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and covered: "\<And>slot shape. (slot,shape)\<in>set specs \<Longrightarrow>
   slot\<in>vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_environment_transport A specs eta sigma"
proof -
 have actual: "lpc_mgu_resolve (LPIFun f (arg#actuals))
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) bs sigma rho"
  using mgu call_shape by simp
 obtain nu where matching: "lp_ieval (Fun f
   (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) nu=lp_ieval call eta"
  using lpp_spine_head_matching_witness[OF spine actual distinct lengths] by (auto simp: call_shape)
 show ?thesis by (rule lpp_leaf_environment_matching[OF mgu matching covered])
qed

ML \<open>
val checked = @{thms lpp_spine_head_matching_witness lpp_leaf_environment_spine_head};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf spine head" else ();
\<close>
end
