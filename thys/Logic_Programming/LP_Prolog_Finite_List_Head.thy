theory LP_Prolog_Finite_List_Head
 imports LP_Prolog_Finite_Matching_Head LP_Prolog_Constructor_Arguments
begin

text \<open>A proper observed spine and successful resolution expose the cons
constructor, even when the symbolic selected argument is a variable. Elements
need not be ground. Finite call and continuation premises remain explicit.\<close>

lemma lpp_list_head_success_shape:
 assumes spine: "lpp_list_length arg n"
 and mgu: "lpc_mgu_resolve (LPIFun f (arg#actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # hs)) bs sigma rho"
 shows "\<exists>a b. arg=LPIFun (LPCUser ''2:prolog_data_2e'') [a,b]"
 using spine mgu unfolding lpc_mgu_resolve_def
 by (cases rule: lpp_list_length.cases) auto

lemma lpp_list_head_finite_resolution:
 assumes spine: "lpp_list_length arg n"
 and mgu: "lpc_mgu_resolve (LPIFun f (arg#actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) bs sigma rho"
 and distinct: "distinct (x#y#H)"
 and lengths: "length H=length actuals"
 and finite: "lpp_finite_term (LPIFun f (arg#actuals))"
 and continuation: "lpp_finite_goals gs"
 shows "lpp_finite_term (lp_ieval
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) rho) \<and>
   lpp_finite_goals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs @
     map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof -
 obtain a b where shape: "arg=LPIFun (LPCUser ''2:prolog_data_2e'') [a,b]"
   using lpp_list_head_success_shape[OF spine mgu] by blast
 let ?nu = "lpp_partial_arguments (x#y#H) (a#b#actuals)"
 have exact: "map ?nu (x#y#H)=a#b#actuals"
   by (rule lpp_partial_arguments_exact[OF _ distinct]) (simp add: lengths)
 have matching: "lp_ieval (Fun f
   (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # map Var H)) ?nu =
   LPIFun f (arg#actuals)"
   using exact by (simp add: shape map_map o_def)
 show ?thesis using lpp_matching_head_finite_instance[OF mgu matching finite]
   lpp_matching_head_resolution_finite[OF mgu matching finite continuation] by blast
qed


lemma lpp_list_head_tail_observation:
 assumes spine: "lpp_list_length arg n"
 and mgu: "lpc_mgu_resolve (LPIFun f (arg#actuals)) gs
   (Fun f (Fun (LPCUser ''2:prolog_data_2e'') [Var x,Var y] # hs)) bs sigma rho"
 shows "\<exists>k. n=Suc k \<and> lpp_list_length (rho y) k"
proof -
 have preserved: "lpp_list_length (lp_isubst arg sigma) n"
   by (rule lpp_list_length_subst[OF spine])
 have equation: "lp_isubst arg sigma=LPIFun (LPCUser ''2:prolog_data_2e'') [rho x,rho y]"
   using mgu by (simp add: lpc_mgu_resolve_def)
 show ?thesis using preserved unfolding equation
   by (cases rule: lpp_list_length.cases) auto
qed

ML \<open>
val checked = @{thms lpp_list_head_success_shape lpp_list_head_finite_resolution
 lpp_list_head_tail_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite list head" else ();
\<close>
end
