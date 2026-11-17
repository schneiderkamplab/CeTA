theory LP_Prolog_Pattern_Head
 imports LP_Prolog_Head_Constraints LP_Prolog_Scalar_Recurrence_Interface
begin

definition lpp_pattern_args where
 "lpp_pattern_args H constants = map (\<lambda>i. case constants!i of
    None \<Rightarrow> Var (H!i) | Some f \<Rightarrow> Fun (LPCUser f) []) [0..<length H]"
definition lpp_pattern_variables where
 "lpp_pattern_variables H constants = map (\<lambda>i. H!i)
    (filter (\<lambda>i. constants!i=None) [0..<length H])"
definition lpp_pattern_constraints where
 "lpp_pattern_constraints actuals constants = concat (map (\<lambda>i.
    case constants!i of None \<Rightarrow> [] | Some f \<Rightarrow> [(actuals!i,f)]) [0..<length constants])"

lemma lpp_pattern_args_nth:
 "i<length H \<Longrightarrow> lpp_pattern_args H constants!i =
   (case constants!i of None \<Rightarrow> Var (H!i) | Some f \<Rightarrow> Fun (LPCUser f) [])"
 by (cases "constants!i") (simp_all add: lpp_pattern_args_def)

lemma lpp_pattern_variables_exact:
 "set (lpp_pattern_variables H constants)=vars_term (Fun (LPCUser q) (lpp_pattern_args H constants))"
 by (auto simp: lpp_pattern_variables_def lpp_pattern_args_def split: option.splits)

lemma lpp_pattern_constraints_iff:
 "lpp_head_constraints (lpp_pattern_constraints actuals constants) sigma =
  (\<forall>i<length constants. \<forall>f. constants!i=Some f \<longrightarrow>
    lp_isubst (actuals!i) sigma=LPIFun (LPCUser f) [])"
 by (auto simp: lpp_head_constraints_def lpp_pattern_constraints_def list_all_iff split: option.splits)

lemma lpp_pattern_unifier_constraints:
 assumes lengths: "length H=length constants" "length actuals=length constants"
   and unified: "lp_isubst (LPIFun (LPCUser q) actuals) sigma =
     lp_ieval (Fun (LPCUser q) (lpp_pattern_args H constants)) rho"
 shows "lpp_head_constraints (lpp_pattern_constraints actuals constants) sigma"
proof (unfold lpp_pattern_constraints_iff, intro allI impI)
 fix i f assume bound: "i<length constants" and const_row: "constants!i=Some f"
 have maps: "map (\<lambda>t. lp_isubst t sigma) actuals =
   map (\<lambda>t. lp_ieval t rho) (lpp_pattern_args H constants)"
   using unified by simp
 show "lp_isubst (actuals!i) sigma=LPIFun (LPCUser f) []"
   using arg_cong[OF maps, of "\<lambda>ts. ts!i"] bound lengths const_row
   by (cases "constants!i") (simp_all add: lpp_pattern_args_def)
qed

lemma lpp_pattern_head_match:
 assumes lengths: "length H=length constants" "length actuals=length constants"
   and distinct: "distinct H"
   and solved: "lpp_head_constraints (lpp_pattern_constraints actuals constants) mu"
 shows "lp_isubst (LPIFun (LPCUser q) actuals) mu =
   lp_ieval (Fun (LPCUser q) (lpp_pattern_args H constants))
     (lpp_partial_arguments H (map (\<lambda>t. lp_isubst t mu) actuals))"
proof -
 let ?eta = "lpp_partial_arguments H (map (\<lambda>t. lp_isubst t mu) actuals)"
 have each: "lp_isubst (actuals!i) mu=lp_ieval (lpp_pattern_args H constants!i) ?eta"
   if bound: "i<length H" for i
 proof (cases "constants!i")
  case None
  have nth: "?eta (H!i)=lp_isubst (actuals!i) mu"
    using lpp_partial_arguments_nth[OF _ distinct bound,
      where actuals="map (\<lambda>t. lp_isubst t mu) actuals"] lengths bound by simp
  show ?thesis using nth None bound by (simp add: lpp_pattern_args_nth)
 next
  case (Some f)
  have val: "lp_isubst (actuals!i) mu=LPIFun (LPCUser f) []"
    using solved Some bound lengths by (auto simp: lpp_pattern_constraints_iff)
  show ?thesis using val Some bound by (simp add: lpp_pattern_args_nth)
 qed
 have maps: "map (\<lambda>t. lp_isubst t mu) actuals = map (\<lambda>t. lp_ieval t ?eta) (lpp_pattern_args H constants)"
   proof (rule nth_equalityI)
   show "length (map (\<lambda>t. lp_isubst t mu) actuals)=length (map (\<lambda>t. lp_ieval t ?eta) (lpp_pattern_args H constants))"
     using lengths by (simp add: lpp_pattern_args_def)
  next
   fix i assume bound: "i<length (map (\<lambda>t. lp_isubst t mu) actuals)"
   have index: "i<length H" using bound lengths by simp
   show "map (\<lambda>t. lp_isubst t mu) actuals!i = map (\<lambda>t. lp_ieval t ?eta) (lpp_pattern_args H constants)!i"
     using each[OF index] index lengths by (cases "constants!i") (simp_all add: lpp_pattern_args_def)
  qed
 show ?thesis using maps by simp
qed

lemma lpp_pattern_head_mgu:
 fixes actuals :: "(string lp_cut_symbol,string) lp_iterm list"
 assumes lengths: "length H=length constants" "length actuals=length constants"
   and distinct: "distinct H"
   and solved: "lpp_solve_head_constraints (lpp_pattern_constraints actuals constants)=Some mu"
 shows "lpc_mgu_resolve (LPIFun (LPCUser q) actuals) gs
   (Fun (LPCUser q) (lpp_pattern_args H constants)) bs
   (\<lambda>x. lp_isubst (mu x) lpc_fresh_caller)
   (lpc_fresh_head_environment (lpp_pattern_variables H constants)
     (lpp_partial_arguments H (map (\<lambda>t. lp_isubst t mu) actuals)))"
proof (rule lpc_factored_head_mgu)
 show "set (lpp_pattern_variables H constants)=vars_term (Fun (LPCUser q) (lpp_pattern_args H constants))"
   by (rule lpp_pattern_variables_exact)
 show "lp_isubst (LPIFun (LPCUser q) actuals) mu =
   lp_ieval (Fun (LPCUser q) (lpp_pattern_args H constants))
     (lpp_partial_arguments H (map (\<lambda>t. lp_isubst t mu) actuals))"
   by (rule lpp_pattern_head_match[OF lengths distinct lpp_solve_head_constraints_sound[OF solved]])
next
 fix tau nu :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" and x
 assume unifies: "lp_isubst (LPIFun (LPCUser q) actuals) tau =
   lp_ieval (Fun (LPCUser q) (lpp_pattern_args H constants)) nu"
 show "lp_isubst (mu x) tau=tau x"
   by (rule lpp_solve_head_constraints_preserves[OF solved lpp_pattern_unifier_constraints[OF lengths unifies]])
qed

ML \<open>
val checked = [@{thm lpp_pattern_head_mgu}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted linear constructor head matching" else ();
\<close>
end
