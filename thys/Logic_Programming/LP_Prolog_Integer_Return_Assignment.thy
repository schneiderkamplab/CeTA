theory LP_Prolog_Integer_Return_Assignment
  imports LP_Prolog_Partial_Integer_Iteration
begin

text \<open>A helper output can refer to a caller variable. Its assignment must
substitute the whole active continuation, including aliases. Saved failure
alternatives retain their original values.\<close>

lemma lpp_return_assignment_known:
  assumes known: "\<And>y. y\<in>set K \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and fresh: "eta x=LPIVar slot"
    and member: "y\<in>set (x#K)"
  shows "lp_isubst (eta y) (LPIVar(slot:=lpp_integer_value n))=
    lpp_integer_value ((rho(x:=n)) y)"
  using known fresh member by auto

lemma lpp_return_assignment_step:
  assumes checked: "lpp_expression_check K e"
    and known: "\<And>y. y\<in>set K \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and fresh: "eta x=LPIVar slot"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (lpp_recurrence_goal (LPPRSet x e)#rest) @ pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (\<lambda>y. lp_isubst (eta y) (LPIVar(slot:=lpp_integer_value (lpp_expression_value e rho)))))) rest @
        map (lp_cut_map (\<lambda>t. lp_isubst t (LPIVar(slot:=lpp_integer_value (lpp_expression_value e rho))))) pending)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?n = "lpp_expression_value e rho"
  let ?mu = "LPIVar(slot:=lpp_integer_value ?n)"
  have evaluated: "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) eta) ?n"
    by (rule lpp_expression_evaluation[OF checked known])
  have assigned: "lpp_integer_unifier (eta x) ?n=Some ?mu" by (simp add: fresh)
  note step = lpp_integer_recurrence_assignment[OF evaluated assigned,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest @ pending" and es=es and P=P]
  show ?thesis using step by (simp add: map_map lp_cut_map_comp lp_ieval_subst o_def)
qed

lemma lpc_return_fresh_caller_assignment:
  "lp_isubst (lp_isubst t lpc_fresh_caller)
      (LPIVar((CHR ''0''#slot):=lpp_integer_value n)) =
    lp_isubst t (lpc_fresh_caller(slot:=lpp_integer_value n))"
proof -
  have composed: "(\<lambda>x. lp_isubst (lpc_fresh_caller x)
      (LPIVar((CHR ''0''#slot):=lpp_integer_value n)))=
      lpc_fresh_caller(slot:=lpp_integer_value n)"
    by (rule ext) (simp add: lpc_fresh_caller_def)
  show ?thesis by (simp only: lpc_isubst_comp composed)
qed

ML \<open>
val checked = [@{thm lpp_return_assignment_known}, @{thm lpp_return_assignment_step},
  @{thm lpc_return_fresh_caller_assignment}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted integer return assignment dependency" else ();
\<close>
end
