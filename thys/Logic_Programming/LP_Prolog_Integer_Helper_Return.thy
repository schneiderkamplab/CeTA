theory LP_Prolog_Integer_Helper_Return
  imports LP_Prolog_Integer_Return_Assignment
begin

text \<open>This contract constructs an actual finite successful helper execution.
The output binding reaches the caller continuation; it is not inferred from a
termination certificate or from an arbitrary abstract helper answer.\<close>

lemma lpp_single_assignment_helper_success:
  assumes selection: "lp_cut_slice P (LPCUser f) (length H)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var H),[lpp_recurrence_goal (LPPRSet x e)])"
    and ordinary: "(f,length H)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and observed_head: "\<And>y. y\<in>set K \<Longrightarrow> y\<in>set H"
    and known: "\<And>y. y\<in>set K \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and output_head: "x\<in>set H"
    and fresh: "eta x=LPIVar slot"
    and expression: "lpp_expression_check K e"
  shows "\<exists>mark. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value (lpp_expression_value e rho))))) pending)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark) cs @
        LPCBarrier mark#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?env = "lpc_fresh_head_environment H eta"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
  let ?n = "lpp_expression_value e rho"
  let ?mu = "LPIVar((CHR ''0''#slot):=lpp_integer_value ?n)"
  obtain mark where selected: "(LPCGoals (LPCAtom ?call#pending)#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        [lpp_recurrence_goal (LPPRSet x e)] @ ?pending)#
      (map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_partial_selected_clause_steps[OF selection index clause ordinary failed] by blast
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#es"
  have typed: "?env y=lpp_integer_value (rho y)" if "y\<in>set K" for y
    using observed_head[OF that] known[OF that]
    by (simp add: lpc_fresh_head_environment_def)
  have target: "?env x=LPIVar (CHR ''0''#slot)"
    using output_head fresh by (simp add: lpc_fresh_head_environment_def lpc_fresh_caller_def)
  note assigned = lpp_return_assignment_step[where eta="?env" and rho=rho and x=x and slot="CHR ''0''#slot", OF expression typed target,
    where rest="[]" and pending="?pending" and es="?saved" and P=P]
  have completed: "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        [lpp_recurrence_goal (LPPRSet x e)] @ ?pending)#?saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value ?n)))) pending)#?saved)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using assigned by (simp add: map_map lp_cut_map_comp lpc_return_fresh_caller_assignment o_def)
  show ?thesis using selected completed by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpp_single_assignment_helper_success}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted actual helper return dependency" else ();
\<close>
end
