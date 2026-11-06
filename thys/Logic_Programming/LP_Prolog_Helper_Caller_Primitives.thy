theory LP_Prolog_Helper_Caller_Primitives
  imports LP_Prolog_Helper_Caller_Context
begin

lemma lpp_caller_comparison_step:
  assumes ctx: "lpp_caller_numeric_context H K rho eta names"
    and descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
    and holds: "lpp_integer_compare c
      (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho)"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
      (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest) @ pending)#saved,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest @ pending)#saved)
    \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  have known: "eta y=lpp_integer_value (rho y)" if "y\<in>set K" for y
    using ctx that by (simp add: lpp_caller_numeric_context_def)
  have guard: "lpp_integer_compare c
      (if reversed then lpp_expression_value b rho else lpp_expression_value a rho)
      (if reversed then lpp_expression_value a rho else lpp_expression_value b rho)"
    using holds by (cases reversed) simp_all
  note step = lpp_integer_recurrence_comparison_success[OF descriptor
    lpp_expression_evaluation[OF left known] lpp_expression_evaluation[OF right known] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest @ pending" and es=saved and P=P]
  show ?thesis using step by simp
qed

lemma lpp_caller_assignment_step:
  assumes ctx: "lpp_caller_numeric_context H K rho eta names"
    and local_fresh: "x\<notin>set H" and unknown: "x\<notin>set K"
    and expression: "lpp_expression_check K e"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
      (lpp_recurrence_goal (LPPRSet x e)#rest) @ pending)#saved,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
      (\<lambda>y. lp_isubst (eta y) (LPIVar(names x:=lpp_integer_value (lpp_expression_value e rho)))))) rest @
      map (lp_cut_map (\<lambda>t. lp_isubst t (LPIVar(names x:=lpp_integer_value (lpp_expression_value e rho))))) pending)#saved)
    \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  have known: "eta y=lpp_integer_value (rho y)" if "y\<in>set K" for y
    using ctx that by (simp add: lpp_caller_numeric_context_def)
  have fresh: "eta x=LPIVar (names x)"
    using ctx local_fresh unknown by (simp add: lpp_caller_numeric_context_def)
  show ?thesis by (rule lpp_return_assignment_step[where eta=eta and rho=rho and x=x and slot="names x",
    OF expression known fresh])
qed

ML \<open>
val checked = [@{thm lpp_caller_comparison_step}, @{thm lpp_caller_assignment_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted caller primitive composition" else ();
\<close>
end
