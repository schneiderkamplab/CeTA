theory LP_Prolog_Guarded_Helper_Return
  imports LP_Prolog_Integer_Helper_Return
begin

text \<open>A checked arithmetic prefix may establish local integer values and
successful guards before the helper assigns a caller output. All earlier
clause failures remain explicit. The conclusion is an actual source execution,
with the original saved alternatives and a substituted caller continuation.
No groundness-to-integer conversion or abstract return assumption is used.\<close>

lemma lpp_guarded_assignment_helper_success:
  assumes selection: "lp_cut_slice P (LPCUser f) (length H)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var H),(map lpp_recurrence_goal ops @ [lpp_recurrence_goal (LPPRSet x e)]))"
    and ordinary: "(f,length H)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and observed_head: "\<And>y. y\<in>set K \<Longrightarrow> y\<in>set H"
    and known: "\<And>y. y\<in>set K \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and output_head: "x\<in>set H"
    and fresh: "eta x=LPIVar slot"
    and prefix_check: "lpp_partial_recurrence_check H K ops"
    and prefix_guards: "lpp_recurrence_guards ops rho"
    and output_unknown: "x\<notin>set (lpp_recurrence_known K ops)"
    and expression: "lpp_expression_check (lpp_recurrence_known K ops) e"
  shows "\<exists>mark. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value (lpp_expression_value e (lpp_recurrence_values ops rho)))))) pending)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var H)) eta)#pending) d mark) cs @
        LPCBarrier mark#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?call = "lp_ieval (Fun (LPCUser f) (map Var H)) eta"
  let ?env = "lpc_fresh_head_environment H eta"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending"
  let ?n = "lpp_expression_value e (lpp_recurrence_values ops rho)"
  let ?mu = "LPIVar((CHR ''0''#slot):=lpp_integer_value ?n)"
  obtain mark where selected: "(LPCGoals (LPCAtom ?call#pending)#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        (map lpp_recurrence_goal ops @ [lpp_recurrence_goal (LPPRSet x e)]) @ ?pending)#
      (map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_partial_selected_clause_steps[OF selection index clause ordinary failed] by blast
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?call#pending) d mark) cs @ LPCBarrier mark#es"
  let ?K = "lpp_recurrence_known K ops"
  let ?rho = "lpp_recurrence_values ops rho"
  let ?returned = "lpp_partial_environment H ?K ?rho eta"
  have initial: "?env=lpp_partial_environment H K rho eta"
    by (rule lpp_partial_initial_environment[OF observed_head known])
  note prefix = lpp_partial_body_source_steps[OF prefix_check prefix_guards,
    where rest="[lpp_recurrence_goal (LPPRSet x e)]" and pending=pending and eta=eta and es="?saved" and P=P]
  have progressed: "(LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?env))
        (map lpp_recurrence_goal ops @ [lpp_recurrence_goal (LPPRSet x e)]) @ ?pending)#?saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?returned))
        [lpp_recurrence_goal (LPPRSet x e)] @ ?pending)#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using prefix by (simp add: initial map_map o_def lpp_recurrence_bind_goal)
  have typed: "?returned y=lpp_integer_value (?rho y)" if "y\<in>set ?K" for y
    using that by (simp add: lpp_partial_environment_def)
  have target: "?returned x=LPIVar (CHR ''0''#slot)"
    using output_head fresh output_unknown
    by (simp add: lpp_partial_environment_def lpc_fresh_caller_def)
  note assigned = lpp_return_assignment_step[where eta="?returned" and rho="?rho" and x=x and slot="CHR ''0''#slot", OF expression typed target,
    where rest="[]" and pending="?pending" and es="?saved" and P=P]
  have completed: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?returned))
        [lpp_recurrence_goal (LPPRSet x e)] @ ?pending)#?saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value ?n)))) pending)#?saved)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using assigned by (simp add: map_map lp_cut_map_comp lpc_return_fresh_caller_assignment o_def)
  show ?thesis using selected progressed completed by (meson r_into_trancl trancl_trans trancl_rtrancl_trancl)
qed

ML \<open>
val checked = [@{thm lpp_guarded_assignment_helper_success}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted guarded helper return dependency" else ();
\<close>
end
