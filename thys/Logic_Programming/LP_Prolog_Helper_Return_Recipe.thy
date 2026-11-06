theory LP_Prolog_Helper_Return_Recipe
  imports LP_Prolog_Helper_Return_Continuation
begin

text \<open>A finite source-bound helper recipe for exact call proofs. This
checker describes one complete, uniquely defined helper body. It does not
establish termination of a surrounding graph or replace universal return
contracts. Input values and caller-output freshness remain state premises.\<close>

record lpp_helper_return_recipe =
  lpphr_clause :: nat
  lpphr_predicate :: string
  lpphr_head :: "string list"
  lpphr_inputs :: "string list"
  lpphr_prefix :: "lpp_recurrence_operation list"
  lpphr_output :: string
  lpphr_expression :: "string lpp_integer_expression"

definition lpp_check_helper_return_recipe where
  "lpp_check_helper_return_recipe P r \<longleftrightarrow>
    lpphr_clause r<length P \<and>
     lp_cut_slice P (LPCUser (lpphr_predicate r)) (length (lpphr_head r))=[lpphr_clause r] \<and>
     P!(lpphr_clause r)=(Fun (LPCUser (lpphr_predicate r)) (map Var (lpphr_head r)),
       map lpp_recurrence_goal (lpphr_prefix r) @
         [lpp_recurrence_goal (LPPRSet (lpphr_output r) (lpphr_expression r))]) \<and>
     (lpphr_predicate r,length (lpphr_head r))\<notin>lpp_builtin_signature \<and>
     set (lpphr_inputs r)\<subseteq> set (lpphr_head r) \<and>
     lpphr_output r\<in> set (lpphr_head r) \<and>
     lpp_partial_recurrence_check (lpphr_head r) (lpphr_inputs r) (lpphr_prefix r) \<and>
     lpphr_output r\<notin> set (lpp_recurrence_known (lpphr_inputs r) (lpphr_prefix r)) \<and>
     lpp_expression_check (lpp_recurrence_known (lpphr_inputs r) (lpphr_prefix r)) (lpphr_expression r)"

theorem lpp_helper_return_recipe_sound:
  assumes checked: "lpp_check_helper_return_recipe P r"
    and known: "\<And>y. y\<in> set (lpphr_inputs r) \<Longrightarrow> eta y=lpp_integer_value (rho y)"
    and fresh: "eta (lpphr_output r)=LPIVar slot"
    and guards: "lpp_recurrence_guards (lpphr_prefix r) rho"
  shows "\<exists>mark. (LPCGoals (LPCAtom (lp_ieval
      (Fun (LPCUser (lpphr_predicate r)) (map Var (lpphr_head r))) eta)#pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t
        (lpc_fresh_caller(slot:=lpp_integer_value (lpp_expression_value (lpphr_expression r)
          (lpp_recurrence_values (lpphr_prefix r) rho)))))) pending)#LPCBarrier mark#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  have selected: "lp_cut_slice P (LPCUser (lpphr_predicate r)) (length (lpphr_head r))=
      []@lpphr_clause r#[]"
    using checked by (simp add: lpp_check_helper_return_recipe_def)
  note run = lpp_guarded_assignment_helper_success[OF selected,
    where eta=eta and rho=rho and K="lpphr_inputs r" and x="lpphr_output r"
      and e="lpphr_expression r" and ops="lpphr_prefix r" and slot=slot and pending=pending and es=saved]
  show ?thesis using run checked known fresh guards
    by (auto simp: lpp_check_helper_return_recipe_def)
qed

ML \<open>
val checked = [@{thm lpp_helper_return_recipe_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted source helper recipe dependency" else ();
\<close>
end
