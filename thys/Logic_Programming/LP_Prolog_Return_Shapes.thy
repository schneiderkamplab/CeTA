theory LP_Prolog_Return_Shapes
  imports LP_Return_Shape_Contracts LP_Prolog_Guarded_Ground_Return
begin

text \<open>Forgetting guards overapproximates successful helper answers.
This bridge retains the established guarded source model and its actual-return
connection. It does not claim termination or discharge source coverage.\<close>

definition lpp_shape_clause where
  "lpp_shape_clause c = (case c of (h,bs,gs) \<Rightarrow> (lpp_lift_atom h,map lpp_lift_atom bs))"

definition lpp_shape_program where
  "lpp_shape_program P = map lpp_shape_clause P"

lemma lpp_guarded_success_shape_model:
  assumes success: "lpp_guarded_success P E a"
  shows "lp_answer_model (lpp_shape_program P) (lpp_lift_iatom a)"
  using success
proof (induct rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  obtain i where bound: "i<length P" and selected: "P!i=(h,bs,gs)"
    using clause.hyps(1) by (auto simp: in_set_conv_nth)
  have head: "lpp_lift_iatom (lpp_success_atom_eval h eta)=
      lp_atom_eval (fst (lpp_shape_program P!i)) eta"
    using bound selected by (cases h)
      (simp add: lpp_shape_program_def lpp_shape_clause_def lpp_lift_iatom_def
        lpp_lift_atom_def lp_atom_eval_def lpp_success_atom_eval_def)
  show ?case unfolding head
  proof (rule lp_answer_model.clause)
    show "i<length (lpp_shape_program P)" using bound by (simp add: lpp_shape_program_def)
    fix b assume member: "b\<in>set (snd (lpp_shape_program P!i))"
    obtain a where a: "a\<in>set bs" "b=lpp_lift_atom a"
      using member bound selected by (auto simp: lpp_shape_program_def lpp_shape_clause_def)
    show "lp_answer_model (lpp_shape_program P) (lp_atom_eval b eta)"
      using clause.hyps a by (cases a)
        (auto simp: list_all_iff lpp_lift_iatom_def lpp_lift_atom_def
          lp_atom_eval_def lpp_success_atom_eval_def)
  qed
qed

lemma lpp_guarded_return_shape_contracts:
  fixes P :: "'v lpp_success_clause list"
    and a :: "string \<times> (string lp_cut_symbol,'v) lp_iterm list"
  assumes checked: "lp_return_shape_program_check fuel G modes (lpp_shape_program P)"
    and success: "lpp_guarded_success P E a"
  shows "lp_return_contracts G modes (lpp_lift_iatom a)"
  using lp_return_shape_program_check_sound[OF checked]
    lpp_guarded_success_shape_model[OF success]
  by (cases "lpp_lift_iatom a") (auto simp: lp_return_shape_model_def)

ML \<open>
val audited = [@{thm lpp_guarded_success_shape_model}, @{thm lpp_guarded_return_shape_contracts}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted Prolog return-shape bridge dependency" else ();
\<close>
end
