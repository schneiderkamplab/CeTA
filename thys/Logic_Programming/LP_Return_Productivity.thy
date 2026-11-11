theory LP_Return_Productivity
  imports LP_Return_Shapes
begin

text \<open>Nonproductive predicates have no finite successful derivation.
They may still diverge. These checks restrict actual returns only; they do not
remove a helper termination obligation or a saved failure alternative.\<close>

definition lp_return_signature where
  "lp_return_signature a = (fst a,length (snd a))"

definition lp_return_nonproductive_check where
  "lp_return_nonproductive_check P blocked =
    list_all (\<lambda>(h,bs). lp_return_signature h\<in>set blocked \<longrightarrow>
      list_ex (\<lambda>b. lp_return_signature b\<in>set blocked) bs) P"

lemma lp_return_signature_eval[simp]:
  "lp_return_signature (lp_atom_eval a rho)=lp_return_signature a"
  by (simp add: lp_return_signature_def lp_atom_eval_def)

theorem lp_return_nonproductive_sound:
  assumes checked: "lp_return_nonproductive_check P blocked"
    and answer: "lp_answer_model P a"
  shows "lp_return_signature a\<notin>set blocked"
  using answer
proof (induct rule: lp_answer_model.induct)
  case (clause c rho)
  have cover: "lp_return_signature (fst (P!c))\<in>set blocked \<longrightarrow>
      (\<exists>b\<in>set (snd (P!c)). lp_return_signature b\<in>set blocked)"
    using checked clause.hyps(1)
    by (auto simp: lp_return_nonproductive_check_def list_all_iff list_ex_iff
      split_def dest!: bspec[where x="P!c"])
  show ?case using cover clause.hyps by auto
qed

definition lp_return_productive_program where
  "lp_return_productive_program P blocked =
    filter (\<lambda>(h,bs). list_all (\<lambda>b. lp_return_signature b\<notin>set blocked) bs) P"

theorem lp_return_productive_model:
  assumes checked: "lp_return_nonproductive_check P blocked"
    and answer: "lp_answer_model P a"
  shows "lp_answer_model (lp_return_productive_program P blocked) a"
  using answer
proof (induct rule: lp_answer_model.induct)
  case (clause c rho)
  have child: "lp_return_signature b\<notin>set blocked"
    if "b\<in>set (snd (P!c))" for b
  proof -
    have answer: "lp_answer_model P (lp_atom_eval b rho)"
      using clause.hyps that by blast
    show ?thesis using lp_return_nonproductive_sound[OF checked answer] by simp
  qed
  have live: "list_all (\<lambda>b. lp_return_signature b\<notin>set blocked) (snd (P!c))"
    using child by (auto simp: list_all_iff)
  have member: "P!c\<in>set (lp_return_productive_program P blocked)"
    using clause.hyps(1) live
    by (auto simp: lp_return_productive_program_def split_def)
  obtain i where bound: "i<length (lp_return_productive_program P blocked)"
    and selected: "lp_return_productive_program P blocked!i=P!c"
    using member by (auto simp: in_set_conv_nth)
  have result: "lp_answer_model (lp_return_productive_program P blocked)
      (lp_atom_eval (fst (lp_return_productive_program P blocked!i)) rho)"
    by (rule lp_answer_model.clause[OF bound])
      (use selected clause.hyps in auto)
  show ?case using result selected by simp
qed

theorem lp_return_productive_shapes:
  assumes checked: "lp_return_nonproductive_check P blocked"
    and model: "lp_return_shape_model (lp_return_productive_program P blocked) G modes"
  shows "lp_return_shape_model P G modes"
  using lp_return_productive_model[OF checked] model
  by (auto simp: lp_return_shape_model_def)

ML \<open>
val checked = [@{thm lp_return_nonproductive_sound},
  @{thm lp_return_productive_model}, @{thm lp_return_productive_shapes}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (names checked)
  then error "Untrusted return-productivity dependency" else ();
\<close>
end
