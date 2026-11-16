theory LP_Prolog_Guarded_Returns
  imports LP_Prolog_Guarded_Triples LP_Prolog_Numeric_Observations
begin

text \<open>Successful-helper evidence is stable under the same substitutions
as the shared LP-with-cut return stack. This is closure of finite successful
derivations, not a replacement for a helper termination proof.\<close>

definition lpp_success_iatom_subst where
  "lpp_success_iatom_subst a sigma = (fst a,map (\<lambda>t. lp_isubst t sigma) (snd a))"

lemma lpp_success_atom_eval_subst:
  "lpp_success_iatom_subst (lpp_success_atom_eval a eta) sigma =
    lpp_success_atom_eval a (\<lambda>x. lp_isubst (eta x) sigma)"
  by (simp add: lpp_success_iatom_subst_def lpp_success_atom_eval_def map_map o_def lp_ieval_subst)

lemma lpp_success_guard_integer_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes "lpp_success_guard_holds lpp_integer_result eta success_guard"
  shows "lpp_success_guard_holds lpp_integer_result (\<lambda>x. lp_isubst (eta x) sigma) success_guard"
  using assms by (cases success_guard) (auto simp: lp_ieval_subst[symmetric] lp_seg_ground_subst
    intro: lpp_is_integer_subst lpp_integer_result_subst)

lemma lpp_guarded_success_integer_subst:
  fixes a :: "'w lpp_success_iatom" and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes success: "lpp_guarded_success P lpp_integer_result a"
  shows "lpp_guarded_success P lpp_integer_result (lpp_success_iatom_subst a sigma)"
  using success
proof (induct rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  have guards: "list_all (lpp_success_guard_holds lpp_integer_result (\<lambda>x. lp_isubst (eta x) sigma)) gs"
    using clause.hyps by (auto simp: list_all_iff intro: lpp_success_guard_integer_subst)
  have body: "list_all (lpp_guarded_success P lpp_integer_result)
    (map (\<lambda>b. lpp_success_atom_eval b (\<lambda>x. lp_isubst (eta x) sigma)) bs)"
    using clause.hyps by (auto simp: list_all_iff lpp_success_atom_eval_subst[symmetric])
  show ?case unfolding lpp_success_atom_eval_subst
    by (rule lpp_guarded_success.clause[OF clause.hyps(1) guards body])
qed

definition lpp_guarded_prefix_invariant where
  "lpp_guarded_prefix_invariant P ps ss = list_all (\<lambda>frame.
    list_all (\<lambda>a. lpp_guarded_success P lpp_integer_result (lpp_success_atom_eval a (snd frame))) ps) ss"

lemma lpp_guarded_prefix_preserved:
  fixes ss :: "((string lp_cut_symbol,string) lp_iterm lp_cut_entry *
    ('v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm)) list"
  assumes step: "lpp_answer_transition P B U ss event tt"
    and known: "lpp_guarded_prefix_invariant Q ps ss"
  shows "lpp_guarded_prefix_invariant Q ps tt \<and>
    (\<forall>eta. event=Some eta \<longrightarrow>
      list_all (\<lambda>a. lpp_guarded_success Q lpp_integer_result (lpp_success_atom_eval a eta)) ps)"
  unfolding lpp_guarded_prefix_invariant_def
proof (rule lpp_answer_substitution_property[OF _ step known[unfolded lpp_guarded_prefix_invariant_def]])
  fix eta :: "'v \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and sigma :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assume "list_all (\<lambda>a. lpp_guarded_success Q lpp_integer_result (lpp_success_atom_eval a eta)) ps"
  then show "list_all (\<lambda>a. lpp_guarded_success Q lpp_integer_result
    (lpp_success_atom_eval a (\<lambda>x. lp_isubst (eta x) sigma))) ps"
    by (auto simp: list_all_iff lpp_success_atom_eval_subst[symmetric]
      intro: lpp_guarded_success_integer_subst)
qed

ML \<open>
val checked = [@{thm lpp_guarded_success_integer_subst}, @{thm lpp_guarded_prefix_preserved}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted guarded return dependency" else ();
\<close>
end
