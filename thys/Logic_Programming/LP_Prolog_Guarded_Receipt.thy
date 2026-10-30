theory LP_Prolog_Guarded_Receipt
  imports LP_Prolog_Guarded_Returns LP_Cut_SEG_Triple_Receipt
begin

text \<open>Guarded helper clauses use the existing finite substitution receipt.
Every body atom and every source guard must be supported by the current saved
answer context; selecting a clause is not permission to omit its premises.\<close>

definition lpp_success_atom_subst where
  "lpp_success_atom_subst a mu = (fst a,map (\<lambda>t. t\<cdot>mu) (snd a))"

fun lpp_success_guard_subst where
  "lpp_success_guard_subst (LPPSInteger t) mu = LPPSInteger (t\<cdot>mu)"
| "lpp_success_guard_subst (LPPSEvaluates e t) mu = LPPSEvaluates (e\<cdot>mu) (t\<cdot>mu)"
| "lpp_success_guard_subst (LPPSOpaque t) mu = LPPSOpaque (t\<cdot>mu)"

lemma lpp_success_atom_subst_eval:
  "lpp_success_atom_eval (lpp_success_atom_subst a mu) eta =
    lpp_success_atom_eval a (\<lambda>x. lp_ieval (mu x) eta)"
  by (simp add: lpp_success_atom_subst_def lpp_success_atom_eval_def map_map o_def lp_ieval_finite_subst)

lemma lpp_success_guard_subst_eval:
  "lpp_success_guard_holds E eta (lpp_success_guard_subst success_guard mu) =
    lpp_success_guard_holds E (\<lambda>x. lp_ieval (mu x) eta) success_guard"
  by (cases success_guard) (simp_all add: lp_ieval_finite_subst)

definition lpp_check_guarded_model_clause where
  "lpp_check_guarded_model_clause P facts guards head c bindings =
    (c<length P \<and> (case P!c of (h,bs,gs) \<Rightarrow>
      let mu=lpc_triple_model_subst (lpp_lift_atom head) bindings in
      lpp_success_atom_subst h mu=head \<and>
      list_all (\<lambda>b. lpp_success_atom_subst b mu\<in>set facts) bs \<and>
      list_all (\<lambda>g. lpp_success_guard_subst g mu\<in>set guards) gs))"

lemma lpp_checked_guarded_model_clause:
  assumes checked: "lpp_check_guarded_model_clause P facts guards head c bindings"
    and facts: "\<And>b. b\<in>set facts \<Longrightarrow> lpp_guarded_success P E (lpp_success_atom_eval b eta)"
    and guards: "\<And>g. g\<in>set guards \<Longrightarrow> lpp_success_guard_holds E eta g"
  shows "lpp_guarded_success P E (lpp_success_atom_eval head eta)"
proof -
  let ?mu = "lpc_triple_model_subst (lpp_lift_atom head) bindings"
  obtain h bs gs where row: "P!c=(h,bs,gs)" by (cases "P!c") auto
  have index: "c<length P" and head: "lpp_success_atom_subst h ?mu=head"
    and body: "list_all (\<lambda>b. lpp_success_atom_subst b ?mu\<in>set facts) bs"
    and tested: "list_all (\<lambda>g. lpp_success_guard_subst g ?mu\<in>set guards) gs"
    using checked by (auto simp: lpp_check_guarded_model_clause_def row Let_def)
  have member: "(h,bs,gs)\<in>set P" using nth_mem[OF index] row by simp
  have models: "list_all (lpp_guarded_success P E)
    (map (\<lambda>b. lpp_success_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta)) bs)"
    using body facts by (auto simp: list_all_iff lpp_success_atom_subst_eval[symmetric])
  have conditions: "list_all (lpp_success_guard_holds E (\<lambda>x. lp_ieval (?mu x) eta)) gs"
    using tested guards by (auto simp: list_all_iff lpp_success_guard_subst_eval[symmetric])
  have result: "lpp_guarded_success P E (lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta))"
    by (rule lpp_guarded_success.clause[OF member conditions models])
  have head_eval: "lpp_success_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)=lpp_success_atom_eval head eta"
    using arg_cong[OF head, of "\<lambda>a. lpp_success_atom_eval a eta"]
    by (simp only: lpp_success_atom_subst_eval)
  show ?thesis using result by (simp only: head_eval)
qed

ML \<open>
val checked = [@{thm lpp_checked_guarded_model_clause}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted guarded clause receipt dependency" else ();
\<close>
end
