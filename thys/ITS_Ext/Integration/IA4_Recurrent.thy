theory IA4_Recurrent
  imports IA4_Nontermination
begin

text \<open>A reachable recurrent region with an explicit, total successor policy.
  The policy supplies post-state and intermediate values as typed expressions.
  Neither satisfiability alone nor an abstract cycle is used as a proof.\<close>

type_synonym 'v ia4_policy = "(('v \<times> IA.ty) \<times> 'v ia4_exp) list"

fun ia4_policy_exp where
  "ia4_policy_exp [] x = Var x"
| "ia4_policy_exp ((y,e)#xs) x = (if x=y then e else ia4_policy_exp xs x)"

definition ia4_policy_typed where
  "ia4_policy_typed xs = (\<forall>(x,e)\<in>set xs. IA4.has_type e (snd x))"

lemma ia4_policy_exp_typed:
  "ia4_policy_typed xs \<Longrightarrow> IA4.has_type (ia4_policy_exp xs x) (snd x)"
  by (induct xs; auto simp: ia4_policy_typed_def split: prod.splits)

definition ia4_policy_val where
  "ia4_policy_val xs a x = IA4.eval (ia4_policy_exp xs x) a"

lemma ia4_policy_val_eq:
  "(\<lambda>x. IA4.eval (ia4_policy_exp xs x) a) = ia4_policy_val xs a"
  by (rule ext, simp add: ia4_policy_val_def)

lemma ia4_policy_assignment:
  assumes "ia4_policy_typed xs" "IA4.assignment a"
  shows "IA4.assignment (ia4_policy_val xs a)"
  unfolding IA4.assignment_def ia4_policy_val_def
  using IA4.eval_types[OF assms(2) ia4_policy_exp_typed[OF assms(1)]] by blast

fun ia4_step_policy where
  "ia4_step_policy post local (Pre x,t) = Var (x,t)"
| "ia4_step_policy post local (Post x,t) = ia4_policy_exp post (x,t)"
| "ia4_step_policy post local (Intermediate x,t) = ia4_policy_exp local (x,t)"

definition ia4_subst_formula where
  "ia4_subst_formula s f = map_formula (\<lambda>e. e \<cdot> s) f"

lemma ia4_subst_formula_satisfies:
  "IA4.satisfies a (ia4_subst_formula s f) = IA4.satisfies (\<lambda>x. IA4.eval (s x) a) f"
  by (induct f; auto simp: ia4_subst_formula_def IA4.subst_eval)

lemma ia4_step_policy_val:
  "(\<lambda>x. IA4.eval (ia4_step_policy post local x) a) =
   IA4Termination.pre_post_inter a (ia4_policy_val post a) (ia4_policy_val local a)"
  by (rule ext, rename_tac x, case_tac x, rename_tac v t, case_tac v,
      auto simp: ia4_policy_val_def)

definition ia4_recurrent_obligation where
  "ia4_recurrent_obligation P l region transition_guard post local =
    Disjunction [form_not region, Conjunction [
      ia4_subst_formula (ia4_step_policy post local) transition_guard,
      ia4_subst_formula (ia4_policy_exp post) (assertion_of P l),
      ia4_subst_formula (ia4_policy_exp post) region]]"

definition ia4_check_recurrent_policy where
  "ia4_check_recurrent_policy P l region tau post local = do {
    check (tau \<in> set (transitions_impl P) \<and> source (snd tau)=l \<and> target (snd tau)=l)
      (showsl_lit (STR ''recurrent transition must be an original self-loop''));
    check (ia4_policy_typed post \<and> ia4_policy_typed local \<and> IA4.formula region)
      (showsl_lit (STR ''ill-typed recurrent region or successor policy''));
    let obligation = ia4_recurrent_obligation P l region (transition_formula (snd tau)) post local;
    check (IA4.formula obligation) (showsl_lit (STR ''ill-typed recurrent obligation''));
    IA4Check.check_valid_formula default obligation
  }"

lemma ia4_check_recurrent_policy:
  assumes ok: "isOK (ia4_check_recurrent_policy P l region tau post local)"
      and state: "IA4Termination.state_lts (lts_of P) (State a l)"
      and region: "IA4.satisfies a region"
  shows "(State a l, State (ia4_policy_val post a) l) \<in> IA4Termination.transition (lts_of P) \<and>
    IA4Termination.state_lts (lts_of P) (State (ia4_policy_val post a) l) \<and>
    IA4.satisfies (ia4_policy_val post a) region"
proof -
  obtain lab src tgt transition_guard where tau: "tau=(lab,Transition src tgt transition_guard)"
    by (cases tau; cases "snd tau", auto)
  from ok have mem: "(lab,Transition l l transition_guard) \<in> set (transitions_impl P)"
    and typed: "ia4_policy_typed post" "ia4_policy_typed local"
    and valid: "isOK (IA4Check.check_valid_formula default (ia4_recurrent_obligation P l region transition_guard post local))"
    and form: "IA4.formula (ia4_recurrent_obligation P l region transition_guard post local)"
    by (auto simp: ia4_check_recurrent_policy_def tau Let_def)
  from state have ass: "IA4.assignment a" by auto
  from IA4Check.check_valid_formula[OF valid form] ass region have facts:
    "IA4.satisfies (IA4Termination.pre_post_inter a (ia4_policy_val post a) (ia4_policy_val local a)) transition_guard"
    "IA4.satisfies (ia4_policy_val post a) (assertion_of P l)"
    "IA4.satisfies (ia4_policy_val post a) region"
    by (auto simp: IA4.valid_def ia4_recurrent_obligation_def ia4_subst_formula_satisfies
      ia4_step_policy_val ia4_policy_val_eq)
  have target: "IA4Termination.state_lts (lts_of P) (State (ia4_policy_val post a) l)"
    using facts(2) ia4_policy_assignment[OF typed(1) ass] by simp
  have rule: "Transition l l transition_guard \<in> transition_rules (lts_of P)"
    using mem by (cases P, auto simp: lts_of_def)
  have step: "(State a l, State (ia4_policy_val post a) l) \<in>
    IA4Termination.transition_step_lts (lts_of P) (Transition l l transition_guard)"
    by (rule IA4Termination.mem_transition_step_TransitionI[OF state target],
        insert facts(1) ia4_policy_assignment[OF typed(2) ass], auto)
  from IA4Termination.mem_transitionI[OF rule step] target facts(3) show ?thesis by blast
qed


definition ia4_check_recurrent where
  "ia4_check_recurrent P init stem region tau post local = do {
    IA4Termination.check_lts_impl P;
    check (snd init \<in> set (initial P) \<and> ia4_ground_state_ok P init)
      (showsl_lit (STR ''invalid recurrent initial state''));
    head \<leftarrow> ia4_check_ground_seq P init stem;
    check (IA4.satisfies (ia4_ground_val (fst head)) region)
      (showsl_lit (STR ''stem does not reach the recurrent region''));
    ia4_check_recurrent_policy P (snd head) region tau post local
  }"

lemma ia4_check_recurrent_sound:
  assumes ok: "isOK (ia4_check_recurrent P init stem region tau post local)"
  shows "\<not> IA4Termination.lts_termination (lts_of P)"
proof -
  from ok have init: "ia4_ground_state init \<in> IA4Termination.initial_states (lts_of P)"
    and state: "IA4Termination.state_lts (lts_of P) (ia4_ground_state init)"
    by (auto simp: ia4_check_recurrent_def IA4Termination.initial_states_def
      ia4_ground_state_def ia4_ground_state_ok_def)
  from ok obtain head where stem: "ia4_check_ground_seq P init stem = return head"
    by (auto simp: ia4_check_recurrent_def split: sum.splits)
  from ok stem have pol: "isOK (ia4_check_recurrent_policy P (snd head) region tau post local)"
    and region: "IA4.satisfies (ia4_ground_val (fst head)) region"
    by (auto simp: ia4_check_recurrent_def)
  from ia4_check_ground_seq[OF stem state] have reach:
    "(ia4_ground_state init,ia4_ground_state head) \<in> (IA4Termination.transition (lts_of P))\<^sup>*"
    and hs: "IA4Termination.state_lts (lts_of P) (ia4_ground_state head)"
    using relpow_imp_rtrancl by auto
  let ?a = "\<lambda>n. (ia4_policy_val post ^^ n) (ia4_ground_val (fst head))"
  let ?s = "\<lambda>n. State (?a n) (snd head)"
  have holds: "IA4Termination.state_lts (lts_of P) (?s n) \<and> IA4.satisfies (?a n) region" for n
  proof (induct n)
    case 0 then show ?case using hs region by (simp add: ia4_ground_state_def)
  next
    case (Suc n)
    from ia4_check_recurrent_policy[OF pol conjunct1[OF Suc] conjunct2[OF Suc]]
    show ?case by (simp add: funpow_Suc_right)
  qed
  have step: "(?s n,?s (Suc n)) \<in> IA4Termination.transition (lts_of P)" for n
    using ia4_check_recurrent_policy[OF pol conjunct1[OF holds] conjunct2[OF holds]]
    by (simp add: funpow_Suc_right)
  have chain: "chain (IA4Termination.transition (lts_of P)) ?s" using step by auto
  show ?thesis
  proof
    assume "IA4Termination.lts_termination (lts_of P)"
    then have sn: "SN_on (IA4Termination.transition (lts_of P))
      ((IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P))"
      by (rule SN_on_Image_rtrancl)
    from init reach have start: "?s 0 \<in> (IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P)"
      by (auto simp: ia4_ground_state_def)
    have infinite: "\<exists>f. f 0 \<in> (IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P) \<and>
      chain (IA4Termination.transition (lts_of P)) f"
      by (rule exI[of _ ?s], rule conjI, fact start, fact chain)
    with sn show False unfolding SN_on_def by blast
  qed
qed

declare ia4_policy_typed_def[code] ia4_policy_val_def[code]
  ia4_subst_formula_def[code] ia4_recurrent_obligation_def[code]
  ia4_check_recurrent_policy_def[code] ia4_check_recurrent_def[code]

end
