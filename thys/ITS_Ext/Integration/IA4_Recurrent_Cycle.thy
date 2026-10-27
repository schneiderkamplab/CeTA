theory IA4_Recurrent_Cycle
  imports IA4_Recurrent
begin

type_synonym 'v ia4_policy_step =
  "(string \<times> (ia4_sig,'v,IA.ty,string) transition_rule) \<times> 'v ia4_policy \<times> 'v ia4_policy"

fun ia4_policy_path_valid where
  "ia4_policy_path_valid P l [] = True"
| "ia4_policy_path_valid P l ((tau,post,local)#steps) =
    (tau \<in> set (transitions_impl P) \<and> source (snd tau)=l \<and>
      ia4_policy_typed post \<and> ia4_policy_typed local \<and>
      ia4_policy_path_valid P (target (snd tau)) steps)"
fun ia4_policy_path_end where
  "ia4_policy_path_end l [] = l"
| "ia4_policy_path_end l ((tau,post,local)#steps) = ia4_policy_path_end (target (snd tau)) steps"
fun ia4_policy_path_val where
  "ia4_policy_path_val [] a = a"
| "ia4_policy_path_val ((tau,post,local)#steps) a = ia4_policy_path_val steps (ia4_policy_val post a)"
fun ia4_policy_path_wp where
  "ia4_policy_path_wp P [] region = region"
| "ia4_policy_path_wp P ((tau,post,local)#steps) region = Conjunction [
    ia4_subst_formula (ia4_step_policy post local) (transition_formula (snd tau)),
    ia4_subst_formula (ia4_policy_exp post) (assertion_of P (target (snd tau))),
    ia4_subst_formula (ia4_policy_exp post) (ia4_policy_path_wp P steps region)]"

lemma ia4_policy_path_sound:
  assumes valid: "ia4_policy_path_valid P l steps"
      and state: "IA4Termination.state_lts (lts_of P) (State a l)"
      and wp: "IA4.satisfies a (ia4_policy_path_wp P steps region)"
  shows "(State a l, State (ia4_policy_path_val steps a) (ia4_policy_path_end l steps))
      \<in> (IA4Termination.transition (lts_of P))^^length steps \<and>
    IA4Termination.state_lts (lts_of P) (State (ia4_policy_path_val steps a) (ia4_policy_path_end l steps)) \<and>
    IA4.satisfies (ia4_policy_path_val steps a) region"
  using valid state wp
proof (induct steps arbitrary: a l)
  case Nil then show ?case by simp
next
  case (Cons item steps)
  obtain lab src tgt transition_guard post local where item:
    "item=((lab,Transition src tgt transition_guard),post,local)"
    by (cases item; cases "fst item"; cases "snd (fst item)", auto)
  from Cons.prems(1) have mem: "(lab,Transition l tgt transition_guard) \<in> set (transitions_impl P)"
    and typed: "ia4_policy_typed post" "ia4_policy_typed local"
    and rest: "ia4_policy_path_valid P tgt steps"
    by (auto simp: item)
  from Cons.prems(2) have ass: "IA4.assignment a" by auto
  from Cons.prems(3) have facts:
    "IA4.satisfies (IA4Termination.pre_post_inter a (ia4_policy_val post a) (ia4_policy_val local a)) transition_guard"
    "IA4.satisfies (ia4_policy_val post a) (assertion_of P tgt)"
    "IA4.satisfies (ia4_policy_val post a) (ia4_policy_path_wp P steps region)"
    by (auto simp: item ia4_subst_formula_satisfies ia4_step_policy_val ia4_policy_val_eq)
  have target: "IA4Termination.state_lts (lts_of P) (State (ia4_policy_val post a) tgt)"
    using facts(2) ia4_policy_assignment[OF typed(1) ass] by simp
  have rule: "Transition l tgt transition_guard \<in> transition_rules (lts_of P)"
    using mem by (cases P, auto simp: lts_of_def)
  have step: "(State a l, State (ia4_policy_val post a) tgt) \<in>
    IA4Termination.transition_step_lts (lts_of P) (Transition l tgt transition_guard)"
    by (rule IA4Termination.mem_transition_step_TransitionI[OF Cons.prems(2) target],
        insert facts(1) ia4_policy_assignment[OF typed(2) ass], auto)
  from IA4Termination.mem_transitionI[OF rule step] have edge:
    "(State a l, State (ia4_policy_val post a) tgt) \<in> IA4Termination.transition (lts_of P)" .
  from Cons.hyps[OF rest target facts(3)] have tail:
    "(State (ia4_policy_val post a) tgt, State (ia4_policy_path_val steps (ia4_policy_val post a)) (ia4_policy_path_end tgt steps))
      \<in> (IA4Termination.transition (lts_of P))^^length steps"
    "IA4Termination.state_lts (lts_of P) (State (ia4_policy_path_val steps (ia4_policy_val post a)) (ia4_policy_path_end tgt steps))"
    "IA4.satisfies (ia4_policy_path_val steps (ia4_policy_val post a)) region" by auto
  from relpow_Suc_I2[OF edge tail(1)] tail(2-3) show ?case by (simp add: item)
qed

definition ia4_check_recurrent_cycle where
  "ia4_check_recurrent_cycle P init stem region steps = do {
    IA4Termination.check_lts_impl P;
    check (snd init \<in> set (initial P) \<and> ia4_ground_state_ok P init)
      (showsl_lit (STR ''invalid recurrent initial state''));
    head \<leftarrow> ia4_check_ground_seq P init stem;
    check (IA4.formula region \<and> IA4.satisfies (ia4_ground_val (fst head)) region)
      (showsl_lit (STR ''stem does not reach a typed recurrent region''));
    check (steps \<noteq> [] \<and> ia4_policy_path_valid P (snd head) steps \<and> ia4_policy_path_end (snd head) steps = snd head)
      (showsl_lit (STR ''invalid or empty recurrent cycle''));
    let obligation = Disjunction [form_not region, ia4_policy_path_wp P steps region];
    check (IA4.formula obligation) (showsl_lit (STR ''ill-typed recurrent cycle obligation''));
    IA4Check.check_valid_formula default obligation
  }"

lemma ia4_check_recurrent_cycle_sound:
  assumes ok: "isOK (ia4_check_recurrent_cycle P init stem region steps)"
  shows "\<not> IA4Termination.lts_termination (lts_of P)"
proof -
  from ok have init: "ia4_ground_state init \<in> IA4Termination.initial_states (lts_of P)"
    and state: "IA4Termination.state_lts (lts_of P) (ia4_ground_state init)"
    by (auto simp: ia4_check_recurrent_cycle_def IA4Termination.initial_states_def
      ia4_ground_state_def ia4_ground_state_ok_def Let_def)
  from ok obtain head where stem: "ia4_check_ground_seq P init stem = return head"
    by (auto simp: ia4_check_recurrent_cycle_def Let_def split: sum.splits)
  let ?ob = "Disjunction [form_not region,ia4_policy_path_wp P steps region]"
  from ok stem have checked: "isOK (IA4Check.check_valid_formula default ?ob)"
    and form: "IA4.formula ?ob"
    and region: "IA4.satisfies (ia4_ground_val (fst head)) region"
    and valid: "ia4_policy_path_valid P (snd head) steps"
    and last: "ia4_policy_path_end (snd head) steps = snd head"
    and ne: "length steps > 0"
    by (auto simp: ia4_check_recurrent_cycle_def Let_def)
  from IA4Check.check_valid_formula[OF checked form] have wp:
    "IA4.assignment a \<Longrightarrow> IA4.satisfies a region \<Longrightarrow> IA4.satisfies a (ia4_policy_path_wp P steps region)" for a
    by (auto simp: IA4.valid_def)
  from ia4_check_ground_seq[OF stem state] have reach:
    "(ia4_ground_state init,ia4_ground_state head) \<in> (IA4Termination.transition (lts_of P))\<^sup>*"
    and hs: "IA4Termination.state_lts (lts_of P) (ia4_ground_state head)"
    using relpow_imp_rtrancl by auto
  let ?a = "\<lambda>n. (ia4_policy_path_val steps ^^ n) (ia4_ground_val (fst head))"
  let ?s = "\<lambda>n. State (?a n) (snd head)"
  have holds: "IA4Termination.state_lts (lts_of P) (?s n) \<and> IA4.satisfies (?a n) region" for n
  proof (induct n)
    case 0 then show ?case using hs region by (simp add: ia4_ground_state_def)
  next
    case (Suc n)
    from Suc have a: "IA4.assignment (?a n)" by auto
    from ia4_policy_path_sound[OF valid conjunct1[OF Suc] wp[OF a conjunct2[OF Suc]]]
    show ?case by (simp add: last funpow_Suc_right)
  qed
  have step: "(?s n,?s (Suc n)) \<in> (IA4Termination.transition (lts_of P))\<^sup>+" for n
  proof -
    from holds have a: "IA4.assignment (?a n)" by auto
    from ia4_policy_path_sound[OF valid conjunct1[OF holds] wp[OF a conjunct2[OF holds]]]
    have "(?s n,?s (Suc n)) \<in> (IA4Termination.transition (lts_of P))^^length steps"
      by (simp add: last funpow_Suc_right)
    with ne trancl_power show ?thesis by blast
  qed
  have chain: "chain ((IA4Termination.transition (lts_of P))\<^sup>+) ?s" using step by auto
  show ?thesis
  proof
    assume sn0: "IA4Termination.lts_termination (lts_of P)"
    from SN_on_Image_rtrancl[OF sn0] have sn:
      "SN_on ((IA4Termination.transition (lts_of P))\<^sup>+)
        ((IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P))"
      by (rule SN_on_trancl)
    from init reach have start: "?s 0 \<in> (IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P)"
      by (auto simp: ia4_ground_state_def)
    have infinite: "\<exists>f. f 0 \<in> (IA4Termination.transition (lts_of P))\<^sup>* `` IA4Termination.initial_states (lts_of P) \<and>
      chain ((IA4Termination.transition (lts_of P))\<^sup>+) f"
      by (rule exI[of _ ?s], rule conjI, fact start, fact chain)
    with sn show False unfolding SN_on_def by blast
  qed
qed

declare ia4_check_recurrent_cycle_def[code]
end
