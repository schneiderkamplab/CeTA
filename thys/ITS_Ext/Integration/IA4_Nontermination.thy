theory IA4_Nontermination
  imports IA4_Instance LTS.LTS_Nontermination_Prover
begin

text \<open>Ground integer states for the existing exact-state lasso criterion.
  Unlisted integer coordinates are zero; Boolean coordinates are false.
  These total valuations avoid a non-executable universal assignment test.\<close>

type_synonym 'v ia4_ground_state = "('v \<times> int) list \<times> string"
type_synonym 'v ia4_ground_step =
  "(string \<times> (ia4_sig,'v,IA.ty,string) transition_rule) \<times> 'v ia4_ground_state"
datatype 'v ia4_nontermination_proof = IA4_EquivalentState
  "'v ia4_ground_state" "'v ia4_ground_step list" "'v ia4_ground_step list"


fun ia4_ground_val where
  "ia4_ground_val vs (x,IA.IntT) = IA.Int (map_of_default 0 vs x)"
| "ia4_ground_val vs (x,IA.BoolT) = IA.Bool False"

lemma ia4_ground_assignment[simp]: "IA4.assignment (ia4_ground_val vs)"
  unfolding IA4.assignment_def
  by (intro allI, rename_tac x, case_tac x, rename_tac a b, case_tac b, auto)

definition ia4_ground_state where "ia4_ground_state s = State (ia4_ground_val (fst s)) (snd s)"
definition ia4_ground_state_ok where
  "ia4_ground_state_ok P s = IA4.satisfies (ia4_ground_val (fst s)) (assertion_of P (snd s))"

lemma ia4_ground_state_ok:
  "ia4_ground_state_ok P s \<Longrightarrow> IA4Termination.state_lts (lts_of P) (ia4_ground_state s)"
  by (simp add: ia4_ground_state_ok_def ia4_ground_state_def)

fun ia4_check_ground_step where
  "ia4_check_ground_step P src ((lab,Transition l r f),tgt) = do {
    check ((lab,Transition l r f) \<in> set (transitions_impl P)) (showsl_lit (STR ''unknown lasso transition''));
    check (ia4_ground_state_ok P tgt) (showsl_lit (STR ''invalid target valuation''));
    check (snd src = l \<and> snd tgt = r) (showsl_lit (STR ''lasso endpoints''));
    check (IA4.satisfies (IA4Termination.pre_post_inter (ia4_ground_val (fst src)) (ia4_ground_val (fst tgt)) (ia4_ground_val [])) f)
      (showsl_lit (STR ''lasso guard or update is false''))
  }"

lemma ia4_check_ground_step:
  assumes ok: "isOK (ia4_check_ground_step P src (tau,tgt))"
      and src: "IA4Termination.state_lts (lts_of P) (ia4_ground_state src)"
  shows "(ia4_ground_state src,ia4_ground_state tgt) \<in> IA4Termination.transition (lts_of P) \<and>
    IA4Termination.state_lts (lts_of P) (ia4_ground_state tgt)"
proof -
  obtain lab l r f where tau: "tau = (lab,Transition l r f)"
    by (cases tau; cases "snd tau", auto)
  from ok have mem: "(lab,Transition l r f) \<in> set (transitions_impl P)"
    and tgt: "IA4Termination.state_lts (lts_of P) (ia4_ground_state tgt)"
    and loc: "snd src = l" "snd tgt = r"
    and sat: "IA4.satisfies (IA4Termination.pre_post_inter (ia4_ground_val (fst src)) (ia4_ground_val (fst tgt)) (ia4_ground_val [])) f"
    by (auto simp: tau dest: ia4_ground_state_ok)
  have "Transition l r f \<in> transition_rules (lts_of P)"
    using mem by (cases P, auto simp: lts_of_def)
  moreover have "(ia4_ground_state src,ia4_ground_state tgt) \<in> IA4Termination.transition_step_lts (lts_of P) (Transition l r f)"
    by (rule IA4Termination.mem_transition_step_TransitionI[OF src tgt], insert loc sat, auto simp: ia4_ground_state_def)
  ultimately have step: "(ia4_ground_state src,ia4_ground_state tgt) \<in> IA4Termination.transition (lts_of P)"
    by (rule IA4Termination.mem_transitionI)
  from step tgt show ?thesis by blast
qed

fun ia4_check_ground_seq where
  "ia4_check_ground_seq P src [] = return src"
| "ia4_check_ground_seq P src ((tau,tgt)#ts) = do {
      ia4_check_ground_step P src (tau,tgt);
      ia4_check_ground_seq P tgt ts
    }"

lemma ia4_check_ground_seq:
  assumes "ia4_check_ground_seq P src ts = return tgt"
      and "IA4Termination.state_lts (lts_of P) (ia4_ground_state src)"
  shows "(ia4_ground_state src,ia4_ground_state tgt) \<in> (IA4Termination.transition (lts_of P))^^length ts \<and>
    IA4Termination.state_lts (lts_of P) (ia4_ground_state tgt)"
  using assms
proof (induct ts arbitrary: src)
  case Nil then show ?case by simp
next
  case (Cons a ts)
  obtain tau mid where a: "a = (tau,mid)" by (cases a, auto)
  from Cons.prems have step: "isOK (ia4_check_ground_step P src (tau,mid))"
    and rest: "ia4_check_ground_seq P mid ts = return tgt" by (auto simp: a)
  from ia4_check_ground_step[OF step Cons.prems(2)] have one:
    "(ia4_ground_state src,ia4_ground_state mid) \<in> IA4Termination.transition (lts_of P)"
    "IA4Termination.state_lts (lts_of P) (ia4_ground_state mid)" by auto
  from Cons.hyps[OF rest one(2)] have reach:
    "(ia4_ground_state mid,ia4_ground_state tgt) \<in> (IA4Termination.transition (lts_of P))^^length ts"
    and target: "IA4Termination.state_lts (lts_of P) (ia4_ground_state tgt)" by auto
  from relpow_Suc_I2[OF one(1) reach] target show ?case by simp
qed

fun ia4_check_ground_nontermination where
  "ia4_check_ground_nontermination P (IA4_EquivalentState init stem loop) = do {
     IA4Termination.check_lts_impl P;
     check (snd init \<in> set (initial P) \<and> ia4_ground_state_ok P init)
       (showsl_lit (STR ''invalid initial lasso state''));
     head \<leftarrow> ia4_check_ground_seq P init stem;
     last \<leftarrow> ia4_check_ground_seq P head loop;
     check (loop \<noteq> [] \<and> head = last)
       (showsl_lit (STR ''empty or non-closing lasso''))
   }"

lemma ia4_check_ground_nontermination:
  assumes "isOK (ia4_check_ground_nontermination P proof)"
  shows "\<not> IA4Termination.lts_termination (lts_of P)"
proof (cases "proof")
  case (IA4_EquivalentState init stem loop)
  note ok = assms[unfolded IA4_EquivalentState ia4_check_ground_nontermination.simps]
  from ok have init: "ia4_ground_state init \<in> IA4Termination.initial_states (lts_of P)"
    and state: "IA4Termination.state_lts (lts_of P) (ia4_ground_state init)"
    by (auto simp: IA4Termination.initial_states_def ia4_ground_state_def ia4_ground_state_ok_def)
  from ok have "isOK (ia4_check_ground_seq P init stem)" by auto
  then obtain head where stem: "ia4_check_ground_seq P init stem = return head"
    by (cases "ia4_check_ground_seq P init stem", auto)
  from ok stem have loop: "ia4_check_ground_seq P head loop = return head"
    and ne: "length loop > 0"
    by (cases "ia4_check_ground_seq P head loop"; auto)+
  from ia4_check_ground_seq[OF stem state] have reach:
    "(ia4_ground_state init,ia4_ground_state head) \<in> (IA4Termination.transition (lts_of P))\<^sup>*"
    and hs: "IA4Termination.state_lts (lts_of P) (ia4_ground_state head)"
    using relpow_imp_rtrancl by auto
  from ia4_check_ground_seq[OF loop hs] ne trancl_power have cyclic:
    "(ia4_ground_state head,ia4_ground_state head) \<in> (IA4Termination.transition (lts_of P))\<^sup>+" by blast
  let ?T = "IA4Termination.transition (lts_of P)"
  show ?thesis
  proof (cases "ia4_ground_state init = ia4_ground_state head")
    case True
    have "chain (?T\<^sup>+) (\<lambda>_.ia4_ground_state head)" using cyclic by auto
    with init True have "\<not> SN_on (?T\<^sup>+) (IA4Termination.initial_states (lts_of P))"
      by (auto simp: SN_on_def)
    then show ?thesis using SN_on_trancl by auto
  next
    case False
    with reach have first: "(ia4_ground_state init,ia4_ground_state head) \<in> ?T\<^sup>+"
      by (auto simp: rtrancl_eq_or_trancl)
    let ?f = "\<lambda>i. case i of 0 \<Rightarrow> ia4_ground_state init | Suc j \<Rightarrow> ia4_ground_state head"
    have links: "(?f i,?f (Suc i)) \<in> ?T\<^sup>+" for i
      by (cases i, insert first cyclic, auto)
    have "\<exists>f. f 0 \<in> IA4Termination.initial_states (lts_of P) \<and> chain (?T\<^sup>+) f"
      unfolding chain_def by (rule exI[of _ ?f], insert init links, auto)
    then have "\<not> SN_on (?T\<^sup>+) (IA4Termination.initial_states (lts_of P))"
      unfolding SN_on_def by auto
    then show ?thesis using SN_on_trancl by auto
  qed
qed

declare formula.satisfies.simps[code]

declare ia4_ground_val.simps[code] ia4_ground_state_ok_def[code]
  ia4_check_ground_step.simps[code] ia4_check_ground_seq.simps[code]
  ia4_check_ground_nontermination.simps[code]
end
