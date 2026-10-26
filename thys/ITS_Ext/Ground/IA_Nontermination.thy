theory IA_Nontermination
  imports LTS.IA_Instance LTS.LTS_Nontermination_Prover
begin

text \<open>Ground integer states for the existing exact-state lasso criterion.
  Unlisted integer coordinates are zero; Boolean coordinates are false.
  These total valuations avoid a non-executable universal assignment test.\<close>

type_synonym 'v ia_ground_state = "('v \<times> int) list \<times> string"
type_synonym 'v ia_ground_step =
  "(string \<times> (IA.sig,'v,IA.ty,string) transition_rule) \<times> 'v ia_ground_state"
datatype 'v ia_nontermination_proof = IA_EquivalentState
  "'v ia_ground_state" "'v ia_ground_step list" "'v ia_ground_step list"

context IA_locale
begin

fun ground_val where
  "ground_val vs (x,IntT) = Int (map_of_default 0 vs x)"
| "ground_val vs (x,BoolT) = Bool False"

lemma ground_assignment[simp]: "assignment (ground_val vs)"
  unfolding assignment_def
  by (intro allI, rename_tac x, case_tac x, rename_tac a b, case_tac b, auto)

definition ground_state where "ground_state s = State (ground_val (fst s)) (snd s)"
definition ground_state_ok where
  "ground_state_ok P s = (ground_val (fst s) \<Turnstile> assertion_of P (snd s))"

lemma ground_state_ok:
  "ground_state_ok P s \<Longrightarrow> state_lts (lts_of P) (ground_state s)"
  by (simp add: ground_state_ok_def ground_state_def)

fun check_ground_step where
  "check_ground_step P src ((lab,Transition l r f),tgt) = do {
    check ((lab,Transition l r f) \<in> set (transitions_impl P)) (showsl_lit (STR ''unknown lasso transition''));
    check (ground_state_ok P tgt) (showsl_lit (STR ''invalid target valuation''));
    check (snd src = l \<and> snd tgt = r) (showsl_lit (STR ''lasso endpoints''));
    check (pre_post_inter (ground_val (fst src)) (ground_val (fst tgt)) (ground_val []) \<Turnstile> f)
      (showsl_lit (STR ''lasso guard or update is false''))
  }"

lemma check_ground_step:
  assumes ok: "isOK (check_ground_step P src (tau,tgt))"
      and src: "state_lts (lts_of P) (ground_state src)"
  shows "(ground_state src,ground_state tgt) \<in> transition (lts_of P) \<and>
    state_lts (lts_of P) (ground_state tgt)"
proof -
  obtain lab l r f where tau: "tau = (lab,Transition l r f)"
    by (cases tau; cases "snd tau", auto)
  from ok have mem: "(lab,Transition l r f) \<in> set (transitions_impl P)"
    and tgt: "state_lts (lts_of P) (ground_state tgt)"
    and loc: "snd src = l" "snd tgt = r"
    and sat: "pre_post_inter (ground_val (fst src)) (ground_val (fst tgt)) (ground_val []) \<Turnstile> f"
    by (auto simp: tau dest: ground_state_ok)
  have "Transition l r f \<in> transition_rules (lts_of P)"
    using mem by (cases P, auto simp: lts_of_def)
  moreover have "(ground_state src,ground_state tgt) \<in> transition_step_lts (lts_of P) (Transition l r f)"
    by (rule mem_transition_step_TransitionI[OF src tgt], insert loc sat, auto simp: ground_state_def)
  ultimately have step: "(ground_state src,ground_state tgt) \<in> transition (lts_of P)"
    by (rule mem_transitionI)
  from step tgt show ?thesis by blast
qed

fun check_ground_seq where
  "check_ground_seq P src [] = return src"
| "check_ground_seq P src ((tau,tgt)#ts) = do {
      check_ground_step P src (tau,tgt);
      check_ground_seq P tgt ts
    }"

lemma check_ground_seq:
  assumes "check_ground_seq P src ts = return tgt"
      and "state_lts (lts_of P) (ground_state src)"
  shows "(ground_state src,ground_state tgt) \<in> (transition (lts_of P))^^length ts \<and>
    state_lts (lts_of P) (ground_state tgt)"
  using assms
proof (induct ts arbitrary: src)
  case Nil then show ?case by simp
next
  case (Cons a ts)
  obtain tau mid where a: "a = (tau,mid)" by (cases a, auto)
  from Cons.prems have step: "isOK (check_ground_step P src (tau,mid))"
    and rest: "check_ground_seq P mid ts = return tgt" by (auto simp: a)
  from check_ground_step[OF step Cons.prems(2)] have one:
    "(ground_state src,ground_state mid) \<in> transition (lts_of P)"
    "state_lts (lts_of P) (ground_state mid)" by auto
  from Cons.hyps[OF rest one(2)] have reach:
    "(ground_state mid,ground_state tgt) \<in> (transition (lts_of P))^^length ts"
    and target: "state_lts (lts_of P) (ground_state tgt)" by auto
  from relpow_Suc_I2[OF one(1) reach] target show ?case by simp
qed

fun check_ground_nontermination where
  "check_ground_nontermination P (IA_EquivalentState init stem loop) = do {
     check_lts_impl P;
     check (snd init \<in> set (initial P) \<and> ground_state_ok P init)
       (showsl_lit (STR ''invalid initial lasso state''));
     head \<leftarrow> check_ground_seq P init stem;
     last \<leftarrow> check_ground_seq P head loop;
     check (loop \<noteq> [] \<and> head = last)
       (showsl_lit (STR ''empty or non-closing lasso''))
   }"

lemma check_ground_nontermination:
  assumes "isOK (check_ground_nontermination P proof)"
  shows "\<not> lts_termination (lts_of P)"
proof (cases "proof")
  case (IA_EquivalentState init stem loop)
  note ok = assms[unfolded IA_EquivalentState check_ground_nontermination.simps]
  from ok have init: "ground_state init \<in> initial_states (lts_of P)"
    and state: "state_lts (lts_of P) (ground_state init)"
    by (auto simp: initial_states_def ground_state_def ground_state_ok_def)
  from ok have "isOK (check_ground_seq P init stem)" by auto
  then obtain head where stem: "check_ground_seq P init stem = return head"
    by (cases "check_ground_seq P init stem", auto)
  from ok stem have loop: "check_ground_seq P head loop = return head"
    and ne: "length loop > 0"
    by (cases "check_ground_seq P head loop"; auto)+
  from check_ground_seq[OF stem state] have reach:
    "(ground_state init,ground_state head) \<in> (transition (lts_of P))\<^sup>*"
    and hs: "state_lts (lts_of P) (ground_state head)"
    using relpow_imp_rtrancl by auto
  from check_ground_seq[OF loop hs] ne trancl_power have cyclic:
    "(ground_state head,ground_state head) \<in> (transition (lts_of P))\<^sup>+" by blast
  let ?T = "transition (lts_of P)"
  show ?thesis
  proof (cases "ground_state init = ground_state head")
    case True
    have "chain (?T\<^sup>+) (\<lambda>_.ground_state head)" using cyclic by auto
    with init True have "\<not> SN_on (?T\<^sup>+) (initial_states (lts_of P))"
      by (auto simp: SN_on_def)
    then show ?thesis using SN_on_trancl by auto
  next
    case False
    with reach have first: "(ground_state init,ground_state head) \<in> ?T\<^sup>+"
      by (auto simp: rtrancl_eq_or_trancl)
    let ?f = "\<lambda>i. case i of 0 \<Rightarrow> ground_state init | Suc j \<Rightarrow> ground_state head"
    have links: "(?f i,?f (Suc i)) \<in> ?T\<^sup>+" for i
      by (cases i, insert first cyclic, auto)
    have "\<exists>f. f 0 \<in> initial_states (lts_of P) \<and> chain (?T\<^sup>+) f"
      unfolding chain_def by (rule exI[of _ ?f], insert init links, auto)
    then have "\<not> SN_on (?T\<^sup>+) (initial_states (lts_of P))"
      unfolding SN_on_def by auto
    then show ?thesis using SN_on_trancl by auto
  qed
qed
end

declare formula.satisfies.simps[code]

declare IA.ground_val.simps[code] IA.ground_state_ok_def[code]
  IA.check_ground_step.simps[code] IA.check_ground_seq.simps[code]
  IA.check_ground_nontermination.simps[code]
end
