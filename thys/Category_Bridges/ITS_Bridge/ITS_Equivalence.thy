theory ITS_Equivalence
  imports Category_Properties.ITS_Properties ITS_Ext.ITS4_Parser
begin

text \<open>The native logic has integer and Boolean variables. Encode the latter
by 0 and 1 in disjoint typed store slots. Integer and Boolean
source arguments therefore retain their values and types.\<close>
fun its_decode_store where
  "its_decode_store a (x,IA.IntT) = IA.Int (a (x,IA.IntT))"
| "its_decode_store a (x,IA.BoolT) = IA.Bool (a (x,IA.BoolT) \<noteq> 0)"
fun its_encode_value where
  "its_encode_value (IA.Int n) = n"
| "its_encode_value (IA.Bool b) = (if b then 1 else 0)"
definition its_encode_store where
  "its_encode_store a = its_encode_value \<circ> a"
definition its_store_canonical where
  "its_store_canonical a \<longleftrightarrow> (\<forall>x. a (x,IA.BoolT) = 0 \<or> a (x,IA.BoolT) = 1)"

lemma its_decode_assignment[simp]: "IA4.assignment (its_decode_store a)"
  by (unfold pre_sorted_algebra.assignment_def; intro allI; rename_tac x;
    case_tac x; rename_tac v ty; case_tac ty; simp)

lemma its_encode_canonical:
  assumes "IA4.assignment a"
  shows "its_store_canonical (its_encode_store a)"
proof -
  have "its_encode_store a (x,IA.BoolT)=0 \<or> its_encode_store a (x,IA.BoolT)=1" for x
  proof -
    obtain b where "a (x,IA.BoolT)=IA.Bool b"
      using IA4.assignmentD[OF assms, of "(x,IA.BoolT)"] by auto
    then show ?thesis by (simp add: its_encode_store_def)
  qed
  then show ?thesis by (simp add: its_store_canonical_def)
qed

lemma its_decode_encode:
  fixes a :: "'v \<times> IA.ty \<Rightarrow> IA.val"
  assumes "IA4.assignment a"
  shows "its_decode_store (its_encode_store a) = a"
proof (rule ext)
  fix x :: "'v \<times> IA.ty"
  obtain v ty where x: "x=(v,ty)" by (cases x) auto
  have "a x \<in> IA.Values_of_type ty" using IA4.assignmentD[OF assms, of x] x by simp
  then show "its_decode_store (its_encode_store a) x = a x"
    by (cases ty) (auto simp: x its_encode_store_def)
qed

lemma its_encode_decode:
  fixes a :: "'v \<times> IA.ty \<Rightarrow> int"
  assumes "its_store_canonical a"
  shows "its_encode_store (its_decode_store a) = a"
proof (rule ext)
  fix x :: "'v \<times> IA.ty"
  obtain v ty where x: "x=(v,ty)" by (cases x) auto
  show "its_encode_store (its_decode_store a) x = a x"
    using assms by (cases ty) (auto simp: x its_encode_store_def its_store_canonical_def)
qed

definition its_encode_state where
  "its_encode_state s = (LTS.location s, its_encode_store (valuation s))"
definition its_decode_state where
  "its_decode_state s = State (its_decode_store (snd s)) (fst s)"

fun its_translate_rule where
  "its_translate_rule (Transition l r g) = (l,r,\<lambda>a b z.
    IA4.satisfies (lts.pre_post_inter (its_decode_store a) (its_decode_store b) (its_decode_store z)) g)"
definition its_translate where
  "its_translate P = \<lparr>its_entries = lts.initial P,
    its_rules = its_translate_rule ` transition_rules P,
    its_allowed = \<lambda>l a. its_store_canonical a \<and>
      IA4.satisfies (its_decode_store a) (assertion P l)\<rparr>"

lemma its_translate_finite:
  "set (lts_impl.initial P) = {l} \<Longrightarrow> its_problem (its_translate (lts_of P))"
  by (simp add: its_problem_def its_translate_def)

lemma its_initial_encode:
  "IA4Termination.state s \<Longrightarrow>
    its_initial (its_translate P) (its_encode_state s) \<longleftrightarrow>
    s \<in> IA4Termination.initial_states P"
  by (simp add: its_initial_def its_translate_def its_encode_state_def
    lts.initial_states_def its_encode_canonical its_decode_encode)

lemma its_initial_decode:
  "its_initial (its_translate P) s \<Longrightarrow>
    its_decode_state s \<in> IA4Termination.initial_states P"
  by (auto simp: its_initial_def its_translate_def its_decode_state_def lts.initial_states_def)

lemma its_step_decode:
  assumes "its_step (its_translate P) s t"
  shows "(its_decode_state s, its_decode_state t) \<in> IA4Termination.transition P"
proof -
  obtain tr g z where tr: "tr \<in> transition_rules P"
    and eq: "its_translate_rule tr = (fst s,fst t,g)"
    and sat: "g (snd s) (snd t) z"
    and states: "its_allowed (its_translate P) (fst s) (snd s)"
      "its_allowed (its_translate P) (fst t) (snd t)"
    proof -
    from assms obtain g z where allowed:
      "its_allowed (its_translate P) (fst s) (snd s)"
      "its_allowed (its_translate P) (fst t) (snd t)"
      and member: "(fst s,fst t,g) \<in> its_rules (its_translate P)"
      and holds: "g (snd s) (snd t) z"
      unfolding its_step_def by blast
    from member obtain tr where "tr \<in> transition_rules P"
      "its_translate_rule tr = (fst s,fst t,g)"
      unfolding its_translate_def by auto
    with allowed holds show thesis using that by blast
  qed
  obtain l r phi where shape: "tr = Transition l r phi" by (cases tr) auto
  have "(its_decode_state s,its_decode_state t) \<in>
    IA4Termination.transition_step (IA4Termination.state_lts P) tr"
    using eq sat states unfolding shape
    by (auto simp: its_decode_state_def its_translate_def lts.transition_step_def
      intro!: exI[of _ "its_decode_store z"])
  from tr this show ?thesis by (rule IA4Termination.mem_transitionI)
qed

lemma its_native_step_encode:
  assumes "(s,t) \<in> IA4Termination.transition P"
  shows "its_step (its_translate P) (its_encode_state s) (its_encode_state t)"
proof -
  obtain phi z where tr: "Transition (LTS.location s) (LTS.location t) phi \<in> transition_rules P"
    and states: "IA4Termination.state_lts P s" "IA4Termination.state_lts P t"
    and z: "IA4.assignment z"
    and sat: "IA4.satisfies (lts.pre_post_inter (valuation s) (valuation t) z) phi"
    using assms by (cases rule: IA4Termination.mem_transitionE) auto
  have rule: "(LTS.location s,LTS.location t,\<lambda>a b z.
    IA4.satisfies (lts.pre_post_inter (its_decode_store a) (its_decode_store b) (its_decode_store z)) phi)
    \<in> its_rules (its_translate P)"
    using imageI[OF tr, of its_translate_rule] by (simp add: its_translate_def)
  have permitted_s: "its_allowed (its_translate P) (LTS.location s) (its_encode_store (valuation s))"
    using states(1) by (simp add: its_translate_def its_encode_canonical its_decode_encode)
  have permitted_t: "its_allowed (its_translate P) (LTS.location t) (its_encode_store (valuation t))"
    using states(2) by (simp add: its_translate_def its_encode_canonical its_decode_encode)
  have condition: "IA4.satisfies
    (lts.pre_post_inter (its_decode_store (its_encode_store (valuation s)))
      (its_decode_store (its_encode_store (valuation t)))
      (its_decode_store (its_encode_store z))) phi"
    using sat states z by (simp add: its_decode_encode)
  show ?thesis
    unfolding its_step_def its_encode_state_def fst_conv snd_conv
    apply (intro conjI permitted_s permitted_t)
    apply (rule exI[of _ "\<lambda>a b z. IA4.satisfies
      (lts.pre_post_inter (its_decode_store a) (its_decode_store b) (its_decode_store z)) phi"])
    apply (rule exI[of _ "its_encode_store z"])
    using rule condition by blast
qed

lemma its_step_encode:
  assumes "IA4Termination.state s" "IA4Termination.state t"
  shows "its_step (its_translate P) (its_encode_state s) (its_encode_state t) \<longleftrightarrow>
    (s,t) \<in> IA4Termination.transition P"
proof -
  have roundtrip: "its_decode_state (its_encode_state u) = u" if "IA4Termination.state u" for u
    using that by (cases u) (simp add: its_decode_state_def its_encode_state_def its_decode_encode)
  show ?thesis
  proof
    assume step: "its_step (its_translate P) (its_encode_state s) (its_encode_state t)"
    have "(its_decode_state (its_encode_state s), its_decode_state (its_encode_state t))
      \<in> IA4Termination.transition P" by (rule its_step_decode[OF step])
    then show "(s,t) \<in> IA4Termination.transition P"
      by (simp only: roundtrip[OF assms(1)] roundtrip[OF assms(2)])
  next
    assume "(s,t) \<in> IA4Termination.transition P"
    then show "its_step (its_translate P) (its_encode_state s) (its_encode_state t)"
      by (rule its_native_step_encode)
  qed
qed

text \<open>Both directions preserve complete executions and their initial state.
No reachability, ranking-function or arithmetic-checker premise is assumed.\<close>
theorem its_termination_iff:
  "its_terminates (its_translate P) \<longleftrightarrow> IA4Termination.lts_termination P"
proof -
  have forward: "\<exists>s. its_initial (its_translate P) (s 0) \<and>
    (\<forall>n. its_step (its_translate P) (s n) (s (Suc n)))"
    if init: "f 0 \<in> IA4Termination.initial_states P"
    and steps: "\<forall>n. (f n,f (Suc n)) \<in> IA4Termination.transition P" for f
  proof -
    have valid: "IA4Termination.state (f 0)" using init by (simp add: lts.initial_states_def)
    have encoded_initial: "its_initial (its_translate P) (its_encode_state (f 0))"
      using its_initial_encode[OF valid, of P] init by blast
    have encoded_steps: "\<forall>n. its_step (its_translate P) (its_encode_state (f n))
      (its_encode_state (f (Suc n)))"
      by (intro allI; rule its_native_step_encode; rule spec[OF steps])
    show ?thesis by (rule exI[of _ "its_encode_state \<circ> f"])
      (simp add: encoded_initial encoded_steps)
  qed
  have backward: "\<exists>f. f 0 \<in> IA4Termination.initial_states P \<and>
    (\<forall>n. (f n,f (Suc n)) \<in> IA4Termination.transition P)"
    if init: "its_initial (its_translate P) (s 0)"
    and steps: "\<forall>n. its_step (its_translate P) (s n) (s (Suc n))" for s
  proof -
    have decoded_initial: "its_decode_state (s 0) \<in> IA4Termination.initial_states P"
      by (rule its_initial_decode[OF init])
    have decoded_steps: "\<forall>n. (its_decode_state (s n),its_decode_state (s (Suc n)))
      \<in> IA4Termination.transition P"
      by (intro allI; rule its_step_decode; rule spec[OF steps])
    show ?thesis by (rule exI[of _ "its_decode_state \<circ> s"])
      (simp add: decoded_initial decoded_steps)
  qed
  show ?thesis unfolding its_terminates_def SN_on_def using forward backward by blast
qed

end
