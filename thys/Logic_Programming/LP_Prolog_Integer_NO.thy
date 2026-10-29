theory LP_Prolog_Integer_NO
  imports LP_Prolog_NO_Pumping
begin

text \<open>The source parser uses a disjoint, canonical integer alphabet.
A quoted numeric atom cannot inhabit this alphabet: the reserved NUL tag is
rejected in source identifiers. The checker reconstructs the whole encoded
name from an arbitrary-precision integer, rather than trusting a type label.\<close>
definition lpp_hex_char where
  "lpp_hex_char c = [''0123456789abcdef'' ! (nat_of_char c div 16),
    ''0123456789abcdef'' ! (nat_of_char c mod 16)]"
definition lpp_integer_name :: "int \<Rightarrow> string" where
  "lpp_integer_name n = ''0:prolog_data_'' @ concat (map lpp_hex_char
    (char_of_nat 0 # (''prolog.integer:'' @ show n)))"
definition lpp_integer_term where
  "lpp_integer_term n = Fun (LPCUser (lpp_integer_name n)) []"
definition lpp_integer_value where
  "lpp_integer_value n = LPIFun (LPCUser (lpp_integer_name n)) []"

text \<open>This NO rule is a verified underapproximation: evaluating an
integer literal returns that same integer, and unifying it with itself leaves
the continuation unchanged. Other arithmetic outcomes are not asserted here.
The final nontermination theorem is preserved by every builtin extension that
contains these concrete operations. It cannot be used as a YES semantics.\<close>
definition lpp_integer_no_builtin where
  "lpp_integer_no_builtin f ts result = (lpp_test_builtin f ts result \<or>
    (\<exists>n. f=''2:is'' \<and> ts=[lpp_integer_value n,lpp_integer_value n] \<and>
      result=LPPBuiltinSuccess LPIVar))"

lemma lpp_integer_value_eval[simp]:
  "lp_ieval (lpp_integer_term n) LPIVar=lpp_integer_value n"
  by (simp add: lpp_integer_term_def lpp_integer_value_def)

lemma lpp_builtin_source_mono:
  assumes extends: "\<And>f ts result. U f ts result \<Longrightarrow> V f ts result"
  shows "lpp_builtin_source P U \<subseteq> lpp_builtin_source P V"
proof -
  have atomic: "(s,t)\<in>lpp_atomic_source P lpp_builtin_signature U \<Longrightarrow>
    (s,t)\<in>lpp_atomic_source P lpp_builtin_signature V" for s t
    by (erule lpp_atomic_source.cases)
      (use extends in \<open>auto intro: lpp_atomic_source.intros\<close>)
  show ?thesis using atomic by (auto simp: lp_prolog_source_def)
qed

datatype lpp_integer_no_action = LPPIOrdinary lpp_no_action | LPPIIdentity int

fun lpp_integer_no_step where
  "lpp_integer_no_step fuel P s (LPPIOrdinary action) t = lpp_no_step fuel P s action t"
| "lpp_integer_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPIIdentity n) t =
    (f=''2:is'' \<and> a=lpp_integer_term n \<and> b=lpp_integer_term n \<and> t=LPCGoals gs#es)"
| "lpp_integer_no_step fuel P s (LPPIIdentity n) t = False"

lemma lpp_integer_identity_step:
  "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [lpp_integer_term n,lpp_integer_term n])#gs)#es) LPIVar,
    lp_cut_state_eval (LPCGoals gs#es) LPIVar)\<in>lpp_builtin_source P lpp_integer_no_builtin"
proof -
  have outcome: "lpp_integer_no_builtin ''2:is'' [lpp_integer_value n,lpp_integer_value n] (LPPBuiltinSuccess LPIVar)"
    by (auto simp: lpp_integer_no_builtin_def)
  have selected: "(''2:is'',2)\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def)
  show ?thesis using lpp_atomic_source.success[where U=lpp_integer_no_builtin and f="''2:is''" and ts="[lpp_integer_value n,lpp_integer_value n]" and sigma=LPIVar and P=P and B=lpp_builtin_signature
    and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
    and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF outcome] selected
    by (auto simp: lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def numeral_2_eq_2)
qed

theorem lpp_integer_no_step_sound:
  "lpp_integer_no_step fuel P s action t \<Longrightarrow>
    (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>lpp_builtin_source P lpp_integer_no_builtin"
proof (induct fuel P s action t rule: lpp_integer_no_step.induct)
  case (1 fuel P s action t)
  have included: "lp_prolog_test_source P \<subseteq> lpp_builtin_source P lpp_integer_no_builtin"
    unfolding lp_prolog_test_source_def
    by (rule lpp_builtin_source_mono) (auto simp: lpp_integer_no_builtin_def)
  show ?case using included lpp_no_step_sound[of fuel P s action t] 1 by auto
next
  case (2 fuel P f a b gs es n t)
  then show ?case using lpp_integer_identity_step[of n gs es P] by simp
qed simp_all


fun lpp_integer_no_trace where
  "lpp_integer_no_trace fuel P s [] t = (s=t)"
| "lpp_integer_no_trace fuel P s ((action,u)#rest) t =
    (lpp_integer_no_step fuel P s action u \<and> lpp_integer_no_trace fuel P u rest t)"

lemma lpp_integer_no_trace_sound:
  "lpp_integer_no_trace fuel P s steps t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>(lpp_builtin_source P lpp_integer_no_builtin)\<^sup>*"
proof (induct steps arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons entry rest)
  obtain action u where entry: "entry=(action,u)" by (cases entry) auto
  have step: "(lp_cut_state_eval s LPIVar,lp_cut_state_eval u LPIVar)\<in>lpp_builtin_source P lpp_integer_no_builtin"
    using Cons.prems entry by (auto intro: lpp_integer_no_step_sound)
  have tail: "(lp_cut_state_eval u LPIVar,lp_cut_state_eval t LPIVar)\<in>(lpp_builtin_source P lpp_integer_no_builtin)\<^sup>*"
    using Cons.hyps Cons.prems entry by auto
  show ?case using step tail by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpp_integer_no_trace_path:
  assumes program: "lp_cut_source_program P" and trace: "lpp_integer_no_trace fuel P s steps t"
  shows "lp_barrier_execution.path (lpp_builtin_source P lpp_integer_no_builtin) (lp_cut_state_eval s LPIVar)
     (map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps)"
proof -
  interpret source: lp_barrier_execution "lpp_builtin_source P lpp_integer_no_builtin"
    by (rule lpp_builtin_barrier_execution[OF program])
  from trace show ?thesis
    by (induct steps arbitrary: s) (auto intro: lpp_integer_no_step_sound split: prod.splits)
qed

lemma lpp_integer_no_trace_last:
  "lpp_integer_no_trace fuel P s steps t \<Longrightarrow> last (s # map snd steps) = t"
  by (induct steps arbitrary: s) (auto split: prod.splits)

lemma lpp_integer_no_trace_pump:
  assumes program: "lp_cut_source_program P"
    and loop: "lpp_integer_no_trace fuel P [LPCGoals [LPCAtom a]] steps
      ([LPCGoals [LPCAtom a]] @ after)"
    and progress: "steps \<noteq> []"
    and suffix: "lp_cut_barriers after \<and> lp_cut_barriers before"
  shows "\<not> SN_on (lpp_builtin_source P lpp_integer_no_builtin)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
proof -
  interpret source: lp_barrier_execution "lpp_builtin_source P lpp_integer_no_builtin"
    by (rule lpp_builtin_barrier_execution[OF program])
  let ?core = "lp_cut_state_eval [LPCGoals [LPCAtom a]] LPIVar"
  obtain u us where steps: "map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps = u#us"
    using progress by (cases steps) auto
  have path: "source.path ?core (u#us)"
    using lpp_integer_no_trace_path[OF program loop] steps by simp
  have nonempty: "map snd steps \<noteq> []" using progress by simp
  have last_finite: "last (map snd steps) = [LPCGoals [LPCAtom a]] @ after"
    using lpp_integer_no_trace_last[OF loop] progress by (cases steps) auto
  have last_mapped: "last (map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps)) =
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
    using last_map[OF nonempty, of "\<lambda>s. lp_cut_state_eval s LPIVar"] last_finite by simp
  have last: "last (u#us) = ?core @ lp_cut_state_eval after LPIVar"
  proof -
    have mapped: "map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps) = u#us"
      using steps by (simp only: map_map o_def)
    have eq: "last (u#us) = lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
      using last_mapped mapped by metis
    show ?thesis using eq by (simp only: lp_cut_state_map_def map_append)
  qed
  have bar: "lp_cut_barriers (lp_cut_state_eval bs LPIVar)" if "lp_cut_barriers bs" for bs
    using that
  proof (induct bs)
    case Nil then show ?case by (simp add: lp_cut_state_map_def)
  next
    case (Cons e es)
    have head: "lp_cut_is_barrier (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar) e)"
      using Cons.prems by (cases e) auto
    show ?case using Cons head by (simp add: lp_cut_state_map_def)
  qed
  have core: "map (lp_cut_scope_entry r) ?core = ?core" for r
    by (simp add: lp_cut_state_map_def)
  have after: "lp_cut_barriers (lp_cut_state_eval after LPIVar)" using bar suffix by blast
  have before: "lp_cut_barriers (lp_cut_state_eval before LPIVar)" using bar suffix by blast
  show ?thesis using source.barrier_pump[OF path last after core before]
    by (simp add: lp_cut_state_map_def)
qed

definition lpp_integer_no_check_source where
  "lpp_integer_no_check_source fuel P q modes argv a before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     lp_cut_barriers before \<and> lp_cut_barriers after \<and> steps \<noteq> [] \<and>
     lpp_integer_no_trace fuel P [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpp_integer_no_trace fuel P [LPCGoals [LPCAtom a]] steps
       ([LPCGoals [LPCAtom a]] @ after))"

theorem lpp_integer_no_check_source_sound:
  assumes checked: "lpp_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lpp_builtin_source P lpp_integer_no_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have pump: "\<not> SN_on (lpp_builtin_source P lpp_integer_no_builtin)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
    by (rule lpp_integer_no_trace_pump)
      (use checked in \<open>auto simp: lpp_integer_no_check_source_def\<close>)
  have reach: "(lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar,
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar) \<in> (lpp_builtin_source P lpp_integer_no_builtin)\<^sup>*"
    by (rule lpp_integer_no_trace_sound[where fuel=fuel and steps=initial_steps])
      (use checked in \<open>simp add: lpp_integer_no_check_source_def\<close>)
  have root: "\<not> SN_on (lpp_builtin_source P lpp_integer_no_builtin)
    {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
  proof
    assume sn: "SN_on (lpp_builtin_source P lpp_integer_no_builtin)
      {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
    have included: "{lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}
      \<subseteq> (lpp_builtin_source P lpp_integer_no_builtin)\<^sup>* ``
        {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
      using reach by auto
    have "SN_on (lpp_builtin_source P lpp_integer_no_builtin)
      {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
      by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
    then show False using pump by contradiction
  qed
  show ?thesis using checked root
    by (simp add: lpp_integer_no_check_source_def lp_cut_state_map_def)
qed

corollary lpp_integer_no_builtin_extension:
  assumes checked: "lpp_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
    and extends: "\<And>f ts result. lpp_integer_no_builtin f ts result \<Longrightarrow> U f ts result"
  shows "\<not> SN_on (lpp_builtin_source P U)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof
  let ?initial = "[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
  assume sn: "SN_on (lpp_builtin_source P U) {?initial}"
  have included: "lpp_builtin_source P lpp_integer_no_builtin \<subseteq> lpp_builtin_source P U"
    by (rule lpp_builtin_source_mono[OF extends])
  have smaller: "SN_on (lpp_builtin_source P lpp_integer_no_builtin) {?initial}"
    by (rule SN_on_subset1[OF sn included])
  have no: "\<not> SN_on (lpp_builtin_source P lpp_integer_no_builtin) {?initial}"
    using lpp_integer_no_check_source_sound[OF checked] by simp
  show False using no smaller by contradiction
qed

end
