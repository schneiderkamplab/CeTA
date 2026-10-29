theory LP_Prolog_Test_NO
  imports LP_Prolog_Local_Static LP_SEG_Finite_Measure LP_Cut_NO_Certificate
begin

text \<open>The prefix is checked against the exact source relation. In
particular, undefined calls cannot be traversed as ordinary backtracking.\<close>

fun lpp_no_clear where
  "lpp_no_clear P (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) =
    ((f,length ts)\<notin>lpp_builtin_signature \<and> lpp_defined P (f,length ts))"
| "lpp_no_clear P (LPCGoals (LPCAtom a#gs)#es) = False"
| "lpp_no_clear P s = True"

lemma lpp_no_clear_sound:
  "lpp_no_clear P s \<Longrightarrow>
    \<not>lpp_builtin_active lpp_builtin_signature (lp_cut_state_eval s LPIVar) \<and>
    \<not>lpp_undefined P (lp_cut_state_eval s LPIVar)"
  by (induct P s rule: lpp_no_clear.induct)
    (auto simp: lp_cut_state_map_def lpp_builtin_active_def lpp_undefined_def
      split: Term.term.splits lp_cut_symbol.splits)

fun lpp_finite_var where
  "lpp_finite_var (Var x) = True"
| "lpp_finite_var (Fun f ts) = False"

fun lpp_no_test where
  "lpp_no_test f [a] = (if lpp_var_name f then
    Some (if f=''1:var'' then lpp_finite_var a else \<not>lpp_finite_var a) else None)"
| "lpp_no_test f [a,b] = (if lpp_identity_name f then
    Some (if f=''2:=='' then a=b else a\<noteq>b) else None)"
| "lpp_no_test f ts = None"

lemma lpp_finite_var_eval:
  "lpp_is_var (lp_ieval a LPIVar) = lpp_finite_var a"
  by (cases a) simp_all

lemma lpp_no_test_sound:
  assumes "lpp_no_test f ts=Some passed"
  shows "lpp_test_builtin f (map (\<lambda>a. lp_ieval a LPIVar) ts)
    (if passed then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
  using assms
  by (induct f ts rule: lpp_no_test.induct)
    (auto simp: lpp_test_builtin_def lpp_var_builtin_def lpp_var_holds_def
      lpp_identity_holds_def lpp_finite_var_eval
      dest: lp_seg_ieval_injective split: if_splits)

datatype lpp_no_action = LPPNOOrdinary "string lpc_no_action" | LPPNOTest

fun lpp_no_step where
  "lpp_no_step fuel P s (LPPNOOrdinary action) t =
    (lpp_no_clear P s \<and> lpc_no_step fuel P s action t)"
| "lpp_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) LPPNOTest t =
    (case lpp_no_test f ts of None \<Rightarrow> False |
      Some passed \<Rightarrow> t=(if passed then LPCGoals gs#es else es))"
| "lpp_no_step fuel P s LPPNOTest t = False"

lemma lpp_no_test_step:
  assumes tested: "lpp_no_test f ts=Some passed"
  shows "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) LPIVar,
    lp_cut_state_eval (if passed then LPCGoals gs#es else es) LPIVar)
      \<in>lp_prolog_test_source P"
proof -
  let ?ts = "map (\<lambda>a. lp_ieval a LPIVar) ts"
  have outcome: "lpp_test_builtin f ?ts
    (if passed then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
    by (rule lpp_no_test_sound[OF tested])
  have selected: "(f,length ?ts)\<in>lpp_builtin_signature"
    by (rule lpp_test_builtin_selected[OF outcome])
  have atomic: "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) LPIVar,
    lp_cut_state_eval (if passed then LPCGoals gs#es else es) LPIVar)
      \<in>lpp_atomic_source P lpp_builtin_signature lpp_test_builtin"
  proof (cases passed)
    case True
    have success: "lpp_test_builtin f ?ts (LPPBuiltinSuccess LPIVar)"
      using outcome True by simp
    show ?thesis using lpp_atomic_source.success[where U=lpp_test_builtin and f=f and ts="?ts" and sigma=LPIVar
      and P=P and B=lpp_builtin_signature and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
      and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF success]
      by (simp add: True lp_cut_state_map_def)
  next
    case False
    then show ?thesis using outcome
      by (auto simp: lp_cut_state_map_def intro: lpp_atomic_source.failure)
  qed
  show ?thesis using atomic selected
    by (auto simp: lp_prolog_test_source_def lp_prolog_source_def
      lp_cut_state_map_def lpp_builtin_active_def)
qed

theorem lpp_no_step_sound:
  "lpp_no_step fuel P s action t \<Longrightarrow>
    (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>lp_prolog_test_source P"
proof (induct fuel P s action t rule: lpp_no_step.induct)
  case (1 fuel P s action t)
  then show ?case using lpp_no_clear_sound[of P s] lpc_no_step_sound[of fuel P s action t]
    by (auto simp: lp_prolog_test_source_def lp_prolog_source_def)
next
  case (2 fuel P f ts gs es t)
  then show ?case using lpp_no_test_step[of f ts _ gs es P]
    by (auto split: option.splits)
qed simp_all

fun lpp_no_trace where
  "lpp_no_trace fuel P s [] t = (s=t)"
| "lpp_no_trace fuel P s ((action,u)#rest) t =
    (lpp_no_step fuel P s action u \<and> lpp_no_trace fuel P u rest t)"

theorem lpp_no_trace_sound:
  "lpp_no_trace fuel P s steps t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>(lp_prolog_test_source P)\<^sup>*"
proof (induct steps arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons entry rest)
  obtain action u where entry: "entry=(action,u)" by (cases entry) auto
  have step: "(lp_cut_state_eval s LPIVar,lp_cut_state_eval u LPIVar)\<in>lp_prolog_test_source P"
    using Cons.prems entry by (auto intro: lpp_no_step_sound)
  have tail: "(lp_cut_state_eval u LPIVar,lp_cut_state_eval t LPIVar)\<in>(lp_prolog_test_source P)\<^sup>*"
    using Cons.hyps Cons.prems entry by auto
  show ?case using step tail by (meson r_into_rtrancl rtrancl_trans)
qed

fun lpp_no_static_entry where
  "lpp_no_static_entry A (LPCGoals gs) = list_all (lpp_static_template A) gs"
| "lpp_no_static_entry A (LPCClause gs c m) = list_all (lpp_static_template A) gs"
| "lpp_no_static_entry A (LPCBarrier m) = True"

lemma lpp_no_static_state_sound:
  "list_all (lpp_no_static_entry A) s \<Longrightarrow> lpp_static_state A (lp_cut_state_eval s LPIVar)"
proof -
  have goal: "lpp_static_template A g \<Longrightarrow>
    lpp_static_goal A (lp_cut_map (\<lambda>t. lp_ieval t LPIVar) g)" for g
    by (cases g) auto
  have entry: "lpp_no_static_entry A e \<Longrightarrow>
    lpp_static_entry A (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar) e)" for e
    by (cases e) (auto simp: list_all_iff intro: goal)
  show "list_all (lpp_no_static_entry A) s \<Longrightarrow> lpp_static_state A (lp_cut_state_eval s LPIVar)"
    by (auto simp: lpp_static_state_def lp_cut_state_map_def list_all_iff intro: entry)
qed

definition lpp_no_check_source where
  "lpp_no_check_source fuel P q modes A argv a before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     ((lp_cut_barriers before \<and> lp_cut_barriers after) \<or>
       list_all (\<lambda>x. lpc_no_suffix_safe (snd x)) steps) \<and> steps \<noteq> [] \<and>
     lpp_local_program (set A) P \<and>
     list_all (\<lambda>a. a\<notin>lpp_builtin_signature \<and> lpp_defined P a) A \<and>
     list_all (lpp_no_static_entry (set A)) ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpp_no_trace fuel P [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpc_no_trace fuel P [LPCGoals [LPCAtom a]] steps
       ([LPCGoals [LPCAtom a]] @ after))"

theorem lpp_no_check_source_sound:
  assumes checked: "lpp_no_check_source fuel P q modes A argv a before after initial_steps steps"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_prolog_test_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  let ?entry = "lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar"
  let ?initial = "lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar"
  have pump: "\<not> SN_on (lp_cut_mgu_source P) {?entry}"
    by (rule lpc_no_trace_pump)
      (use checked in \<open>auto simp: lpp_no_check_source_def\<close>)
  have static: "lpp_static_state (set A) ?entry"
    by (rule lpp_no_static_state_sound)
      (use checked in \<open>simp add: lpp_no_check_source_def\<close>)
  have no: "\<not> SN_on (lp_prolog_test_source P) {?entry}"
    unfolding lp_prolog_test_source_def
    by (rule lp_prolog_local_nontermination[OF pump static])
      (use checked in \<open>auto simp: lpp_no_check_source_def list_all_iff\<close>)
  have reach: "(?initial,?entry)\<in>(lp_prolog_test_source P)\<^sup>*"
    by (rule lpp_no_trace_sound[where fuel=fuel and steps=initial_steps])
      (use checked in \<open>simp add: lpp_no_check_source_def\<close>)
  have root: "\<not> SN_on (lp_prolog_test_source P) {?initial}"
  proof
    assume sn: "SN_on (lp_prolog_test_source P) {?initial}"
    have included: "{?entry}\<subseteq>(lp_prolog_test_source P)\<^sup>* `` {?initial}"
      using reach by auto
    have "SN_on (lp_prolog_test_source P) {?entry}"
      by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
    then show False using no by contradiction
  qed
  show ?thesis using checked root
    by (simp add: lpp_no_check_source_def lp_cut_state_map_def)
qed

end
