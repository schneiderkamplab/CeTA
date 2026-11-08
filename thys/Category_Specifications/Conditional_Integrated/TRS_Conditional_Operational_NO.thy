theory TRS_Conditional_Operational_NO
  imports TRS_Conditional_NO_Bridge
begin
lemma ranked_eval_select:
  assumes "native_conditional_inference F R g gs" "i<length gs"
    "\<forall>j<i. native_conditional_success F R (gs!j)"
  shows "(g,gs!i) \<in> ranked_conditional_evaluation F R"
  using assms by (auto simp: ranked_conditional_evaluation_def)
lemma ranked_eval_rewrite:
  assumes step: "(s,u) \<in> ranked_cstep F R" and wf: "funas_term v \<subseteq> F"
  shows "((True,s,v),(True,u,v)) \<in> ranked_conditional_evaluation F R"
proof -
  have success: "native_conditional_success F R (False,s,u)"
    using step by (simp add: ranked_cstep_def)
  have inf: "native_conditional_inference F R (True,s,v) [(False,s,u),(True,u,v)]"
    using native_success_correct[OF success] wf by (intro native_conditional_inference.transitive) auto
  show ?thesis using ranked_eval_select[OF inf, of 1] success by simp
qed

lemma ranked_eval_call:
  assumes mem: "((l,r),cs) \<in> R"
    and ctx: "funas_ctxt C \<subseteq> F" and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
    and wf: "funas_term (l \<cdot> sigma) \<subseteq> F" "funas_term (r \<cdot> sigma) \<subseteq> F"
      "funas_term v \<subseteq> F"
    and cswf: "\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F"
    and idx: "i<length cs"
    and pre: "\<forall>j<i. native_conditional_success F R (True,fst (cs!j) \<cdot> sigma,snd (cs!j) \<cdot> sigma)"
  shows "((True,C\<langle>l \<cdot> sigma\<rangle>,v),(True,fst (cs!i) \<cdot> sigma,snd (cs!i) \<cdot> sigma))
    \<in> (ranked_conditional_evaluation F R)^+"
proof -
  let ?s = "C\<langle>l \<cdot> sigma\<rangle>"
  let ?t = "C\<langle>r \<cdot> sigma\<rangle>"
  have first_inf: "native_conditional_inference F R (True,?s,v) [(False,?s,?t),(True,?t,v)]"
    using ctx wf by (intro native_conditional_inference.transitive) auto
  have first: "((True,?s,v),(False,?s,?t)) \<in> ranked_conditional_evaluation F R"
    using ranked_eval_select[OF first_inf, of 0] by simp
  have second_inf: "native_conditional_inference F R (False,?s,?t)
    (map (\<lambda>(a,b). (True,a \<cdot> sigma,b \<cdot> sigma)) cs)"
    by (rule native_conditional_inference.apply_rule[OF mem ctx sub]) (use ctx wf cswf in auto)
  have second: "((False,?s,?t),(True,fst (cs!i) \<cdot> sigma,snd (cs!i) \<cdot> sigma)) \<in> ranked_conditional_evaluation F R"
    using ranked_eval_select[OF second_inf, of i] idx pre
    by (simp add: split_def)
  show ?thesis using first second by (meson r_into_trancl trancl_trans)
qed

fun ranked_operational_guard where
  "ranked_operational_guard F Rs (Conditional_rewrite p) = ranked_cproof_guard F Rs p"
| "ranked_operational_guard F Rs (Conditional_argument f ts i) = (funas_term (Fun f ts) \<subseteq> F)"
| "ranked_operational_guard F Rs (Conditional_call k sigma i ps s t) =
    (k<length Rs \<and> (let ((l,r),cs)=Rs!k in
      (\<forall>x. funas_term (sigma x) \<subseteq> F) \<and>
      funas_term (l \<cdot> sigma) \<subseteq> F \<and> funas_term (r \<cdot> sigma) \<subseteq> F \<and>
      (\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F) \<and>
      list_all (list_all (ranked_cproof_guard F Rs)) ps))"
fun has_effect where
  "has_effect [] = False"
| "has_effect (Conditional_argument f ts i # ps) = has_effect ps"
| "has_effect (p#ps) = True"
fun evaluation_environment where
  "evaluation_environment Rs C v [] = (C,v)"
| "evaluation_environment Rs C v (Conditional_argument f ts i # ps) =
    evaluation_environment Rs (C \<circ>\<^sub>c More f (take i ts) Hole (drop (Suc i) ts)) v ps"
| "evaluation_environment Rs C v (Conditional_call k sigma i proofs s t # ps) =
    evaluation_environment Rs Hole (snd (snd (Rs!k)!i) \<cdot> sigma) ps"
| "evaluation_environment Rs C v (Conditional_rewrite p # ps) = evaluation_environment Rs C v ps"

lemma ranked_operational_trace:
  fixes Rs :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_trace Rs s t ps" "list_all (ranked_operational_guard F Rs) ps"
    "funas_ctxt C \<subseteq> F" "funas_term v \<subseteq> F"
  shows "(let (D,w)=evaluation_environment Rs C v ps in
      ((True,C\<langle>s\<rangle>,v),(True,D\<langle>t\<rangle>,w)) \<in> (ranked_conditional_evaluation F (set Rs))^* \<and>
      (has_effect ps \<longrightarrow> ((True,C\<langle>s\<rangle>,v),(True,D\<langle>t\<rangle>,w)) \<in> (ranked_conditional_evaluation F (set Rs))^+) \<and>
      funas_ctxt D \<subseteq> F \<and> funas_term w \<subseteq> F)"
  using assms
proof (induct ps arbitrary: s C v)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases p)
    case (Conditional_rewrite q)
    have first: "(s,descent_target p) \<in> ranked_cstep F (set Rs)"
      using ranked_check_cstep_and_csteps(1)[of Rs q F] Cons.prems
      by (auto simp: Conditional_rewrite ranked_cstep_def)
    have lifted: "(C\<langle>s\<rangle>,C\<langle>descent_target p\<rangle>) \<in> ranked_cstep F (set Rs)"
      by (rule ranked_cstep_context[OF first Cons.prems(3)])
    have edge: "((True,C\<langle>s\<rangle>,v),(True,C\<langle>descent_target p\<rangle>,v)) \<in> ranked_conditional_evaluation F (set Rs)"
      by (rule ranked_eval_rewrite[OF lifted Cons.prems(4)])
    show ?thesis using Cons.hyps[of "descent_target p" C v] Cons.prems edge
      by (auto simp: Conditional_rewrite split: prod.splits intro: rtrancl_into_trancl2 rtrancl_into_rtrancl)
  next
    case (Conditional_argument f ts i)
    let ?D = "More f (take i ts) Hole (drop (Suc i) ts)"
    have idx: "i<length ts" and wf: "funas_term (Fun f ts) \<subseteq> F"
      and src: "s=Fun f ts" and trace: "check_conditional_trace Rs (ts!i) t ps"
      and guard: "list_all (ranked_operational_guard F Rs) ps"
      using Cons.prems by (auto simp: Conditional_argument)
    have ctx: "funas_ctxt (C \<circ>\<^sub>c ?D) \<subseteq> F"
      using ranked_argument_context(2)[OF idx wf] Cons.prems by simp
    show ?thesis using Cons.hyps[OF trace guard ctx Cons.prems(4)]
      ranked_argument_context(1)[OF idx wf] src
      by (simp add: Conditional_argument)
  next
    case (Conditional_call k sigma i proofs u z)
    obtain l r cs where rule: "Rs!k=((l,r),cs)" by (cases "Rs!k") auto
    have idx: "k<length Rs" "i<length cs" "length proofs=i"
      and src: "s=l \<cdot> sigma" and trg: "z=fst (cs!i) \<cdot> sigma"
      and checked: "\<forall>j<i. isOK (check_csteps Rs (fst (cs!j) \<cdot> sigma) (snd (cs!j) \<cdot> sigma) (proofs!j))"
      and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
      and wf: "funas_term (l \<cdot> sigma) \<subseteq> F" "funas_term (r \<cdot> sigma) \<subseteq> F"
      and cswf: "\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F"
      and guards: "list_all (list_all (ranked_cproof_guard F Rs)) proofs"
      and tail: "check_conditional_trace Rs z t ps" "list_all (ranked_operational_guard F Rs) ps"
      using Cons.prems by (auto simp: Conditional_call rule Let_def)
    have mem: "((l,r),cs) \<in> set Rs" using nth_mem[OF idx(1)] rule by simp
    have pre: "native_conditional_success F (set Rs) (True,fst (cs!j) \<cdot> sigma,snd (cs!j) \<cdot> sigma)"
      if "j<i" for j
    proof -
      have cj: "cs!j \<in> set cs" using that idx by auto
      have ends: "funas_term (fst (cs!j) \<cdot> sigma) \<subseteq> F"
        "funas_term (snd (cs!j) \<cdot> sigma) \<subseteq> F"
        using cswf cj by (cases "cs!j"; auto)+
      have gp: "list_all (ranked_cproof_guard F Rs) (proofs!j)"
        using guards idx that by (simp add: list_all_length)
      show ?thesis by (rule ranked_check_cstep_and_csteps(2)[OF _ ends gp]) (use checked that in auto)
    qed
    have edge: "((True,C\<langle>s\<rangle>,v),(True,z,snd (cs!i) \<cdot> sigma)) \<in> (ranked_conditional_evaluation F (set Rs))^+"
      using ranked_eval_call[OF mem Cons.prems(3) sub wf Cons.prems(4) cswf idx(2)] pre src trg by simp
    have vw: "funas_term (snd (cs!i) \<cdot> sigma) \<subseteq> F"
      using cswf nth_mem[OF idx(2)] by (cases "cs!i") auto
    show ?thesis using Cons.hyps[OF tail, of Hole "snd (cs!i) \<cdot> sigma"] vw edge
      by (auto simp: Conditional_call rule split: prod.splits intro: trancl_rtrancl_trancl trancl_into_rtrancl)
  qed
qed

theorem conditional_checked_operational_cycle_NO:
  fixes Rs :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes accepted: "check_conditional_cycle Rs s ps"
    and rules: "set Rs=to_conditional_rules R"
    and guard: "list_all (ranked_operational_guard (to_signature A) Rs) ps"
    and progress: "has_effect ps"
    and target: "funas_term v \<subseteq> to_signature A"
    and closed: "evaluation_environment Rs Hole v ps=(Hole,v)"
  shows "\<not> trs_conditional_operationally_terminates A R"
proof -
  have trace: "check_conditional_trace Rs s s ps" using accepted by (simp add: check_conditional_cycle_def)
  have cycle: "((True,s,v),(True,s,v)) \<in>
    (ranked_conditional_evaluation (to_signature A) (to_conditional_rules R))^+"
    using ranked_operational_trace[OF trace guard, of Hole v] target closed progress rules by simp
  have "\<not> SN ((ranked_conditional_evaluation (to_signature A) (to_conditional_rules R))^+)"
    by (rule steps_imp_not_SN[of "\<lambda>_. (True,s,v)" "\<lambda>n. n"]) (simp add: cycle)
  then have "\<not> SN (ranked_conditional_evaluation (to_signature A) (to_conditional_rules R))"
    using SN_imp_SN_trancl by blast
  then show ?thesis using trs_conditional_operationally_terminates_iff_ranked by blast
qed
lemma evaluation_environment_last_call:
  "evaluation_environment Rs C v (ps @ [Conditional_call k sigma i proofs s t]) =
    (Hole,snd (snd (Rs!k)!i) \<cdot> sigma)"
proof (induct ps arbitrary: C v)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases p) auto
qed
lemma has_effect_last_call:
  "has_effect (ps @ [Conditional_call k sigma i proofs s t])"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases p) auto
qed

text \<open>The native binder rotates a call cycle so its last step is a call,
then checks that rotated witness again. The environment closes by construction;
there is no semantic nontermination premise supplied by the front end.\<close>
corollary conditional_checked_operational_call_cycle_NO:
  fixes Rs :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes accepted: "check_conditional_cycle Rs s (ps @ [Conditional_call k sigma i proofs u t])"
    and rules: "set Rs=to_conditional_rules R"
    and guards: "list_all (ranked_operational_guard (to_signature A) Rs)
      (ps @ [Conditional_call k sigma i proofs u t])"
    and target: "funas_term (snd (snd (Rs!k)!i) \<cdot> sigma) \<subseteq> to_signature A"
  shows "\<not> trs_conditional_operationally_terminates A R"
  by (rule conditional_checked_operational_cycle_NO[OF accepted rules guards
        has_effect_last_call target evaluation_environment_last_call])

corollary conditional_checked_rewrite_loop_operational_NO:
  assumes "conditional_check_rewrite_loop Rs s ps xs"
    "set Rs=to_conditional_rules R"
    "list_all (ranked_ordinary_guard (to_signature A) Rs) ps"
    "has_rewrite ps"
    "\<forall>x. funas_term (conditional_substitution xs x) \<subseteq> to_signature A"
  shows "\<not> trs_conditional_operationally_terminates A R"
  using conditional_checked_ordinary_NO[OF assms] operational_implies_ordinary by blast

ML \<open>
  val results = @{thms conditional_inference_iff conditional_success_iff
    conditional_step_iff_ranked conditional_evaluation_iff_ranked
    trs_conditional_terminates_iff_ranked trs_conditional_operationally_terminates_iff_ranked
    ranked_check_cstep_and_csteps conditional_checked_ordinary_NO
    conditional_checked_operational_cycle_NO conditional_checked_operational_call_cycle_NO
    conditional_checked_rewrite_loop_operational_NO}
  val _ = if Thm_Deps.has_skip_proof results then error "Conditional NO: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = writeln ("Conditional ranked/NO oracle dependencies: " ^ commas names)
\<close>

end
