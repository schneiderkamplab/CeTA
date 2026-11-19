theory TRS_Conditional_NO_Bridge
  imports Category_Conditional_Bridge.TRS_Conditional_Loops
    Conditional_Checker.Conditional_Nontermination
begin
fun ranked_ordinary_guard where
  "ranked_ordinary_guard F Rs (Conditional_rewrite p) = ranked_cproof_guard F Rs p"
| "ranked_ordinary_guard F Rs (Conditional_argument f ts i) = (funas_term (Fun f ts) \<subseteq> F)"
| "ranked_ordinary_guard F Rs (Conditional_call k sigma i ps s t) = False"
fun has_rewrite where
  "has_rewrite [] = False"
| "has_rewrite (Conditional_rewrite p # ps) = True"
| "has_rewrite (p#ps) = has_rewrite ps"
fun descent_context where
  "descent_context C [] = C"
| "descent_context C (Conditional_argument f ts i # ps) =
    descent_context (C \<circ>\<^sub>c More f (take i ts) Hole (drop (Suc i) ts)) ps"
| "descent_context C (p#ps) = descent_context C ps"

lemma ranked_argument_context:
  assumes "i<length ts" "funas_term (Fun f ts) \<subseteq> F"
  shows "(More f (take i ts) Hole (drop (Suc i) ts))\<langle>ts!i\<rangle> = Fun f ts"
    "funas_ctxt (More f (take i ts) Hole (drop (Suc i) ts)) \<subseteq> F"
proof -
  have eq: "(More f (take i ts) Hole (drop (Suc i) ts))\<langle>ts!i\<rangle> = Fun f ts"
    using id_take_nth_drop[OF assms(1)] by simp
  then show "(More f (take i ts) Hole (drop (Suc i) ts))\<langle>ts!i\<rangle> = Fun f ts" .
  show "funas_ctxt (More f (take i ts) Hole (drop (Suc i) ts)) \<subseteq> F"
    using assms(2) eq funas_term_ctxt_apply by (metis Un_subset_iff)
qed

lemma ranked_ordinary_trace:
  fixes Rs :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_trace Rs s t ps"
    "list_all (ranked_ordinary_guard F Rs) ps" "funas_ctxt C \<subseteq> F"
  shows "(C\<langle>s\<rangle>,(descent_context C ps)\<langle>t\<rangle>) \<in> (ranked_cstep F (set Rs))^* \<and>
    (has_rewrite ps \<longrightarrow> (C\<langle>s\<rangle>,(descent_context C ps)\<langle>t\<rangle>) \<in> (ranked_cstep F (set Rs))^+) \<and>
    funas_ctxt (descent_context C ps) \<subseteq> F"
  using assms
proof (induct ps arbitrary: s C)
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
    have tail: "(C\<langle>descent_target p\<rangle>,(descent_context C ps)\<langle>t\<rangle>) \<in> (ranked_cstep F (set Rs))^*"
      "funas_ctxt (descent_context C ps) \<subseteq> F"
      using Cons.hyps[of "descent_target p" C] Cons.prems by auto
    have pos: "(C\<langle>s\<rangle>,(descent_context C ps)\<langle>t\<rangle>) \<in> (ranked_cstep F (set Rs))^+"
      by (rule rtrancl_into_trancl2[OF lifted tail(1)])
    show ?thesis using pos tail by (auto simp: Conditional_rewrite)
  next
    case (Conditional_argument f ts i)
    let ?D = "More f (take i ts) Hole (drop (Suc i) ts)"
    have idx: "i<length ts" and wf: "funas_term (Fun f ts) \<subseteq> F"
      and src: "s=Fun f ts" and trace: "check_conditional_trace Rs (ts!i) t ps"
      and guard: "list_all (ranked_ordinary_guard F Rs) ps"
      using Cons.prems by (auto simp: Conditional_argument)
    have ctx: "funas_ctxt (C \<circ>\<^sub>c ?D) \<subseteq> F"
      using ranked_argument_context(2)[OF idx wf] Cons.prems by simp
    show ?thesis using Cons.hyps[OF trace guard ctx]
      ranked_argument_context(1)[OF idx wf] src by (simp add: Conditional_argument)
  next
    case (Conditional_call k sigma i proofs u v)
    then show ?thesis using Cons.prems by simp
  qed
qed

theorem conditional_checked_ordinary_NO:
  assumes accepted: "conditional_check_rewrite_loop Rs s ps xs"
    and rules: "set Rs=to_conditional_rules R"
    and guards: "list_all (ranked_ordinary_guard (to_signature A) Rs) ps"
    and progress: "has_rewrite ps"
    and sub: "\<forall>x. funas_term (conditional_substitution xs x) \<subseteq> to_signature A"
  shows "\<not> trs_conditional_terminates A R"
proof -
  have trace: "check_conditional_trace Rs s (s \<cdot> conditional_substitution xs) ps"
    using accepted by (simp add: conditional_check_rewrite_loop_def check_conditional_loop_def)
  note data = ranked_ordinary_trace[OF trace guards, of Hole]
  have path: "(s,(descent_context Hole ps)\<langle>s \<cdot> conditional_substitution xs\<rangle>) \<in>
      (ranked_cstep (to_signature A) (to_conditional_rules R))^+"
    and ctx: "funas_ctxt (descent_context Hole ps) \<subseteq> to_signature A"
    using data progress rules by auto
  show ?thesis by (rule conditional_ranked_loop_ordinary_NO[OF path ctx sub])
qed
end
