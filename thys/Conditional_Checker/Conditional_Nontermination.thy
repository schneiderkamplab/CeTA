theory Conditional_Nontermination
  imports CTRS.Quasi_Decreasingness CTRS.Conditional_Rewriting_Impl
begin

text \<open>A condition call is available only after all earlier conditions
have succeeded. Unlike ordinary rewriting, the called condition need not
return successfully. Keeping these two relations separate is essential for
operational nontermination.\<close>

definition conditional_call where
  "conditional_call R = {(s,t). \<exists>l r cs i \<sigma>.
    ((l,r),cs) \<in> R \<and> i < length cs \<and>
    (\<forall>j<i. (fst (cs!j) \<cdot> \<sigma>, snd (cs!j) \<cdot> \<sigma>) \<in> (cstep R)^*) \<and>
    s = l \<cdot> \<sigma> \<and> t = fst (cs!i) \<cdot> \<sigma>}"

definition conditional_descent where
  "conditional_descent R = cstep R \<union> {\<rhd>} \<union> conditional_call R"

lemma conditional_descent_subset:
  assumes "quasi_decreasing_order R S"
  shows "conditional_descent R \<subseteq> S"
  using assms
  unfolding conditional_descent_def conditional_call_def quasi_decreasing_order_def
  by auto

theorem conditional_descent_nontermination:
  assumes "\<not> SN (conditional_descent R)"
  shows "\<not> quasi_decreasing R"
proof
  assume "quasi_decreasing R"
  then obtain S where order: "quasi_decreasing_order R S"
    unfolding quasi_decreasing_def by blast
  have sn: "SN S" using order unfolding quasi_decreasing_order_def by simp
  have "SN (conditional_descent R)"
    by (rule SN_subset[OF sn conditional_descent_subset[OF order]])
  with assms show False by contradiction
qed

text \<open>This theorem deliberately concludes non-quasi-decreasingness,
not merely non-quasi-reductivity. The operational characterization applies
to deterministic conditional systems; an executable front end must check
that applicability condition before reporting operational NO.\<close>

datatype ('f,'v) conditional_descent_proof =
    Conditional_rewrite "('f,'v) cstep_proof"
  | Conditional_call nat "('f,'v) subst" nat "('f,'v) cstep_proof list list"
      "('f,'v) term" "('f,'v) term"
  | Conditional_argument 'f "('f,'v) term list" nat

fun descent_source where
  "descent_source (Conditional_rewrite p) = cstep_src p"
| "descent_source (Conditional_call k \<sigma> i ps s t) = s"
| "descent_source (Conditional_argument f ts i) = Fun f ts"

fun descent_target where
  "descent_target (Conditional_rewrite p) = cstep_trg p"
| "descent_target (Conditional_call k \<sigma> i ps s t) = t"
| "descent_target (Conditional_argument f ts i) = ts!i"

fun check_conditional_descent where
  "check_conditional_descent R (Conditional_rewrite p) = isOK (check_cstep R p)"
| "check_conditional_descent R (Conditional_call k \<sigma> i ps s t) =
    (k < length R \<and> (let ((l,r),cs) = R!k in
      i < length cs \<and> length ps = i \<and>
      s = l \<cdot> \<sigma> \<and> t = fst (cs!i) \<cdot> \<sigma> \<and>
      (\<forall>j<i. isOK (check_csteps R (fst (cs!j) \<cdot> \<sigma>)
         (snd (cs!j) \<cdot> \<sigma>) (ps!j)))))"
| "check_conditional_descent R (Conditional_argument f ts i) = (i < length ts)"

lemma check_conditional_descent_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_descent R p"
  shows "(descent_source p, descent_target p) \<in> conditional_descent (set R)"
  using assms
proof (cases p)
  case (Conditional_rewrite q)
  then show ?thesis using assms check_cstep
    by (auto simp: conditional_descent_def)
next
  case (Conditional_call k \<sigma> i ps s t)
  obtain l r cs where rule: "R!k = ((l,r),cs)" by (cases "R!k") auto
  have index: "k < length R" and bound: "i < length cs"
    and src: "s = l \<cdot> \<sigma>" and trg: "t = fst (cs!i) \<cdot> \<sigma>"
    and prefix: "\<forall>j<i. isOK (check_csteps R (fst (cs!j) \<cdot> \<sigma>)
       (snd (cs!j) \<cdot> \<sigma>) (ps!j))"
    using assms by (auto simp: Conditional_call rule Let_def)
  have member: "((l,r),cs) \<in> set R" using nth_mem[OF index] rule by simp
  have conditions: "\<forall>j<i. (fst (cs!j) \<cdot> \<sigma>, snd (cs!j) \<cdot> \<sigma>) \<in> (cstep (set R))^*"
    using prefix check_csteps by blast
  have "(s,t) \<in> conditional_call (set R)"
    unfolding conditional_call_def
    by (intro CollectI case_prodI exI[of _ l] exI[of _ r] exI[of _ cs]
        exI[of _ i] exI[of _ \<sigma>]) (simp add: member bound src trg conditions)
  then show ?thesis by (simp add: Conditional_call conditional_descent_def)
next
  case (Conditional_argument f ts i)
  have "i < length ts" using assms Conditional_argument by simp
  then have "Fun f ts \<rhd> ts!i" by auto
  then show ?thesis by (simp add: Conditional_argument conditional_descent_def)
qed

fun check_conditional_trace where
  "check_conditional_trace R s t [] = (s=t)"
| "check_conditional_trace R s t (p#ps) =
    (s = descent_source p \<and> check_conditional_descent R p \<and>
      check_conditional_trace R (descent_target p) t ps)"

lemma check_conditional_trace_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_trace R s t ps"
  shows "(s,t) \<in> (conditional_descent (set R))^* \<and>
    (ps \<noteq> [] \<longrightarrow> (s,t) \<in> (conditional_descent (set R))^+)"
  using assms
proof (induct ps arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have step: "(s,descent_target p) \<in> conditional_descent (set R)"
    using Cons.prems check_conditional_descent_sound by auto
  have tail: "(descent_target p,t) \<in> (conditional_descent (set R))^*"
    using Cons by auto
  have "(s,t) \<in> (conditional_descent (set R))^+"
    using step tail by (rule rtrancl_into_trancl2)
  then show ?case by auto
qed

definition check_conditional_cycle where
  "check_conditional_cycle R s ps = (ps \<noteq> [] \<and> check_conditional_trace R s s ps)"

theorem check_conditional_cycle_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_cycle R s ps"
  shows "\<not> quasi_decreasing (set R)"
proof (rule conditional_descent_nontermination)
  have loop: "(s,s) \<in> (conditional_descent (set R))^+"
    using assms check_conditional_trace_sound unfolding check_conditional_cycle_def by blast
  have "\<not> SN ((conditional_descent (set R))^+)"
    by (rule steps_imp_not_SN[of "\<lambda>_. s" "\<lambda>n. n"]) (simp add: loop)
  then show "\<not> SN (conditional_descent (set R))" using SN_imp_SN_trancl by blast
qed

lemma conditional_call_subst:
  assumes "(s,t) \<in> conditional_call R"
  shows "(s \<cdot> \<sigma>,t \<cdot> \<sigma>) \<in> conditional_call R"
proof -
  from assms obtain l r cs i \<tau> where member: "((l,r),cs) \<in> R"
    and bound: "i < length cs" and src: "s = l \<cdot> \<tau>"
    and trg: "t = fst (cs!i) \<cdot> \<tau>"
    and prefix: "\<forall>j<i. (fst (cs!j) \<cdot> \<tau>,snd (cs!j) \<cdot> \<tau>) \<in> (cstep R)^*"
    unfolding conditional_call_def by blast
  have closed: "subst.closed ((cstep R)^*)"
    by (rule subst.closed_rtrancl[OF subst_closed_cstep])
  have prefix': "\<forall>j<i. (fst (cs!j) \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>),snd (cs!j) \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>)) \<in> (cstep R)^*"
    using prefix subst.closedD[OF closed, of _ _ \<sigma>] by auto
  show ?thesis unfolding conditional_call_def
    apply (simp only: mem_Collect_eq case_prod_conv)
    apply (rule exI[of _ l])
    apply (rule exI[of _ r])
    apply (rule exI[of _ cs])
    apply (rule exI[of _ i])
    apply (rule exI[of _ "\<tau> \<circ>\<^sub>s \<sigma>"])
    using member bound src trg prefix' by simp
qed

lemma conditional_descent_stable:
  "subst.closed (conditional_descent R)"
  unfolding conditional_descent_def
  by (intro subst.closed_Un subst_closed_cstep subst_closed_supt subst.closedI conditional_call_subst)

definition check_conditional_loop where
  "check_conditional_loop R s ps \<sigma> =
    (ps \<noteq> [] \<and> check_conditional_trace R s (s \<cdot> \<sigma>) ps)"

theorem check_conditional_loop_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_loop R s ps \<sigma>"
  shows "\<not> quasi_decreasing (set R)"
proof (rule conditional_descent_nontermination)
  have path: "(s,s \<cdot> \<sigma>) \<in> (conditional_descent (set R))^+"
    using check_conditional_trace_sound[of R s "s \<cdot> \<sigma>" ps] assms
    unfolding check_conditional_loop_def by blast
  have "\<not> SN_on (conditional_descent (set R)) {s}"
    by (rule stable_loop_imp_not_SN[OF conditional_descent_stable path])
  then show "\<not> SN (conditional_descent (set R))" unfolding SN_on_def by auto
qed

definition conditional_check :: "(integer,integer list) crule list \<Rightarrow>
  (integer,integer list) term \<Rightarrow> (integer,integer list) conditional_descent_proof list \<Rightarrow> bool" where
  "conditional_check R s ps = (isOK (check_wf_ctrs R) \<and> check_conditional_cycle R s ps)"

theorem conditional_check_sound:
  "conditional_check R s ps \<Longrightarrow> wf_ctrs (set R) \<and> \<not> quasi_decreasing (set R)"
  using check_conditional_cycle_sound[of R s ps]
  by (auto simp: conditional_check_def)

definition conditional_substitution :: "(integer list \<times> (integer,integer list) term) list \<Rightarrow> (integer,integer list) subst" where
  "conditional_substitution xs x = (case map_of xs x of None \<Rightarrow> Var x | Some t \<Rightarrow> t)"

definition conditional_check_loop where
  "conditional_check_loop R s ps xs = (isOK (check_wf_ctrs R) \<and>
    check_conditional_loop R s ps (conditional_substitution xs))"

theorem conditional_check_loop_sound:
  "conditional_check_loop R s ps xs \<Longrightarrow> wf_ctrs (set R) \<and> \<not> quasi_decreasing (set R)"
  using check_conditional_loop_sound[of R s ps "conditional_substitution xs"]
  by (auto simp: conditional_check_loop_def)

fun ordinary_descent_step where
  "ordinary_descent_step (Conditional_rewrite p) = True"
| "ordinary_descent_step (Conditional_argument f ts i) = True"
| "ordinary_descent_step (Conditional_call k s i ps t u) = False"

lemma ordinary_descent_step_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_descent R p" "ordinary_descent_step p"
  shows "(descent_source p,descent_target p) \<in> cstep (set R) \<union> {\<rhd>}"
  using assms check_cstep[of R]
  by (cases p) auto

lemma ordinary_descent_trace_sound:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  assumes "check_conditional_trace R s t ps" "list_all ordinary_descent_step ps"
  shows "(s,t) \<in> (cstep (set R) \<union> {\<rhd>})^* \<and>
    (ps \<noteq> [] \<longrightarrow> (s,t) \<in> (cstep (set R) \<union> {\<rhd>})^+)"
  using assms
proof (induct ps arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have step: "(s,descent_target p) \<in> cstep (set R) \<union> {\<rhd>}"
    using Cons.prems ordinary_descent_step_sound[of R p] by auto
  have tail: "(descent_target p,t) \<in> (cstep (set R) \<union> {\<rhd>})^*"
    using Cons by auto
  have "(s,t) \<in> (cstep (set R) \<union> {\<rhd>})^+"
    using step tail by (rule rtrancl_into_trancl2)
  then show ?case by auto
qed

definition conditional_check_rewrite_loop where
  "conditional_check_rewrite_loop R s ps xs = (list_all ordinary_descent_step ps \<and>
    check_conditional_loop R s ps (conditional_substitution xs))"

theorem conditional_check_rewrite_loop_sound:
  assumes "conditional_check_rewrite_loop R s ps xs"
  shows "\<not> SN (cstep (set R))"
proof
  assume sn: "SN (cstep (set R))"
  have extended: "SN (cstep (set R) \<union> {\<rhd>})"
    by (rule SN_imp_SN_union_supt[OF sn cstep_ctxt_closed])
  have path: "(s,s \<cdot> conditional_substitution xs) \<in> (cstep (set R) \<union> {\<rhd>})^+"
    using ordinary_descent_trace_sound[of R s "s \<cdot> conditional_substitution xs" ps] assms
    unfolding conditional_check_rewrite_loop_def check_conditional_loop_def by blast
  have stable: "subst.closed (cstep (set R) \<union> {\<rhd>})"
    by (rule subst.closed_Un[OF subst_closed_cstep subst_closed_supt])
  have "\<not> SN_on (cstep (set R) \<union> {\<rhd>}) {s}"
    by (rule stable_loop_imp_not_SN[OF stable path])
  with extended show False unfolding SN_on_def by auto
qed

export_code conditional_check conditional_check_loop conditional_check_rewrite_loop conditional_substitution Conditional_rewrite Conditional_call
  Conditional_argument Cstep_step Var Fun nat_of_integer
  in Haskell module_name Conditional_Checker

end
