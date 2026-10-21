theory LP_Infinite_Resolution
  imports LP_Infinite_Machine
begin

lemma lp_atom_eval_subst[simp]:
  "lp_iatom_subst (lp_atom_eval a \<rho>) \<sigma> =
    lp_atom_eval a (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
  by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def lp_ieval_subst)

lemma lp_iatom_subst_id[simp]: "lp_iatom_subst a LPIVar = a"
  by (cases a) (simp add: lp_iatom_subst_def)

lemma lp_iconfig_subst_id[simp]: "lp_iconfig_subst s LPIVar = s"
  by (induct s) simp_all

lemma lp_ilocal_machine: "lp_ilocal P \<subseteq> lp_imachine P"
  unfolding lp_imachine_def by (auto intro!: exI[where x=LPIVar])

fun lp_ianswer where
  "lp_ianswer P (LPICall a) = a"
| "lp_ianswer P (LPIDone a) = a"
| "lp_ianswer P (LPIWait c i \<rho> k) = lp_atom_eval (fst (P!c)) \<rho>"

fun lp_igoals where
  "lp_igoals P (LPICall a) = [a]"
| "lp_igoals P (LPIDone a) = []"
| "lp_igoals P (LPIWait c i \<rho> k) = lp_igoals P k @
    map (\<lambda>a. lp_atom_eval a \<rho>) (drop (Suc i) (snd (P!c)))"

fun lp_ivalid where
  "lp_ivalid P (LPICall a) = True"
| "lp_ivalid P (LPIDone a) = True"
| "lp_ivalid P (LPIWait c i \<rho> k) = (c < length P \<and> i < length (snd (P!c)) \<and>
    lp_ivalid P k \<and> lp_ianswer P k = lp_atom_eval (snd (P!c)!i) \<rho>)"

fun lp_ifocused where
  "lp_ifocused (LPICall a) = True"
| "lp_ifocused (LPIDone a) = False"
| "lp_ifocused (LPIWait c i \<rho> k) = lp_ifocused k"

lemma lp_ianswer_subst[simp]:
  "lp_ianswer P (lp_iconfig_subst s \<sigma>) = lp_iatom_subst (lp_ianswer P s) \<sigma>"
  by (cases s) simp_all

lemma lp_igoals_subst[simp]:
  "lp_igoals P (lp_iconfig_subst s \<sigma>) = map (\<lambda>a. lp_iatom_subst a \<sigma>) (lp_igoals P s)"
  by (induct s) (simp_all add: o_def)

lemma lp_ivalid_subst: "lp_ivalid P s \<Longrightarrow> lp_ivalid P (lp_iconfig_subst s \<sigma>)"
  by (induct s) auto

lemma lp_ifocused_nonempty: "lp_ifocused s \<Longrightarrow> lp_igoals P s \<noteq> []"
  by (induct s) auto

lemma lp_ilocal_frame_steps:
  "(s,t) \<in> (lp_ilocal P)\<^sup>* \<Longrightarrow> (LPIWait c i \<rho> s,LPIWait c i \<rho> t) \<in> (lp_ilocal P)\<^sup>*"
  by (induct rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl lp_ilocal.frame)

lemma lp_inormalize_returns:
  assumes "lp_ivalid P s"
  obtains t where "(s,t) \<in> (lp_ilocal P)\<^sup>*" "lp_ivalid P t"
    "lp_igoals P t = lp_igoals P s" "lp_ianswer P t = lp_ianswer P s"
    "lp_ifocused t \<or> (\<exists>a. t = LPIDone a)"
  using assms
proof (induct s arbitrary: thesis)
  case (LPICall a)
  show ?case by (rule LPICall.prems(1)[of "LPICall a"]) simp_all
next
  case (LPIDone a)
  show ?case by (rule LPIDone.prems(1)[of "LPIDone a"]) auto
next
  case (LPIWait c i \<rho> k)
  have c: "c < length P" and i: "i < length (snd (P!c))" and vk: "lp_ivalid P k"
    and ak: "lp_ianswer P k = lp_atom_eval (snd (P!c)!i) \<rho>"
    using LPIWait.prems(2) by simp_all
  obtain t where steps: "(k,t) \<in> (lp_ilocal P)\<^sup>*" and vt: "lp_ivalid P t"
    and gt: "lp_igoals P t = lp_igoals P k" and at: "lp_ianswer P t = lp_ianswer P k"
    and form: "lp_ifocused t \<or> (\<exists>a. t = LPIDone a)"
    by (rule LPIWait.hyps[OF _ vk]) blast
  have lifted: "(LPIWait c i \<rho> k,LPIWait c i \<rho> t) \<in> (lp_ilocal P)\<^sup>*"
    by (rule lp_ilocal_frame_steps[OF steps])
  show ?case
  proof (cases "lp_ifocused t")
    case True
    show ?thesis by (rule LPIWait.prems(1)[of "LPIWait c i \<rho> t"])
      (use lifted c i vt gt at ak True in auto)
  next
    case False
    obtain a where t: "t = LPIDone a" using form False by blast
    have a: "a = lp_atom_eval (snd (P!c)!i) \<rho>" using at ak t by simp
    have empty: "lp_igoals P k = []" using gt t by simp
    show ?thesis
    proof (cases "Suc i < length (snd (P!c))")
      case True
      let ?q = "LPIWait c (Suc i) \<rho> (LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>))"
      have last: "(LPIWait c i \<rho> t,?q) \<in> lp_ilocal P"
        unfolding t a by (rule lp_ilocal.advance[OF c True])
      have path: "(LPIWait c i \<rho> k,?q) \<in> (lp_ilocal P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF lifted last])
      have drop: "drop (Suc i) (snd (P!c)) = snd (P!c)!Suc i # drop (Suc (Suc i)) (snd (P!c))"
        using True by (simp add: Cons_nth_drop_Suc)
      show ?thesis by (rule LPIWait.prems(1)[of ?q])
        (use path c True empty drop in auto)
    next
      case False
      have last_index: "Suc i = length (snd (P!c))" using i False by arith
      let ?q = "LPIDone (lp_atom_eval (fst (P!c)) \<rho>)"
      have last: "(LPIWait c i \<rho> t,?q) \<in> lp_ilocal P"
        unfolding t a by (rule lp_ilocal.leave[OF c i last_index])
      have path: "(LPIWait c i \<rho> k,?q) \<in> (lp_ilocal P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF lifted last])
      show ?thesis by (rule LPIWait.prems(1)[of ?q])
        (use path empty last_index in auto)
    qed
  qed
qed

inductive_set lp_ild :: "('f,'v) lp_clause list \<Rightarrow> ('f,'w) lp_iatom list rel"
  for P where
  resolve: "c < length P \<Longrightarrow> lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho> \<Longrightarrow>
    (a#gs, map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) gs) \<in> lp_ild P"

lemma lp_ifocused_resolve:
  assumes valid: "lp_ivalid P s" and focus: "lp_ifocused s"
    and goals: "lp_igoals P s = a#gs" and c: "c < length P"
    and match: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
  obtains t where "(lp_iconfig_subst s \<sigma>,t) \<in> lp_ilocal P" "lp_ivalid P t"
    "lp_ianswer P t = lp_iatom_subst (lp_ianswer P s) \<sigma>"
    "lp_igoals P t = map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_iatom_subst b \<sigma>) gs"
  using valid focus goals match
proof (induct s arbitrary: a gs thesis)
  case (LPICall b)
  have b: "b=a" and gs: "gs=[]" using LPICall.prems by auto
  show ?case
  proof (cases "snd (P!c) = []")
    case True
    let ?t = "LPIDone (lp_atom_eval (fst (P!c)) \<rho>)"
    show ?thesis by (rule LPICall.prems(1)[of ?t])
      (use lp_ilocal.fact[OF c True, of \<rho>] LPICall.prems(5) in \<open>simp_all add: b gs True\<close>)
  next
    case False
    let ?t = "LPIWait c 0 \<rho> (LPICall (lp_atom_eval (snd (P!c)!0) \<rho>))"
    have bs: "snd (P!c) = snd (P!c)!0 # drop 1 (snd (P!c))"
      using False by (cases "snd (P!c)") auto
    have mapped: "map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) =
      lp_atom_eval (snd (P!c)!0) \<rho> # map (\<lambda>b. lp_atom_eval b \<rho>) (drop 1 (snd (P!c)))"
      using arg_cong[OF bs, of "map (\<lambda>b. lp_atom_eval b \<rho>)"] by (simp only: list.map)
    show ?thesis by (rule LPICall.prems(1)[of ?t])
      (use lp_ilocal.enter[OF c False, of \<rho>] LPICall.prems(5) c False mapped in \<open>auto simp: b gs\<close>)
  qed
next
  case (LPIDone b)
  then show ?case by simp
next
  case (LPIWait d i \<eta> k)
  have vk: "lp_ivalid P k" and fk: "lp_ifocused k" using LPIWait.prems by simp_all
  obtain ks where kg: "lp_igoals P k = a#ks"
    using lp_ifocused_nonempty[OF fk, of P] LPIWait.prems(4) by (cases "lp_igoals P k") auto
  have gs: "gs = ks @ map (\<lambda>b. lp_atom_eval b \<eta>) (drop (Suc i) (snd (P!d)))"
    using LPIWait.prems(4) kg by simp
  obtain t where kt: "(lp_iconfig_subst k \<sigma>,t) \<in> lp_ilocal P" and vt: "lp_ivalid P t"
    and at: "lp_ianswer P t = lp_iatom_subst (lp_ianswer P k) \<sigma>"
    and gt: "lp_igoals P t = map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_iatom_subst b \<sigma>) ks"
    by (rule LPIWait.hyps[OF _ vk fk kg LPIWait.prems(5)]) blast
  let ?t = "LPIWait d i (\<lambda>x. lp_isubst (\<eta> x) \<sigma>) t"
  show ?case by (rule LPIWait.prems(1)[of ?t])
    (use lp_ilocal.frame[OF kt, of d i "\<lambda>x. lp_isubst (\<eta> x) \<sigma>"] vt at gt LPIWait.prems(2) in
      \<open>auto simp: gs o_def\<close>)
qed

lemma lp_ild_simulation:
  assumes valid: "lp_ivalid P s" and step: "(lp_igoals P s,gs) \<in> lp_ild P"
  obtains t where "(s,t) \<in> (lp_imachine P)\<^sup>+" "lp_ivalid P t" "lp_igoals P t = gs"
proof -
  obtain a rest c \<sigma> \<rho> where sg: "lp_igoals P s = a#rest" and c: "c < length P"
    and match: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
    and gs: "gs = map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_iatom_subst b \<sigma>) rest"
    using step by (cases rule: lp_ild.cases) auto
  obtain q where sq: "(s,q) \<in> (lp_ilocal P)\<^sup>*" and vq: "lp_ivalid P q"
    and gq: "lp_igoals P q = lp_igoals P s" and form: "lp_ifocused q \<or> (\<exists>a. q = LPIDone a)"
    by (rule lp_inormalize_returns[OF valid]) blast
  have fq: "lp_ifocused q" using form gq sg by auto
  obtain t where qt: "(lp_iconfig_subst q \<sigma>,t) \<in> lp_ilocal P" and vt: "lp_ivalid P t"
    and gt: "lp_igoals P t = gs"
    by (rule lp_ifocused_resolve[OF vq fq HOL.trans[OF gq sg] c match]) (auto simp: gs)
  have qm: "(q,t) \<in> lp_imachine P" unfolding lp_imachine_def using qt by blast
  have sm: "(s,q) \<in> (lp_imachine P)\<^sup>*"
    by (rule rtrancl_mono[OF lp_ilocal_machine, THEN subsetD, OF sq])
  have st: "(s,t) \<in> (lp_imachine P)\<^sup>+" using sm qm by (rule rtrancl_into_trancl1)
  show thesis by (rule that[OF st vt gt])
qed

theorem lp_imachine_implies_ld_termination:
  assumes sn: "SN_on (lp_imachine P) {s}" and valid: "lp_ivalid P s"
  shows "SN_on (lp_ild P) {lp_igoals P s}"
proof -
  have implication: "lp_ivalid P s \<longrightarrow> SN_on (lp_ild P) {lp_igoals P s}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix q assume ih: "\<And>t. (q,t) \<in> (lp_imachine P)\<^sup>+ \<Longrightarrow>
      lp_ivalid P t \<longrightarrow> SN_on (lp_ild P) {lp_igoals P t}"
    show "lp_ivalid P q \<longrightarrow> SN_on (lp_ild P) {lp_igoals P q}"
    proof
      assume vq: "lp_ivalid P q"
      show "SN_on (lp_ild P) {lp_igoals P q}"
      proof (rule step_reflects_SN_on)
        fix gs assume step: "(lp_igoals P q,gs) \<in> lp_ild P"
        obtain t where qt: "(q,t) \<in> (lp_imachine P)\<^sup>+" and vt: "lp_ivalid P t"
          and gt: "lp_igoals P t = gs"
          by (rule lp_ild_simulation[OF vq step]) blast
        show "SN_on (lp_ild P) {gs}" using ih[OF qt] vt by (simp add: gt)
      qed
    qed
  qed
  show ?thesis using implication valid by blast
qed

end
