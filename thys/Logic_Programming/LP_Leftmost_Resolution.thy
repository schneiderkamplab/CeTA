theory LP_Leftmost_Resolution
  imports LP_Continuation_Machine
begin

lemma lp_atom_subst_comp[simp]:
  "lp_atom_subst (lp_atom_subst a \<rho>) \<sigma> = lp_atom_subst a (\<lambda>x. \<rho> x \<cdot> \<sigma>)"
proof -
  have comp: "\<And>t. t \<cdot> \<rho> \<cdot> \<sigma> = t \<cdot> (\<lambda>x. \<rho> x \<cdot> \<sigma>)"
    using subst_subst_compose[of _ \<rho> \<sigma>, symmetric] by (simp only: subst_compose_def)
  show ?thesis by (simp only: lp_atom_subst_def fst_conv snd_conv map_map o_def comp)
qed

lemma lp_atom_subst_id[simp]: "lp_atom_subst a Var = a"
  by (cases a) (simp add: lp_atom_subst_def)

lemma lp_config_subst_id[simp]: "lp_config_subst s Var = s"
  by (induct s) simp_all

lemma lp_local_machine: "lp_local P \<subseteq> lp_machine P"
  unfolding lp_machine_def by (auto intro!: exI[where x=Var])

fun lp_answer where
  "lp_answer P (LPCall a) = a"
| "lp_answer P (LPDone a) = a"
| "lp_answer P (LPWait c i \<rho> k) = lp_atom_subst (fst (P!c)) \<rho>"

fun lp_goals where
  "lp_goals P (LPCall a) = [a]"
| "lp_goals P (LPDone a) = []"
| "lp_goals P (LPWait c i \<rho> k) = lp_goals P k @
    map (\<lambda>a. lp_atom_subst a \<rho>) (drop (Suc i) (snd (P!c)))"

fun lp_valid where
  "lp_valid P (LPCall a) = True"
| "lp_valid P (LPDone a) = True"
| "lp_valid P (LPWait c i \<rho> k) = (c < length P \<and> i < length (snd (P!c)) \<and>
    lp_valid P k \<and> lp_answer P k = lp_atom_subst (snd (P!c)!i) \<rho>)"

fun lp_focused where
  "lp_focused (LPCall a) = True"
| "lp_focused (LPDone a) = False"
| "lp_focused (LPWait c i \<rho> k) = lp_focused k"

lemma lp_answer_subst[simp]:
  "lp_answer P (lp_config_subst s \<sigma>) = lp_atom_subst (lp_answer P s) \<sigma>"
  by (cases s) simp_all

lemma lp_goals_subst[simp]:
  "lp_goals P (lp_config_subst s \<sigma>) = map (\<lambda>a. lp_atom_subst a \<sigma>) (lp_goals P s)"
  by (induct s) (simp_all add: o_def)

lemma lp_valid_subst: "lp_valid P s \<Longrightarrow> lp_valid P (lp_config_subst s \<sigma>)"
  by (induct s) auto

lemma lp_focused_nonempty: "lp_focused s \<Longrightarrow> lp_goals P s \<noteq> []"
  by (induct s) auto

lemma lp_local_frame_steps:
  "(s,t) \<in> (lp_local P)\<^sup>* \<Longrightarrow> (LPWait c i \<rho> s,LPWait c i \<rho> t) \<in> (lp_local P)\<^sup>*"
  by (induct rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl lp_local.frame)

lemma lp_normalize_returns:
  assumes "lp_valid P s"
  obtains t where "(s,t) \<in> (lp_local P)\<^sup>*" "lp_valid P t"
    "lp_goals P t = lp_goals P s" "lp_answer P t = lp_answer P s"
    "lp_focused t \<or> (\<exists>a. t = LPDone a)"
  using assms
proof (induct s arbitrary: thesis)
  case (LPCall a)
  show ?case by (rule LPCall.prems(1)[of "LPCall a"]) simp_all
next
  case (LPDone a)
  show ?case by (rule LPDone.prems(1)[of "LPDone a"]) auto
next
  case (LPWait c i \<rho> k)
  have c: "c < length P" and i: "i < length (snd (P!c))" and vk: "lp_valid P k"
    and ak: "lp_answer P k = lp_atom_subst (snd (P!c)!i) \<rho>"
    using LPWait.prems(2) by simp_all
  obtain t where steps: "(k,t) \<in> (lp_local P)\<^sup>*" and vt: "lp_valid P t"
    and gt: "lp_goals P t = lp_goals P k" and at: "lp_answer P t = lp_answer P k"
    and form: "lp_focused t \<or> (\<exists>a. t = LPDone a)"
    by (rule LPWait.hyps[OF _ vk]) blast
  have lifted: "(LPWait c i \<rho> k,LPWait c i \<rho> t) \<in> (lp_local P)\<^sup>*"
    by (rule lp_local_frame_steps[OF steps])
  show ?case
  proof (cases "lp_focused t")
    case True
    show ?thesis by (rule LPWait.prems(1)[of "LPWait c i \<rho> t"])
      (use lifted c i vt gt at ak True in auto)
  next
    case False
    obtain a where t: "t = LPDone a" using form False by blast
    have a: "a = lp_atom_subst (snd (P!c)!i) \<rho>" using at ak t by simp
    have empty: "lp_goals P k = []" using gt t by simp
    show ?thesis
    proof (cases "Suc i < length (snd (P!c))")
      case True
      let ?q = "LPWait c (Suc i) \<rho> (LPCall (lp_atom_subst (snd (P!c)!Suc i) \<rho>))"
      have last: "(LPWait c i \<rho> t,?q) \<in> lp_local P"
        unfolding t a by (rule lp_local.advance[OF c True])
      have path: "(LPWait c i \<rho> k,?q) \<in> (lp_local P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF lifted last])
      have drop: "drop (Suc i) (snd (P!c)) = snd (P!c)!Suc i # drop (Suc (Suc i)) (snd (P!c))"
        using True by (simp add: Cons_nth_drop_Suc)
      show ?thesis by (rule LPWait.prems(1)[of ?q])
        (use path c True empty drop in auto)
    next
      case False
      have last_index: "Suc i = length (snd (P!c))" using i False by arith
      let ?q = "LPDone (lp_atom_subst (fst (P!c)) \<rho>)"
      have last: "(LPWait c i \<rho> t,?q) \<in> lp_local P"
        unfolding t a by (rule lp_local.leave[OF c i last_index])
      have path: "(LPWait c i \<rho> k,?q) \<in> (lp_local P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF lifted last])
      show ?thesis by (rule LPWait.prems(1)[of ?q])
        (use path empty last_index in auto)
    qed
  qed
qed

inductive_set lp_ld :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v) lp_atom list rel"
  for P where
  resolve: "c < length P \<Longrightarrow> lp_atom_subst a \<sigma> = lp_atom_subst (fst (P!c)) \<rho> \<Longrightarrow>
    (a#gs, map (\<lambda>b. lp_atom_subst b \<rho>) (snd (P!c)) @
      map (\<lambda>b. lp_atom_subst b \<sigma>) gs) \<in> lp_ld P"

lemma lp_focused_resolve:
  assumes valid: "lp_valid P s" and focus: "lp_focused s"
    and goals: "lp_goals P s = a#gs" and c: "c < length P"
    and match: "lp_atom_subst a \<sigma> = lp_atom_subst (fst (P!c)) \<rho>"
  obtains t where "(lp_config_subst s \<sigma>,t) \<in> lp_local P" "lp_valid P t"
    "lp_answer P t = lp_atom_subst (lp_answer P s) \<sigma>"
    "lp_goals P t = map (\<lambda>b. lp_atom_subst b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b \<sigma>) gs"
  using valid focus goals match
proof (induct s arbitrary: a gs thesis)
  case (LPCall b)
  have b: "b=a" and gs: "gs=[]" using LPCall.prems by auto
  show ?case
  proof (cases "snd (P!c) = []")
    case True
    let ?t = "LPDone (lp_atom_subst (fst (P!c)) \<rho>)"
    show ?thesis by (rule LPCall.prems(1)[of ?t])
      (use lp_local.fact[OF c True, of \<rho>] LPCall.prems(5) in \<open>simp_all add: b gs True\<close>)
  next
    case False
    let ?t = "LPWait c 0 \<rho> (LPCall (lp_atom_subst (snd (P!c)!0) \<rho>))"
    have bs: "snd (P!c) = snd (P!c)!0 # drop 1 (snd (P!c))"
      using False by (cases "snd (P!c)") auto
    have mapped: "map (\<lambda>b. lp_atom_subst b \<rho>) (snd (P!c)) =
      lp_atom_subst (snd (P!c)!0) \<rho> # map (\<lambda>b. lp_atom_subst b \<rho>) (drop 1 (snd (P!c)))"
      using arg_cong[OF bs, of "map (\<lambda>b. lp_atom_subst b \<rho>)"] by (simp only: list.map)
    show ?thesis by (rule LPCall.prems(1)[of ?t])
      (use lp_local.enter[OF c False, of \<rho>] LPCall.prems(5) c False mapped in \<open>auto simp: b gs\<close>)
  qed
next
  case (LPDone b)
  then show ?case by simp
next
  case (LPWait d i \<eta> k)
  have vk: "lp_valid P k" and fk: "lp_focused k" using LPWait.prems by simp_all
  obtain ks where kg: "lp_goals P k = a#ks"
    using lp_focused_nonempty[OF fk, of P] LPWait.prems(4) by (cases "lp_goals P k") auto
  have gs: "gs = ks @ map (\<lambda>b. lp_atom_subst b \<eta>) (drop (Suc i) (snd (P!d)))"
    using LPWait.prems(4) kg by simp
  obtain t where kt: "(lp_config_subst k \<sigma>,t) \<in> lp_local P" and vt: "lp_valid P t"
    and at: "lp_answer P t = lp_atom_subst (lp_answer P k) \<sigma>"
    and gt: "lp_goals P t = map (\<lambda>b. lp_atom_subst b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b \<sigma>) ks"
    by (rule LPWait.hyps[OF _ vk fk kg LPWait.prems(5)]) blast
  let ?t = "LPWait d i (\<lambda>x. \<eta> x \<cdot> \<sigma>) t"
  show ?case by (rule LPWait.prems(1)[of ?t])
    (use lp_local.frame[OF kt, of d i "\<lambda>x. \<eta> x \<cdot> \<sigma>"] vt at gt LPWait.prems(2) in
      \<open>auto simp: gs o_def\<close>)
qed

lemma lp_ld_simulation:
  assumes valid: "lp_valid P s" and step: "(lp_goals P s,gs) \<in> lp_ld P"
  obtains t where "(s,t) \<in> (lp_machine P)\<^sup>+" "lp_valid P t" "lp_goals P t = gs"
proof -
  obtain a rest c \<sigma> \<rho> where sg: "lp_goals P s = a#rest" and c: "c < length P"
    and match: "lp_atom_subst a \<sigma> = lp_atom_subst (fst (P!c)) \<rho>"
    and gs: "gs = map (\<lambda>b. lp_atom_subst b \<rho>) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b \<sigma>) rest"
    using step by (cases rule: lp_ld.cases) auto
  obtain q where sq: "(s,q) \<in> (lp_local P)\<^sup>*" and vq: "lp_valid P q"
    and gq: "lp_goals P q = lp_goals P s" and form: "lp_focused q \<or> (\<exists>a. q = LPDone a)"
    by (rule lp_normalize_returns[OF valid]) blast
  have fq: "lp_focused q" using form gq sg by auto
  obtain t where qt: "(lp_config_subst q \<sigma>,t) \<in> lp_local P" and vt: "lp_valid P t"
    and gt: "lp_goals P t = gs"
    by (rule lp_focused_resolve[OF vq fq HOL.trans[OF gq sg] c match]) (auto simp: gs)
  have qm: "(q,t) \<in> lp_machine P" unfolding lp_machine_def using qt by blast
  have sm: "(s,q) \<in> (lp_machine P)\<^sup>*"
    by (rule rtrancl_mono[OF lp_local_machine, THEN subsetD, OF sq])
  have st: "(s,t) \<in> (lp_machine P)\<^sup>+" using sm qm by (rule rtrancl_into_trancl1)
  show thesis by (rule that[OF st vt gt])
qed

theorem lp_machine_implies_ld_termination:
  assumes sn: "SN_on (lp_machine P) {s}" and valid: "lp_valid P s"
  shows "SN_on (lp_ld P) {lp_goals P s}"
proof -
  have implication: "lp_valid P s \<longrightarrow> SN_on (lp_ld P) {lp_goals P s}"
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI])
    fix q assume ih: "\<And>t. (q,t) \<in> (lp_machine P)\<^sup>+ \<Longrightarrow>
      lp_valid P t \<longrightarrow> SN_on (lp_ld P) {lp_goals P t}"
    show "lp_valid P q \<longrightarrow> SN_on (lp_ld P) {lp_goals P q}"
    proof
      assume vq: "lp_valid P q"
      show "SN_on (lp_ld P) {lp_goals P q}"
      proof (rule step_reflects_SN_on)
        fix gs assume step: "(lp_goals P q,gs) \<in> lp_ld P"
        obtain t where qt: "(q,t) \<in> (lp_machine P)\<^sup>+" and vt: "lp_valid P t"
          and gt: "lp_goals P t = gs"
          by (rule lp_ld_simulation[OF vq step]) blast
        show "SN_on (lp_ld P) {gs}" using ih[OF qt] vt by (simp add: gt)
      qed
    qed
  qed
  show ?thesis using implication valid by blast
qed

end
