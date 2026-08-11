(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_GM_Transformation
  imports
    CSR_Checker_Extensions.CSR_Conservative_Checker
    CSR_Checker_Extensions.CSR_Innermost_DP_Checker
    CSR_Checker_Extensions.CSR_Innermost_Unhiding_Checker
    CSR_Checker_Extensions.CSR_Innermost_Unhiding_RTA08
begin

text \<open>
  Semantic support for the sound, incomplete Giesl--Middeldorp
  transformation from context-sensitive rewriting to ordinary rewriting.
  This theory is kept in a separate session while the simulation theorem is
  developed; stable checker sessions therefore remain cached.
\<close>

lemma csstep_cond_subst:
  assumes cond: "csstep_cond \<mu> p s"
    and poss: "p \<in> poss s"
  shows "csstep_cond \<mu> p (s \<cdot> \<tau>)"
  unfolding csstep_cond_def
proof (intro allI impI)
  fix p1 i p2
  assume split: "p = p1 @ i # p2 \<and> p \<in> poss (s \<cdot> \<tau>)"
  from poss split have p1: "p1 \<in> poss s"
    by (metis append_Cons poss_append_poss)
  from cond[unfolded csstep_cond_def, rule_format, of p1 i p2]
    poss split obtain f ts where root: "s |_ p1 = Fun f ts"
      and active: "i \<in> \<mu> (f, length ts)"
    by auto
  have "(s \<cdot> \<tau>) |_ p1 = (s |_ p1) \<cdot> \<tau>"
    by (rule subt_at_subst[OF p1])
  also from root have "... = Fun f (map (\<lambda>t. t \<cdot> \<tau>) ts)"
    by simp
  finally show "\<exists>f ts. (s \<cdot> \<tau>) |_ p1 = Fun f ts \<and>
      i \<in> \<mu> (f, length ts)"
    using active by auto
qed

lemma csstep_subst_closed:
  assumes step: "(s,t) \<in> csstep \<mu> R"
  shows "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> csstep \<mu> R"
proof -
  from step obtain p lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_def csstep_p_def by auto
  from raw have poss: "p \<in> poss s"
    unfolding rstep_r_p_s_def' by auto
  have raw_subst: "(s \<cdot> \<tau>, t \<cdot> \<tau>) \<in>
      rstep_r_p_s R lr p (\<sigma> \<circ>\<^sub>s \<tau>)"
    using raw unfolding rstep_r_p_s_def'
    by (auto simp: ctxt_of_pos_term_subst)
  have cond_subst: "csstep_cond \<mu> p (s \<cdot> \<tau>)"
    by (rule csstep_cond_subst[OF cond poss])
  show ?thesis
    unfolding csstep_def csstep_p_def
    using raw_subst cond_subst by blast
qed

fun gm_nf and gm_nf_args where
  "gm_nf \<mu> D act mark (Var x) = Fun mark [Var x]"
| "gm_nf \<mu> D act mark (Fun f ts) =
    Fun (if (f, length ts) \<in> D then act (f, length ts) else f)
      (gm_nf_args \<mu> D act mark f (length ts) 0 ts)"
| "gm_nf_args \<mu> D act mark f n i [] = []"
| "gm_nf_args \<mu> D act mark f n i (t # ts) =
    (if i \<in> \<mu> (f, n)
      then gm_nf \<mu> D act mark t else t)
      # gm_nf_args \<mu> D act mark f n (Suc i) ts"

fun gm_lhs where
  "gm_lhs D act (Var x) = Var x"
| "gm_lhs D act (Fun f ts) =
    Fun (if (f, length ts) \<in> D then act (f, length ts) else f) ts"

definition gm_rule where
  "gm_rule \<mu> D act mark lr =
    (gm_lhs D act (fst lr), gm_nf \<mu> D act mark (snd lr))"

definition gm_original_rules where
  "gm_original_rules \<mu> D act mark R =
    {gm_rule \<mu> D act mark lr |lr. lr \<in> R}"

definition gm_vars where
  "gm_vars n = map Var (x\<^sub>1_to_x\<^sub>n n)"

definition gm_mark_rule where
  "gm_mark_rule \<mu> D act mark fn =
    (let f = fst fn; n = snd fn; xs = gm_vars n
     in (Fun mark [Fun f xs], gm_nf \<mu> D act mark (Fun f xs)))"

definition gm_deactivate_rule where
  "gm_deactivate_rule act fn =
    (let f = fst fn; n = snd fn; xs = gm_vars n
     in (Fun (act fn) xs, Fun f xs))"

definition gm_transformed_rules_list where
  "gm_transformed_rules_list \<mu> D act mark F R Ds =
    map (gm_rule \<mu> D act mark) R @
    map (gm_mark_rule \<mu> D act mark) F @
    map (gm_deactivate_rule act) Ds"

fun gm_mark_args where
  "gm_mark_args \<mu> mark f n i [] = []"
| "gm_mark_args \<mu> mark f n i (t # ts) =
    (if i \<in> \<mu> (f,n) then Fun mark [t] else t) #
      gm_mark_args \<mu> mark f n (Suc i) ts"

lemma length_gm_mark_args[simp]:
  "length (gm_mark_args \<mu> mark f n i ts) = length ts"
  by (induct ts arbitrary: i) auto

lemma nth_gm_mark_args:
  assumes "j < length ts"
  shows "gm_mark_args \<mu> mark f n i ts ! j =
    (if i + j \<in> \<mu> (f,n) then Fun mark [ts ! j] else ts ! j)"
  using assms
proof (induct ts arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    with Cons.prems have k: "k < length ts" by simp
    from Cons.hyps[OF k, of "Suc i"] Suc show ?thesis by simp
  qed
qed

lemma length_gm_nf_args_early:
  "length (gm_nf_args \<mu> D act mark f n i ts) = length ts"
  by (induct ts arbitrary: i) auto

lemma nth_gm_nf_args_early:
  assumes "j < length ts"
  shows "gm_nf_args \<mu> D act mark f n i ts ! j =
    (if i + j \<in> \<mu> (f,n)
      then gm_nf \<mu> D act mark (ts ! j) else ts ! j)"
  using assms
proof (induct ts arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    with Cons.prems have k: "k < length ts" by simp
    from Cons.hyps[OF k, of "Suc i"] Suc show ?thesis by simp
  qed
qed

lemma rule_instance_rstep:
  assumes "(l,r) \<in> R"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep R"
proof -
  have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rrstep R"
    using assms unfolding rrstep_def' by blast
  then show ?thesis unfolding rstep_iff_rrstep_or_nrrstep by auto
qed

lemma gm_vars_length[simp]: "length (gm_vars n) = n"
  unfolding gm_vars_def by simp

lemma gm_mark_rule_instance:
  fixes R1 :: "('f,string) trs"
  assumes rule: "gm_mark_rule \<mu> D act mark (f,n) \<in> R1"
    and len: "length ts = n"
  shows "(Fun mark [Fun f ts],
      Fun (if (f,n) \<in> D then act (f,n) else f)
        (gm_mark_args \<mu> mark f n 0 ts)) \<in> rstep R1"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  have args_inst:
    "map (\<lambda>t. t \<cdot> ?\<sigma>)
        (gm_nf_args \<mu> D act mark f n 0 ?xs) =
      gm_mark_args \<mu> mark f n 0 ts"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>t. t \<cdot> ?\<sigma>)
        (gm_nf_args \<mu> D act mark f n 0 ?xs)) =
      length (gm_mark_args \<mu> mark f n 0 ts)"
      using fresh len by (simp add: length_gm_nf_args_early)
    fix i
    assume i: "i < length (map (\<lambda>t. t \<cdot> ?\<sigma>)
      (gm_nf_args \<mu> D act mark f n 0 ?xs))"
    have in_: "i < n" using i fresh by (simp add: length_gm_nf_args_early)
    have xi: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
      using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] in_ len by simp
    have map_nth: "map (\<lambda>t. t \<cdot> ?\<sigma>)
        (gm_nf_args \<mu> D act mark f n 0 ?xs) ! i =
      gm_nf_args \<mu> D act mark f n 0 ?xs ! i \<cdot> ?\<sigma>"
      using i by (simp add: length_gm_nf_args_early)
    show "map (\<lambda>t. t \<cdot> ?\<sigma>)
          (gm_nf_args \<mu> D act mark f n 0 ?xs) ! i =
        gm_mark_args \<mu> mark f n 0 ts ! i"
      using nth_gm_nf_args_early[of i ?xs \<mu> D act mark f n 0]
        nth_gm_mark_args[of i ts \<mu> mark f n 0] in_ fresh len xi map_nth
      by (cases "i \<in> \<mu> (f,n)", simp_all)
  qed
  have rule': "(Fun mark [Fun f ?xs],
      gm_nf \<mu> D act mark (Fun f ?xs)) \<in> R1"
    using rule unfolding gm_mark_rule_def gm_vars_def Let_def by simp
  from rule_instance_rstep[OF rule', of ?\<sigma>]
  have raw: "(Fun mark [Fun f ?xs] \<cdot> ?\<sigma>,
      gm_nf \<mu> D act mark (Fun f ?xs) \<cdot> ?\<sigma>) \<in> rstep R1" .
  show ?thesis
    using raw inst args_inst fresh len
    by (cases "(f,n) \<in> D", simp_all)
qed

lemma gm_deactivate_rule_instance:
  fixes R1 :: "('f,string) trs"
  assumes rule: "gm_deactivate_rule act (f,n) \<in> R1"
    and len: "length ts = n"
  shows "(Fun (act (f,n)) ts, Fun f ts) \<in> rstep R1"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  have rule': "(Fun (act (f,n)) ?xs, Fun f ?xs) \<in> R1"
    using rule unfolding gm_deactivate_rule_def gm_vars_def Let_def by simp
  from rule_instance_rstep[OF rule', of ?\<sigma>] inst
  show ?thesis by simp
qed

lemma gm_original_rule_instance:
  fixes R1 :: "('f,string) trs"
  assumes rule: "gm_rule \<mu> D act mark lr \<in> R1"
  shows "(gm_lhs D act (fst lr) \<cdot> \<sigma>,
      gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep R1"
proof -
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  have rule': "(gm_lhs D act l, gm_nf \<mu> D act mark r) \<in> R1"
    using rule unfolding gm_rule_def lr by simp
  from rule_instance_rstep[OF rule', of \<sigma>]
  show ?thesis unfolding lr by simp
qed

lemma gm_generated_mark_steps:
  fixes R1 :: "('f,string) trs"
  assumes cover: "\<And>f n. (f,n) \<in> F \<Longrightarrow>
      gm_mark_rule \<mu> D act mark (f,n) \<in> R1"
    and sig: "funas_term u \<subseteq> F"
    and ground: "ground u"
  shows "(Fun mark [u], gm_nf \<mu> D act mark u) \<in> (rstep R1)\<^sup>*"
  using sig ground
proof (induct u)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have fn: "(f,length ts) \<in> F" using Fun.prems(1) by auto
  from gm_mark_rule_instance[OF cover[OF fn] refl]
  have root_step: "(Fun mark [Fun f ts],
      Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_mark_args \<mu> mark f (length ts) 0 ts)) \<in> rstep R1" .
  have arg_steps: "\<forall>i<length ts.
      (gm_mark_args \<mu> mark f (length ts) 0 ts ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i)
      \<in> (rstep R1)\<^sup>*"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    from Fun.prems i have gi: "ground (ts ! i)" by auto
    have mem: "ts ! i \<in> set ts" using i by simp
    have sub: "funas_term (ts ! i) \<subseteq> \<Union>(funas_term ` set ts)"
      using mem by blast
    from subset_trans[OF sub] Fun.prems(1)
    have si: "funas_term (ts ! i) \<subseteq> F" by auto
    from Fun.hyps[OF nth_mem[OF i] si gi]
    have IH: "(Fun mark [ts ! i], gm_nf \<mu> D act mark (ts ! i))
      \<in> (rstep R1)\<^sup>*" .
    show "(gm_mark_args \<mu> mark f (length ts) 0 ts ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i)
      \<in> (rstep R1)\<^sup>*"
      using nth_gm_mark_args[OF i, of \<mu> mark f "length ts" 0]
        nth_gm_nf_args_early[OF i, of \<mu> D act mark f "length ts" 0] IH
      by (cases "i \<in> \<mu> (f,length ts)", auto)
  qed
  have len_args: "length (gm_mark_args \<mu> mark f (length ts) 0 ts) =
      length (gm_nf_args \<mu> D act mark f (length ts) 0 ts)"
    by (simp add: length_gm_nf_args_early)
  have rest_args:
    "(Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_mark_args \<mu> mark f (length ts) 0 ts),
      Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_nf_args \<mu> D act mark f (length ts) 0 ts)) \<in> (rstep R1)\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length (gm_mark_args \<mu> mark f (length ts) 0 ts) =
      length (gm_nf_args \<mu> D act mark f (length ts) 0 ts)"
      by (rule len_args)
    show "\<forall>i<length (gm_mark_args \<mu> mark f (length ts) 0 ts).
      (gm_mark_args \<mu> mark f (length ts) 0 ts ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i)
      \<in> (rstep R1)\<^sup>*"
      using arg_steps by simp
  qed
  have rest:
    "(Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_mark_args \<mu> mark f (length ts) 0 ts),
      gm_nf \<mu> D act mark (Fun f ts)) \<in> (rstep R1)\<^sup>*"
    using rest_args by simp
  from rtrancl_trans[OF r_into_rtrancl[OF root_step] rest]
  show ?case .
qed

lemma length_gm_nf_args[simp]:
  "length (gm_nf_args \<mu> D act mark f n i ts) = length ts"
  by (induct ts arbitrary: i) auto

lemma nth_gm_nf_args:
  assumes "j < length ts"
  shows "gm_nf_args \<mu> D act mark f n i ts ! j =
    (if i + j \<in> \<mu> (f,n)
      then gm_nf \<mu> D act mark (ts ! j) else ts ! j)"
  using assms
proof (induct ts arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    with Cons.prems have k: "k < length ts" by simp
    from Cons.hyps[OF k, of "Suc i"] Suc show ?thesis
      by simp
  qed
qed

lemma gm_nf_args_list_update:
  assumes "j < length ts"
  shows "gm_nf_args \<mu> D act mark f n i (ts[j := u]) =
    (gm_nf_args \<mu> D act mark f n i ts)
      [j := (if i + j \<in> \<mu> (f,n) then gm_nf \<mu> D act mark u else u)]"
  using assms
proof (induct ts arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    with Cons.prems have k: "k < length ts" by simp
    from Cons.hyps[OF k, of "Suc i"] Suc show ?thesis
      by simp
  qed
qed

lemma ground_gm_nf:
  assumes "ground t"
  shows "ground (gm_nf \<mu> D act mark t)"
  using assms
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have args: "list_all ground (gm_nf_args \<mu> D act mark f n i ts)" for n i
    using Fun.hyps Fun.prems
    by (induct ts arbitrary: i) auto
  from args[of "length ts" 0, unfolded list_all_iff] show ?case by simp
qed

lemma gm_nf_active_subterm:
  assumes cond: "csstep_cond \<mu> p t"
    and poss: "p \<in> poss t"
  shows "p \<in> poss (gm_nf \<mu> D act mark t) \<and>
    gm_nf \<mu> D act mark t |_ p = gm_nf \<mu> D act mark (t |_ p)"
  using cond poss
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  from Cons.prems obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t) auto
  from Cons.prems(1)[unfolded csstep_cond_def] Cons.prems(2) t
  have active: "i \<in> \<mu> (f, length ts)"
    by (drule_tac x = "[]" in spec, drule_tac x = i in spec,
        drule_tac x = p in spec, auto)
  have cond': "csstep_cond \<mu> p (ts ! i)"
    unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 j p2
    assume split: "p = p1 @ j # p2 \<and> p \<in> poss (ts ! i)"
    from split have full: "i # p = (i # p1) @ j # p2"
      by simp
    from Cons.prems(1)[unfolded csstep_cond_def, rule_format,
        of "i # p1" j p2] Cons.prems(2) t split full i
    show "\<exists>g us. (ts ! i) |_ p1 = Fun g us \<and>
      j \<in> \<mu> (g, length us)"
      by auto
  qed
  from Cons.hyps[OF cond' p]
  have sub: "p \<in> poss (gm_nf \<mu> D act mark (ts ! i))"
    "gm_nf \<mu> D act mark (ts ! i) |_ p =
      gm_nf \<mu> D act mark (ts ! i |_ p)"
    by auto
  have nth: "gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i =
      gm_nf \<mu> D act mark (ts ! i)"
    using nth_gm_nf_args[OF i, of \<mu> D act mark f "length ts" 0] active
    by simp
  from t i sub nth show ?case by simp
qed

lemma csstep_cond_ConsD:
  assumes cond: "csstep_cond \<mu> (i # p) (Fun f ts)"
    and i: "i < length ts"
    and p: "p \<in> poss (ts ! i)"
  shows "i \<in> \<mu> (f, length ts)"
    and "csstep_cond \<mu> p (ts ! i)"
proof -
  from cond[unfolded csstep_cond_def, rule_format, of "[]" i p] i p
  show "i \<in> \<mu> (f, length ts)"
    by auto
  show "csstep_cond \<mu> p (ts ! i)"
    unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 j p2
    assume split: "p = p1 @ j # p2 \<and> p \<in> poss (ts ! i)"
    from split have full: "i # p = (i # p1) @ j # p2"
      by simp
    from cond[unfolded csstep_cond_def, rule_format,
        of "i # p1" j p2] split full i
    show "\<exists>g us. (ts ! i) |_ p1 = Fun g us \<and>
      j \<in> \<mu> (g, length us)"
      by auto
  qed
qed

lemma gm_nf_active_replace_at:
  assumes cond: "csstep_cond \<mu> p t"
    and poss: "p \<in> poss t"
  shows "gm_nf \<mu> D act mark (replace_at t p u) =
    replace_at (gm_nf \<mu> D act mark t) p (gm_nf \<mu> D act mark u)"
  using cond poss
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  from Cons.prems obtain f ts where t: "t = Fun f ts"
    and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
    by (cases t) auto
  from csstep_cond_ConsD[OF Cons.prems(1)[unfolded t] i p]
  have active: "i \<in> \<mu> (f, length ts)"
    and cond': "csstep_cond \<mu> p (ts ! i)"
    by auto
  from Cons.hyps[OF cond' p]
  have IH: "gm_nf \<mu> D act mark (replace_at (ts ! i) p u) =
    replace_at (gm_nf \<mu> D act mark (ts ! i)) p
      (gm_nf \<mu> D act mark u)" .
  have update: "gm_nf_args \<mu> D act mark f (length ts) 0
      (ts[i := replace_at (ts ! i) p u]) =
    (gm_nf_args \<mu> D act mark f (length ts) 0 ts)
      [i := gm_nf \<mu> D act mark (replace_at (ts ! i) p u)]"
    using gm_nf_args_list_update[OF i, of \<mu> D act mark f "length ts" 0
        "replace_at (ts ! i) p u"] active
    by simp
  have nth: "gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i =
      gm_nf \<mu> D act mark (ts ! i)"
    using nth_gm_nf_args[OF i, of \<mu> D act mark f "length ts" 0] active
    by simp
  from t i p update nth IH show ?case
    by (simp add: upd_conv_take_nth_drop)
qed

lemma rsteps_plus_ctxt:
  fixes s t :: "('f,'v) term"
    and C :: "('f,'v) ctxt"
    and R :: "('f,'v) trs"
  assumes "(s,t) \<in> (rstep R)\<^sup>+"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> (rstep R)\<^sup>+"
  using assms
proof (induct rule: trancl_induct)
  case (base y)
  from rstep_ctxt[OF base, of C] show ?case by auto
next
  case (step y z)
  from rstep_ctxt[OF step.hyps(2), of C]
  show ?case
    using step.hyps(1) step.hyps(3) by auto
qed

lemma root_gm_nf[simp]:
  "root (gm_nf \<mu> D act mark t) =
    (case t of Var x \<Rightarrow> Some (mark, 1)
     | Fun f ts \<Rightarrow>
         Some (if (f, length ts) \<in> D
           then (act (f, length ts), length ts) else (f, length ts)))"
  by (cases t) auto

lemma gm_nf_decode:
  fixes R1 :: "('f,'v) trs"
  assumes deactivate: "\<And>f ts. (f,length ts) \<in> D \<Longrightarrow>
      (Fun (act (f,length ts)) ts, Fun f ts) \<in> rstep R1"
    and ground: "ground t"
  shows "(gm_nf \<mu> D act mark t, t) \<in> (rstep R1)\<^sup>*"
  using ground
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have arg_steps: "\<forall>i<length ts.
      (gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i, ts ! i)
        \<in> (rstep R1)\<^sup>*"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    from Fun.prems i have gi: "ground (ts ! i)" by auto
    from Fun.hyps[OF nth_mem[OF i] gi]
    show "(gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i, ts ! i)
      \<in> (rstep R1)\<^sup>*"
      using nth_gm_nf_args[OF i, of \<mu> D act mark f "length ts" 0]
      by (cases "i \<in> \<mu> (f,length ts)", auto)
  qed
  have len_args: "length (gm_nf_args \<mu> D act mark f (length ts) 0 ts) =
      length ts" by simp
  have args:
    "(Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_nf_args \<mu> D act mark f (length ts) 0 ts),
      Fun (if (f,length ts) \<in> D then act (f,length ts) else f) ts)
      \<in> (rstep R1)\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length (gm_nf_args \<mu> D act mark f (length ts) 0 ts) = length ts"
      by (rule len_args)
    show "\<forall>i<length (gm_nf_args \<mu> D act mark f (length ts) 0 ts).
      (gm_nf_args \<mu> D act mark f (length ts) 0 ts ! i, ts ! i)
        \<in> (rstep R1)\<^sup>*"
      using arg_steps by simp
  qed
  show ?case
  proof (cases "(f,length ts) \<in> D")
    case True
    have args': "(gm_nf \<mu> D act mark (Fun f ts),
        Fun (act (f,length ts)) ts) \<in> (rstep R1)\<^sup>*"
      using args True by simp
    from rtrancl_into_rtrancl[OF args' deactivate[OF True]]
    show ?thesis .
  next
    case False
    with args show ?thesis by simp
  qed
qed

lemma gm_lhs_prepare:
  fixes R1 :: "('f,'v) trs"
  assumes deactivate: "\<And>f ts. (f,length ts) \<in> D \<Longrightarrow>
      (Fun (act (f,length ts)) ts, Fun f ts) \<in> rstep R1"
    and lhs_fun: "is_Fun l"
    and ground: "ground (l \<cdot> \<sigma>)"
  shows "(gm_nf \<mu> D act mark (l \<cdot> \<sigma>), gm_lhs D act l \<cdot> \<sigma>)
    \<in> (rstep R1)\<^sup>*"
proof -
  from lhs_fun obtain f ts where l: "l = Fun f ts"
    by (cases l, auto)
  have arg_steps: "\<forall>i<length ts.
      (gm_nf_args \<mu> D act mark f (length ts) 0
          (map (\<lambda>t. t \<cdot> \<sigma>) ts) ! i,
        map (\<lambda>t. t \<cdot> \<sigma>) ts ! i) \<in> (rstep R1)\<^sup>*"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    from ground l i have gi: "ground (ts ! i \<cdot> \<sigma>)" by auto
    from gm_nf_decode[OF deactivate gi]
    show "(gm_nf_args \<mu> D act mark f (length ts) 0
          (map (\<lambda>t. t \<cdot> \<sigma>) ts) ! i,
        map (\<lambda>t. t \<cdot> \<sigma>) ts ! i) \<in> (rstep R1)\<^sup>*"
      using nth_gm_nf_args[of i "map (\<lambda>t. t \<cdot> \<sigma>) ts" \<mu> D act mark f
          "length ts" 0] i
      by (cases "i \<in> \<mu> (f,length ts)", auto)
  qed
  have len_args: "length (gm_nf_args \<mu> D act mark f (length ts) 0
      (map (\<lambda>t. t \<cdot> \<sigma>) ts)) = length (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
    by simp
  have args:
    "(Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_nf_args \<mu> D act mark f (length ts) 0
          (map (\<lambda>t. t \<cdot> \<sigma>) ts)),
      Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (map (\<lambda>t. t \<cdot> \<sigma>) ts)) \<in> (rstep R1)\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length (gm_nf_args \<mu> D act mark f (length ts) 0
        (map (\<lambda>t. t \<cdot> \<sigma>) ts)) = length (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
      by (rule len_args)
    show "\<forall>i<length (gm_nf_args \<mu> D act mark f (length ts) 0
        (map (\<lambda>t. t \<cdot> \<sigma>) ts)).
      (gm_nf_args \<mu> D act mark f (length ts) 0
          (map (\<lambda>t. t \<cdot> \<sigma>) ts) ! i,
        map (\<lambda>t. t \<cdot> \<sigma>) ts ! i) \<in> (rstep R1)\<^sup>*"
      using arg_steps by simp
  qed
  show ?thesis
    unfolding l
    using args
    by (cases "(f,length ts) \<in> D", simp_all)
qed

lemma gm_nf_subst_finish:
  fixes R1 :: "('f,'v) trs"
  assumes mark_step: "\<And>u. ground u \<Longrightarrow> funas_term u \<subseteq> F \<Longrightarrow>
      (Fun mark [u], gm_nf \<mu> D act mark u) \<in> (rstep R1)\<^sup>*"
    and ground: "ground (t \<cdot> \<sigma>)"
    and sig: "funas_term (t \<cdot> \<sigma>) \<subseteq> F"
  shows "(gm_nf \<mu> D act mark t \<cdot> \<sigma>,
      gm_nf \<mu> D act mark (t \<cdot> \<sigma>)) \<in> (rstep R1)\<^sup>*"
  using ground sig
proof (induct t)
  case (Var x)
  from mark_step[OF Var.prems(1) Var.prems(2)] show ?case by auto
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
  have arg_steps: "\<forall>i<length ts.
      (map (\<lambda>t. t \<cdot> \<sigma>)
          (gm_nf_args \<mu> D act mark f (length ts) 0 ts) ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ?ss ! i)
        \<in> (rstep R1)\<^sup>*"
  proof (intro allI impI)
    fix i
    assume i: "i < length ts"
    from Fun.prems i have gi: "ground (ts ! i \<cdot> \<sigma>)" by auto
    have mem: "ts ! i \<in> set ts" using i by simp
    have sub: "funas_term (ts ! i \<cdot> \<sigma>) \<subseteq>
        \<Union>(funas_term ` (\<lambda>t. t \<cdot> \<sigma>) ` set ts)"
      using mem by blast
    from subset_trans[OF sub] Fun.prems(2)
    have si: "funas_term (ts ! i \<cdot> \<sigma>) \<subseteq> F" by auto
    from Fun.hyps[OF nth_mem[OF i] gi si]
    have IH: "(gm_nf \<mu> D act mark (ts ! i) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (ts ! i \<cdot> \<sigma>)) \<in> (rstep R1)\<^sup>*" .
    have source: "map (\<lambda>t. t \<cdot> \<sigma>)
          (gm_nf_args \<mu> D act mark f (length ts) 0 ts) ! i =
        (if i \<in> \<mu> (f,length ts)
          then gm_nf \<mu> D act mark (ts ! i) \<cdot> \<sigma> else ts ! i \<cdot> \<sigma>)"
      using nth_gm_nf_args[OF i, of \<mu> D act mark f "length ts" 0] i
      by simp
    have target: "gm_nf_args \<mu> D act mark f (length ts) 0 ?ss ! i =
        (if i \<in> \<mu> (f,length ts)
          then gm_nf \<mu> D act mark (ts ! i \<cdot> \<sigma>) else ts ! i \<cdot> \<sigma>)"
      using nth_gm_nf_args[of i ?ss \<mu> D act mark f "length ts" 0] i
      by simp
    show "(map (\<lambda>t. t \<cdot> \<sigma>)
          (gm_nf_args \<mu> D act mark f (length ts) 0 ts) ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ?ss ! i)
      \<in> (rstep R1)\<^sup>*"
      using IH source target by (cases "i \<in> \<mu> (f,length ts)", auto)
  qed
  have len_args: "length (map (\<lambda>t. t \<cdot> \<sigma>)
      (gm_nf_args \<mu> D act mark f (length ts) 0 ts)) =
    length (gm_nf_args \<mu> D act mark f (length ts) 0 ?ss)"
    by simp
  have args:
    "(Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (map (\<lambda>t. t \<cdot> \<sigma>)
          (gm_nf_args \<mu> D act mark f (length ts) 0 ts)),
      Fun (if (f,length ts) \<in> D then act (f,length ts) else f)
        (gm_nf_args \<mu> D act mark f (length ts) 0 ?ss))
      \<in> (rstep R1)\<^sup>*"
  proof (rule args_rsteps_imp_rsteps)
    show "length (map (\<lambda>t. t \<cdot> \<sigma>)
        (gm_nf_args \<mu> D act mark f (length ts) 0 ts)) =
      length (gm_nf_args \<mu> D act mark f (length ts) 0 ?ss)"
      by (rule len_args)
    show "\<forall>i<length (map (\<lambda>t. t \<cdot> \<sigma>)
        (gm_nf_args \<mu> D act mark f (length ts) 0 ts)).
      (map (\<lambda>t. t \<cdot> \<sigma>)
          (gm_nf_args \<mu> D act mark f (length ts) 0 ts) ! i,
        gm_nf_args \<mu> D act mark f (length ts) 0 ?ss ! i)
        \<in> (rstep R1)\<^sup>*"
      using arg_steps by simp
  qed
  show ?case
    using args
    by (cases "(f,length ts) \<in> D", simp_all)
qed

theorem gm_root_simulation_imp_step_simulation:
  fixes R R1 :: "('f,'v) trs"
    and \<mu> :: "'f mu"
    and D :: "'f sig"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark :: 'f
    and P :: "('f,'v) term \<Rightarrow> bool"
  assumes root_simulation: "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow>
      P s \<Longrightarrow> P t \<Longrightarrow>
      (s,t) \<in> csrstep \<mu> R \<Longrightarrow>
      (gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
        \<in> (rstep R1)\<^sup>+"
    and subterm_closed: "\<And>f ts i. P (Fun f ts) \<Longrightarrow> i < length ts \<Longrightarrow>
      P (ts ! i)"
    and gs: "ground s"
    and gt: "ground t"
    and ps: "P s"
    and pt: "P t"
    and step: "(s,t) \<in> csstep \<mu> R"
  shows "(gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
    \<in> (rstep R1)\<^sup>+"
  using gs gt ps pt step
proof (induct s arbitrary: t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  show ?case
  proof (cases "(Fun f ss,t) \<in> csrstep \<mu> R")
    case True
    then show ?thesis
      by (rule root_simulation[OF Fun.prems(1) Fun.prems(2)
          Fun.prems(3) Fun.prems(4)])
  next
    case False
    with Fun.prems(5) have nonroot: "(Fun f ss,t) \<in> csnrstep \<mu> R"
      unfolding csstep_root_nonroot by auto
    from csnrstep_FunE[OF nonroot]
    obtain i ts where i: "i < length ss"
      and active: "i \<in> \<mu> (f, length ss)"
      and t: "t = Fun f ts"
      and len: "length ts = length ss"
      and substep: "(ss ! i, ts ! i) \<in> csstep \<mu> R"
      and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow> ts ! j = ss ! j"
      by blast
    from Fun.prems(1) i have gsi: "ground (ss ! i)"
      by auto
    from Fun.prems(2) t len i have gti: "ground (ts ! i)"
      by auto
    have psi: "P (ss ! i)"
      by (rule subterm_closed[OF Fun.prems(3) i])
    have pti: "P (ts ! i)"
      using subterm_closed[OF Fun.prems(4)[unfolded t], of i] len i by simp
    from Fun.hyps[OF nth_mem[OF i] gsi gti psi pti substep]
    have sub_simulation:
      "(gm_nf \<mu> D act mark (ss ! i), gm_nf \<mu> D act mark (ts ! i))
        \<in> (rstep R1)\<^sup>+" .
    have ts_update: "ts = ss[i := ts ! i]"
    proof (rule nth_equalityI)
      show "length ts = length (ss[i := ts ! i])"
        using len by simp
      fix j
      assume j: "j < length ts"
      show "ts ! j = ss[i := ts ! i] ! j"
      proof (cases "j = i")
        case True
        with i show ?thesis by simp
      next
        case False
        from same[of j] j len False show ?thesis by simp
      qed
    qed
    have pos: "[i] \<in> poss (Fun f ss)"
      using i by simp
    have cond: "csstep_cond \<mu> [i] (Fun f ss)"
      unfolding csstep_cond_def
      using i active by auto
    from gm_nf_active_subterm[OF cond pos, of D act mark]
    have enc_pos: "[i] \<in> poss (gm_nf \<mu> D act mark (Fun f ss))"
      and enc_sub: "gm_nf \<mu> D act mark (Fun f ss) |_ [i] =
        gm_nf \<mu> D act mark (ss ! i)"
      by auto
    let ?C = "ctxt_of_pos_term [i] (gm_nf \<mu> D act mark (Fun f ss))"
    from rsteps_plus_ctxt[OF sub_simulation, of ?C]
    have lifted: "(?C\<langle>gm_nf \<mu> D act mark (ss ! i)\<rangle>,
        ?C\<langle>gm_nf \<mu> D act mark (ts ! i)\<rangle>)
      \<in> (rstep R1)\<^sup>+" .
    have source: "?C\<langle>gm_nf \<mu> D act mark (ss ! i)\<rangle> =
        gm_nf \<mu> D act mark (Fun f ss)"
      using ctxt_supt_id[OF enc_pos] enc_sub by simp
    have replace: "replace_at (Fun f ss) [i] (ts ! i) = t"
      using t ts_update i by (simp add: upd_conv_take_nth_drop)
    have target: "?C\<langle>gm_nf \<mu> D act mark (ts ! i)\<rangle> =
        gm_nf \<mu> D act mark t"
      using gm_nf_active_replace_at[OF cond pos, of D act mark "ts ! i"]
        replace by simp
    from lifted source target show ?thesis by simp
  qed
qed

theorem gm_root_simulation:
  fixes R R1 :: "('f,'v) trs"
    and \<mu> :: "'f mu"
    and D :: "'f sig"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark :: 'f
    and P :: "('f,'v) term \<Rightarrow> bool"
  assumes original_steps: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (gm_lhs D act (fst lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep R1"
    and lhs_prepare: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow> ground (fst lr \<cdot> \<sigma>) \<Longrightarrow>
      (gm_nf \<mu> D act mark (fst lr \<cdot> \<sigma>), gm_lhs D act (fst lr) \<cdot> \<sigma>)
        \<in> (rstep R1)\<^sup>*"
    and rhs_finish: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow> ground (snd lr \<cdot> \<sigma>) \<Longrightarrow>
      P (snd lr \<cdot> \<sigma>) \<Longrightarrow>
      (gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (snd lr \<cdot> \<sigma>))
        \<in> (rstep R1)\<^sup>*"
    and gs: "ground s"
    and gt: "ground t"
    and ps: "P s"
    and pt: "P t"
    and step: "(s,t) \<in> csrstep \<mu> R"
  shows "(gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
    \<in> (rstep R1)\<^sup>+"
proof -
  from step obtain lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr [] \<sigma>"
    unfolding csrstep_iff_rstep_root by blast
  from raw have lr: "lr \<in> R" and s: "s = fst lr \<cdot> \<sigma>"
    and t: "t = snd lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  have gl: "ground (fst lr \<cdot> \<sigma>)"
    using gs s by simp
  have prefix: "(gm_nf \<mu> D act mark s, gm_lhs D act (fst lr) \<cdot> \<sigma>)
      \<in> (rstep R1)\<^sup>*"
    using lhs_prepare[OF lr gl] s by simp
  have middle: "(gm_lhs D act (fst lr) \<cdot> \<sigma>,
      gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep R1"
    by (rule original_steps[OF lr])
  have gr: "ground (snd lr \<cdot> \<sigma>)"
    using gt t by simp
  have pr: "P (snd lr \<cdot> \<sigma>)"
    using pt t by simp
  have suffix: "(gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>,
      gm_nf \<mu> D act mark t) \<in> (rstep R1)\<^sup>*"
    using rhs_finish[OF lr gr pr] t by simp
  from prefix middle have first: "(gm_nf \<mu> D act mark s,
      gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> (rstep R1)\<^sup>+"
    by (rule rtrancl_into_trancl1)
  from rtranclD[OF suffix] show ?thesis
  proof
    assume "gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma> =
        gm_nf \<mu> D act mark t"
    with first show ?thesis by simp
  next
    assume "gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma> \<noteq>
        gm_nf \<mu> D act mark t \<and>
      (gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark t) \<in> (rstep R1)\<^sup>+"
    with first show ?thesis by (meson trancl_trans)
  qed
qed

theorem gm_simulation_imp_SN_csstep:
  fixes R R1 :: "('f,'v) trs"
    and \<mu> :: "'f mu"
    and D :: "'f sig"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark c :: 'f
  assumes transformed_SN: "SN (rstep R1)"
    and simulation: "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow>
      (s,t) \<in> csstep \<mu> R \<Longrightarrow>
      (gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
        \<in> (rstep R1)\<^sup>+"
  shows "SN (csstep \<mu> R)"
proof -
  let ?ground = "\<lambda>(_::'v). Fun c []"
  let ?encode = "\<lambda>t. gm_nf \<mu> D act mark (t \<cdot> ?ground)"
  have target: "SN_rel (rstep R1) {}"
    using transformed_SN by simp
  have source: "SN_rel (csstep \<mu> R) {}"
  proof (rule SN_rel_map[OF target, of _ ?encode])
    fix s t :: "('f,'v) term"
    assume step: "(s,t) \<in> csstep \<mu> R"
    have grounded: "(s \<cdot> ?ground, t \<cdot> ?ground) \<in> csstep \<mu> R"
      by (rule csstep_subst_closed[OF step])
    have gs: "ground (s \<cdot> ?ground)" and gt: "ground (t \<cdot> ?ground)"
      by auto
    from simulation[OF gs gt grounded]
    have "(?encode s, ?encode t) \<in> rstep R1 O (rstep R1)\<^sup>*"
      unfolding trancl_unfold_left .
    then show "(?encode s, ?encode t) \<in>
      (rstep R1 \<union> {})\<^sup>* O rstep R1 O (rstep R1 \<union> {})\<^sup>*"
      by regexp
  next
    fix s t :: "('f,'v) term"
    assume "(s,t) \<in> {}"
    then show "(?encode s, ?encode t) \<in> (rstep R1 \<union> {})\<^sup>*"
      by simp
  qed
  from source show ?thesis by simp
qed

theorem gm_simulation_imp_SN_sig_csstep:
  fixes R R1 :: "('f,'v) trs"
    and \<mu> :: "'f mu"
    and D F :: "'f sig"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark c :: 'f
  assumes transformed_SN: "SN (rstep R1)"
    and c: "(c,0) \<in> F"
    and simulation: "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow>
      funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow>
      (s,t) \<in> csstep \<mu> R \<Longrightarrow>
      (gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
        \<in> (rstep R1)\<^sup>+"
  shows "SN (sig_step F (csstep \<mu> R))"
proof -
  let ?ground = "\<lambda>(_::'v). Fun c []"
  let ?encode = "\<lambda>t. gm_nf \<mu> D act mark (t \<cdot> ?ground)"
  have target: "SN_rel (rstep R1) {}"
    using transformed_SN by simp
  have source: "SN_rel (sig_step F (csstep \<mu> R)) {}"
  proof (rule SN_rel_map[OF target, of _ ?encode])
    fix s t :: "('f,'v) term"
    assume step: "(s,t) \<in> sig_step F (csstep \<mu> R)"
    from step have csr: "(s,t) \<in> csstep \<mu> R"
      and fs: "funas_term s \<subseteq> F" and ft: "funas_term t \<subseteq> F"
      unfolding sig_step_def by auto
    have grounded: "(s \<cdot> ?ground, t \<cdot> ?ground) \<in> csstep \<mu> R"
      by (rule csstep_subst_closed[OF csr])
    have gs: "ground (s \<cdot> ?ground)" and gt: "ground (t \<cdot> ?ground)"
      by auto
    have fgs: "funas_term (s \<cdot> ?ground) \<subseteq> F"
      using fs c unfolding funas_term_subst by auto
    have fgt: "funas_term (t \<cdot> ?ground) \<subseteq> F"
      using ft c unfolding funas_term_subst by auto
    from simulation[OF gs gt fgs fgt grounded]
    have "(?encode s, ?encode t) \<in> rstep R1 O (rstep R1)\<^sup>*"
      unfolding trancl_unfold_left .
    then show "(?encode s, ?encode t) \<in>
      (rstep R1 \<union> {})\<^sup>* O rstep R1 O (rstep R1 \<union> {})\<^sup>*"
      by regexp
  next
    fix s t :: "('f,'v) term"
    assume "(s,t) \<in> {}"
    then show "(?encode s, ?encode t) \<in> (rstep R1 \<union> {})\<^sup>*"
      by simp
  qed
  from source show ?thesis by simp
qed

theorem gm_generated_steps_imp_SN_csstep:
  fixes R R1 :: "('f,'v) trs"
    and \<mu> :: "'f mu"
    and D :: "'f sig"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark :: 'f
  assumes wf: "wf_trs R"
    and transformed_SN: "SN (rstep R1)"
    and deactivate: "\<And>f ts. (f,length ts) \<in> D \<Longrightarrow>
      (Fun (act (f,length ts)) ts, Fun f ts) \<in> rstep R1"
    and mark_step: "\<And>u. ground u \<Longrightarrow>
      (Fun mark [u], gm_nf \<mu> D act mark u) \<in> (rstep R1)\<^sup>*"
    and original_step: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (gm_lhs D act (fst lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep R1"
  shows "SN (csstep \<mu> R)"
proof (rule gm_simulation_imp_SN_csstep[OF transformed_SN,
    where \<mu> = \<mu> and D = D and act = act and mark = mark])
  fix s t
  assume gs: "ground s" and gt: "ground t"
    and step: "(s,t) \<in> csstep \<mu> R"
  have invariant: "\<And>f ts i. (\<lambda>_. True) (Fun f ts) \<Longrightarrow>
      i < length ts \<Longrightarrow> (\<lambda>_. True) (ts ! i)" by simp
  show "(gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
    \<in> (rstep R1)\<^sup>+"
  proof (rule gm_root_simulation_imp_step_simulation[
      where P="\<lambda>_. True", OF _ invariant gs gt TrueI TrueI step])
    fix u v
    assume gu: "ground u" and gv: "ground v"
      and "True" and "True"
      and root: "(u,v) \<in> csrstep \<mu> R"
    show "(gm_nf \<mu> D act mark u, gm_nf \<mu> D act mark v)
      \<in> (rstep R1)\<^sup>+"
    proof (rule gm_root_simulation[where P="\<lambda>_. True",
        OF original_step _ _ gu gv TrueI TrueI root])
      fix lr :: "('f,'v) rule" and \<sigma> :: "('f,'v) subst"
      assume lr: "lr \<in> R" and gl: "ground (fst lr \<cdot> \<sigma>)"
      obtain l r where lr_pair: "lr = (l,r)"
        by (cases lr, auto)
      have lrr: "(l,r) \<in> R" using lr lr_pair by simp
      from wf have wf_rules:
        "\<forall>l r. (l,r) \<in> R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and>
          vars_term r \<subseteq> vars_term l"
        unfolding wf_trs_def wf_rule_def by simp
      from wf_rules[rule_format, OF lrr]
      obtain f ts where l: "l = Fun f ts" by blast
      have lhs_fun: "is_Fun (fst lr)" unfolding lr_pair l by simp
      show "(gm_nf \<mu> D act mark (fst lr \<cdot> \<sigma>),
          gm_lhs D act (fst lr) \<cdot> \<sigma>) \<in> (rstep R1)\<^sup>*"
        by (rule gm_lhs_prepare[OF deactivate lhs_fun gl])
    next
      fix lr :: "('f,'v) rule" and \<sigma> :: "('f,'v) subst"
      assume "lr \<in> R" and gr: "ground (snd lr \<cdot> \<sigma>)" and "True"
      show "(gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>,
          gm_nf \<mu> D act mark (snd lr \<cdot> \<sigma>)) \<in> (rstep R1)\<^sup>*"
        apply (rule gm_nf_subst_finish[where F=UNIV])
        subgoal for u by (intro mark_step; assumption)
        using gr apply assumption
        by simp
    qed
  qed
qed

theorem gm_transformed_rules_list_sound:
  fixes R T :: "('f,string) rules"
    and F Ds :: "('f \<times> nat) list"
    and \<mu> :: "'f mu"
    and act :: "'f \<times> nat \<Rightarrow> 'f"
    and mark c :: 'f
  defines "D \<equiv> set Ds"
  assumes wf: "wf_trs (set R)"
    and source_sig: "funas_trs (set R) \<subseteq> set F"
    and ground_const: "(c,0) \<in> set F"
    and transformed: "set (gm_transformed_rules_list \<mu> D act mark F R Ds) \<subseteq> set T"
    and transformed_SN: "SN (rstep (set T))"
  shows "SN (sig_step (set F) (csstep \<mu> (set R)))"
proof (rule gm_simulation_imp_SN_sig_csstep[OF transformed_SN ground_const,
    where D=D and act=act and mark=mark])
  fix s t
  assume gs: "ground s" and gt: "ground t"
    and fs: "funas_term s \<subseteq> set F"
    and ft: "funas_term t \<subseteq> set F"
    and step: "(s,t) \<in> csstep \<mu> (set R)"
  have deactivate:
    "\<And>f ts. (f,length ts) \<in> D \<Longrightarrow>
      (Fun (act (f,length ts)) ts, Fun f ts) \<in> rstep (set T)"
  proof -
    fix f and ts :: "('f,string) term list"
    assume fn: "(f,length ts) \<in> D"
    have generated: "gm_deactivate_rule act (f,length ts) \<in>
        set (gm_transformed_rules_list \<mu> D act mark F R Ds)"
      using fn unfolding D_def gm_transformed_rules_list_def by auto
    from subsetD[OF transformed generated]
    show "(Fun (act (f,length ts)) ts, Fun f ts) \<in> rstep (set T)"
      by (rule gm_deactivate_rule_instance[OF _ refl])
  qed
  have mark_steps:
    "\<And>u. ground u \<Longrightarrow> funas_term u \<subseteq> set F \<Longrightarrow>
      (Fun mark [u], gm_nf \<mu> D act mark u) \<in> (rstep (set T))\<^sup>*"
  proof -
    fix u :: "('f,string) term"
    assume gu: "ground u" and fu: "funas_term u \<subseteq> set F"
    show "(Fun mark [u], gm_nf \<mu> D act mark u) \<in> (rstep (set T))\<^sup>*"
    proof (rule gm_generated_mark_steps[OF _ fu gu])
      fix f n
      assume fn: "(f,n) \<in> set F"
      have generated: "gm_mark_rule \<mu> D act mark (f,n) \<in>
          set (gm_transformed_rules_list \<mu> D act mark F R Ds)"
        using fn unfolding gm_transformed_rules_list_def by auto
      show "gm_mark_rule \<mu> D act mark (f,n) \<in> set T"
        by (rule subsetD[OF transformed generated])
    qed
  qed
  have original_steps:
    "\<And>lr \<sigma>. lr \<in> set R \<Longrightarrow>
      (gm_lhs D act (fst lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep (set T)"
  proof -
    fix lr \<sigma>
    assume lr: "lr \<in> set R"
    have generated: "gm_rule \<mu> D act mark lr \<in>
        set (gm_transformed_rules_list \<mu> D act mark F R Ds)"
      using lr unfolding gm_transformed_rules_list_def by auto
    from subsetD[OF transformed generated]
    show "(gm_lhs D act (fst lr) \<cdot> \<sigma>,
        gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>) \<in> rstep (set T)"
      by (rule gm_original_rule_instance)
  qed
  have invariant:
    "\<And>f ts i. funas_term (Fun f ts) \<subseteq> set F \<Longrightarrow>
      i < length ts \<Longrightarrow> funas_term (ts ! i) \<subseteq> set F"
  proof -
    fix f ts i
    assume all: "funas_term (Fun f ts) \<subseteq> set F"
      and i: "i < length ts"
    have mem: "ts ! i \<in> set ts" using i by simp
    have sub: "funas_term (ts ! i) \<subseteq> \<Union>(funas_term ` set ts)"
      using mem by blast
    from subset_trans[OF sub] all show "funas_term (ts ! i) \<subseteq> set F"
      by auto
  qed
  show "(gm_nf \<mu> D act mark s, gm_nf \<mu> D act mark t)
    \<in> (rstep (set T))\<^sup>+"
  proof (rule gm_root_simulation_imp_step_simulation[
      where P="\<lambda>t. funas_term t \<subseteq> set F",
      OF _ invariant gs gt fs ft step])
    fix u v
    assume gu: "ground u" and gv: "ground v"
      and fu: "funas_term u \<subseteq> set F"
      and fv: "funas_term v \<subseteq> set F"
      and root: "(u,v) \<in> csrstep \<mu> (set R)"
    show "(gm_nf \<mu> D act mark u, gm_nf \<mu> D act mark v)
      \<in> (rstep (set T))\<^sup>+"
    proof (rule gm_root_simulation[
        where P="\<lambda>t. funas_term t \<subseteq> set F",
        OF original_steps _ _ gu gv fu fv root])
      fix lr :: "('f,string) rule" and \<sigma> :: "('f,string) subst"
      assume lr: "lr \<in> set R" and gl: "ground (fst lr \<cdot> \<sigma>)"
      obtain l r where pair: "lr = (l,r)" by (cases lr, auto)
      have lrr: "(l,r) \<in> set R" using lr pair by simp
      from wf have rules:
        "\<forall>l r. (l,r) \<in> set R \<longrightarrow> (\<exists>f ts. l = Fun f ts) \<and>
          vars_term r \<subseteq> vars_term l"
        unfolding wf_trs_def wf_rule_def by simp
      from rules[rule_format, OF lrr]
      obtain f ls where l: "l = Fun f ls" by blast
      have lhs_fun: "is_Fun (fst lr)" unfolding pair l by simp
      show "(gm_nf \<mu> D act mark (fst lr \<cdot> \<sigma>),
          gm_lhs D act (fst lr) \<cdot> \<sigma>) \<in> (rstep (set T))\<^sup>*"
        by (rule gm_lhs_prepare[OF deactivate lhs_fun gl])
    next
      fix lr :: "('f,string) rule" and \<sigma> :: "('f,string) subst"
      assume lr: "lr \<in> set R" and gr: "ground (snd lr \<cdot> \<sigma>)"
        and rhs_sig: "funas_term (snd lr \<cdot> \<sigma>) \<subseteq> set F"
      show "(gm_nf \<mu> D act mark (snd lr) \<cdot> \<sigma>,
          gm_nf \<mu> D act mark (snd lr \<cdot> \<sigma>)) \<in> (rstep (set T))\<^sup>*"
        by (rule gm_nf_subst_finish[OF mark_steps gr rhs_sig])
    qed
  qed
qed

datatype ('f, 'l, 'v) gm_extended_csr_termination_proof =
    Existing_CSR_Proof "('f, 'l, 'v) extended_csr_termination_proof"
  | Innermost_CSR_Dependency_Pairs
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) trsLL"
      "('f, 'l, 'v) csr_dp_termination_proof"
  | GM_CSR_Transformation
      "('f, 'l) lab"
      "('f, 'l) lab"
      "((('f, 'l) lab \<times> nat) \<times> ('f, 'l) lab) list"
      "('f, 'l, 'v) trs_termination_proof"

fun check_gm_extended_csr_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   bool \<Rightarrow> showsl \<Rightarrow> (('f,label_type) lab) muL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) gm_extended_csr_termination_proof \<Rightarrow> showsl check"
where
  "check_gm_extended_csr_termination_proof I J a i \<mu> R
      (Existing_CSR_Proof prf) =
    check_extended_csr_termination_proof I J a i \<mu> R prf"
| "check_gm_extended_csr_termination_proof I J a i \<mu> R
      (Innermost_CSR_Dependency_Pairs P S prf) =
    (if S = [] then
       check_innermost_csr_or_rta08_termination_proof I J i \<mu> R P prf
     else
       debug i (STR ''direct innermost CSR dependency pairs'') (do {
         dpp \<leftarrow> direct_innermost_csr_dependency_pairs_tt J \<mu> R P (R @ S);
         check_csr_dp_termination_proof I J False (add_index i 1) dpp prf
       }))"
| "check_gm_extended_csr_termination_proof I J a i \<mu> R
      (GM_CSR_Transformation mark c active prf) =
    debug i (STR ''Giesl-Middeldorp CSR transformation'') (do {
      check_wf_trs R;
      let D = defined_list R;
      let F = remdups (funas_trs_list R);
      check (distinct (map fst active) \<and> set (map fst active) = set D)
        (showsl_lit (STR ''active-symbol map does not cover the defined signature exactly''));
      check ((c, 0) \<in> set F)
        (showsl_lit (STR ''ground source-signature constant is missing''));
      let act = (\<lambda>fn. the (map_of active fn));
      let T = gm_transformed_rules_list (mu_of \<mu>) (set D) act mark F R D;
      check_trs_termination_proof I J False (add_index i 1)
        (tp_ops.mk I False [] T []) prf
    })"

lemma check_gm_extended_csr_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_gm_extended_csr_termination_proof
      I J a i \<mu> R p)"
  shows "SN (sig_step (set (funas_trs_list R))
    (csstep (mu_of \<mu>) (set R)))"
proof (cases p)
  case (Existing_CSR_Proof old)
  with ok have old_ok:
    "isOK (check_extended_csr_termination_proof I J a i \<mu> R old)"
    by simp
  from check_extended_csr_termination_proof_sound[OF I J old_ok]
  show ?thesis .
next
  case (Innermost_CSR_Dependency_Pairs P S child)
  show ?thesis
  proof (cases "S = []")
    case True
    from ok Innermost_CSR_Dependency_Pairs True have rec:
        "isOK (check_innermost_csr_or_rta08_termination_proof
          I J i \<mu> R P child)"
      by simp
    have "SN (csstep (mu_of \<mu>) (set R))"
      by (rule check_innermost_csr_or_rta08_termination_proof_sound[
        OF I J rec])
    then show ?thesis
      by (rule SN_subset, unfold sig_step_def, auto)
  next
    case False
    from ok Innermost_CSR_Dependency_Pairs False obtain dpp where tt:
        "direct_innermost_csr_dependency_pairs_tt J \<mu> R P (R @ S) = Inr dpp"
      and rec: "isOK (check_csr_dp_termination_proof
        I J False (add_index i 1) dpp child)"
      by auto
    have fin: "finite_dpp (dpp_ops.dpp J dpp)"
      by (rule check_csr_dp_termination_proof_sound[OF I J rec])
    have "SN (csstep (mu_of \<mu>) (set R))"
      by (rule direct_innermost_csr_dependency_pairs_tt_finite_imp_SN[
        OF J tt fin])
    then show ?thesis
      by (rule SN_subset, unfold sig_step_def, auto)
  qed
next
  case (GM_CSR_Transformation mark c active child)
  let ?D = "defined_list R"
  let ?F = "remdups (funas_trs_list R)"
  let ?act = "\<lambda>fn. the (map_of active fn)"
  let ?T = "gm_transformed_rules_list (mu_of \<mu>) (set ?D) ?act mark ?F R ?D"
  from ok GM_CSR_Transformation have wf: "wf_trs (set R)"
    and keys: "distinct (map fst active) \<and> set (map fst active) = set ?D"
    and ground_c: "(c, 0) \<in> set ?F"
    and child_ok: "isOK (check_trs_termination_proof I J False (add_index i 1)
      (tp_ops.mk I False [] ?T []) child)"
    by (auto simp: Let_def)
  from check_trs_termination_proof[OF I J child_ok]
  have child_SN: "SN (rstep (set ?T))"
    unfolding tp_spec.mk_sound[OF I] SN_qrel_def by auto
  have source_sig: "funas_trs (set R) \<subseteq> set ?F" by simp
  have transformed: "set (gm_transformed_rules_list (mu_of \<mu>) (set ?D)
      ?act mark ?F R ?D) \<subseteq> set ?T" by simp
  from gm_transformed_rules_list_sound[OF wf source_sig ground_c transformed child_SN]
  show ?thesis by simp
qed

end
