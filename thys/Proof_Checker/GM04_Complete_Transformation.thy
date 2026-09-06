(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory GM04_Complete_Transformation
  imports
    CSR_GM_Transformation
    Auxx.RenamingN_String
begin

lemma gm04_inj_clean_string:
  "inj (x_var_list \<circ> (\<lambda>t. (Countable.to_nat t, [])) ::
    (('f::countable),string) term \<Rightarrow> string)"
proof (unfold inj_def, intro allI impI)
  fix x y :: "('f,string) term"
  assume equal:
    "(x_var_list \<circ> (\<lambda>t. (Countable.to_nat t, []))) x =
      (x_var_list \<circ> (\<lambda>t. (Countable.to_nat t, []))) y"
  have equal':
      "x_var_list (Countable.to_nat x, []) =
        x_var_list (Countable.to_nat y, [])"
    using equal by simp
  from injD[OF inj_x_var_list equal']
  have "Countable.to_nat x = Countable.to_nat y" by simp
  then show "x = y" by (rule injD[OF Countable.inj_to_nat])
qed

text \<open>
  The complete Giesl--Middeldorp transformation (JFP 2004, Definition 23).
  This is the inverse transformation used by AProVE's QTRSToCSR processor:
  a transformed ordinary/innermost problem is checked against the complete
  schema below, and termination of the reconstructed source CSRS is then used
  to establish termination of the transformed problem.
\<close>

definition gm04_vars where
  "gm04_vars n = map Var (x\<^sub>1_to_x\<^sub>n n)"

lemma length_gm04_vars[simp]: "length (gm04_vars n) = n"
  by (simp add: gm04_vars_def)

lemma gm04_vars_zero[simp]: "gm04_vars 0 = []"
  by (rule length_0_conv[THEN iffD1], simp)

lemma gm04_vars_term_list_update[simp]:
  assumes "i < length xs"
  shows "vars_term (Fun f (xs[i := Fun role [xs ! i]])) =
    vars_term (Fun f xs)"
proof (rule equalityI)
  show "vars_term (Fun f (xs[i := Fun role [xs ! i]]))
      \<subseteq> vars_term (Fun f xs)"
  proof
    fix x
    assume "x \<in> vars_term (Fun f (xs[i := Fun role [xs ! i]]))"
    then obtain u where u:
        "u \<in> set (xs[i := Fun role [xs ! i]])" "x \<in> vars_term u"
      by auto
    from set_update_subset_insert[of xs i "Fun role [xs ! i]"] u(1)
    have "u = Fun role [xs ! i] \<or> u \<in> set xs" by auto
    then show "x \<in> vars_term (Fun f xs)"
    proof
      assume "u = Fun role [xs ! i]"
      moreover have "xs ! i \<in> set xs" using assms by (rule nth_mem)
      ultimately show ?thesis using u(2) by auto
    next
      assume "u \<in> set xs"
      with u(2) show ?thesis by auto
    qed
  qed
next
  show "vars_term (Fun f xs)
      \<subseteq> vars_term (Fun f (xs[i := Fun role [xs ! i]]))"
  proof
    fix x
    assume "x \<in> vars_term (Fun f xs)"
    then obtain t where t: "t \<in> set xs" "x \<in> vars_term t" by auto
    then obtain j where j: "j < length xs" "t = xs ! j"
      by (metis in_set_conv_nth)
    show "x \<in> vars_term (Fun f (xs[i := Fun role [xs ! i]]))"
    proof (cases "j = i")
      case True
      have member: "Fun role [xs ! i] \<in> set (xs[i := Fun role [xs ! i]])"
        using assms by (rule set_update_memI)
      have x_wrapper: "x \<in> vars_term (Fun role [xs ! i])"
        using t j True by simp
      have "\<exists>u\<in>set (xs[i := Fun role [xs ! i]]). x \<in> vars_term u"
        using member x_wrapper by blast
      then show ?thesis by simp
    next
      case False
      have member: "xs ! j \<in> set (xs[i := Fun role [xs ! i]])"
        using j False by (metis length_list_update nth_list_update_neq nth_mem)
      with t j show ?thesis by auto
    qed
  qed
qed

definition gm04_source_rules where
  "gm04_source_rules active mark R =
    map (\<lambda>(l,r). (Fun active [l], Fun mark [r])) R"

definition gm04_active_rule where
  "gm04_active_rule active fn i =
    (let f = fst fn; n = snd fn; xs = gm04_vars n
     in (Fun active [Fun f xs],
       Fun f (xs[i := Fun active [xs ! i]])))"

definition gm04_mark_rule where
  "gm04_mark_rule mark fn i =
    (let f = fst fn; n = snd fn; xs = gm04_vars n
     in (Fun f (xs[i := Fun mark [xs ! i]]),
       Fun mark [Fun f xs]))"

definition gm04_active_rules where
  "gm04_active_rules \<mu> active F = concat
    (map (\<lambda>fn. map (gm04_active_rule active fn)
      (filter (\<lambda>i. i < snd fn) (sorted_list_of_set (\<mu> fn)))) F)"

definition gm04_mark_rules where
  "gm04_mark_rules \<mu> mark F = concat
    (map (\<lambda>fn. map (gm04_mark_rule mark fn)
      (filter (\<lambda>i. i < snd fn) (sorted_list_of_set (\<mu> fn)))) F)"

definition gm04_proper_rule where
  "gm04_proper_rule proper ok fn =
    (let f = fst fn; n = snd fn; xs = gm04_vars n
     in if n = 0 then
       (Fun proper [Fun f []], Fun ok [Fun f []])
     else
       (Fun proper [Fun f xs],
        Fun f (map (\<lambda>x. Fun proper [x]) xs)))"

lemma gm04_proper_rule_rhs_nonzero_instance:
  assumes nonzero: "n \<noteq> 0"
    and u: "u = snd (gm04_proper_rule proper ok (g,n)) \<cdot> \<sigma>"
    and gf: "g = f"
    and xs: "xs = map (\<lambda>z. z \<cdot> \<sigma>) (gm04_vars n)"
  shows "u = Fun f (map (\<lambda>z. Fun proper [z]) xs)"
  using assms unfolding gm04_proper_rule_def
  by (simp add: Let_def o_def)

definition gm04_ok_rule where
  "gm04_ok_rule proper ok fn =
    (let f = fst fn; n = snd fn; xs = gm04_vars n
     in if n = 0 then
       (Fun proper [Fun f []], Fun ok [Fun f []])
     else
       (Fun f (map (\<lambda>x. Fun ok [x]) xs),
        Fun ok [Fun f xs]))"

definition gm04_top_rules where
  "gm04_top_rules active mark proper ok top_sym = [
    (Fun top_sym [Fun mark [Var ''__gm04_x'']],
      Fun top_sym [Fun proper [Var ''__gm04_x'']]),
    (Fun top_sym [Fun ok [Var ''__gm04_x'']],
      Fun top_sym [Fun active [Var ''__gm04_x'']])]"

definition gm04_top_pairs where
  "gm04_top_pairs active mark proper ok top_sharp = [
    (Fun top_sharp [Fun ok [Var ''__gm04_x'']],
      Fun top_sharp [Fun active [Var ''__gm04_x'']]),
    (Fun top_sharp [Fun mark [Var ''__gm04_x'']],
      Fun top_sharp [Fun proper [Var ''__gm04_x'']])]"

lemma set_gm04_top_pairs:
  "set (gm04_top_pairs active mark proper ok top_sharp) = {
    (Fun top_sharp [Fun ok [Var ''__gm04_x'']],
      Fun top_sharp [Fun active [Var ''__gm04_x'']]),
    (Fun top_sharp [Fun mark [Var ''__gm04_x'']],
      Fun top_sharp [Fun proper [Var ''__gm04_x'']])}"
  by (simp add: gm04_top_pairs_def)

lemma gm04_top_pair_instance_cases:
  fixes u v :: "('f,string) term"
  assumes pair: "(u,v) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
  obtains x where
      "u = Fun top_sharp [Fun ok [x]]"
      "v = Fun top_sharp [Fun active [x]]"
    | x where
      "u = Fun top_sharp [Fun mark [x]]"
      "v = Fun top_sharp [Fun proper [x]]"
proof -
  from pair obtain l r \<sigma> where lr:
      "(l,r) \<in> set (gm04_top_pairs active mark proper ok top_sharp)"
    and uv: "u = l \<cdot> \<sigma>" "v = r \<cdot> \<sigma>"
    by (auto elim: subst.closure.cases)
  from lr consider
      (ok) "l = Fun top_sharp [Fun ok [Var ''__gm04_x'']]"
        "r = Fun top_sharp [Fun active [Var ''__gm04_x'']]"
    | (mark) "l = Fun top_sharp [Fun mark [Var ''__gm04_x'']]"
        "r = Fun top_sharp [Fun proper [Var ''__gm04_x'']]"
    unfolding set_gm04_top_pairs by auto
  then show thesis
  proof cases
    case ok
    show thesis
      by (rule that(1)[of "\<sigma> ''__gm04_x''"],
          simp_all add: uv ok)
  next
    case mark
    show thesis
      by (rule that(2)[of "\<sigma> ''__gm04_x''"],
          simp_all add: uv mark)
  qed
qed

definition gm04_non_top_rules where
  "gm04_non_top_rules \<mu> active mark proper ok F R =
    gm04_source_rules active mark R @
    gm04_active_rules \<mu> active F @
    gm04_mark_rules \<mu> mark F @
    map (gm04_proper_rule proper ok) F @
    map (gm04_ok_rule proper ok) (filter (\<lambda>fn. snd fn > 0) F)"

definition gm04_complete_rules where
  "gm04_complete_rules \<mu> active mark proper ok top_sym F R =
    gm04_non_top_rules \<mu> active mark proper ok F R @
    gm04_top_rules active mark proper ok top_sym"

definition gm04_roles_fresh where
  "gm04_roles_fresh active mark proper ok top_sym F \<longleftrightarrow>
    distinct [active,mark,proper,ok,top_sym] \<and>
    (\<forall>f n. (f,n) \<in> set F \<longrightarrow>
      f \<notin> {active,mark,proper,ok,top_sym})"

definition gm04_complete_schema_check where
  "gm04_complete_schema_check \<mu> active mark proper ok top_sym F R T \<longleftrightarrow>
    gm04_roles_fresh active mark proper ok top_sym F \<and>
    funas_trs (set R) \<subseteq> set F \<and>
      set T \<subseteq> set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)"

lemma gm04_non_top_rules_wf:
  assumes "wf_trs (set R)"
  shows "wf_trs (set (gm04_non_top_rules
    \<mu> active mark proper ok F R))"
proof -
  have source: "wf_trs (set (gm04_source_rules active mark R))"
    using assms unfolding wf_trs_def gm04_source_rules_def by (auto, blast)
  have active: "wf_trs (set (gm04_active_rules \<mu> active F))"
    unfolding wf_trs_def
  proof (intro allI impI)
    fix l r
    assume pair: "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    from pair obtain f n i where i: "i < n"
      and lr: "(l,r) = gm04_active_rule active (f,n) i"
      unfolding gm04_active_rules_def by auto
    from lr have lhs: "l = Fun active [Fun f (gm04_vars n)]"
      and rhs: "r = Fun f ((gm04_vars n)
        [i := Fun active [(gm04_vars n) ! i]])"
      unfolding gm04_active_rule_def by (simp_all add: Let_def)
    have vars_eq: "vars_term (Fun f ((gm04_vars n)
          [i := Fun active [(gm04_vars n) ! i]])) =
        vars_term (Fun f (gm04_vars n))"
      by (rule gm04_vars_term_list_update, use i in simp)
    show "(\<exists>g ts. l = Fun g ts) \<and> vars_term r \<subseteq> vars_term l"
    proof
      from lhs show "\<exists>g ts. l = Fun g ts" by blast
      from vars_eq show "vars_term r \<subseteq> vars_term l"
        unfolding lhs rhs by simp
    qed
  qed
  have mark: "wf_trs (set (gm04_mark_rules \<mu> mark F))"
    unfolding wf_trs_def
  proof (intro allI impI)
    fix l r
    assume pair: "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    from pair obtain f n i where i: "i < n"
      and lr: "(l,r) = gm04_mark_rule mark (f,n) i"
      unfolding gm04_mark_rules_def by auto
    from lr have lhs: "l = Fun f ((gm04_vars n)
        [i := Fun mark [(gm04_vars n) ! i]])"
      and rhs: "r = Fun mark [Fun f (gm04_vars n)]"
      unfolding gm04_mark_rule_def by (simp_all add: Let_def)
    have vars_eq: "vars_term (Fun f ((gm04_vars n)
          [i := Fun mark [(gm04_vars n) ! i]])) =
        vars_term (Fun f (gm04_vars n))"
      by (rule gm04_vars_term_list_update, use i in simp)
    show "(\<exists>g ts. l = Fun g ts) \<and> vars_term r \<subseteq> vars_term l"
    proof
      from lhs show "\<exists>g ts. l = Fun g ts" by blast
      from vars_eq show "vars_term r \<subseteq> vars_term l"
        unfolding lhs rhs by simp
    qed
  qed
  have proper: "wf_trs (set (map (gm04_proper_rule proper ok) F))"
    unfolding wf_trs_def gm04_proper_rule_def gm04_vars_def
    by (auto simp: Let_def split: prod.splits if_splits)
  have ok: "wf_trs (set (map (gm04_ok_rule proper ok)
      (filter (\<lambda>fn. snd fn > 0) F)))"
    unfolding wf_trs_def gm04_ok_rule_def gm04_vars_def
    by (auto simp: Let_def split: prod.splits if_splits)
  from source active mark proper ok show ?thesis
    unfolding gm04_non_top_rules_def wf_trs_def by auto
qed

lemma gm04_roles_pairwise:
  assumes "gm04_roles_fresh active mark proper ok top_sym F"
  shows "active \<noteq> mark" "active \<noteq> proper" "active \<noteq> ok"
    "mark \<noteq> proper" "mark \<noteq> ok" "proper \<noteq> ok"
    "top_sym \<noteq> active" "top_sym \<noteq> mark"
    "top_sym \<noteq> proper" "top_sym \<noteq> ok"
  using assms unfolding gm04_roles_fresh_def by auto

lemma gm04_source_symbol_not_role:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and fn: "(f,n) \<in> set F"
  shows "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
    "f \<noteq> top_sym"
  using fresh fn unfolding gm04_roles_fresh_def by auto

definition gm04_role_symbols where
  "gm04_role_symbols active mark proper ok top_sym =
    {active, mark, proper, ok, top_sym}"

lemma gm04_role_not_source_signature:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and role: "w \<in> gm04_role_symbols active mark proper ok top_sym"
  shows "(w,n) \<notin> set F"
  using fresh role
  unfolding gm04_roles_fresh_def gm04_role_symbols_def by auto

lemma gm04_source_rhs_contains_mark:
  assumes "lr \<in> set (gm04_source_rules active mark R)"
  shows "(mark,1) \<in> funas_term (snd lr)"
  using assms unfolding gm04_source_rules_def
  by (auto split: prod.splits)

lemma gm04_active_rhs_contains_active:
  assumes "lr \<in> set (gm04_active_rules \<mu> active F)"
  shows "(active,1) \<in> funas_term (snd lr)"
proof -
  from assms obtain f n i where fn: "(f,n) \<in> set F"
    and i: "i \<in> set (filter (\<lambda>i. i < n)
      (sorted_list_of_set (\<mu> (f,n))))"
    and lr: "lr = gm04_active_rule active (f,n) i"
    unfolding gm04_active_rules_def by auto
  have len: "length (gm04_vars n) = n"
    unfolding gm04_vars_def by (simp only: length_map x\<^sub>1_to_x\<^sub>n(1))
  from i have below: "i < n" by simp
  from below len have pos: "i < length (gm04_vars n)" by simp
  have member: "Fun active [gm04_vars n ! i] \<in>
      set ((gm04_vars n)[i := Fun active [gm04_vars n ! i]])"
    using pos by (rule set_update_memI)
  have nested: "\<exists>t\<in>set ((gm04_vars n)
      [i := Fun active [gm04_vars n ! i]]).
      (active,1) \<in> funas_term t"
  proof
    show "Fun active [gm04_vars n ! i] \<in>
        set ((gm04_vars n)[i := Fun active [gm04_vars n ! i]])"
      by (rule member)
    show "(active,1) \<in> funas_term (Fun active [gm04_vars n ! i])"
      by simp
  qed
  from lr nested show ?thesis
    by (simp add: gm04_active_rule_def Let_def)
qed

lemma gm04_mark_rhs_contains_mark:
  assumes "lr \<in> set (gm04_mark_rules \<mu> mark F)"
  shows "(mark,1) \<in> funas_term (snd lr)"
  using assms unfolding gm04_mark_rules_def
  by (auto simp: gm04_mark_rule_def Let_def)

lemma gm04_proper_rhs_contains_role:
  assumes "lr \<in> set (map (gm04_proper_rule proper ok) F)"
  shows "(proper,1) \<in> funas_term (snd lr) \<or>
      (ok,1) \<in> funas_term (snd lr)"
proof -
  from assms obtain f n where fn: "(f,n) \<in> set F"
    and lr: "lr = gm04_proper_rule proper ok (f,n)" by auto
  show ?thesis
  proof (cases n)
    case 0
    with lr show ?thesis
      by (simp add: gm04_proper_rule_def Let_def)
  next
    case (Suc m)
    have nonempty: "gm04_vars n \<noteq> []"
    proof
      assume empty: "gm04_vars n = []"
      from arg_cong[OF empty, of length] Suc show False by simp
    qed
    with nonempty lr show ?thesis
      by (auto simp: gm04_proper_rule_def Let_def)
  qed
qed

lemma gm04_ok_rhs_contains_ok:
  assumes "lr \<in> set (map (gm04_ok_rule proper ok)
      (filter (\<lambda>fn. snd fn > 0) F))"
  shows "(ok,1) \<in> funas_term (snd lr)"
  using assms
  by (auto simp: gm04_ok_rule_def Let_def)

lemma gm04_non_top_rhs_contains_role:
  assumes rule: "lr \<in> set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
  shows "\<exists>w n. w \<in> gm04_role_symbols active mark proper ok top_sym \<and>
      (w,n) \<in> funas_term (snd lr)"
proof -
  from rule consider
      (source) "lr \<in> set (gm04_source_rules active mark R)"
    | (active) "lr \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "lr \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "lr \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "lr \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  then show ?thesis
  proof cases
    case source
    from gm04_source_rhs_contains_mark[OF source] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case active
    from gm04_active_rhs_contains_active[OF active] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case mark
    from gm04_mark_rhs_contains_mark[OF mark] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case proper
    from gm04_proper_rhs_contains_role[OF proper] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case ok
    from gm04_ok_rhs_contains_ok[OF ok] show ?thesis
      unfolding gm04_role_symbols_def by auto
  qed
qed

lemma gm04_source_lhs_contains_active:
  assumes "lr \<in> set (gm04_source_rules active mark R)"
  shows "(active,1) \<in> funas_term (fst lr)"
  using assms unfolding gm04_source_rules_def by (auto split: prod.splits)

lemma gm04_active_lhs_contains_active:
  assumes "lr \<in> set (gm04_active_rules \<mu> active F)"
  shows "(active,1) \<in> funas_term (fst lr)"
  using assms unfolding gm04_active_rules_def gm04_active_rule_def
  by (auto simp: Let_def split: prod.splits)

lemma gm04_mark_lhs_contains_mark:
  assumes "lr \<in> set (gm04_mark_rules \<mu> mark F)"
  shows "(mark,1) \<in> funas_term (fst lr)"
proof -
  from assms obtain f n i where fn: "(f,n) \<in> set F"
    and i: "i \<in> set (sorted_list_of_set (\<mu> (f,n)))" "i < n"
    and lr: "lr = gm04_mark_rule mark (f,n) i"
    unfolding gm04_mark_rules_def by auto
  have pos: "i < length (gm04_vars n)"
    using i(2) by simp
  have marked: "Fun mark [gm04_vars n ! i] \<in>
      set ((gm04_vars n)[i := Fun mark [gm04_vars n ! i]])"
    using pos by (rule set_update_memI)
  have role: "(mark,1) \<in> (\<Union>t\<in>
      set ((gm04_vars n)[i := Fun mark [gm04_vars n ! i]]).
      funas_term t)"
  proof (rule UN_I[OF marked])
    show "(mark,1) \<in> funas_term (Fun mark [gm04_vars n ! i])"
      by simp
  qed
  show ?thesis
    unfolding lr gm04_mark_rule_def
    using role by (simp add: Let_def)
qed

lemma gm04_proper_lhs_contains_proper:
  assumes "lr \<in> set (map (gm04_proper_rule proper ok) F)"
  shows "(proper,1) \<in> funas_term (fst lr)"
  using assms unfolding gm04_proper_rule_def
  by (auto simp: Let_def split: prod.splits)

lemma gm04_ok_lhs_contains_ok:
  assumes "lr \<in> set (map (gm04_ok_rule proper ok)
      (filter (\<lambda>fn. snd fn > 0) F))"
  shows "(ok,1) \<in> funas_term (fst lr)"
  using assms unfolding gm04_ok_rule_def
  by (auto simp: Let_def split: prod.splits)

lemma gm04_non_top_lhs_contains_role:
  assumes rule: "lr \<in> set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
  shows "\<exists>w n. w \<in> gm04_role_symbols active mark proper ok top_sym \<and>
      (w,n) \<in> funas_term (fst lr)"
proof -
  from rule consider
      (source) "lr \<in> set (gm04_source_rules active mark R)"
    | (active) "lr \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "lr \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "lr \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "lr \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  then show ?thesis
  proof cases
    case source
    from gm04_source_lhs_contains_active[OF source] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case active
    from gm04_active_lhs_contains_active[OF active] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case mark
    from gm04_mark_lhs_contains_mark[OF mark] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case proper
    from gm04_proper_lhs_contains_proper[OF proper] show ?thesis
      unfolding gm04_role_symbols_def by auto
  next
    case ok
    from gm04_ok_lhs_contains_ok[OF ok] show ?thesis
      unfolding gm04_role_symbols_def by auto
  qed
qed

lemma gm04_non_top_rhs_instance_not_source:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and rule: "lr \<in> set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
  shows "\<not> funas_term (snd lr \<cdot> \<sigma>) \<subseteq> set F"
proof
  assume source: "funas_term (snd lr \<cdot> \<sigma>) \<subseteq> set F"
  from gm04_non_top_rhs_contains_role[OF rule, of top_sym]
  obtain w n where role: "w \<in>
      gm04_role_symbols active mark proper ok top_sym"
    and rhs: "(w,n) \<in> funas_term (snd lr)" by blast
  from rhs have "(w,n) \<in> funas_term (snd lr \<cdot> \<sigma>)"
    unfolding funas_term_subst by blast
  with source gm04_role_not_source_signature[OF fresh role]
  show False by blast
qed

lemma gm04_non_top_lhs_root_cases:
  assumes pair: "(l,r) \<in> set
    (gm04_non_top_rules \<mu> active mark proper ok F R)"
  obtains ts where "l = Fun active ts"
    | ts where "l = Fun proper ts"
    | f ts where "l = Fun f ts" "(f,length ts) \<in> set F"
  using pair
  unfolding gm04_non_top_rules_def gm04_source_rules_def
    gm04_active_rules_def gm04_mark_rules_def gm04_active_rule_def
    gm04_mark_rule_def gm04_proper_rule_def gm04_ok_rule_def
  by (auto simp: Let_def split: prod.splits if_splits)

lemma gm04_non_top_role_not_defined:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and role: "role = mark \<or> role = ok \<or> role = top_sym"
  shows "\<not> defined
    (set (gm04_non_top_rules \<mu> active mark proper ok F R)) (role,1)"
proof
  assume def: "defined
      (set (gm04_non_top_rules \<mu> active mark proper ok F R)) (role,1)"
  then obtain l r where pair: "(l,r) \<in> set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and root: "root l = Some (role,1)"
    unfolding defined_def by blast
  from gm04_non_top_lhs_root_cases[OF pair]
  show False
  proof cases
    case (1 ts)
    with root fresh role show False
      unfolding gm04_roles_fresh_def by auto
  next
    case (2 ts)
    with root fresh role show False
      unfolding gm04_roles_fresh_def by auto
  next
    case (3 f ts)
    with root fresh role show False
      unfolding gm04_roles_fresh_def by auto
  qed
qed

lemma gm04_non_top_step_cannot_produce_source:
  fixes S :: "('f,string) trs"
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and S: "S = set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
    and step: "(s,t) \<in> rstep S"
    and source: "funas_term t \<subseteq> set F"
  shows False
proof -
  from step obtain C \<sigma> l r where lr: "(l,r) \<in> S"
    and target: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by (cases rule: rstep.cases) auto
  from source target have rhs_source:
      "funas_term (r \<cdot> \<sigma>) \<subseteq> set F"
    unfolding funas_term_ctxt_apply by auto
  have pair: "(l,r) \<in> set (gm04_non_top_rules
      \<mu> active mark proper ok F R)" using lr S by simp
  from gm04_non_top_rhs_instance_not_source[OF fresh pair, of \<sigma>]
  have "\<not> funas_term (r \<cdot> \<sigma>) \<subseteq> set F" by simp
  with rhs_source show False by blast
qed

lemma gm04_top_wrapper_rsteps_iff:
  fixes S :: "('f,string) trs"
  assumes wf: "wf_trs S"
    and fresh_top: "\<not> defined S (top_sharp,1)"
  shows "(Fun top_sharp [s], Fun top_sharp [t]) \<in> (rstep S)\<^sup>*
    \<longleftrightarrow> (s,t) \<in> (rstep S)\<^sup>*"
proof
  assume wrapped: "(Fun top_sharp [s], Fun top_sharp [t]) \<in> (rstep S)\<^sup>*"
  have lhs: "\<forall>(l,r)\<in>S. is_Fun l"
    using wf unfolding wf_trs_def by blast
  have fresh_top': "\<not> defined S (top_sharp,length [s])"
    using fresh_top by simp
  have decomposition:
      "\<exists>ts. length ts = 1
        \<and> Fun top_sharp [t] = Fun top_sharp ts
        \<and> (\<forall>i<1. ([s] ! i,ts ! i) \<in> (rstep S)\<^sup>*)"
    using nondef_root_imp_arg_steps[OF wrapped lhs fresh_top'] by simp
  then obtain ts where facts:
      "length ts = 1
        \<and> Fun top_sharp [t] = Fun top_sharp ts
        \<and> (\<forall>i<1. ([s] ! i,ts ! i) \<in> (rstep S)\<^sup>*)" ..
  then have len: "length ts = 1"
    and target: "Fun top_sharp [t] = Fun top_sharp ts"
    and args: "\<forall>i<1. ([s] ! i,ts ! i) \<in> (rstep S)\<^sup>*"
    by auto
  from len target have "ts = [t]" by auto
  with args show "(s,t) \<in> (rstep S)\<^sup>*" by simp
next
  assume step: "(s,t) \<in> (rstep S)\<^sup>*"
  have len: "length [s] = length [t]" by simp
  have args: "\<forall>i<length [s]. ([s] ! i,[t] ! i) \<in> (rstep S)\<^sup>*"
    using step by simp
  show "(Fun top_sharp [s], Fun top_sharp [t]) \<in> (rstep S)\<^sup>*"
    by (rule args_rsteps_imp_rsteps[OF len args])
qed

lemma gm04_non_top_role_wrapper_rsteps_iff:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and wf: "wf_trs S"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and role: "role = mark \<or> role = ok \<or> role = top_sym"
  shows "(Fun role [s], Fun role [t]) \<in> (rstep S)\<^sup>*
    \<longleftrightarrow> (s,t) \<in> (rstep S)\<^sup>*"
proof -
  have undefined: "\<not> defined S (role,1)"
    unfolding S by (rule gm04_non_top_role_not_defined[OF fresh role])
  show ?thesis by (rule gm04_top_wrapper_rsteps_iff[OF wf undefined])
qed

lemma gm04_q_top_wrapper_rsteps_iff:
  fixes S :: "('f,string) trs"
  assumes lhs_fun: "\<forall>(l,r)\<in>S. is_Fun l"
    and fresh_top: "\<not> defined S (top_sharp,1)"
  shows "(Fun top_sharp [s], Fun top_sharp [t])
      \<in> (qrstep nfs Q S)\<^sup>* \<longleftrightarrow>
    (s,t) \<in> (qrstep nfs Q S)\<^sup>*"
proof
  assume wrapped: "(Fun top_sharp [s], Fun top_sharp [t])
      \<in> (qrstep nfs Q S)\<^sup>*"
  have decomposition:
      "\<exists>ts. length ts = length [s]
        \<and> Fun top_sharp [t] = Fun top_sharp ts
        \<and> (\<forall>i<length [s]. ([s] ! i,ts ! i)
          \<in> (qrstep nfs Q S)\<^sup>*)"
  proof (rule nondef_root_imp_arg_qrsteps)
    show "(Fun top_sharp [s],Fun top_sharp [t])
        \<in> (qrstep nfs Q S)\<^sup>*" by (rule wrapped)
    show "\<forall>(l,r)\<in>S. is_Fun l" by (rule lhs_fun)
    show "\<not> defined S (top_sharp,length [s])" using fresh_top by simp
  qed
  from decomposition obtain ts where facts:
      "length ts = length [s]
        \<and> Fun top_sharp [t] = Fun top_sharp ts
        \<and> (\<forall>i<length [s]. ([s] ! i,ts ! i)
          \<in> (qrstep nfs Q S)\<^sup>*)" ..
  from facts have len: "length ts = 1"
    and target: "Fun top_sharp [t] = Fun top_sharp ts"
    and args: "\<forall>i<1. ([s] ! i,ts ! i)
      \<in> (qrstep nfs Q S)\<^sup>*" by simp_all
  from len target have "ts = [t]" by auto
  with args show "(s,t) \<in> (qrstep nfs Q S)\<^sup>*" by simp
next
  assume inner: "(s,t) \<in> (qrstep nfs Q S)\<^sup>*"
  have len: "length [s] = length [t]" by simp
  have args: "\<And>i. i < length [s] \<Longrightarrow>
      ([s] ! i,[t] ! i) \<in> (qrstep nfs Q S)\<^sup>*"
    using inner by simp
  from args_qrsteps_imp_qrsteps[OF len, of nfs Q S top_sharp] args
  show "(Fun top_sharp [s], Fun top_sharp [t])
      \<in> (qrstep nfs Q S)\<^sup>*" by simp
qed

fun gm04_phase_bit where
  "gm04_phase_bit active mark proper ok (Var x) = False"
| "gm04_phase_bit active mark proper ok (Fun f ts) =
    (if f = active \<or> f = mark then True
     else if f = proper \<or> f = ok then False
     else list_ex (gm04_phase_bit active mark proper ok) ts)"

lemma gm04_phase_bit_ctxt:
  fixes C :: "('f,'v) ctxt" and s t :: "('f,'v) term"
  assumes "gm04_phase_bit active mark proper ok s =
    gm04_phase_bit active mark proper ok t"
  shows "gm04_phase_bit active mark proper ok (C\<langle>s\<rangle>) =
    gm04_phase_bit active mark proper ok (C\<langle>t\<rangle>)"
  using assms by (induct C; auto)

lemma list_ex_update_true:
  fixes P :: "'a \<Rightarrow> bool" and xs :: "'a list"
  assumes i: "i < length xs" and val_true: "P v"
  shows "list_ex P (xs[i := v])"
proof -
  have "v \<in> set (xs[i := v])"
    using i by (rule set_update_memI)
  with val_true show ?thesis unfolding list_ex_iff by blast
qed

lemma gm04_phase_bit_update_active[intro]:
  assumes "i < length xs"
  shows "list_ex (gm04_phase_bit active mark proper ok)
    (xs[i := Fun active [t]])"
  by (rule list_ex_update_true[OF assms], simp)

lemma gm04_phase_bit_update_mark[intro]:
  assumes "i < length xs"
  shows "list_ex (gm04_phase_bit active mark proper ok)
    (xs[i := Fun mark [t]])"
  by (rule list_ex_update_true[OF assms], simp)

lemma gm04_phase_bit_map_proper[simp]:
  assumes "proper \<noteq> active" "proper \<noteq> mark"
  shows "\<not> list_ex (gm04_phase_bit active mark proper ok)
    (map (\<lambda>x. Fun proper [x]) xs)"
  using assms by (induct xs; simp)

lemma gm04_phase_bit_map_ok[simp]:
  assumes "ok \<noteq> active" "ok \<noteq> mark"
  shows "\<not> list_ex (gm04_phase_bit active mark proper ok)
    (map (\<lambda>x. Fun ok [x]) xs)"
  using assms by (induct xs; simp)

lemma gm04_phase_bit_map_proper_subst[simp]:
  assumes "proper \<noteq> active" "proper \<noteq> mark"
  shows "\<not> list_ex (gm04_phase_bit active mark proper ok)
    (map (\<lambda>x. Fun proper [\<sigma> x]) xs)"
  using assms by (induct xs; simp)

lemma gm04_phase_bit_map_ok_subst[simp]:
  assumes "ok \<noteq> active" "ok \<noteq> mark"
  shows "\<not> list_ex (gm04_phase_bit active mark proper ok)
    (map (\<lambda>x. Fun ok [\<sigma> x]) xs)"
  using assms by (induct xs; simp)

lemma gm04_source_rule_instance_preserves_phase_bit:
  assumes pair: "(l,r) \<in> set (gm04_source_rules active mark R)"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
  using pair unfolding gm04_source_rules_def
  by (auto split: prod.splits)

lemma gm04_active_rule_instance_preserves_phase_bit:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
proof -
  from pair obtain f n i where fn: "(f,n) \<in> set F" and i: "i < n"
    and lr: "(l,r) = gm04_active_rule active (f,n) i"
    unfolding gm04_active_rules_def by auto
  have f: "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
    using fresh fn unfolding gm04_roles_fresh_def by auto
  have len: "i < length (map \<sigma> (x\<^sub>1_to_x\<^sub>n n))"
    using i by simp
  have bit: "list_ex (gm04_phase_bit active mark proper ok)
      ((map \<sigma> (x\<^sub>1_to_x\<^sub>n n))[i :=
        Fun active [\<sigma> (x\<^sub>1_to_x\<^sub>n n ! i)]])"
    by (rule gm04_phase_bit_update_active[OF len])
  have nth: "map Var (x\<^sub>1_to_x\<^sub>n n) ! i \<cdot> \<sigma> =
      \<sigma> (x\<^sub>1_to_x\<^sub>n n ! i)"
    using i by (simp add: nth_map)
  from lr f bit nth show ?thesis
    unfolding gm04_active_rule_def gm04_vars_def
    by (simp add: Let_def nth_map map_update o_def)
qed

lemma gm04_mark_rule_instance_preserves_phase_bit:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
proof -
  from pair obtain f n i where fn: "(f,n) \<in> set F" and i: "i < n"
    and lr: "(l,r) = gm04_mark_rule mark (f,n) i"
    unfolding gm04_mark_rules_def by auto
  have f: "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
    using fresh fn unfolding gm04_roles_fresh_def by auto
  have len: "i < length (map \<sigma> (x\<^sub>1_to_x\<^sub>n n))"
    using i by simp
  have bit: "list_ex (gm04_phase_bit active mark proper ok)
      ((map \<sigma> (x\<^sub>1_to_x\<^sub>n n))[i :=
        Fun mark [\<sigma> (x\<^sub>1_to_x\<^sub>n n ! i)]])"
    by (rule gm04_phase_bit_update_mark[OF len])
  have nth: "map Var (x\<^sub>1_to_x\<^sub>n n) ! i \<cdot> \<sigma> =
      \<sigma> (x\<^sub>1_to_x\<^sub>n n ! i)"
    using i by (simp add: nth_map)
  from lr f bit nth show ?thesis
    unfolding gm04_mark_rule_def gm04_vars_def
    by (simp add: Let_def nth_map map_update o_def)
qed

lemma gm04_proper_rule_instance_preserves_phase_bit:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
  using pair fresh unfolding gm04_proper_rule_def gm04_vars_def
    gm04_roles_fresh_def
  by (auto simp: Let_def o_def split: prod.splits if_splits)

lemma gm04_ok_rule_instance_preserves_phase_bit:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (map (gm04_ok_rule proper ok)
      (filter (\<lambda>fn. snd fn > 0) F))"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
  using pair fresh unfolding gm04_ok_rule_def gm04_vars_def
    gm04_roles_fresh_def
  by (auto simp: Let_def o_def split: prod.splits if_splits)

lemma gm04_non_top_rule_instance_preserves_phase_bit:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
  shows "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
    gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
proof -
  from pair have cases:
      "(l,r) \<in> set (gm04_source_rules active mark R) \<or>
       (l,r) \<in> set (gm04_active_rules \<mu> active F) \<or>
       (l,r) \<in> set (gm04_mark_rules \<mu> mark F) \<or>
       (l,r) \<in> set (map (gm04_proper_rule proper ok) F) \<or>
       (l,r) \<in> set (map (gm04_ok_rule proper ok)
         (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  from cases show ?thesis
  proof (elim disjE)
    assume p: "(l,r) \<in> set (gm04_source_rules active mark R)"
    show ?thesis by (rule gm04_source_rule_instance_preserves_phase_bit[OF p])
  next
    assume p: "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    show ?thesis by (rule gm04_active_rule_instance_preserves_phase_bit[OF fresh p])
  next
    assume p: "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    show ?thesis by (rule gm04_mark_rule_instance_preserves_phase_bit[OF fresh p])
  next
    assume p: "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    show ?thesis by (rule gm04_proper_rule_instance_preserves_phase_bit[OF fresh p])
  next
    assume p: "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    show ?thesis by (rule gm04_ok_rule_instance_preserves_phase_bit[OF fresh p])
  qed
qed

lemma gm04_non_top_step_preserves_phase_bit:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and step: "(s,t) \<in> rstep S"
  shows "gm04_phase_bit active mark proper ok s =
    gm04_phase_bit active mark proper ok t"
proof -
  from step obtain C l r \<sigma> where pair: "(l,r) \<in> S"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by (cases rule: rstep.cases) auto
  have base: "gm04_phase_bit active mark proper ok (l \<cdot> \<sigma>) =
      gm04_phase_bit active mark proper ok (r \<cdot> \<sigma>)"
    by (rule gm04_non_top_rule_instance_preserves_phase_bit[
        OF fresh pair[unfolded S]])
  from gm04_phase_bit_ctxt[OF base, of C] show ?thesis
    unfolding s t .
qed

lemma gm04_non_top_steps_preserve_phase_bit:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and steps: "(s,t) \<in> (rstep S)\<^sup>*"
  shows "gm04_phase_bit active mark proper ok s =
    gm04_phase_bit active mark proper ok t"
  using steps
proof (induct rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yz: "gm04_phase_bit active mark proper ok y =
      gm04_phase_bit active mark proper ok z"
    by (rule gm04_non_top_step_preserves_phase_bit[OF S fresh step.hyps(2)])
  have sy: "gm04_phase_bit active mark proper ok s =
      gm04_phase_bit active mark proper ok y"
    by (rule step.hyps(3))
  also have "gm04_phase_bit active mark proper ok y =
      gm04_phase_bit active mark proper ok z"
    by (rule yz)
  finally show ?case .
qed

lemma gm04_non_top_cross_phases_impossible:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
  shows "(Fun active [x], Fun ok [y]) \<notin> (rstep S)\<^sup>*"
    and "(Fun proper [x], Fun mark [y]) \<notin> (rstep S)\<^sup>*"
proof -
  from fresh have roles: "distinct [active,mark,proper,ok,top_sym]"
    unfolding gm04_roles_fresh_def by simp
  from roles have neq: "ok \<noteq> active" "ok \<noteq> mark" "ok \<noteq> proper"
      "proper \<noteq> active" "proper \<noteq> mark"
    by auto
  have phase_active:
      "gm04_phase_bit active mark proper ok (Fun active [x]) = True"
  proof -
    have cond: "active = active \<or> active = mark"
      by (rule disjI1, rule refl)
    show ?thesis
      by (subst gm04_phase_bit.simps, subst if_P[OF cond], rule refl)
  qed
  have phase_ok:
      "gm04_phase_bit active mark proper ok (Fun ok [y]) = False"
  proof -
    have first: "\<not> (ok = active \<or> ok = mark)"
      using neq(1,2) by auto
    have second: "ok = proper \<or> ok = ok"
      by (rule disjI2, rule refl)
    show ?thesis
      by (subst gm04_phase_bit.simps, subst if_not_P[OF first],
          subst if_P[OF second], rule refl)
  qed
  have phase_proper:
      "gm04_phase_bit active mark proper ok (Fun proper [x]) = False"
  proof -
    have first: "\<not> (proper = active \<or> proper = mark)"
      using neq(4,5) by auto
    have second: "proper = proper \<or> proper = ok"
      by (rule disjI1, rule refl)
    show ?thesis
      by (subst gm04_phase_bit.simps, subst if_not_P[OF first],
          subst if_P[OF second], rule refl)
  qed
  have phase_mark:
      "gm04_phase_bit active mark proper ok (Fun mark [y]) = True"
  proof -
    have cond: "mark = active \<or> mark = mark"
      by (rule disjI2, rule refl)
    show ?thesis
      by (subst gm04_phase_bit.simps, subst if_P[OF cond], rule refl)
  qed
  show "(Fun active [x], Fun ok [y]) \<notin> (rstep S)\<^sup>*"
  proof
    assume steps: "(Fun active [x], Fun ok [y]) \<in> (rstep S)\<^sup>*"
    have "gm04_phase_bit active mark proper ok (Fun active [x]) =
        gm04_phase_bit active mark proper ok (Fun ok [y])"
      by (rule gm04_non_top_steps_preserve_phase_bit[OF S fresh steps])
    then have "True = False"
      by (simp only: phase_active phase_ok)
    then show False by simp
  qed
  show "(Fun proper [x], Fun mark [y]) \<notin> (rstep S)\<^sup>*"
  proof
    assume steps: "(Fun proper [x], Fun mark [y]) \<in> (rstep S)\<^sup>*"
    have "gm04_phase_bit active mark proper ok (Fun proper [x]) =
        gm04_phase_bit active mark proper ok (Fun mark [y])"
      by (rule gm04_non_top_steps_preserve_phase_bit[OF S fresh steps])
    then have "False = True"
      by (simp only: phase_proper phase_mark)
    then show False by simp
  qed
qed

corollary gm04_non_top_q_cross_phases_impossible:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
  shows "(Fun active [x], Fun ok [y])
      \<notin> (qrstep nfs Q S)\<^sup>*"
    and "(Fun proper [x], Fun mark [y])
      \<notin> (qrstep nfs Q S)\<^sup>*"
proof -
  show "(Fun active [x], Fun ok [y])
      \<notin> (qrstep nfs Q S)\<^sup>*"
  proof
    assume steps: "(Fun active [x], Fun ok [y])
        \<in> (qrstep nfs Q S)\<^sup>*"
    have rsteps: "(Fun active [x], Fun ok [y]) \<in> (rstep S)\<^sup>*"
      by (rule qrsteps_into_rsteps[OF steps])
    from gm04_non_top_cross_phases_impossible(1)[OF S fresh] rsteps
    show False by contradiction
  qed
  show "(Fun proper [x], Fun mark [y])
      \<notin> (qrstep nfs Q S)\<^sup>*"
  proof
    assume steps: "(Fun proper [x], Fun mark [y])
        \<in> (qrstep nfs Q S)\<^sup>*"
    have rsteps: "(Fun proper [x], Fun mark [y]) \<in> (rstep S)\<^sup>*"
      by (rule qrsteps_into_rsteps[OF steps])
    from gm04_non_top_cross_phases_impossible(2)[OF S fresh] rsteps
    show False by contradiction
  qed
qed

lemma gm04_complete_schema_rules_subset:
  assumes "gm04_complete_schema_check \<mu> active mark proper ok top_sym F R T"
  shows "set T \<subseteq> set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)"
  using assms unfolding gm04_complete_schema_check_def by auto

lemma gm04_complete_schema_rstep_subset:
  assumes schema:
    "gm04_complete_schema_check \<mu> active mark proper ok top_sym F R T"
  shows "rstep (set T) \<subseteq> rstep (set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R))"
  by (rule rstep_mono[OF gm04_complete_schema_rules_subset[OF schema]])

lemma gm04_complete_schema_SN_subset:
  assumes schema:
    "gm04_complete_schema_check \<mu> active mark proper ok top_sym F R T"
    and complete: "SN (rstep (set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R)))"
  shows "SN (rstep (set T))"
  by (rule SN_subset[OF complete
    gm04_complete_schema_rstep_subset[OF schema]])

lemma gm04_active_rule_shapes:
  assumes "i < snd fn"
  shows "fst (gm04_active_rule active fn i) =
      Fun active [Fun (fst fn) (gm04_vars (snd fn))]"
    and "snd (gm04_active_rule active fn i) =
      Fun (fst fn) ((gm04_vars (snd fn))
        [i := Fun active [(gm04_vars (snd fn)) ! i]])"
  using assms by (auto simp: gm04_active_rule_def Let_def)

lemma gm04_mark_rule_shapes:
  assumes "i < snd fn"
  shows "fst (gm04_mark_rule mark fn i) =
      Fun (fst fn) ((gm04_vars (snd fn))
        [i := Fun mark [(gm04_vars (snd fn)) ! i]])"
    and "snd (gm04_mark_rule mark fn i) =
      Fun mark [Fun (fst fn) (gm04_vars (snd fn))]"
  using assms by (auto simp: gm04_mark_rule_def Let_def)

text \<open>
  A big-step view of the active/mark phase.  Keeping this relation separate
  makes the semantic core of the checker independent of list generation and
  variable names.
\<close>

inductive_set gm04_search_step ::
  "('f \<times> nat \<Rightarrow> nat set) \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) term rel"
  for \<mu> and R
where
  root[intro]: "(l,r) \<in> R \<Longrightarrow>
    (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> gm04_search_step \<mu> R"
| descend[intro]: "i < length ts \<Longrightarrow> i \<in> \<mu> (f,length ts) \<Longrightarrow>
    (ts ! i,u) \<in> gm04_search_step \<mu> R \<Longrightarrow>
    (Fun f ts, Fun f (ts[i := u])) \<in> gm04_search_step \<mu> R"

lemma gm04_search_step_imp_csstep:
  assumes "(s,t) \<in> gm04_search_step \<mu> R"
  shows "(s,t) \<in> csstep \<mu> R"
  using assms
proof (induct rule: gm04_search_step.induct)
  case (root l r \<sigma>)
  have raw: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in>
      rstep_r_p_s R (l,r) [] \<sigma>"
    using root.hyps unfolding rstep_r_p_s_def' by auto
  show ?case
    unfolding csstep_def csstep_p_def
    using raw by (auto simp: csstep_cond_def)
next
  case (descend i ts f u)
  from descend.hyps(4) obtain p lr \<sigma> where raw:
      "(ts ! i,u) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (ts ! i)"
    unfolding csstep_def csstep_p_def by auto
  have raw': "(Fun f ts, Fun f (ts[i := u])) \<in>
      rstep_r_p_s R lr (i # p) \<sigma>"
    using raw descend.hyps(1)
    unfolding rstep_r_p_s_def'
    by (auto simp: ctxt_of_pos_term.simps
      upd_conv_take_nth_drop[OF descend.hyps(1)])
  have cond': "csstep_cond \<mu> (i # p) (Fun f ts)"
    by (rule csstep_cond_Cons_FunI[
      OF descend.hyps(1) descend.hyps(2) cond])
  show ?case
    unfolding csstep_def csstep_p_def using raw' cond' by blast
qed

lemma csstep_imp_gm04_search_step:
  assumes "(s,t) \<in> csstep \<mu> R"
  shows "(s,t) \<in> gm04_search_step \<mu> R"
proof -
  from assms obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_def csstep_p_def by auto
  from raw cond show ?thesis
  proof (induct p arbitrary: s t)
    case Nil
    then obtain l r where lr: "lr = (l,r)" by (cases lr) auto
    from Nil.prems show ?case
      unfolding rstep_r_p_s_def' lr by auto
  next
    case (Cons i p)
    from Cons.prems obtain f ts where s: "s = Fun f ts"
      and i: "i < length ts"
      and pp: "p \<in> poss (ts ! i)"
      and lr: "lr \<in> R"
      and lhs: "ts ! i |_ p = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (take i ts @
        (ctxt_of_pos_term p (ts ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle> #
        drop (Suc i) ts)"
      unfolding rstep_r_p_s_def'
      by (cases s; auto simp: nth_mem)
    let ?u = "(ctxt_of_pos_term p (ts ! i))\<langle>snd lr \<cdot> \<sigma>\<rangle>"
    have sub: "(ts ! i, ?u) \<in> rstep_r_p_s R lr p \<sigma>"
      using pp lr lhs unfolding rstep_r_p_s_def' by auto
    have ip: "i # p \<in> poss (Fun f ts)" using i pp by simp
    have active: "i \<in> \<mu> (f,length ts)"
      by (rule csstep_cond_Cons_FunD(1)[
        OF Cons.prems(2)[unfolded s] ip])
    have sub_cond: "csstep_cond \<mu> p (ts ! i)"
      by (rule csstep_cond_Cons_FunD(2)[
        OF Cons.prems(2)[unfolded s] ip])
    from Cons.hyps[OF sub sub_cond]
    have search: "(ts ! i, ?u) \<in> gm04_search_step \<mu> R" .
    have update: "ts[i := ?u] = take i ts @ ?u # drop (Suc i) ts"
      by (rule upd_conv_take_nth_drop[OF i])
    from gm04_search_step.descend[OF i active search] t s update
    show ?case by simp
  qed
qed

theorem gm04_search_step_iff_csstep:
  "gm04_search_step \<mu> R = csstep \<mu> R"
  by (intro equalityI; auto intro: gm04_search_step_imp_csstep
    csstep_imp_gm04_search_step)

fun gm04_erase where
  "gm04_erase W (Var x) = Var x"
| "gm04_erase W (Fun f ts) =
    (if f \<in> W \<and> length ts = 1 then gm04_erase W (hd ts)
     else Fun f (map (gm04_erase W) ts))"

lemma gm04_erase_wrapper[simp]:
  "w \<in> W \<Longrightarrow> gm04_erase W (Fun w [t]) = gm04_erase W t"
  by simp

lemma gm04_erase_source_fun[simp]:
  "f \<notin> W \<Longrightarrow>
    gm04_erase W (Fun f ts) = Fun f (map (gm04_erase W) ts)"
  by simp

lemma gm04_funas_erase_roles:
  assumes fresh: "\<And>w n. w \<in> W \<Longrightarrow> (w,n) \<notin> F"
    and sig: "funas_term t \<subseteq> F \<union> {(w,1) |w. w \<in> W}"
  shows "funas_term (gm04_erase W t) \<subseteq> F"
  using sig
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  show ?case
  proof (cases "f \<in> W \<and> length ts = 1")
    case True
    then obtain u where ts: "ts = [u]" by (cases ts, auto)
    from Fun.prems ts have usig:
        "funas_term u \<subseteq> F \<union> {(w,1) |w. w \<in> W}"
      by auto
    from ts have member: "u \<in> set ts" by simp
    have ih: "funas_term u \<subseteq> F \<union> {(w,1) |w. w \<in> W} \<Longrightarrow>
        funas_term (gm04_erase W u) \<subseteq> F"
      by (rule Fun.hyps[OF member])
    have erased: "funas_term (gm04_erase W u) \<subseteq> F"
      by (rule ih[OF usig])
    from erased True ts show ?thesis by simp
  next
    case False
    have fn: "(f,length ts) \<in> F"
    proof -
      from Fun.prems have "(f,length ts) \<in> F \<union> {(w,1) |w. w \<in> W}"
        by simp
      with False fresh show ?thesis by auto
    qed
    have args: "\<And>u. u \<in> set ts \<Longrightarrow>
        funas_term (gm04_erase W u) \<subseteq> F"
    proof -
      fix u
      assume u: "u \<in> set ts"
      from Fun.prems u have usig:
          "funas_term u \<subseteq> F \<union> {(w,1) |w. w \<in> W}"
        by auto
      show "funas_term (gm04_erase W u) \<subseteq> F"
        by (rule Fun.hyps[OF u usig])
    qed
    from False fn args show ?thesis by auto
  qed
qed

lemma gm04_SN_sig_csstep_trancl:
  assumes source: "SN (sig_step F (csstep \<mu> R))"
    and signature: "funas_trs R \<subseteq> F"
    and wf: "wf_trs R"
  shows "SN (sig_step F ((csstep \<mu> R)\<^sup>+))"
proof -
  have preserve: "\<And>s t. funas_term s \<subseteq> F \<Longrightarrow>
      (s,t) \<in> csstep \<mu> R \<Longrightarrow> funas_term t \<subseteq> F"
  proof -
    fix s t
    assume s: "funas_term s \<subseteq> F" and step: "(s,t) \<in> csstep \<mu> R"
    from csstep_subset_rstep[THEN subsetD, OF step]
    show "funas_term t \<subseteq> F"
      by (rule rstep_preserves_funas_terms[OF signature s _ wf])
  qed
  have "SN ((sig_step F (csstep \<mu> R))\<^sup>+)"
    by (rule SN_imp_SN_trancl[OF source])
  then show ?thesis
    by (simp only: sig_trancl[OF preserve])
qed

lemma gm04_erase_ctxt_cong:
  fixes C :: "('f,'v) ctxt"
  assumes "gm04_erase W s = gm04_erase W t"
  shows "gm04_erase W (C\<langle>s\<rangle>) = gm04_erase W (C\<langle>t\<rangle>)"
  using assms
proof (induct C)
  case Hole
  then show ?case by simp
next
  case (More f bef C aft)
  then show ?case
    by (cases "f \<in> W \<and> length (bef @ C\<langle>s\<rangle> # aft) = 1";
        auto simp: nth_append)
qed

lemma gm04_erase_update:
  "map (gm04_erase W) (ts[i := u]) =
    (map (gm04_erase W) ts)[i := gm04_erase W u]"
  by (rule map_update)

lemma gm04_erase_subst_source:
  assumes source: "\<And>f n. (f,n) \<in> funas_term t \<Longrightarrow> f \<notin> W"
  shows "gm04_erase W (t \<cdot> \<sigma>) =
    t \<cdot> (\<lambda>x. gm04_erase W (\<sigma> x))"
  using source
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have f: "f \<notin> W"
    by (rule Fun.prems[of f "length ts"], simp)
  have args: "map (gm04_erase W) (map (\<lambda>t. t \<cdot> \<sigma>) ts) =
      map (\<lambda>t. t \<cdot> (\<lambda>x. gm04_erase W (\<sigma> x))) ts"
    unfolding map_map o_def
  proof (rule map_cong[OF refl])
    fix u
    assume u: "u \<in> set ts"
    show "gm04_erase W (u \<cdot> \<sigma>) =
        u \<cdot> (\<lambda>x. gm04_erase W (\<sigma> x))"
      by (rule Fun.hyps[OF u], use Fun.prems u in auto)
  qed
  show ?case using f args by simp
qed

corollary gm04_erase_subst_fresh_source:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "funas_term t \<subseteq> set F"
  shows "gm04_erase {active,mark,proper,ok} (t \<cdot> \<sigma>) =
    t \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x))"
proof (rule gm04_erase_subst_source)
  fix f n
  assume "(f,n) \<in> funas_term t"
  with source have "(f,n) \<in> set F" by blast
  with fresh show "f \<notin> {active,mark,proper,ok}"
    unfolding gm04_roles_fresh_def by auto
qed

lemma gm04_source_rule_instance_erases_to_csstep:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and pair: "(l,r) \<in> set (gm04_source_rules active mark R)"
  shows "(gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>),
      gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>))
      \<in> csstep \<mu> (set R)"
proof -
  from pair obtain l0 r0 where lr: "(l0,r0) \<in> set R"
    and pair: "(l,r) = (Fun active [l0],Fun mark [r0])"
    unfolding gm04_source_rules_def by auto
  have lhs_sig: "funas_term l0 \<subseteq> set F"
    and rhs_sig: "funas_term r0 \<subseteq> set F"
    using signature lr unfolding funas_trs_def
    by (force simp: funas_rule_def)+
  have lhs: "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
      l0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x))"
  proof -
    have erased: "gm04_erase {active,mark,proper,ok} (l0 \<cdot> \<sigma>) =
        l0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x))"
      by (rule gm04_erase_subst_fresh_source[OF fresh lhs_sig])
    from pair erased show ?thesis by simp
  qed
  have rhs: "gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>) =
      r0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x))"
  proof -
    have erased: "gm04_erase {active,mark,proper,ok} (r0 \<cdot> \<sigma>) =
        r0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x))"
      by (rule gm04_erase_subst_fresh_source[OF fresh rhs_sig])
    from pair erased show ?thesis by simp
  qed
  have "(l0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x)),
      r0 \<cdot> (\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x)))
      \<in> gm04_search_step \<mu> (set R)"
    by (rule gm04_search_step.root[OF lr])
  then show ?thesis unfolding lhs rhs gm04_search_step_iff_csstep .
qed

lemma gm04_active_rule_instance_preserves_erase:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
  shows "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
proof -
  from pair obtain f n i where fn: "(f,n) \<in> set F" and i: "i < n"
    and lr: "(l,r) = gm04_active_rule active (f,n) i"
    unfolding gm04_active_rules_def by auto
  from fresh fn have f: "f \<notin> {active,mark,proper,ok}"
    unfolding gm04_roles_fresh_def by auto
  have ilen: "i < length (x\<^sub>1_to_x\<^sub>n n)" using i by simp
  let ?es = "\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x)"
  have nth: "map ?es (x\<^sub>1_to_x\<^sub>n n) ! i = ?es (x\<^sub>1_to_x\<^sub>n n ! i)"
    by (rule nth_map[OF ilen])
  have update: "(map ?es (x\<^sub>1_to_x\<^sub>n n))[i := ?es (x\<^sub>1_to_x\<^sub>n n ! i)] =
      map ?es (x\<^sub>1_to_x\<^sub>n n)"
    unfolding nth[symmetric] by (rule list_update_id)
  from lr f i update show ?thesis
    unfolding gm04_active_rule_def gm04_vars_def
    by (simp add: Let_def nth_map map_update gm04_erase_update o_def)
qed

lemma gm04_mark_rule_instance_preserves_erase:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
  shows "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
proof -
  from pair obtain f n i where fn: "(f,n) \<in> set F" and i: "i < n"
    and lr: "(l,r) = gm04_mark_rule mark (f,n) i"
    unfolding gm04_mark_rules_def by auto
  from fresh fn have f: "f \<notin> {active,mark,proper,ok}"
    unfolding gm04_roles_fresh_def by auto
  have ilen: "i < length (x\<^sub>1_to_x\<^sub>n n)" using i by simp
  let ?es = "\<lambda>x. gm04_erase {active,mark,proper,ok} (\<sigma> x)"
  have nth: "map ?es (x\<^sub>1_to_x\<^sub>n n) ! i = ?es (x\<^sub>1_to_x\<^sub>n n ! i)"
    by (rule nth_map[OF ilen])
  have update: "(map ?es (x\<^sub>1_to_x\<^sub>n n))[i := ?es (x\<^sub>1_to_x\<^sub>n n ! i)] =
      map ?es (x\<^sub>1_to_x\<^sub>n n)"
    unfolding nth[symmetric] by (rule list_update_id)
  from lr f i update show ?thesis
    unfolding gm04_mark_rule_def gm04_vars_def
    by (simp add: Let_def nth_map map_update gm04_erase_update o_def)
qed

lemma gm04_proper_rule_instance_preserves_erase:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
  shows "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
  using pair fresh unfolding gm04_proper_rule_def gm04_vars_def
    gm04_roles_fresh_def
  by (auto simp: Let_def o_def split: prod.splits if_splits)

lemma gm04_ok_rule_instance_preserves_erase:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and pair: "(l,r) \<in> set (map (gm04_ok_rule proper ok)
      (filter (\<lambda>fn. snd fn > 0) F))"
  shows "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
  using pair fresh unfolding gm04_ok_rule_def gm04_vars_def
    gm04_roles_fresh_def
  by (auto simp: Let_def o_def split: prod.splits if_splits)

lemma gm04_administrative_rule_instance_preserves_erase:
  assumes pair: "(l,r) \<in> set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and not_source: "(l,r) \<notin> set (gm04_source_rules active mark R)"
    and not_active: "(l,r) \<notin> set (gm04_active_rules \<mu> active F)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
  shows "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
proof -
  from pair not_source not_active consider
      (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  then show ?thesis
  proof cases
    case mark
    show ?thesis by (rule gm04_mark_rule_instance_preserves_erase[OF fresh mark])
  next
    case proper
    show ?thesis by (rule gm04_proper_rule_instance_preserves_erase[OF fresh proper])
  next
    case ok
    show ?thesis by (rule gm04_ok_rule_instance_preserves_erase[OF fresh ok])
  qed
qed

lemma gm04_administrative_rhs_has_no_active:
  assumes pair: "(l,r) \<in> set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and not_source: "(l,r) \<notin> set (gm04_source_rules active mark R)"
    and not_active: "(l,r) \<notin> set (gm04_active_rules \<mu> active F)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
  shows "\<And>n. (active,n) \<notin> funas_term r"
proof -
  fix n
  from pair not_source not_active consider
      (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  then show "(active,n) \<notin> funas_term r"
  proof cases
    case mark
    then show ?thesis using fresh
      unfolding gm04_mark_rules_def gm04_mark_rule_def gm04_vars_def
        gm04_roles_fresh_def
      by (auto simp: Let_def split: prod.splits)
  next
    case proper
    then show ?thesis using fresh
      unfolding gm04_proper_rule_def gm04_vars_def gm04_roles_fresh_def
      by (auto simp: Let_def split: prod.splits if_splits)
  next
    case ok
    then show ?thesis using fresh
      unfolding gm04_ok_rule_def gm04_vars_def gm04_roles_fresh_def
      by (auto simp: Let_def split: prod.splits if_splits)
  qed
qed

inductive gm04_focus ::
  "('f \<times> nat \<Rightarrow> nat set) \<Rightarrow> 'f \<Rightarrow>
    ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
  for \<mu> and wrap
where
  root[intro]: "gm04_focus \<mu> wrap s (Fun wrap [s])"
| descend[intro]: "i < length ts \<Longrightarrow> i \<in> \<mu> (f,length ts) \<Longrightarrow>
    gm04_focus \<mu> wrap (ts ! i) u \<Longrightarrow>
    gm04_focus \<mu> wrap (Fun f ts) (Fun f (ts[i := u]))"

lemma gm04_focus_fun_cases:
  assumes "gm04_focus \<mu> wrap (Fun f ts) u"
  obtains (root) "u = Fun wrap [Fun f ts]"
    | (descend) i v where "i < length ts" "i \<in> \<mu> (f,length ts)"
        "gm04_focus \<mu> wrap (ts ! i) v"
        "u = Fun f (ts[i := v])"
  using assms by (cases rule: gm04_focus.cases) auto

lemma gm04_focus_var_cases:
  assumes "gm04_focus \<mu> wrap (Var x) u"
  shows "u = Fun wrap [Var x]"
  using assms by (cases rule: gm04_focus.cases) auto

lemma gm04_focus_has_single_wrapper:
  assumes focus: "gm04_focus \<mu> wrap s u"
  shows "(wrap,1) \<in> funas_term u"
  using focus
proof induct
  case (root s)
  then show ?case by simp
next
  case (descend i ts f u)
  have nth_member: "(ts[i := u]) ! i \<in> set (ts[i := u])"
    by (rule nth_mem, simp only: length_list_update descend.hyps(1))
  have member: "u \<in> set (ts[i := u])"
    using nth_member descend.hyps(1) by (simp only: nth_list_update_eq)
  have unionmem: "(wrap,1) \<in>
      \<Union>(funas_term ` set (args (Fun f (ts[i := u]))))"
    using member descend.hyps(4) by auto
  from subsetD[OF funas_term_args unionmem] show ?case .
qed

lemma gm04_rule_instance_rstep:
  assumes "(l,r) \<in> S"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep S"
proof -
  have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rrstep S"
    using assms unfolding rrstep_def' by blast
  then show ?thesis unfolding rstep_iff_rrstep_or_nrrstep by auto
qed

lemma gm04_vars_instance:
  fixes ts :: "('f,string) term list"
  assumes len: "length ts = n"
  shows "\<exists>\<sigma>. map (\<lambda>t. t \<cdot> \<sigma>) (gm04_vars n) = ts"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have "map (\<lambda>t. t \<cdot> ?\<sigma>) (map Var ?vs) = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  then show ?thesis unfolding gm04_vars_def by blast
qed

lemma gm04_active_rule_instance:
  fixes S :: "('f,string) trs"
  assumes rule: "gm04_active_rule active (f,length ts) i \<in> S"
    and pos: "i < length ts"
  shows "(Fun active [Fun f ts],
      Fun f (ts[i := Fun active [ts ! i]])) \<in> rstep S"
proof -
  from gm04_vars_instance[OF refl, of ts] obtain \<sigma> where inst:
      "map (\<lambda>t. t \<cdot> \<sigma>) (gm04_vars (length ts)) = ts" by blast
  have pair: "(fst (gm04_active_rule active (f,length ts) i),
      snd (gm04_active_rule active (f,length ts) i)) \<in> S"
    using rule by simp
  have step: "(fst (gm04_active_rule active (f,length ts) i) \<cdot> \<sigma>,
      snd (gm04_active_rule active (f,length ts) i) \<cdot> \<sigma>) \<in> rstep S"
    by (rule gm04_rule_instance_rstep[OF pair])
  have nth: "gm04_vars (length ts) ! i \<cdot> \<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] pos by simp
  from step
  show ?thesis
    using inst pos nth
    by (simp add: gm04_active_rule_def Let_def nth_map map_update)
qed

lemma gm04_mark_rule_instance:
  fixes S :: "('f,string) trs"
  assumes rule: "gm04_mark_rule mark (f,length ts) i \<in> S"
    and pos: "i < length ts"
  shows "(Fun f (ts[i := Fun mark [ts ! i]]),
      Fun mark [Fun f ts]) \<in> rstep S"
proof -
  from gm04_vars_instance[OF refl, of ts] obtain \<sigma> where inst:
      "map (\<lambda>t. t \<cdot> \<sigma>) (gm04_vars (length ts)) = ts" by blast
  have pair: "(fst (gm04_mark_rule mark (f,length ts) i),
      snd (gm04_mark_rule mark (f,length ts) i)) \<in> S"
    using rule by simp
  have step: "(fst (gm04_mark_rule mark (f,length ts) i) \<cdot> \<sigma>,
      snd (gm04_mark_rule mark (f,length ts) i) \<cdot> \<sigma>) \<in> rstep S"
    by (rule gm04_rule_instance_rstep[OF pair])
  have nth: "gm04_vars (length ts) ! i \<cdot> \<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] pos by simp
  from step
  show ?thesis
    using inst pos nth
    by (simp add: gm04_mark_rule_def Let_def nth_map map_update)
qed

lemma gm04_proper_rule_instance:
  fixes S :: "('f,string) trs"
  assumes rule: "gm04_proper_rule proper ok (f,length ts) \<in> S"
  shows "(Fun proper [Fun f ts],
      if ts = [] then Fun ok [Fun f []]
      else Fun f (map (\<lambda>t. Fun proper [t]) ts)) \<in> rstep S"
proof -
  from gm04_vars_instance[OF refl, of ts] obtain \<sigma> where inst:
      "map (\<lambda>t. t \<cdot> \<sigma>) (gm04_vars (length ts)) = ts" by blast
  have pair: "(fst (gm04_proper_rule proper ok (f,length ts)),
      snd (gm04_proper_rule proper ok (f,length ts))) \<in> S"
    using rule by simp
  have wrapped: "map (\<lambda>x. Fun proper [x \<cdot> \<sigma>])
      (gm04_vars (length ts)) = map (\<lambda>t. Fun proper [t]) ts"
    using arg_cong[OF inst, of "map (\<lambda>t. Fun proper [t])"]
    by (simp add: o_def)
  from gm04_rule_instance_rstep[OF pair, of \<sigma>] inst wrapped
  show ?thesis
    by (cases ts; simp add: gm04_proper_rule_def Let_def o_def)
qed

lemma gm04_ok_rule_instance:
  fixes S :: "('f,string) trs"
  assumes rule: "gm04_ok_rule proper ok (f,length ts) \<in> S"
    and nonempty: "ts \<noteq> []"
  shows "(Fun f (map (\<lambda>t. Fun ok [t]) ts),
      Fun ok [Fun f ts]) \<in> rstep S"
proof -
  from gm04_vars_instance[OF refl, of ts] obtain \<sigma> where inst:
      "map (\<lambda>t. t \<cdot> \<sigma>) (gm04_vars (length ts)) = ts" by blast
  have pair: "(fst (gm04_ok_rule proper ok (f,length ts)),
      snd (gm04_ok_rule proper ok (f,length ts))) \<in> S"
    using rule by simp
  have wrapped: "map (\<lambda>x. Fun ok [x \<cdot> \<sigma>])
      (gm04_vars (length ts)) = map (\<lambda>t. Fun ok [t]) ts"
    using arg_cong[OF inst, of "map (\<lambda>t. Fun ok [t])"]
    by (simp add: o_def)
  from gm04_rule_instance_rstep[OF pair, of \<sigma>] inst wrapped nonempty
  show ?thesis
    by (simp add: gm04_ok_rule_def Let_def o_def)
qed

definition gm04_source_term where
  "gm04_source_term F t \<longleftrightarrow> ground t \<and> funas_term t \<subseteq> set F"

lemma gm04_source_signature_no_non_top_step:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "funas_term t \<subseteq> set F"
  shows "\<nexists>u. (t,u) \<in> rstep S"
proof
  assume "\<exists>u. (t,u) \<in> rstep S"
  then obtain u where step: "(t,u) \<in> rstep S" ..
  from step obtain C l r \<sigma> where pair: "(l,r) \<in> S"
    and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>"
    by (cases rule: rstep.cases) auto
  from gm04_non_top_lhs_contains_role[OF pair[unfolded S], of top_sym]
  obtain w n where role: "w \<in>
      gm04_role_symbols active mark proper ok top_sym"
    and lhs0: "(w,n) \<in> funas_term (fst (l,r))" by blast
  from lhs0 have lhs: "(w,n) \<in> funas_term l" by simp
  from lhs have inst: "(w,n) \<in> funas_term (l \<cdot> \<sigma>)"
    unfolding funas_term_subst by blast
  have "funas_term (l \<cdot> \<sigma>) \<subseteq> funas_term t"
    unfolding t funas_term_ctxt_apply by blast
  with inst source have in_F: "(w,n) \<in> set F"
    by blast
  have notin_F: "(w,n) \<notin> set F"
    by (rule gm04_role_not_source_signature[OF fresh role])
  from in_F notin_F show False by contradiction
qed

lemma gm04_source_term_no_non_top_step:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "gm04_source_term F t"
  shows "\<nexists>u. (t,u) \<in> rstep S"
  by (rule gm04_source_signature_no_non_top_step[OF S fresh],
      use source in \<open>simp add: gm04_source_term_def\<close>)

text \<open>
  Lemma 25 of Giesl--Middeldorp, in its constructive direction: every ground
  source term passes through the administrative proper/ok phase.  The proof
  is signature-generic; no source symbol name or arity is built in.
\<close>

lemma gm04_proper_ok_phase:
  fixes S :: "('f,string) trs"
  assumes proper_rules: "\<And>fn. fn \<in> set F \<Longrightarrow>
      gm04_proper_rule proper ok fn \<in> S"
    and ok_rules: "\<And>fn. fn \<in> set F \<Longrightarrow> snd fn > 0 \<Longrightarrow>
      gm04_ok_rule proper ok fn \<in> S"
    and source: "gm04_source_term F t"
  shows "(Fun proper [t], Fun ok [t]) \<in> (rstep S)\<^sup>+"
  using source
proof (induct t)
  case (Var x)
  then show ?case by (simp add: gm04_source_term_def)
next
  case (Fun f ts)
  from Fun.prems have ground: "ground (Fun f ts)"
    and sig: "funas_term (Fun f ts) \<subseteq> set F"
    unfolding gm04_source_term_def by auto
  have fn: "(f,length ts) \<in> set F" using sig by simp
  show ?case
  proof (cases "ts = []")
    case True
    from gm04_proper_rule_instance[OF proper_rules[OF fn]] True
    show ?thesis by (simp add: r_into_trancl)
  next
    case False
    have arg_source: "\<And>u. u \<in> set ts \<Longrightarrow> gm04_source_term F u"
      using ground sig unfolding gm04_source_term_def by auto
    have arg_steps: "\<And>i. i < length ts \<Longrightarrow>
        (Fun proper [ts ! i], Fun ok [ts ! i]) \<in> (rstep S)\<^sup>*"
    proof -
      fix i
      assume i: "i < length ts"
      from Fun.hyps[OF nth_mem[OF i] arg_source[OF nth_mem[OF i]]]
      show "(Fun proper [ts ! i], Fun ok [ts ! i]) \<in> (rstep S)\<^sup>*"
        by (rule trancl_into_rtrancl)
    qed
    have first: "(Fun proper [Fun f ts],
        Fun f (map (\<lambda>u. Fun proper [u]) ts)) \<in> rstep S"
      using gm04_proper_rule_instance[OF proper_rules[OF fn]] False
      by simp
    have middle: "(Fun f (map (\<lambda>u. Fun proper [u]) ts),
        Fun f (map (\<lambda>u. Fun ok [u]) ts)) \<in> (rstep S)\<^sup>*"
    proof (rule args_rsteps_imp_rsteps)
      show "length (map (\<lambda>u. Fun proper [u]) ts) =
          length (map (\<lambda>u. Fun ok [u]) ts)" by simp
      show "\<forall>i<length (map (\<lambda>u. Fun proper [u]) ts).
          ((map (\<lambda>u. Fun proper [u]) ts) ! i,
           (map (\<lambda>u. Fun ok [u]) ts) ! i) \<in> (rstep S)\<^sup>*"
        using arg_steps by auto
    qed
    have positive: "snd (f,length ts) > 0" using False by simp
    have last: "(Fun f (map (\<lambda>u. Fun ok [u]) ts),
        Fun ok [Fun f ts]) \<in> rstep S"
      by (rule gm04_ok_rule_instance[OF ok_rules[OF fn positive] False])
    from r_into_trancl[OF first]
      rtrancl_into_trancl1[OF middle last]
    show ?thesis by (rule trancl_trans)
  qed
qed

text \<open>
  One complete active/mark phase simulates exactly one source CS step in the
  forward direction.  The assumptions are deliberately phrased as rule
  membership: the executable checker will discharge them after comparing the
  submitted TRS with the generated schema.
\<close>

lemma gm04_search_step_simulation:
  fixes S :: "('f,string) trs"
  assumes source_rules: "\<And>l r. (l,r) \<in> R \<Longrightarrow>
      (Fun active [l], Fun mark [r]) \<in> S"
    and active_rules: "\<And>f (ts :: ('f,string) term list) i. i < length ts \<Longrightarrow>
      i \<in> \<mu> (f,length ts) \<Longrightarrow>
      gm04_active_rule active (f,length ts) i \<in> S"
    and mark_rules: "\<And>f (ts :: ('f,string) term list) i. i < length ts \<Longrightarrow>
      i \<in> \<mu> (f,length ts) \<Longrightarrow>
      gm04_mark_rule mark (f,length ts) i \<in> S"
    and search: "(s,t) \<in> gm04_search_step \<mu> R"
  shows "(Fun active [s], Fun mark [t]) \<in> (rstep S)\<^sup>+"
  using search
proof induct
  case (root l r \<sigma>)
  have rule: "(Fun active [l], Fun mark [r]) \<in> S"
    by (rule source_rules[OF root.hyps])
  from gm04_rule_instance_rstep[OF rule, of \<sigma>]
  show ?case by simp
next
  case (descend i ts f u)
  let ?A = "Fun f (ts[i := Fun active [ts ! i]])"
  let ?M = "Fun f (ts[i := Fun mark [u]])"
  let ?C = "More f (take i ts) \<box> (drop (Suc i) ts)"
  have first: "(Fun active [Fun f ts], ?A) \<in> rstep S"
    by (rule gm04_active_rule_instance[OF
      active_rules[OF descend.hyps(1) descend.hyps(2)] descend.hyps(1)])
  from trancl_rstep_ctxt[OF descend.hyps(4), of ?C]
  have middle: "(?A, ?M) \<in> (rstep S)\<^sup>+"
    using descend.hyps(1)
    by (simp add: upd_conv_take_nth_drop)
  have last0: "(Fun f ((ts[i := u])
        [i := Fun mark [(ts[i := u]) ! i]]),
      Fun mark [Fun f (ts[i := u])]) \<in> rstep S"
    by (rule gm04_mark_rule_instance[OF _ _],
      simp_all add: descend.hyps(1) descend.hyps(2) mark_rules)
  have last: "(?M, Fun mark [Fun f (ts[i := u])]) \<in> rstep S"
    using last0 descend.hyps(1) by simp
  from r_into_trancl[OF first] middle
  have prefix: "(Fun active [Fun f ts], ?M) \<in> (rstep S)\<^sup>+"
    by (rule trancl_trans)
  from prefix r_into_trancl[OF last]
  show ?case by (rule trancl_trans)
qed

corollary gm04_csstep_simulation:
  fixes S :: "('f,string) trs"
  assumes source_rules: "\<And>l r. (l,r) \<in> R \<Longrightarrow>
      (Fun active [l], Fun mark [r]) \<in> S"
    and active_rules: "\<And>f (ts :: ('f,string) term list) i. i < length ts \<Longrightarrow>
      i \<in> \<mu> (f,length ts) \<Longrightarrow>
      gm04_active_rule active (f,length ts) i \<in> S"
    and mark_rules: "\<And>f (ts :: ('f,string) term list) i. i < length ts \<Longrightarrow>
      i \<in> \<mu> (f,length ts) \<Longrightarrow>
      gm04_mark_rule mark (f,length ts) i \<in> S"
    and step: "(s,t) \<in> csstep \<mu> R"
  shows "(Fun active [s], Fun mark [t]) \<in> (rstep S)\<^sup>+"
proof -
  have search: "(s,t) \<in> gm04_search_step \<mu> R"
    using step unfolding gm04_search_step_iff_csstep .
  show ?thesis
    by (rule gm04_search_step_simulation[OF source_rules active_rules
      mark_rules search])
qed

lemma gm04_search_step_complete_simulation:
  fixes R :: "('f::countable,string) rules"
  assumes finite_mu: "\<And>fn. finite (\<mu> fn)"
    and signature: "funas_term s \<subseteq> set F"
    and search: "(s,t) \<in> gm04_search_step \<mu> (set R)"
  shows "(Fun active [s],Fun mark [t]) \<in>
    (rstep (set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R)))\<^sup>+"
  using search signature
proof induct
  case (root l r \<sigma>)
  have rule: "(Fun active [l],Fun mark [r]) \<in>
      set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)"
    using root.hyps unfolding gm04_complete_rules_def
      gm04_non_top_rules_def gm04_source_rules_def by auto
  from gm04_rule_instance_rstep[OF rule, of \<sigma>]
  show ?case by (simp add: r_into_trancl)
next
  case (descend i ts f u)
  let ?S = "set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)"
  let ?A = "Fun f (ts[i := Fun active [ts ! i]])"
  let ?M = "Fun f (ts[i := Fun mark [u]])"
  let ?C = "More f (take i ts) \<box> (drop (Suc i) ts)"
  from descend.prems have fn: "(f,length ts) \<in> set F" by simp
  have i_sorted: "i \<in> set (sorted_list_of_set (\<mu> (f,length ts)))"
    using descend.hyps(2) finite_mu[of "(f,length ts)"] by simp
  have active_inner: "gm04_active_rule active (f,length ts) i \<in>
      set (map (gm04_active_rule active (f,length ts))
        (filter (\<lambda>j. j < length ts)
          (sorted_list_of_set (\<mu> (f,length ts)))))"
    using descend.hyps(1) i_sorted by simp
  let ?active_for_fn = "map (gm04_active_rule active (f,length ts))
    (filter (\<lambda>j. j < length ts)
      (sorted_list_of_set (\<mu> (f,length ts))))"
  have active_outer: "?active_for_fn \<in> set (map (\<lambda>fn.
      map (gm04_active_rule active fn)
        (filter (\<lambda>j. j < snd fn) (sorted_list_of_set (\<mu> fn)))) F)"
    using fn by force
  have active_union: "gm04_active_rule active (f,length ts) i \<in>
      (\<Union>xs\<in>set (map (\<lambda>fn.
        map (gm04_active_rule active fn)
          (filter (\<lambda>j. j < snd fn) (sorted_list_of_set (\<mu> fn)))) F).
        set xs)"
    using active_outer active_inner by blast
  have active_local: "gm04_active_rule active (f,length ts) i \<in>
      set (gm04_active_rules \<mu> active F)"
    using active_union unfolding gm04_active_rules_def by simp
  have active_rule: "gm04_active_rule active (f,length ts) i \<in> ?S"
    using active_local
    unfolding gm04_complete_rules_def gm04_non_top_rules_def by auto
  have first: "(Fun active [Fun f ts],?A) \<in> rstep ?S"
    by (rule gm04_active_rule_instance[OF active_rule descend.hyps(1)])
  have child: "ts ! i \<in> set ts"
    using descend.hyps(1) by (rule nth_mem)
  from descend.prems have args_sig:
      "(\<Union>u\<in>set ts. funas_term u) \<subseteq> set F" by simp
  have sub_sig: "funas_term (ts ! i) \<subseteq> set F"
    using child args_sig by blast
  from trancl_rstep_ctxt[OF descend.hyps(4)[OF sub_sig], of ?C]
  have middle: "(?A,?M) \<in> (rstep ?S)\<^sup>+"
    using descend.hyps(1) by (simp add: upd_conv_take_nth_drop)
  have mark_inner: "gm04_mark_rule mark (f,length ts) i \<in>
      set (map (gm04_mark_rule mark (f,length ts))
        (filter (\<lambda>j. j < length ts)
          (sorted_list_of_set (\<mu> (f,length ts)))))"
    using descend.hyps(1) i_sorted by simp
  let ?mark_for_fn = "map (gm04_mark_rule mark (f,length ts))
    (filter (\<lambda>j. j < length ts)
      (sorted_list_of_set (\<mu> (f,length ts))))"
  have mark_outer: "?mark_for_fn \<in> set (map (\<lambda>fn.
      map (gm04_mark_rule mark fn)
        (filter (\<lambda>j. j < snd fn) (sorted_list_of_set (\<mu> fn)))) F)"
    using fn by force
  have mark_union: "gm04_mark_rule mark (f,length ts) i \<in>
      (\<Union>xs\<in>set (map (\<lambda>fn.
        map (gm04_mark_rule mark fn)
          (filter (\<lambda>j. j < snd fn) (sorted_list_of_set (\<mu> fn)))) F).
        set xs)"
    using mark_outer mark_inner by blast
  have mark_local: "gm04_mark_rule mark (f,length ts) i \<in>
      set (gm04_mark_rules \<mu> mark F)"
    using mark_union unfolding gm04_mark_rules_def by simp
  have mark_rule: "gm04_mark_rule mark (f,length ts) i \<in> ?S"
    using mark_local
    unfolding gm04_complete_rules_def gm04_non_top_rules_def by auto
  have mark_rule_updated:
      "gm04_mark_rule mark (f,length (ts[i := u])) i \<in> ?S"
    using mark_rule by simp
  have last: "(?M,Fun mark [Fun f (ts[i := u])]) \<in> rstep ?S"
    using gm04_mark_rule_instance[OF mark_rule_updated]
      descend.hyps(1) by simp
  from r_into_trancl[OF first] middle have prefix:
      "(Fun active [Fun f ts],?M) \<in> (rstep ?S)\<^sup>+"
    by (rule trancl_trans)
  from prefix r_into_trancl[OF last]
  show ?case by (rule trancl_trans)
qed

lemma gm04_complete_ground_step_simulation:
  fixes R :: "('f::countable,string) rules"
  assumes finite_mu: "\<And>fn. finite (\<mu> fn)"
    and signature: "funas_term s \<subseteq> set F" "funas_term t \<subseteq> set F"
    and ground: "ground t"
    and step: "(s,t) \<in> csstep \<mu> (set R)"
  shows "(Fun top_sym [Fun active [s]],Fun top_sym [Fun active [t]]) \<in>
    (rstep (set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R)))\<^sup>+"
proof -
  let ?S = "set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)"
  let ?Top = "More top_sym [] \<box> []"
  have search: "(s,t) \<in> gm04_search_step \<mu> (set R)"
    using step unfolding gm04_search_step_iff_csstep .
  from trancl_rstep_ctxt[
      OF gm04_search_step_complete_simulation[
        OF finite_mu signature(1) search], of ?Top]
  have first: "(Fun top_sym [Fun active [s]],
      Fun top_sym [Fun mark [t]]) \<in> (rstep ?S)\<^sup>+" by simp
  have mark_proper: "(Fun top_sym [Fun mark [t]],
      Fun top_sym [Fun proper [t]]) \<in> rstep ?S"
  proof -
    have pair: "(Fun top_sym [Fun mark [Var ''__gm04_x'']],
        Fun top_sym [Fun proper [Var ''__gm04_x'']]) \<in> ?S"
      by (simp add: gm04_complete_rules_def gm04_top_rules_def)
    from gm04_rule_instance_rstep[OF pair,
        of "\<lambda>x. if x = ''__gm04_x'' then t else Var x"]
    show ?thesis by simp
  qed
  have source_t: "gm04_source_term F t"
    using ground signature(2) unfolding gm04_source_term_def by simp
  have proper_ok0: "(Fun proper [t],Fun ok [t]) \<in> (rstep ?S)\<^sup>+"
  proof (rule gm04_proper_ok_phase[OF _ _ source_t])
    show "\<And>fn. fn \<in> set F \<Longrightarrow>
        gm04_proper_rule proper ok fn \<in> ?S"
      unfolding gm04_complete_rules_def gm04_non_top_rules_def by auto
    show "\<And>fn. fn \<in> set F \<Longrightarrow> 0 < snd fn \<Longrightarrow>
        gm04_ok_rule proper ok fn \<in> ?S"
      unfolding gm04_complete_rules_def gm04_non_top_rules_def by auto
  qed
  from trancl_rstep_ctxt[OF proper_ok0, of ?Top]
  have proper_ok: "(Fun top_sym [Fun proper [t]],
      Fun top_sym [Fun ok [t]]) \<in> (rstep ?S)\<^sup>+" by simp
  have ok_active: "(Fun top_sym [Fun ok [t]],
      Fun top_sym [Fun active [t]]) \<in> rstep ?S"
  proof -
    have pair: "(Fun top_sym [Fun ok [Var ''__gm04_x'']],
        Fun top_sym [Fun active [Var ''__gm04_x'']]) \<in> ?S"
      by (simp add: gm04_complete_rules_def gm04_top_rules_def)
    from gm04_rule_instance_rstep[OF pair,
        of "\<lambda>x. if x = ''__gm04_x'' then t else Var x"]
    show ?thesis by simp
  qed
  from first r_into_trancl[OF mark_proper] have prefix:
      "(Fun top_sym [Fun active [s]],Fun top_sym [Fun proper [t]])
        \<in> (rstep ?S)\<^sup>+"
    by (rule trancl_trans)
  from prefix proper_ok have prefix':
      "(Fun top_sym [Fun active [s]],Fun top_sym [Fun ok [t]])
        \<in> (rstep ?S)\<^sup>+"
    by (rule trancl_trans)
  from prefix' r_into_trancl[OF ok_active] show ?thesis
    by (rule trancl_trans)
qed

text \<open>
  The complete transformation reflects nontermination.  Equivalently,
  termination of the generated ordinary TRS implies context-sensitive
  termination of the source.  A source constant grounds an arbitrary chain;
  it is not otherwise used by the generated system.
\<close>

theorem gm04_complete_SN_imp_source_SN:
  fixes R T :: "('f::countable,string) rules"
  assumes transformed: "SN (rstep (set T))"
    and has_constant: "(c,0) \<in> set F"
    and finite_mu: "\<And>fn. finite (\<mu> fn)"
    and schema:
      "gm04_complete_schema_check \<mu> active mark proper ok top_sym F R T"
    and complete: "set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R) \<subseteq> set T"
  shows "SN (sig_step (set F) (csstep \<mu> (set R)))"
proof -
  let ?ground = "\<lambda>(_::string). Fun c []"
  let ?encode = "\<lambda>t. Fun top_sym [Fun active [t \<cdot> ?ground]]"
  have complete_SN: "SN (rstep (set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R)))"
    by (rule SN_subset[OF transformed], rule rstep_mono[OF complete])
  have target: "SN_rel (rstep (set (gm04_complete_rules
      \<mu> active mark proper ok top_sym F R))) {}" using complete_SN by simp
  have source: "SN_rel (sig_step (set F) (csstep \<mu> (set R))) {}"
  proof (rule SN_rel_map[OF target, of _ ?encode])
    fix s t :: "('f,string) term"
    assume st: "(s,t) \<in> sig_step (set F) (csstep \<mu> (set R))"
    from st have step: "(s,t) \<in> csstep \<mu> (set R)"
      and fs: "funas_term s \<subseteq> set F"
      and ft: "funas_term t \<subseteq> set F"
      unfolding sig_step_def by auto
    have grounded: "(s \<cdot> ?ground,t \<cdot> ?ground) \<in> csstep \<mu> (set R)"
      by (rule csstep_subst_closed[OF step])
    have fgs: "funas_term (s \<cdot> ?ground) \<subseteq> set F"
      using fs has_constant unfolding funas_term_subst by auto
    have fgt: "funas_term (t \<cdot> ?ground) \<subseteq> set F"
      using ft has_constant unfolding funas_term_subst by auto
    have gt: "ground (t \<cdot> ?ground)" by auto
    from gm04_complete_ground_step_simulation[
      OF finite_mu fgs fgt gt grounded]
    have "(?encode s,?encode t) \<in>
      rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)) O
      (rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)))\<^sup>*"
      unfolding trancl_unfold_left .
    then show "(?encode s,?encode t) \<in>
      (rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)) \<union> {})\<^sup>* O
      rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)) O
      (rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)) \<union> {})\<^sup>*"
      by regexp
  next
    fix s t :: "('f,string) term"
    assume "(s,t) \<in> {}"
    then show "(?encode s,?encode t) \<in>
      (rstep (set (gm04_complete_rules
        \<mu> active mark proper ok top_sym F R)) \<union> {})\<^sup>*" by simp
  qed
  from source show ?thesis by simp
qed

lemma gm04_SN_rel_and_SN_imp_SN_union:
  assumes relative: "SN_rel R S" and weak: "SN S"
  shows "SN (R \<union> S)"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and> chain (R \<union> S) f"
  then obtain f where chain: "chain (R \<union> S) f" by auto
  from relative[unfolded SN_rel_on_conv SN_rel_on_alt_def, rule_format,
      of f] chain
  have finite_R: "\<not> (INFM i. (f i, f (Suc i)) \<in> R)" by auto
  then obtain m where tail_R: "\<And>i. i > m \<Longrightarrow>
      (f i, f (Suc i)) \<notin> R"
    unfolding INFM_nat by blast
  let ?g = "\<lambda>i. f (Suc m + i)"
  have "chain S ?g"
    unfolding chain_def
  proof
    fix i
    have index: "m < Suc m + i" by simp
    from chain have step: "(f (Suc m + i), f (Suc (Suc m + i))) \<in> R \<union> S"
      unfolding chain_def by auto
    from step tail_R[OF index] show
      "(f (Suc m + i), f (Suc m + Suc i)) \<in> S" by auto
  qed
  then have "\<not> SN S" by (rule not_SN_onI[OF UNIV_I])
  with weak show False by contradiction
qed

lemma gm04_SN_if_two_steps_decrease:
  assumes SN: "SN R" and square: "A O A \<subseteq> R"
  shows "SN A"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and> chain A f"
  then obtain f where chain: "chain A f" by auto
  let ?g = "\<lambda>n. f (2 * n)"
  have "chain R ?g"
    unfolding chain_def
  proof
    fix n
    have first: "(f (2*n), f (Suc (2*n))) \<in> A"
      using chain unfolding chain_def by blast
    have second: "(f (Suc (2*n)), f (Suc (Suc (2*n)))) \<in> A"
      using chain unfolding chain_def by blast
    have composed: "(f (2*n), f (Suc (Suc (2*n)))) \<in> A O A"
      using first second by blast
    from subsetD[OF square composed] show "(?g n, ?g (Suc n)) \<in> R"
      by simp
  qed
  then have "\<not> SN R" by (rule not_SN_onI[OF UNIV_I])
  with SN show False by contradiction
qed

definition gm04_phase_rel :: "'a rel \<Rightarrow> ('a \<times> bool) rel" where
  "gm04_phase_rel R =
    {p. \<exists>s t. p = ((s,False),(t,True)) \<and> (s,t) \<in> R} \<union>
    {p. \<exists>s. p = ((s,True),(s,False))}"

definition gm04_lift_rel :: "'a rel \<Rightarrow> ('a \<times> bool) rel" where
  "gm04_lift_rel R =
    {p. \<exists>s t b. p = ((s,b),(t,b)) \<and> (s,t) \<in> R}"

lemma gm04_SN_lift_rel:
  assumes "SN R"
  shows "SN (gm04_lift_rel R)"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and> chain (gm04_lift_rel R) f"
  then obtain f where chain: "chain (gm04_lift_rel R) f" by auto
  let ?g = "\<lambda>n. fst (f n)"
  have projected: "\<forall>i. (fst (f i), fst (f (Suc i))) \<in> R"
  proof
    fix i
    from chain have step: "(f i, f (Suc i)) \<in> gm04_lift_rel R"
      unfolding chain_def by blast
    then show "(fst (f i), fst (f (Suc i))) \<in> R"
      unfolding gm04_lift_rel_def by auto
  qed
  have "chain R ?g"
    using projected unfolding chain_def by assumption
  then have "\<not> SN R" by (rule not_SN_onI[OF UNIV_I])
  with assms show False by contradiction
qed

lemma gm04_phase_rel_square:
  "gm04_phase_rel R O gm04_phase_rel R \<subseteq> gm04_lift_rel R"
  unfolding gm04_phase_rel_def gm04_lift_rel_def by auto

lemma gm04_SN_phase_rel:
  assumes "SN R"
  shows "SN (gm04_phase_rel R)"
  by (rule gm04_SN_if_two_steps_decrease[
      OF gm04_SN_lift_rel[OF assms] gm04_phase_rel_square])

lemma gm04_SN_via_map:
  assumes target: "SN A"
    and simulation: "\<And>x y. (x,y) \<in> B \<Longrightarrow> (f x,f y) \<in> A"
  shows "SN B"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>g. g 0 \<in> UNIV \<and> chain B g"
  then obtain g where chain: "chain B g" by auto
  have "chain A (\<lambda>i. f (g i))"
    using chain simulation unfolding chain_def by blast
  then have "\<not> SN A" by (rule not_SN_onI[OF UNIV_I])
  with target show False by contradiction
qed

text \<open>
  Generic residual interface used by the certified processor.  A dependency
  pair macro-step consists of arbitrary weak rewriting before and after one
  strict pair.  It is enough to decode every such macro-step into one phase
  step: the two administrative pair kinds alternate, and every second phase
  records a genuine source CS step.  This theorem deliberately knows nothing
  about concrete source or administrative symbol names.
\<close>

theorem gm04_finite_two_phase_dpp:
  fixes decode :: "('f,string) term \<Rightarrow> ('a \<times> bool)"
  assumes source: "SN R"
    and simulation: "\<And>s t. (s,t) \<in>
        (rstep S)\<^sup>* O subst.closure P O (rstep S)\<^sup>* \<Longrightarrow>
      (decode s, decode t) \<in> gm04_phase_rel R"
  shows "finite_dpp (False,False,P,{},{},{},S)"
proof -
  have macro: "SN ((rstep S)\<^sup>* O subst.closure P O (rstep S)\<^sup>*)"
    by (rule gm04_SN_via_map[OF gm04_SN_phase_rel[OF source], of _ decode],
        rule simulation)
  show ?thesis
    using macro unfolding finite_dpp_iff_SN_rel SN_rel_defs by simp
qed

theorem gm04_finite_dpp_from_pair_connectors:
  fixes decode ::
    "(('f,string) term \<times> ('f,string) term) \<Rightarrow> ('a \<times> bool)"
  assumes source: "SN R"
    and simulation: "\<And>l r l' r'.
      (l,r) \<in> subst.closure P \<Longrightarrow>
      (l',r') \<in> subst.closure P \<Longrightarrow>
      (r,l') \<in> (rstep S)\<^sup>* \<Longrightarrow>
      (decode (l,r), decode (l',r')) \<in> gm04_phase_rel R"
  shows "finite_dpp (False,False,P,{},{},{},S)"
proof (rule ccontr)
  assume "\<not> finite_dpp (False,False,P,{},{},{},S)"
  then obtain s t \<sigma> where chain:
      "min_ichain (False,False,P,{},{},{},S) s t \<sigma>"
    unfolding finite_dpp_def by blast
  let ?pair = "\<lambda>i. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i)"
  have ichain: "ichain (False,False,P,{},{},{},S) s t \<sigma>"
    using chain by simp
  have pair: "\<And>i. ?pair i \<in> subst.closure P"
  proof -
    fix i
    from ichain have raw: "(s i,t i) \<in> P"
      by (simp add: ichain.simps)
    show "?pair i \<in> subst.closure P"
      by (rule subst.closureI2[OF raw], simp_all)
  qed
  have connector: "\<And>i. (t i \<cdot> \<sigma> i,
      s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep S)\<^sup>*"
    using ichain by (simp add: ichain.simps)
  have phases: "chain (gm04_phase_rel R) (\<lambda>i. decode (?pair i))"
    unfolding chain_def
  proof (intro allI)
    fix i
    show "(decode (?pair i), decode (?pair (Suc i)))
        \<in> gm04_phase_rel R"
      by (rule simulation[OF pair[of i] pair[of "Suc i"]
            connector[of i]])
  qed
  from phases have "\<not> SN (gm04_phase_rel R)"
    by (rule not_SN_onI[OF UNIV_I])
  with gm04_SN_phase_rel[OF source] show False by contradiction
qed

text \<open>
  Innermost residuals carry more information than an ordinary DP problem:
  every instantiated left-hand side is a Q-normal form and every connector
  uses Q-restricted rewriting.  Keeping that information in the interface is
  essential for complete transformations, whose administrative rules are
  deliberately only deterministic on normal source arguments.
\<close>

theorem gm04_finite_qdpp_from_pair_connectors:
  fixes decode ::
    "(('f,string) term \<times> ('f,string) term) \<Rightarrow> ('a \<times> bool)"
  assumes source: "SN R"
    and simulation: "\<And>l r l' r'.
      (l,r) \<in> subst.closure P \<Longrightarrow>
      (l',r') \<in> subst.closure P \<Longrightarrow>
      l \<in> NF_terms Q \<Longrightarrow>
      l' \<in> NF_terms Q \<Longrightarrow>
      (r,l') \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      (decode (l,r), decode (l',r')) \<in> gm04_phase_rel R"
  shows "finite_dpp (True,m,P,{},Q,S,{})"
proof (rule ccontr)
  assume "\<not> finite_dpp (True,m,P,{},Q,S,{})"
  then obtain s t \<sigma> where chain:
      "min_ichain (True,m,P,{},Q,S,{}) s t \<sigma>"
    unfolding finite_dpp_def by blast
  let ?pair = "\<lambda>i. (s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i)"
  have ichain: "ichain (True,m,P,{},Q,S,{}) s t \<sigma>"
    using chain by simp
  have pair: "\<And>i. ?pair i \<in> subst.closure P"
  proof -
    fix i
    from ichain have raw: "(s i,t i) \<in> P"
      by (simp add: ichain.simps)
    show "?pair i \<in> subst.closure P"
      by (rule subst.closureI2[OF raw], simp_all)
  qed
  have connector: "\<And>i. (t i \<cdot> \<sigma> i,
      s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep True Q S)\<^sup>*"
    using ichain by (simp add: ichain.simps)
  have normal: "\<And>i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
    using ichain by (simp add: ichain.simps)
  have phases: "chain (gm04_phase_rel R) (\<lambda>i. decode (?pair i))"
    unfolding chain_def
  proof (intro allI)
    fix i
    show "(decode (?pair i), decode (?pair (Suc i)))
        \<in> gm04_phase_rel R"
      by (rule simulation[OF pair[of i] pair[of "Suc i"]
            normal[of i] normal[of "Suc i"] connector[of i]])
  qed
  from phases have "\<not> SN (gm04_phase_rel R)"
    by (rule not_SN_onI[OF UNIV_I])
  with gm04_SN_phase_rel[OF source] show False by contradiction
qed

text \<open>
  Signature-restricted source proofs require one extra, standard step.  If an
  arbitrary minimal chain exists, signature cleaning replaces its alien
  substitution terms by fresh variables.  The resulting chain lives entirely
  over the declared transformed signature, so its decoded source phases may be
  checked against a signature-restricted source relation.
\<close>

theorem gm04_finite_qdpp_from_pair_connectors_sig:
  fixes c :: "('f,string) term \<Rightarrow> string"
    and decode ::
      "(('f,string) term \<times> ('f,string) term) \<Rightarrow> ('a \<times> bool)"
  assumes cinj: "inj c"
    and source: "SN R"
    and inn: "NF_terms Q \<subseteq> NF_trs S"
    and qf: "QF_cond F Q"
    and rules: "funas_trs S \<subseteq> F"
    and pairs: "funas_args_trs P \<subseteq> F"
    and wwf: "wwf_qtrs Q S"
    and non_var: "\<And>s t. (s,t) \<in> P \<Longrightarrow> is_Fun s \<and> is_Fun t \<and>
      \<not> defined (applicable_rules Q S) (the (root t))"
    and vars: "\<And>s t. (s,t) \<in> P \<Longrightarrow> vars_term t \<subseteq> vars_term s"
    and simulation: "\<And>l r l' r'.
      (l,r) \<in> subst.closure P \<Longrightarrow>
      (l',r') \<in> subst.closure P \<Longrightarrow>
      l \<in> NF_terms Q \<Longrightarrow>
      l' \<in> NF_terms Q \<Longrightarrow>
      (r,l') \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      funas_args_term l \<subseteq> F \<Longrightarrow> funas_args_term r \<subseteq> F \<Longrightarrow>
      funas_args_term l' \<subseteq> F \<Longrightarrow> funas_args_term r' \<subseteq> F \<Longrightarrow>
      (decode (l,r), decode (l',r')) \<in> gm04_phase_rel R"
  shows "finite_dpp (True,m,P,{},Q,S,{})"
proof (rule ccontr)
  assume "\<not> finite_dpp (True,m,P,{},Q,S,{})"
  then obtain s t \<sigma> where chain:
      "min_ichain (True,m,P,{},Q,S,{}) s t \<sigma>"
    unfolding finite_dpp_def by blast
  interpret cleaning_innermost F c by (unfold_locales, rule cinj)
  have cleaned: "min_ichain_sig (True,m,P,{},Q,S,{}) F s t
      (\<lambda>i. clean_subst (\<sigma> i))"
  proof (rule clean_min_ichain_below[
      where Q=Q and R=S and Rw="{}" and P=P and Pw="{}"
        and nfs=True and m=m and s=s and t=t and \<sigma>=\<sigma>])
    show "NF_terms Q \<subseteq> NF_trs (S \<union> {})" using inn by simp
    show "QF_cond F Q" by (rule qf)
    show "funas_trs (S \<union> {}) \<subseteq> F" using rules by simp
    show "funas_args_trs (P \<union> {}) \<subseteq> F" using pairs by simp
    show "wwf_qtrs Q (S \<union> {})" using wwf by simp
    show "\<And>s t. (s,t) \<in> P \<union> {} \<Longrightarrow> is_Fun s \<and> is_Fun t \<and>
        \<not> defined (applicable_rules Q (S \<union> {})) (the (root t))"
      using non_var by simp
    show "\<And>s t. (s,t) \<in> P \<union> {} \<Longrightarrow> vars_term t \<subseteq> vars_term s"
      using vars by simp
    show "min_ichain (True,m,P,{},Q,S,{}) s t \<sigma>" by (rule chain)
  qed
  let ?\<tau> = "\<lambda>i. clean_subst (\<sigma> i)"
  let ?pair = "\<lambda>i. (s i \<cdot> ?\<tau> i, t i \<cdot> ?\<tau> i)"
  have ichain: "ichain (True,m,P,{},Q,S,{}) s t ?\<tau>"
    using cleaned by simp
  have chain_sig: "funas_ichain s t ?\<tau> \<subseteq> F"
    using cleaned by simp
  have subst_sig: "\<And>i x. funas_term (?\<tau> i x) \<subseteq> F"
    using chain_sig unfolding funas_ichain_def by blast
  have pair: "\<And>i. ?pair i \<in> subst.closure P"
  proof -
    fix i
    from ichain have raw: "(s i,t i) \<in> P"
      by (simp add: ichain.simps)
    show "?pair i \<in> subst.closure P"
      by (rule subst.closureI2[OF raw], simp_all)
  qed
  have pair_sig: "\<And>i. funas_args_term (fst (?pair i)) \<subseteq> F \<and>
      funas_args_term (snd (?pair i)) \<subseteq> F"
  proof -
    fix i
    from ichain have raw: "(s i,t i) \<in> P"
      by (simp add: ichain.simps)
    with pairs have st: "funas_args_term (s i) \<subseteq> F"
        "funas_args_term (t i) \<subseteq> F"
      unfolding funas_args_trs_def funas_args_rule_def by force+
    from non_var[OF raw] have is_fun: "is_Fun (s i)" "is_Fun (t i)"
      by auto
    have clean_s: "clean_term_below (s i \<cdot> \<sigma> i) =
        s i \<cdot> ?\<tau> i"
      by (rule clean_subst_apply_term_below[OF st(1) is_fun(1)])
    have clean_t: "clean_term_below (t i \<cdot> \<sigma> i) =
        t i \<cdot> ?\<tau> i"
      by (rule clean_subst_apply_term_below[OF st(2) is_fun(2)])
    have sig_s: "funas_args_term (s i \<cdot> ?\<tau> i) \<subseteq> F"
      unfolding clean_s[symmetric]
      by (rule funas_args_term_clean_term_below)
    have sig_t: "funas_args_term (t i \<cdot> ?\<tau> i) \<subseteq> F"
      unfolding clean_t[symmetric]
      by (rule funas_args_term_clean_term_below)
    from sig_s sig_t show "funas_args_term (fst (?pair i)) \<subseteq> F \<and>
        funas_args_term (snd (?pair i)) \<subseteq> F"
      by simp
  qed
  have connector: "\<And>i. (t i \<cdot> ?\<tau> i,
      s (Suc i) \<cdot> ?\<tau> (Suc i)) \<in> (qrstep True Q S)\<^sup>*"
    using ichain by (simp add: ichain.simps)
  have normal: "\<And>i. s i \<cdot> ?\<tau> i \<in> NF_terms Q"
    using ichain by (simp add: ichain.simps)
  have phases: "chain (gm04_phase_rel R) (\<lambda>i. decode (?pair i))"
    unfolding chain_def
  proof (intro allI)
    fix i
    from pair_sig[of i] have sig_i:
        "funas_args_term (s i \<cdot> ?\<tau> i) \<subseteq> F"
        "funas_args_term (t i \<cdot> ?\<tau> i) \<subseteq> F" by auto
    from pair_sig[of "Suc i"] have sig_suc:
        "funas_args_term (s (Suc i) \<cdot> ?\<tau> (Suc i)) \<subseteq> F"
        "funas_args_term (t (Suc i) \<cdot> ?\<tau> (Suc i)) \<subseteq> F"
      by auto
    show "(decode (?pair i), decode (?pair (Suc i)))
        \<in> gm04_phase_rel R"
      by (rule simulation[OF pair[of i] pair[of "Suc i"]
            normal[of i] normal[of "Suc i"] connector[of i]
            sig_i sig_suc])
  qed
  from phases have "\<not> SN (gm04_phase_rel R)"
    by (rule not_SN_onI[OF UNIV_I])
  with gm04_SN_phase_rel[OF source] show False by contradiction
qed

definition gm04_decode_top_pair where
  "gm04_decode_top_pair mark pair =
    (case fst pair of
      Fun top_sharp [Fun role [x]] \<Rightarrow> (x, role = mark)
    | _ \<Rightarrow> (Var ''__gm04_invalid'', False))"

definition gm04_decode_top_pair_erased where
  "gm04_decode_top_pair_erased W mark pair =
    (case fst pair of
      Fun top_sharp [Fun role [x]] \<Rightarrow> (gm04_erase W x, role = mark)
    | _ \<Rightarrow> (Var ''__gm04_invalid'', False))"

lemma gm04_NF_terms_subterm:
  assumes "t \<in> NF_terms Q" and "t \<unrhd> s"
  shows "s \<in> NF_terms Q"
  using NF_subterm[of t "Id_on Q" s] assms by simp

definition gm04_active_safe where
  "gm04_active_safe active Q t \<longleftrightarrow>
    (\<forall>u. t \<unrhd> u \<longrightarrow> root u = Some (active,1) \<longrightarrow>
      u \<in> NF_terms Q)"

lemma gm04_NF_active_safe:
  assumes "t \<in> NF_terms Q"
  shows "gm04_active_safe active Q t"
  unfolding gm04_active_safe_def
  using gm04_NF_terms_subterm[OF assms] by blast

lemma gm04_source_instance_active_safe:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "funas_term t \<subseteq> set F"
    and normal: "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x \<in> NF_terms Q"
  shows "gm04_active_safe active Q (t \<cdot> \<sigma>)"
  unfolding gm04_active_safe_def
proof (intro allI impI)
  fix u
  assume sub: "t \<cdot> \<sigma> \<unrhd> u" and root: "root u = Some (active,1)"
  from sub show "u \<in> NF_terms Q"
  proof (rule supteq_subst_cases)
    fix v
    assume vt: "t \<unrhd> v" and vfun: "is_Fun v" and uv: "u = v \<cdot> \<sigma>"
    from vt have "funas_term v \<subseteq> funas_term t"
      by (rule supteq_imp_funas_term_subset)
    moreover from vfun uv root
    have "(active,1) \<in> funas_term v" by (cases v, auto)
    ultimately have "(active,1) \<in> set F" using source by blast
    with fresh show ?thesis unfolding gm04_roles_fresh_def by auto
  next
    fix x
    assume xt: "x \<in> vars_term t" and xu: "\<sigma> x \<unrhd> u"
    from gm04_NF_terms_subterm[OF normal[OF xt] xu]
    show ?thesis .
  qed
qed

lemma gm04_no_active_instance_safe:
  assumes no_active: "\<And>n. (active,n) \<notin> funas_term t"
    and normal: "\<And>x. x \<in> vars_term t \<Longrightarrow> \<sigma> x \<in> NF_terms Q"
  shows "gm04_active_safe active Q (t \<cdot> \<sigma>)"
  unfolding gm04_active_safe_def
proof (intro allI impI)
  fix u
  assume sub: "t \<cdot> \<sigma> \<unrhd> u" and root: "root u = Some (active,1)"
  from sub show "u \<in> NF_terms Q"
  proof (rule supteq_subst_cases)
    fix v
    assume vt: "t \<unrhd> v" and vfun: "is_Fun v" and uv: "u = v \<cdot> \<sigma>"
    from vt have "funas_term v \<subseteq> funas_term t"
      by (rule supteq_imp_funas_term_subset)
    moreover from vfun uv root
    have "(active,1) \<in> funas_term v" by (cases v, auto)
    ultimately show ?thesis using no_active[of 1] by blast
  next
    fix x
    assume xt: "x \<in> vars_term t" and xu: "\<sigma> x \<unrhd> u"
    from gm04_NF_terms_subterm[OF normal[OF xt] xu]
    show ?thesis .
  qed
qed

lemma gm04_lhs_instance_not_normal:
  assumes "(l,r) \<in> S"
  shows "l \<cdot> \<sigma> \<notin> NF_terms (lhss S)"
  using assms unfolding NF_terms_lhss
  by (auto intro: gm04_rule_instance_rstep)

lemma gm04_active_safe_excludes_active_contraction:
  fixes C :: "('f,'v) ctxt"
  assumes safe: "gm04_active_safe active (lhss S) (C\<langle>l \<cdot> \<sigma>\<rangle>)"
    and pair: "(l,r) \<in> S"
    and root: "root (l \<cdot> \<sigma>) = Some (active,1)"
  shows False
proof -
  have sub: "C\<langle>l \<cdot> \<sigma>\<rangle> \<unrhd> l \<cdot> \<sigma>"
    by (rule ctxt_imp_supteq)
  from safe sub root have "l \<cdot> \<sigma> \<in> NF_terms (lhss S)"
    unfolding gm04_active_safe_def by blast
  with gm04_lhs_instance_not_normal[OF pair] show False by blast
qed

lemma gm04_active_safe_qstep_preserves_erase:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and safe: "gm04_active_safe active (lhss S) s"
    and step: "(s,t) \<in> qrstep True (lhss S) S"
  shows "gm04_erase {active,mark,proper,ok} s =
    gm04_erase {active,mark,proper,ok} t"
proof -
  from qrstepE'[OF step] obtain C \<sigma> l r where pair: "(l,r) \<in> S"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (admin) "(l,r) \<notin> set (gm04_source_rules active mark R)"
        "(l,r) \<notin> set (gm04_active_rules \<mu> active F)"
    by auto
  then show ?thesis
  proof cases
    case source
    then have root: "root (l \<cdot> \<sigma>) = Some (active,1)"
      unfolding gm04_source_rules_def by (auto split: prod.splits)
    have false: False
      by (rule gm04_active_safe_excludes_active_contraction[
          OF safe[unfolded s] pair root])
    from false show ?thesis by (rule FalseE)
  next
    case active
    then have root: "root (l \<cdot> \<sigma>) = Some (active,1)"
      unfolding gm04_active_rules_def gm04_active_rule_def
      by (auto simp: Let_def split: prod.splits)
    have false: False
      by (rule gm04_active_safe_excludes_active_contraction[
          OF safe[unfolded s] pair root])
    from false show ?thesis by (rule FalseE)
  next
    case admin
    have erased: "gm04_erase {active,mark,proper,ok} (l \<cdot> \<sigma>) =
        gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>)"
      by (rule gm04_administrative_rule_instance_preserves_erase[
        OF pair[unfolded S] admin fresh])
    show ?thesis unfolding s t
      by (rule gm04_erase_ctxt_cong[OF erased])
  qed
qed

lemma gm04_active_safe_qstep_preserved:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and safe: "gm04_active_safe active (lhss S) s"
    and step: "(s,t) \<in> qrstep True (lhss S) S"
  shows "gm04_active_safe active (lhss S) t"
proof -
  from qrstepE'[OF step] obtain C \<sigma> l r where
      nfs: "NF_subst True (l,r) \<sigma> (lhss S)"
    and pair: "(l,r) \<in> S"
    and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" by blast
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (admin) "(l,r) \<notin> set (gm04_source_rules active mark R)"
        "(l,r) \<notin> set (gm04_active_rules \<mu> active F)"
    by auto
  then show ?thesis
  proof cases
    case source
    then have root: "root (l \<cdot> \<sigma>) = Some (active,1)"
      unfolding gm04_source_rules_def by (auto split: prod.splits)
    have false: False
      by (rule gm04_active_safe_excludes_active_contraction[
          OF safe[unfolded s] pair root])
    from false show ?thesis by (rule FalseE)
  next
    case active
    then have root: "root (l \<cdot> \<sigma>) = Some (active,1)"
      unfolding gm04_active_rules_def gm04_active_rule_def
      by (auto simp: Let_def split: prod.splits)
    have false: False
      by (rule gm04_active_safe_excludes_active_contraction[
          OF safe[unfolded s] pair root])
    from false show ?thesis by (rule FalseE)
  next
    case admin
    have rhs_safe: "gm04_active_safe active (lhss S) (r \<cdot> \<sigma>)"
    proof (rule gm04_no_active_instance_safe)
      show "\<And>n. (active,n) \<notin> funas_term r"
        by (rule gm04_administrative_rhs_has_no_active[
          OF pair[unfolded S] admin fresh])
      show "\<And>x. x \<in> vars_term r \<Longrightarrow> \<sigma> x \<in> NF_terms (lhss S)"
        using NF_subst_right[OF TrueI nfs] by auto
    qed
    show ?thesis unfolding gm04_active_safe_def t
    proof (intro allI impI)
      fix u
      assume sub: "C\<langle>r \<cdot> \<sigma>\<rangle> \<unrhd> u"
        and root_u: "root u = Some (active,1)"
      from sub show "u \<in> NF_terms (lhss S)"
      proof (cases rule: supteq_ctxt_cases)
        case in_ctxt
        have "C\<langle>l \<cdot> \<sigma>\<rangle> \<unrhd> u"
          using suptc_imp_supt[OF in_ctxt, of "l \<cdot> \<sigma>"] by auto
        with safe root_u show ?thesis
          unfolding gm04_active_safe_def s by blast
      next
        case in_term
        with rhs_safe root_u show ?thesis
          unfolding gm04_active_safe_def by blast
      next
        case (sub_ctxt D C')
        let ?v = "C'\<langle>l \<cdot> \<sigma>\<rangle>"
        have root_v: "root ?v = Some (active,1)"
          using root_u sub_ctxt(2,3) by (cases C'; auto)
        have source_sub: "C\<langle>l \<cdot> \<sigma>\<rangle> \<unrhd> ?v"
          using sub_ctxt(1) by (simp add: ctxt_imp_supteq)
        from safe source_sub root_v have nf_v:
            "?v \<in> NF_terms (lhss S)"
          unfolding gm04_active_safe_def s by blast
        have vstep: "(?v,C'\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep S"
          by (rule rstepI[OF pair, of _ C' \<sigma>], simp_all)
        from nf_v[unfolded NF_terms_lhss] vstep show ?thesis by blast
      qed
    qed
  qed
qed

lemma gm04_active_safe_qsteps_preserve:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and safe: "gm04_active_safe active (lhss S) s"
    and steps: "(s,t) \<in> (qrstep True (lhss S) S)\<^sup>*"
  shows "gm04_active_safe active (lhss S) t \<and>
    gm04_erase {active,mark,proper,ok} s =
      gm04_erase {active,mark,proper,ok} t"
  using steps safe
proof induct
  case base
  then show ?case by simp
next
  case (step t u)
  from step(3,4) have safe_t: "gm04_active_safe active (lhss S) t"
    and erased_st: "gm04_erase {active,mark,proper,ok} s =
      gm04_erase {active,mark,proper,ok} t" by auto
  have safe_u: "gm04_active_safe active (lhss S) u"
    by (rule gm04_active_safe_qstep_preserved[OF S fresh safe_t step(2)])
  have erased_tu: "gm04_erase {active,mark,proper,ok} t =
      gm04_erase {active,mark,proper,ok} u"
    by (rule gm04_active_safe_qstep_preserves_erase[
      OF S fresh safe_t step(2)])
  show ?case using safe_u erased_st erased_tu by simp
qed

lemma gm04_source_rhs_qsuffix_preserves_erase:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and lr: "(l,r) \<in> set R"
    and nfs: "NF_subst True (Fun active [l],Fun mark [r]) \<sigma> (lhss S)"
    and steps: "(r \<cdot> \<sigma>,y) \<in> (qrstep True (lhss S) S)\<^sup>*"
  shows "gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>) =
    gm04_erase {active,mark,proper,ok} y"
proof -
  have rhs_sig: "funas_term r \<subseteq> set F"
    using signature lr unfolding funas_trs_def
    by (force simp: funas_rule_def)
  have normal: "\<And>x. x \<in> vars_term r \<Longrightarrow>
      \<sigma> x \<in> NF_terms (lhss S)"
    using NF_subst_right[OF TrueI nfs] by auto
  have safe: "gm04_active_safe active (lhss S) (r \<cdot> \<sigma>)"
    by (rule gm04_source_instance_active_safe[OF fresh rhs_sig normal])
  from gm04_active_safe_qsteps_preserve[OF S fresh safe steps]
  show ?thesis by blast
qed

lemma gm04_csstep_trancl_descend:
  assumes i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
    and steps: "(ts ! i,u) \<in> (csstep \<mu> R)\<^sup>+"
  shows "(Fun f ts,Fun f (ts[i := u])) \<in> (csstep \<mu> R)\<^sup>+"
  using steps
proof induct
  case (base u)
  have one: "(Fun f ts,Fun f (ts[i := u])) \<in> csstep \<mu> R"
    unfolding gm04_search_step_iff_csstep[symmetric]
  proof (rule gm04_search_step.descend)
    show "i < length ts" by (rule i)
    show "i \<in> \<mu> (f,length ts)" by (rule active)
    from base show "(ts ! i,u) \<in> gm04_search_step \<mu> R"
      by (simp add: gm04_search_step_iff_csstep)
  qed
  then show ?case by (rule r_into_trancl)
next
  case (step u v)
  have lifted_raw:
      "(Fun f (ts[i := u]),Fun f ((ts[i := u])[i := v])) \<in> csstep \<mu> R"
    unfolding gm04_search_step_iff_csstep[symmetric]
  proof (rule gm04_search_step.descend)
    show "i < length (ts[i := u])" using i by simp
    show "i \<in> \<mu> (f,length (ts[i := u]))" using i active by simp
    from step.hyps(2) show
      "((ts[i := u]) ! i,v) \<in> gm04_search_step \<mu> R"
      using i by (simp add: gm04_search_step_iff_csstep)
  qed
  have lifted: "(Fun f (ts[i := u]),Fun f (ts[i := v])) \<in> csstep \<mu> R"
    using lifted_raw i by simp
  from step.hyps(3) r_into_trancl[OF lifted]
  show ?case by (rule trancl_trans)
qed

lemma gm04_active_root_source_connector:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and lr: "(l,r) \<in> set R"
    and x: "x = l \<cdot> \<sigma>"
    and nfs: "NF_subst True (Fun active [l],Fun mark [r]) \<sigma> (lhss S)"
    and suffix: "(Fun mark [r \<cdot> \<sigma>],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
    and wf: "wf_trs S"
  shows "(gm04_erase {active,mark,proper,ok} x,
      gm04_erase {active,mark,proper,ok} y)
    \<in> (csstep \<mu> (set R))\<^sup>+"
proof -
  have generated: "(Fun active [l],Fun mark [r])
      \<in> set (gm04_source_rules active mark R)"
    using lr unfolding gm04_source_rules_def by auto
  have wrapped:
      "(gm04_erase {active,mark,proper,ok} (Fun active [l] \<cdot> \<sigma>),
       gm04_erase {active,mark,proper,ok} (Fun mark [r] \<cdot> \<sigma>))
      \<in> csstep \<mu> (set R)"
    by (rule gm04_source_rule_instance_erases_to_csstep[
      OF fresh signature generated])
  have first: "(gm04_erase {active,mark,proper,ok} x,
      gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>))
      \<in> csstep \<mu> (set R)"
    using wrapped unfolding x by simp
  have lhs_fun: "\<forall>(a,b)\<in>S. is_Fun a"
    using wf unfolding wf_trs_def by blast
  have undef_mark: "\<not> defined S (mark,1)"
    unfolding S by (rule gm04_non_top_role_not_defined[OF fresh], simp)
  have inner: "(r \<cdot> \<sigma>,y)
      \<in> (qrstep True (lhss S) S)\<^sup>*"
    using suffix gm04_q_top_wrapper_rsteps_iff[
      OF lhs_fun undef_mark, of "r \<cdot> \<sigma>" y True "lhss S"] by simp
  have erased: "gm04_erase {active,mark,proper,ok} (r \<cdot> \<sigma>) =
      gm04_erase {active,mark,proper,ok} y"
    by (rule gm04_source_rhs_qsuffix_preserves_erase[
      OF S fresh signature lr nfs inner])
  from r_into_trancl[OF first] show ?thesis unfolding erased .
qed

lemma gm04_root_source_step_to_mark_cases_early:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source_root: "(f,length zs) \<in> set F"
    and finite_mu: "finite (\<mu> (f,length zs))"
    and restricted: nfs
    and root_step: "(Fun f zs,u) \<in> rqrstep nfs Q S"
    and suffix: "(u,Fun mark [y]) \<in> (qrstep nfs Q S)\<^sup>*"
  obtains i \<sigma> where
      "i \<in> \<mu> (f,length zs)" "i < length zs"
      "zs = (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
        [i := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars (length zs))) ! i]]"
      "u = Fun mark [Fun f
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
      "set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
        \<subseteq> NF_terms Q"
proof -
  from root_step obtain l r \<sigma> where
      nfsubst: "NF_subst nfs (l,r) \<sigma> Q"
    and pair: "(l,r) \<in> S"
    and lhs: "Fun f zs = l \<cdot> \<sigma>"
    and rhs: "u = r \<cdot> \<sigma>"
    unfolding rqrstep_def by auto
  from fresh source_root have fneq:
      "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
    unfolding gm04_roles_fresh_def by auto
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))" by auto
  then show thesis
  proof cases
    case source
    with lhs fneq show thesis
      unfolding gm04_source_rules_def by (auto split: prod.splits)
  next
    case active
    then obtain g n i where fn: "(g,n) \<in> set F"
      and ipos: "i < n"
      and lr: "(l,r) = gm04_active_rule active (g,n) i"
      unfolding gm04_active_rules_def by auto
    have shape: "fst (gm04_active_rule active (g,n) i) =
        Fun active [Fun g (gm04_vars n)]"
      unfolding gm04_active_rule_def by (simp add: Let_def)
    have l_fst: "l = fst (gm04_active_rule active (g,n) i)"
      using arg_cong[OF lr, of fst] by simp
    have l: "l = Fun active [Fun g (gm04_vars n)]"
    proof -
      from l_fst show ?thesis unfolding shape .
    qed
    from lhs[unfolded l] fneq show thesis by simp
  next
    case mark
    then obtain g n i where fn: "(g,n) \<in> set F"
      and listed: "i \<in> set (sorted_list_of_set (\<mu> (g,n)))"
      and ipos: "i < n"
      and lr: "(l,r) = gm04_mark_rule mark (g,n) i"
      unfolding gm04_mark_rules_def by auto
    from lhs lr have fg: "g = f" and n: "n = length zs"
      and zs: "zs = (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n))
        [i := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars n)) ! i]]"
      unfolding gm04_mark_rule_def
      by (auto simp: Let_def map_update ipos)
    have finite_gn: "finite (\<mu> (g,n))" using finite_mu fg n by simp
    have active_i: "i \<in> \<mu> (g,n)"
      using listed finite_gn by simp
    from rhs lr have u: "u = Fun mark [Fun g
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n))]"
      unfolding gm04_mark_rule_def by (simp add: Let_def)
    have normal:
        "set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n)) \<subseteq> NF_terms Q"
      using NF_subst_right[OF restricted nfsubst] lr ipos
      unfolding gm04_mark_rule_def gm04_vars_def by (auto simp: Let_def)
    show thesis
    proof (rule that[of i \<sigma>])
      show "i \<in> \<mu> (f,length zs)" using active_i fg n by simp
      show "i < length zs" using ipos n by simp
      show "zs = (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
          [i := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
            (gm04_vars (length zs))) ! i]]"
        using zs n by simp
      show "u = Fun mark [Fun f
          (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
        using u fg n by simp
      show "set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
          \<subseteq> NF_terms Q"
        using normal n by simp
    qed
  next
    case proper
    then obtain g n where fn: "(g,n) \<in> set F"
      and lr: "(l,r) = gm04_proper_rule proper ok (g,n)" by auto
    from lhs lr fneq show thesis
      unfolding gm04_proper_rule_def by (auto simp: Let_def split: if_splits)
  next
    case ok
    then obtain g n where fn: "(g,n) \<in> set F" and positive: "n > 0"
      and lr: "(l,r) = gm04_ok_rule proper ok (g,n)" by auto
    from lhs lr positive have fg: "g = f" "n = length zs"
      unfolding gm04_ok_rule_def by (auto simp: Let_def split: if_splits)
    from rhs lr positive fresh have role_u:
      "gm04_phase_bit active mark proper ok u = False"
      unfolding gm04_ok_rule_def gm04_roles_fresh_def
      by (simp add: Let_def neq_commute)
    have rsteps: "(u,Fun mark [y]) \<in> (rstep S)\<^sup>*"
      by (rule qrsteps_into_rsteps[OF suffix])
    from gm04_non_top_steps_preserve_phase_bit[OF S fresh rsteps]
      role_u fresh show thesis
      unfolding gm04_roles_fresh_def by (simp add: neq_commute)
  qed
qed

lemma gm04_NF_qsteps_eq_early:
  assumes normal: "x \<in> NF_terms (lhss S)"
    and steps: "(x,y) \<in> (qrstep nfs (lhss S) S)\<^sup>*"
  shows "x = y"
proof -
  from qrsteps_into_rsteps[OF steps]
  have rsteps: "(x,y) \<in> (rstep S)\<^sup>*" .
  from normal have nf: "x \<in> NF (rstep S)"
    unfolding NF_terms_lhss .
  from rsteps nf show ?thesis by (rule NF_not_suc)
qed

lemma gm04_qstep_normal_wrapper_is_root_early:
  assumes normal: "x \<in> NF_terms (lhss S)"
    and step: "(Fun role [x],t) \<in> qrstep True (lhss S) S"
  shows "(Fun role [x],t) \<in> rqrstep True (lhss S) S"
proof -
  from step consider
      (root) "(Fun role [x],t) \<in> rqrstep True (lhss S) S"
    | (nonroot) "(Fun role [x],t) \<in> nrqrstep True (lhss S) S"
    unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
  then show ?thesis
  proof cases
    case root
    then show ?thesis .
  next
    case nonroot
    from nrqrstep_imp_arg_qrstep[OF nonroot]
    obtain i where i: "i < length (args (Fun role [x]))"
      and arg: "(args (Fun role [x]) ! i, args t ! i)
        \<in> qrstep True (lhss S) S" by blast
    from i have "i = 0" by simp
    with arg have qarg:
        "(x,args t ! 0) \<in> qrstep True (lhss S) S" by simp
    have "(x,args t ! 0) \<in> rstep S"
      by (rule qrstep_into_rstep[OF qarg])
    then have reducible: "\<exists>u. (x,u) \<in> rstep S" by blast
    have false: False
      using normal reducible unfolding NF_terms_lhss NF_def by blast
    from false show ?thesis by (rule FalseE)
  qed
qed

lemma gm04_active_descent_connector:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf: "wf_trs S"
    and source_root: "(f,length xs) \<in> set F"
    and finite_mu: "finite (\<mu> (f,length xs))"
    and i: "i < length xs" "i \<in> \<mu> (f,length xs)"
    and normal_x: "Fun f xs \<in> NF_terms (lhss S)"
    and normal_y: "y \<in> NF_terms (lhss S)"
    and suffix: "(Fun f (xs[i := Fun active [xs ! i]]),Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
    and child: "\<And>z. z \<in> NF_terms (lhss S) \<Longrightarrow>
      (Fun active [xs ! i],Fun mark [z])
        \<in> (qrstep True (lhss S) S)\<^sup>* \<Longrightarrow>
      (gm04_erase {active,mark,proper,ok} (xs ! i),
       gm04_erase {active,mark,proper,ok} z)
        \<in> (csstep \<mu> (set R))\<^sup>+"
  shows "(gm04_erase {active,mark,proper,ok} (Fun f xs),
      gm04_erase {active,mark,proper,ok} y)
    \<in> (csstep \<mu> (set R))\<^sup>+"
proof -
  let ?start = "Fun f (xs[i := Fun active [xs ! i]])"
  from qrsteps_rqrstep_cases_nrqrstep[OF suffix]
  consider
      (same_root) zs where "length zs = length xs"
        "Fun mark [y] = Fun f zs"
    | (root) "(?start,Fun mark [y])
        \<in> (nrqrstep True (lhss S) S)\<^sup>* O
          rqrstep True (lhss S) S O
          (qrstep True (lhss S) S)\<^sup>*"
    by auto
  then show ?thesis
  proof cases
    case same_root
    from fresh source_root same_root show ?thesis
      unfolding gm04_roles_fresh_def by auto
  next
    case root
    then obtain v w where pre: "(?start,v)
        \<in> (nrqrstep True (lhss S) S)\<^sup>*"
      and root_step: "(v,w) \<in> rqrstep True (lhss S) S"
      and post: "(w,Fun mark [y])
        \<in> (qrstep True (lhss S) S)\<^sup>*" by auto
    from nrqrsteps_preserve_root_fun[OF pre]
    obtain zs where v: "v = Fun f zs" by blast
    have len_zs: "length zs = length xs"
      using nrqrsteps_num_args[OF pre] unfolding v by simp
    have arg_steps: "\<And>k. k < length xs \<Longrightarrow>
        ((xs[i := Fun active [xs ! i]]) ! k,zs ! k)
          \<in> (qrstep True (lhss S) S)\<^sup>*"
    proof -
      fix k
      assume k: "k < length xs"
      from nrqrsteps_imp_arg_qrsteps[OF pre, of k] k len_zs
      show "((xs[i := Fun active [xs ! i]]) ! k,zs ! k)
          \<in> (qrstep True (lhss S) S)\<^sup>*"
        unfolding v by simp
    qed
    have finite_zs: "finite (\<mu> (f,length zs))"
      using finite_mu len_zs by simp
    have source_root_zs: "(f,length zs) \<in> set F"
      using source_root len_zs by simp
    from gm04_root_source_step_to_mark_cases_early[
        OF S fresh source_root_zs finite_zs TrueI root_step[unfolded v] post]
    obtain j \<sigma> where j: "j \<in> \<mu> (f,length zs)" "j < length zs"
      and zs: "zs = (map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars (length zs)))
        [j := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars (length zs))) ! j]]"
      and w: "w = Fun mark [Fun f
          (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
      and normal_us: "set (map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars (length zs))) \<subseteq> NF_terms (lhss S)" by blast
    let ?us = "map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs))"
    have len_us: "length ?us = length xs" using len_zs by simp
    have ji: "j = i"
    proof (rule ccontr)
      assume neq: "j \<noteq> i"
      have jx: "j < length xs" using j(2) len_zs by simp
      have normal_j: "xs ! j \<in> NF_terms (lhss S)"
        by (rule gm04_NF_terms_subterm[OF normal_x], simp add: jx)
      have path_j: "(xs ! j,Fun mark [?us ! j])
          \<in> (qrstep True (lhss S) S)\<^sup>*"
        using arg_steps[OF jx] zs j(2) len_zs neq i(1) by simp
      have xj: "xs ! j = Fun mark [?us ! j]"
        by (rule gm04_NF_qsteps_eq_early[OF normal_j path_j])
      let ?base = "xs[j := ?us ! j]"
      have listed_j:
          "j \<in> set (sorted_list_of_set (\<mu> (f,length xs)))"
        using j(1) finite_mu len_zs by simp
      have in_block:
          "gm04_mark_rule mark (f,length xs) j \<in>
            set (map (gm04_mark_rule mark (f,length xs))
              (filter (\<lambda>k. k < length xs)
                (sorted_list_of_set (\<mu> (f,length xs)))))"
        using listed_j j(2) len_zs by simp
      have block_member:
          "map (gm04_mark_rule mark (f,length xs))
              (filter (\<lambda>k. k < length xs)
                (sorted_list_of_set (\<mu> (f,length xs))))
            \<in> set (map (\<lambda>fn. map (gm04_mark_rule mark fn)
              (filter (\<lambda>k. k < snd fn)
                (sorted_list_of_set (\<mu> fn)))) F)"
        unfolding set_map
      proof (rule image_eqI[where x="(f,length xs)"])
        show "map (gm04_mark_rule mark (f,length xs))
            (filter (\<lambda>k. k < length xs)
              (sorted_list_of_set (\<mu> (f,length xs)))) =
          map (gm04_mark_rule mark (f,length xs))
            (filter (\<lambda>k. k < snd (f,length xs))
              (sorted_list_of_set (\<mu> (f,length xs))))" by simp
        show "(f,length xs) \<in> set F" by (rule source_root)
      qed
      have generated_mark:
          "gm04_mark_rule mark (f,length xs) j
            \<in> set (gm04_mark_rules \<mu> mark F)"
        unfolding gm04_mark_rules_def set_concat
        using block_member in_block by blast
      have mark_rule: "gm04_mark_rule mark (f,length xs) j \<in> S"
        unfolding S gm04_non_top_rules_def
        using generated_mark by auto
      have len_base: "length ?base = length xs" by simp
      have mark_rule_base:
          "gm04_mark_rule mark (f,length ?base) j \<in> S"
        using mark_rule len_base by simp
      have redex: "(Fun f xs,Fun mark [Fun f ?base]) \<in> rstep S"
      proof -
        have raw: "(Fun f (?base[j := Fun mark [?base ! j]]),
            Fun mark [Fun f ?base]) \<in> rstep S"
          by (rule gm04_mark_rule_instance[OF mark_rule_base],
              simp add: jx len_base)
        have base_nth: "?base ! j = ?us ! j" using jx by simp
        have replacement: "Fun mark [?us ! j] = xs ! j"
          by (rule sym[OF xj])
        have restore: "?base[j := Fun mark [?base ! j]] = xs"
          unfolding base_nth replacement by (simp add: jx)
        from raw show ?thesis unfolding restore .
      qed
      from normal_x[unfolded NF_terms_lhss] redex show False by blast
    qed
    have child_path: "(Fun active [xs ! i],Fun mark [?us ! i])
        \<in> (qrstep True (lhss S) S)\<^sup>*"
      using arg_steps[OF i(1)] zs ji i len_zs by simp
    have normal_ui: "?us ! i \<in> NF_terms (lhss S)"
      using normal_us i(1) len_us by auto
    have child_steps: "(gm04_erase {active,mark,proper,ok} (xs ! i),
        gm04_erase {active,mark,proper,ok} (?us ! i))
        \<in> (csstep \<mu> (set R))\<^sup>+"
      by (rule child[OF normal_ui child_path])
    have other_eq: "\<And>k. k < length xs \<Longrightarrow> k \<noteq> i \<Longrightarrow>
        xs ! k = ?us ! k"
    proof -
      fix k
      assume k: "k < length xs" and neq: "k \<noteq> i"
      have normal_k: "xs ! k \<in> NF_terms (lhss S)"
        by (rule gm04_NF_terms_subterm[OF normal_x], simp add: k)
      have path_k: "(xs ! k,?us ! k)
          \<in> (qrstep True (lhss S) S)\<^sup>*"
        using arg_steps[OF k] zs ji k neq i(1) len_zs by simp
      show "xs ! k = ?us ! k"
        by (rule gm04_NF_qsteps_eq_early[OF normal_k path_k])
    qed
    have updated: "xs[i := ?us ! i] = ?us"
    proof (rule nth_equalityI)
      show "length (xs[i := ?us ! i]) = length ?us"
        using len_us by simp
      fix k
      assume k: "k < length (xs[i := ?us ! i])"
      show "(xs[i := ?us ! i]) ! k = ?us ! k"
      proof (cases "k = i")
        case True
        with k i(1) show ?thesis by simp
      next
        case False
        from other_eq[of k] k False show ?thesis by simp
      qed
    qed
    let ?W = "{active,mark,proper,ok}"
    have lifted: "(Fun f (map (gm04_erase ?W) xs),
        Fun f (map (gm04_erase ?W) ?us))
        \<in> (csstep \<mu> (set R))\<^sup>+"
    proof -
      have raw: "(Fun f (map (gm04_erase ?W) xs),
          Fun f ((map (gm04_erase ?W) xs)
            [i := gm04_erase ?W (?us ! i)]))
          \<in> (csstep \<mu> (set R))\<^sup>+"
      proof (rule gm04_csstep_trancl_descend)
        show "i < length (map (gm04_erase ?W) xs)" using i(1) by simp
        show "i \<in> \<mu> (f,length (map (gm04_erase ?W) xs))"
          using i(2) by simp
        show "((map (gm04_erase ?W) xs) ! i,
            gm04_erase ?W (?us ! i))
            \<in> (csstep \<mu> (set R))\<^sup>+"
          using child_steps i(1) by simp
      qed
      have mapped_updated:
          "(map (gm04_erase ?W) xs)[i := gm04_erase ?W (?us ! i)] =
            map (gm04_erase ?W) ?us"
      proof -
        from arg_cong[OF updated, of "map (gm04_erase ?W)"]
        show ?thesis by (simp add: map_update)
      qed
      from raw show ?thesis unfolding mapped_updated .
    qed
    have lhs_fun: "\<forall>(a,b)\<in>S. is_Fun a"
      using wf unfolding wf_trs_def by blast
    have undef_mark: "\<not> defined S (mark,1)"
      unfolding S by (rule gm04_non_top_role_not_defined[OF fresh], simp)
    have final_inner: "(Fun f ?us,y)
        \<in> (qrstep True (lhss S) S)\<^sup>*"
      using post w gm04_q_top_wrapper_rsteps_iff[
        OF lhs_fun undef_mark, of "Fun f ?us" y True "lhss S"] by simp
    have source_safe: "gm04_active_safe active (lhss S) (Fun f ?us)"
    proof -
      have raw: "gm04_active_safe active (lhss S)
          (Fun f (gm04_vars (length zs)) \<cdot> \<sigma>)"
      proof (rule gm04_source_instance_active_safe)
        show "gm04_roles_fresh active mark proper ok top_sym F" by fact
        show "funas_term (Fun f (gm04_vars (length zs))) \<subseteq> set F"
          using source_root len_zs unfolding gm04_vars_def by simp
        show "\<And>x. x \<in> vars_term (Fun f (gm04_vars (length zs))) \<Longrightarrow>
            \<sigma> x \<in> NF_terms (lhss S)"
          using normal_us unfolding gm04_vars_def by auto
      qed
      from raw show ?thesis by simp
    qed
    have final_erased: "gm04_erase ?W (Fun f ?us) = gm04_erase ?W y"
      using gm04_active_safe_qsteps_preserve[
        OF S fresh source_safe final_inner] by blast
    have f_fresh:
        "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
      using fresh source_root unfolding gm04_roles_fresh_def by auto
    have erase_x: "gm04_erase ?W (Fun f xs) =
        Fun f (map (gm04_erase ?W) xs)"
      using f_fresh by simp
    have erase_us: "gm04_erase ?W (Fun f ?us) =
        Fun f (map (gm04_erase ?W) ?us)"
      using f_fresh by simp
    have target_eq: "Fun f (map (gm04_erase ?W) ?us) =
        gm04_erase ?W y"
      using final_erased unfolding erase_us .
    from lifted show ?thesis unfolding erase_x target_eq .
  qed
qed

lemma gm04_root_active_step_cases:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and step: "(Fun active [x],t) \<in> rqrstep nfs Q S"
  obtains l r \<sigma> where
      "(l,r) \<in> set R" "x = l \<cdot> \<sigma>" "t = Fun mark [r \<cdot> \<sigma>]"
      "NF_subst nfs (Fun active [l],Fun mark [r]) \<sigma> Q"
    | f n i \<sigma> where
      "(f,n) \<in> set F" "i \<in> \<mu> (f,n)" "i < n"
      "x = Fun f (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
      "t = Fun f ((map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))
        [i := Fun active [(map (\<lambda>u. u \<cdot> \<sigma>)
          (gm04_vars n)) ! i]])"
      "NF_subst nfs (gm04_active_rule active (f,n) i) \<sigma> Q"
proof -
  from step obtain l r \<sigma> where pair: "(l,r) \<in> S"
    and lhs: "Fun active [x] = l \<cdot> \<sigma>"
    and rhs: "t = r \<cdot> \<sigma>"
    and nfsubst: "NF_subst nfs (l,r) \<sigma> Q"
    unfolding rqrstep_def by auto
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))" by auto
  then show thesis
  proof cases
    case source
    then obtain l0 r0 where lr0: "(l0,r0) \<in> set R"
      and lr: "(l,r) = (Fun active [l0],Fun mark [r0])"
      unfolding gm04_source_rules_def by auto
    show thesis
    proof (rule that(1)[OF lr0])
      show "x = l0 \<cdot> \<sigma>" using lhs lr by simp
      show "t = Fun mark [r0 \<cdot> \<sigma>]" using rhs lr by simp
      show "NF_subst nfs (Fun active [l0],Fun mark [r0]) \<sigma> Q"
        using nfsubst lr by simp
    qed
  next
    case active
    then obtain f n i where fn: "(f,n) \<in> set F"
      and listed: "i \<in> set (sorted_list_of_set (\<mu> (f,n)))"
      and ipos: "i < n"
      and lr: "(l,r) = gm04_active_rule active (f,n) i"
      unfolding gm04_active_rules_def by auto
    have active_i: "i \<in> \<mu> (f,n)"
      using listed finite_mu[of f n] by simp
    from lhs lr have x: "x = Fun f
        (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
      unfolding gm04_active_rule_def by (simp add: Let_def)
    have nth: "gm04_vars n ! i \<cdot> \<sigma> =
        map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n) ! i"
      using ipos by simp
    from rhs lr have t: "t = Fun f
        ((map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))
          [i := Fun active [(map (\<lambda>u. u \<cdot> \<sigma>)
            (gm04_vars n)) ! i]])"
      unfolding gm04_active_rule_def
      using nth ipos by (simp add: Let_def map_update)
    show thesis
    proof (rule that(2)[OF fn active_i ipos x t])
      show "NF_subst nfs (gm04_active_rule active (f,n) i) \<sigma> Q"
        using nfsubst lr by simp
    qed
  next
    case mark
    then obtain f n i where fn: "(f,n) \<in> set F" and lr:
        "(l,r) = gm04_mark_rule mark (f,n) i"
      unfolding gm04_mark_rules_def by auto
    from fresh fn have fneq: "f \<noteq> active"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr fneq show thesis
      unfolding gm04_mark_rule_def gm04_roles_fresh_def
      by (auto simp: Let_def split: if_splits)
  next
    case proper
    then obtain f n where fn: "(f,n) \<in> set F"
      and lr: "(l,r) = gm04_proper_rule proper ok (f,n)" by auto
    from fresh fn have neq: "f \<noteq> active" "proper \<noteq> active"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr neq show thesis
      unfolding gm04_proper_rule_def by (auto simp: Let_def split: if_splits)
  next
    case ok
    then obtain f n where fn: "(f,n) \<in> set F"
      and positive: "n > 0"
      and lr: "(l,r) = gm04_ok_rule proper ok (f,n)" by auto
    from fresh fn have neq: "f \<noteq> active" "proper \<noteq> active"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr neq positive show thesis
      unfolding gm04_ok_rule_def by (auto simp: Let_def split: if_splits)
  qed
qed

lemma gm04_active_mark_q_converse:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and normal_x: "x \<in> NF_terms (lhss S)"
    and normal_y: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun active [x],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  shows "(gm04_erase {active,mark,proper,ok} x,
      gm04_erase {active,mark,proper,ok} y)
    \<in> (csstep \<mu> (set R))\<^sup>+"
  using normal_x normal_y steps
proof (induct x arbitrary: y)
  case (Var v)
  from fresh have neq: "active \<noteq> mark"
    unfolding gm04_roles_fresh_def by auto
  from Var.prems(3) obtain u where first:
      "(Fun active [Var v],u) \<in> qrstep True (lhss S) S"
    and suffix: "(u,Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  proof (cases rule: converse_rtranclE)
    case base
    with neq show ?thesis by simp
  next
    case (step u)
    show thesis
    proof (rule that[of u])
      show "(Fun active [Var v],u) \<in> qrstep True (lhss S) S"
        by (rule step(1))
      show "(u,Fun mark [y]) \<in> (qrstep True (lhss S) S)\<^sup>*"
        by (rule step(2))
    qed
  qed
  have root: "(Fun active [Var v],u)
      \<in> rqrstep True (lhss S) S"
    by (rule gm04_qstep_normal_wrapper_is_root_early[OF Var.prems(1) first])
  from gm04_root_active_step_cases[OF S fresh finite_mu root]
  show ?case
  proof cases
    fix l r \<sigma>
    assume lr: "(l,r) \<in> set R" and x: "Var v = l \<cdot> \<sigma>"
    from wf_source lr obtain f ls where "l = Fun f ls"
      unfolding wf_trs_def by blast
    with x show ?thesis by simp
  next
    fix f n i \<sigma>
    assume "Var v = Fun f
      (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
    then show ?thesis by simp
  qed
next
  case (Fun f xs)
  from fresh have neq: "active \<noteq> mark"
    unfolding gm04_roles_fresh_def by auto
  from Fun.prems(3) obtain u where first:
      "(Fun active [Fun f xs],u) \<in> qrstep True (lhss S) S"
    and suffix: "(u,Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  proof (cases rule: converse_rtranclE)
    case base
    with neq show ?thesis by simp
  next
    case (step u)
    show thesis
    proof (rule that[of u])
      show "(Fun active [Fun f xs],u) \<in> qrstep True (lhss S) S"
        by (rule step(1))
      show "(u,Fun mark [y]) \<in> (qrstep True (lhss S) S)\<^sup>*"
        by (rule step(2))
    qed
  qed
  have root: "(Fun active [Fun f xs],u)
      \<in> rqrstep True (lhss S) S"
    by (rule gm04_qstep_normal_wrapper_is_root_early[OF Fun.prems(1) first])
  from gm04_root_active_step_cases[OF S fresh finite_mu root]
  show ?case
  proof cases
    fix l r \<sigma>
    assume lr: "(l,r) \<in> set R"
      and x: "Fun f xs = l \<cdot> \<sigma>"
      and u: "u = Fun mark [r \<cdot> \<sigma>]"
      and nfs: "NF_subst True (Fun active [l],Fun mark [r])
        \<sigma> (lhss S)"
    show ?thesis
      by (rule gm04_active_root_source_connector[
        OF S fresh signature lr x nfs suffix[unfolded u] wf])
  next
    fix g n i \<sigma>
    assume fn: "(g,n) \<in> set F" and active_i: "i \<in> \<mu> (g,n)"
      and i: "i < n"
      and x: "Fun f xs = Fun g
        (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
      and u: "u = Fun g
        ((map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))
          [i := Fun active [(map (\<lambda>u. u \<cdot> \<sigma>)
            (gm04_vars n)) ! i]])"
    from x have gf: "g = f" and n: "n = length xs"
      and args: "map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n) = xs"
      by auto
    have source_root: "(f,length xs) \<in> set F" using fn gf n by simp
    have below: "i < length xs" using i n by simp
    have active_i': "i \<in> \<mu> (f,length xs)" using active_i gf n by simp
    have nth: "(map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n)) ! i = xs ! i"
      using arg_cong[OF args, of "\<lambda>ys. ys ! i"] by simp
    have start_eq:
        "Fun g ((map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))
          [i := Fun active [(map (\<lambda>u. u \<cdot> \<sigma>)
            (gm04_vars n)) ! i]]) =
         Fun f (xs[i := Fun active [xs ! i]])"
      using gf args nth by simp
    have old_suffix:
        "(Fun g ((map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))
          [i := Fun active [(map (\<lambda>u. u \<cdot> \<sigma>)
            (gm04_vars n)) ! i]]),Fun mark [y])
          \<in> (qrstep True (lhss S) S)\<^sup>*"
      using suffix u by simp
    have suffix': "(Fun f (xs[i := Fun active [xs ! i]]),Fun mark [y])
        \<in> (qrstep True (lhss S) S)\<^sup>*"
      using old_suffix unfolding start_eq .
    show ?thesis
    proof (rule gm04_active_descent_connector[
        OF S fresh signature wf source_root finite_mu below active_i'
          Fun.prems(1) Fun.prems(2) suffix'])
      fix z
      assume normal_z: "z \<in> NF_terms (lhss S)"
        and child_path: "(Fun active [xs ! i],Fun mark [z])
          \<in> (qrstep True (lhss S) S)\<^sup>*"
      have member: "xs ! i \<in> set xs" by (rule nth_mem[OF below])
      have normal_child: "xs ! i \<in> NF_terms (lhss S)"
        by (rule gm04_NF_terms_subterm[OF Fun.prems(1)], simp add: below)
      show "(gm04_erase {active,mark,proper,ok} (xs ! i),
          gm04_erase {active,mark,proper,ok} z)
          \<in> (csstep \<mu> (set R))\<^sup>+"
        by (rule Fun.hyps[OF member normal_child normal_z child_path])
    qed
  qed
qed

lemma gm04_qstep_normal_wrapper_is_root:
  assumes normal: "x \<in> NF_terms (lhss S)"
    and step: "(Fun role [x],t) \<in> qrstep True (lhss S) S"
  shows "(Fun role [x],t) \<in> rqrstep True (lhss S) S"
proof -
  from step consider
      (root) "(Fun role [x],t) \<in> rqrstep True (lhss S) S"
    | (nonroot) "(Fun role [x],t) \<in> nrqrstep True (lhss S) S"
    unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
  then show ?thesis
  proof cases
    case root
    then show ?thesis .
  next
    case nonroot
    from nrqrstep_imp_arg_qrstep[OF nonroot]
    obtain i where i: "i < length (args (Fun role [x]))"
      and arg: "(args (Fun role [x]) ! i, args t ! i)
        \<in> qrstep True (lhss S) S" by blast
    from i have "i = 0" by simp
    with arg have qarg:
        "(x,args t ! 0) \<in> qrstep True (lhss S) S" by simp
    have "(x,args t ! 0) \<in> rstep S"
      by (rule qrstep_into_rstep[OF qarg])
    then have reducible: "\<exists>u. (x,u) \<in> rstep S" by blast
    have false: False
      using normal reducible unfolding NF_terms_lhss NF_def by blast
    from false show ?thesis by (rule FalseE)
  qed
qed

lemma gm04_NF_qsteps_eq:
  assumes normal: "x \<in> NF_terms (lhss S)"
    and steps: "(x,y) \<in> (qrstep nfs (lhss S) S)\<^sup>*"
  shows "x = y"
proof -
  from qrsteps_into_rsteps[OF steps]
  have rsteps: "(x,y) \<in> (rstep S)\<^sup>*" .
  from normal have nf: "x \<in> NF (rstep S)"
    unfolding NF_terms_lhss .
  from rsteps nf show ?thesis by (rule NF_not_suc)
qed

lemma gm04_root_proper_step_cases:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and step: "(Fun proper [x],t) \<in> rqrstep nfs Q S"
  obtains f n \<sigma> where
      "(f,n) \<in> set F"
      "x = Fun f (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
      "t = snd (gm04_proper_rule proper ok (f,n)) \<cdot> \<sigma>"
proof -
  from step obtain l r \<sigma> where pair: "(l,r) \<in> S"
    and lhs: "Fun proper [x] = l \<cdot> \<sigma>"
    and rhs: "t = r \<cdot> \<sigma>"
    unfolding rqrstep_def by auto
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))" by auto
  then show thesis
  proof cases
    case source
    with lhs fresh show thesis
      unfolding gm04_source_rules_def gm04_roles_fresh_def
      by (auto split: prod.splits)
  next
    case active
    then obtain f n i where lr:
        "(l,r) = gm04_active_rule active (f,n) i"
      unfolding gm04_active_rules_def by auto
    from lhs lr fresh show thesis
      unfolding gm04_active_rule_def gm04_roles_fresh_def
      by (auto simp: Let_def)
  next
    case mark
    then obtain f n i where fn: "(f,n) \<in> set F" and lr:
        "(l,r) = gm04_mark_rule mark (f,n) i"
      unfolding gm04_mark_rules_def by auto
    from fresh fn have fneq: "f \<noteq> proper"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr fneq show thesis
      unfolding gm04_mark_rule_def by (auto simp: Let_def)
  next
    case proper
    then obtain f n where fn: "(f,n) \<in> set F"
      and lr: "(l,r) = gm04_proper_rule proper ok (f,n)" by auto
    from fresh fn have neq: "f \<noteq> proper"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr have x: "x = Fun f
        (map (\<lambda>u. u \<cdot> \<sigma>) (gm04_vars n))"
      unfolding gm04_proper_rule_def
      using neq by (auto simp: Let_def split: if_splits)
    have r_snd: "r = snd (gm04_proper_rule proper ok (f,n))"
      using arg_cong[OF lr, of snd] by simp
    have target:
        "t = snd (gm04_proper_rule proper ok (f,n)) \<cdot> \<sigma>"
      using rhs unfolding r_snd .
    show thesis by (rule that[OF fn x target])
  next
    case ok
    then obtain f n where fn: "(f,n) \<in> set F"
      and positive: "n > 0"
      and lr: "(l,r) = gm04_ok_rule proper ok (f,n)" by auto
    from fresh fn have neq: "f \<noteq> proper"
      unfolding gm04_roles_fresh_def by auto
    from lhs lr neq positive show thesis
      unfolding gm04_ok_rule_def by (auto simp: Let_def split: if_splits)
  qed
qed

lemma gm04_root_source_step_to_ok_cases:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source_root: "(f,length zs) \<in> set F"
    and root_step: "(Fun f zs,u) \<in> rqrstep nfs Q S"
    and suffix: "(u,Fun ok [y]) \<in> (qrstep nfs Q S)\<^sup>*"
  obtains \<sigma> where
      "zs = map (\<lambda>x. Fun ok [x \<cdot> \<sigma>])
        (gm04_vars (length zs))"
      "u = Fun ok [Fun f
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
      "nfs \<Longrightarrow> set (map (\<lambda>x. x \<cdot> \<sigma>)
        (gm04_vars (length zs))) \<subseteq> NF_terms Q"
proof -
  from root_step obtain l r \<sigma> where
    nf: "\<forall>v\<lhd>l \<cdot> \<sigma>. v \<in> NF_terms Q"
    and pair: "(l,r) \<in> S"
    and lhs: "Fun f zs = l \<cdot> \<sigma>"
    and rhs: "u = r \<cdot> \<sigma>"
    unfolding rqrstep_def by auto
  from fresh source_root have fneq:
      "f \<noteq> active" "f \<noteq> mark" "f \<noteq> proper" "f \<noteq> ok"
    unfolding gm04_roles_fresh_def by auto
  from pair[unfolded S gm04_non_top_rules_def]
  consider
      (source) "(l,r) \<in> set (gm04_source_rules active mark R)"
    | (active) "(l,r) \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "(l,r) \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "(l,r) \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "(l,r) \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))" by auto
  then show thesis
  proof cases
    case source
    with lhs fneq show thesis
      unfolding gm04_source_rules_def by (auto split: prod.splits)
  next
    case active
    then obtain g n i where lr:
        "(l,r) = gm04_active_rule active (g,n) i"
      unfolding gm04_active_rules_def by auto
    from lhs lr fneq show thesis
      unfolding gm04_active_rule_def by (auto simp: Let_def)
  next
    case mark
    from mark obtain g n i where fn: "(g,n) \<in> set F" and
      lr: "(l,r) = gm04_mark_rule mark (g,n) i"
      unfolding gm04_mark_rules_def by auto
    from lhs lr have fg: "g = f" "n = length zs"
      unfolding gm04_mark_rule_def by (auto simp: Let_def)
    from rhs lr have role_u:
      "gm04_phase_bit active mark proper ok u = True"
      unfolding gm04_mark_rule_def by (simp add: Let_def)
    have rsteps: "(u,Fun ok [y]) \<in> (rstep S)\<^sup>*"
      by (rule qrsteps_into_rsteps[OF suffix])
    have phase_eq:
        "gm04_phase_bit active mark proper ok u =
          gm04_phase_bit active mark proper ok (Fun ok [y])"
      by (rule gm04_non_top_steps_preserve_phase_bit[OF S fresh rsteps])
    from fresh have ok_neq: "ok \<noteq> active" "ok \<noteq> mark"
      unfolding gm04_roles_fresh_def by auto
    have phase_ok:
        "gm04_phase_bit active mark proper ok (Fun ok [y]) = False"
      using ok_neq by simp
    from phase_eq role_u phase_ok have False by simp
    then show thesis by (rule FalseE)
  next
    case proper
    then obtain g n where fn: "(g,n) \<in> set F"
      and lr: "(l,r) = gm04_proper_rule proper ok (g,n)" by auto
    from lhs lr fneq show thesis
      unfolding gm04_proper_rule_def by (auto simp: Let_def split: if_splits)
  next
    case ok
    then obtain g n where fn: "(g,n) \<in> set F" and positive: "n > 0"
      and lr: "(l,r) = gm04_ok_rule proper ok (g,n)" by auto
    from lhs lr fneq have fg: "g = f" "n = length zs"
      and zs: "zs = map (\<lambda>x. Fun ok [x \<cdot> \<sigma>]) (gm04_vars n)"
      unfolding gm04_ok_rule_def
      by (auto simp: Let_def o_def split: if_splits)
    from rhs lr positive have u: "u = Fun ok [Fun g
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n))]"
      unfolding gm04_ok_rule_def by (simp add: Let_def o_def)
    have normal: "set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n))
        \<subseteq> NF_terms Q"
    proof
      fix z
      assume z: "z \<in> set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars n))"
      have "Fun ok [z] \<lhd> Fun f zs"
        using z zs by auto
      from nf[rule_format, OF this[unfolded lhs]]
      show "z \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm, simp)
    qed
    show thesis
    proof (rule that[of \<sigma>])
      show "zs = map (\<lambda>x. Fun ok [x \<cdot> \<sigma>])
          (gm04_vars (length zs))"
        using zs fg by simp
      show "u = Fun ok [Fun f
          (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
        using u fg by simp
      assume nfs
      show "set (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
          \<subseteq> NF_terms Q"
        using normal fg by simp
    qed
  qed
qed


lemma gm04_proper_ok_q_converse:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and wf: "wf_trs S"
    and normal_x: "x \<in> NF_terms (lhss S)"
    and normal_y: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun proper [x],Fun ok [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  shows "x = y"
  using normal_x normal_y steps
proof (induct x arbitrary: y)
  case (Var v)
  from fresh have neq: "proper \<noteq> ok"
    unfolding gm04_roles_fresh_def by auto
  have different: "Fun proper [Var v] \<noteq> Fun ok [y]"
    using neq by auto
  from Var.prems(3) different obtain u where first:
      "(Fun proper [Var v],u) \<in> qrstep True (lhss S) S"
    and suffix: "(u,Fun ok [y]) \<in> (qrstep True (lhss S) S)\<^sup>*"
    by (cases rule: converse_rtranclE) auto
  have root: "(Fun proper [Var v],u)
      \<in> rqrstep True (lhss S) S"
    by (rule gm04_qstep_normal_wrapper_is_root[OF Var.prems(1) first])
  from gm04_root_proper_step_cases[OF S fresh root]
  show ?case by auto
next
  case (Fun f xs)
  from fresh have neq: "proper \<noteq> ok"
    unfolding gm04_roles_fresh_def by auto
  have different: "Fun proper [Fun f xs] \<noteq> Fun ok [y]"
    using neq by auto
  from Fun.prems(3) different obtain u where first:
      "(Fun proper [Fun f xs],u) \<in> qrstep True (lhss S) S"
    and suffix: "(u,Fun ok [y]) \<in> (qrstep True (lhss S) S)\<^sup>*"
    by (cases rule: converse_rtranclE) auto
  have root: "(Fun proper [Fun f xs],u)
      \<in> rqrstep True (lhss S) S"
    by (rule gm04_qstep_normal_wrapper_is_root[OF Fun.prems(1) first])
  from gm04_root_proper_step_cases[OF S fresh root]
  obtain g n \<sigma> where fn: "(g,n) \<in> set F"
    and x: "Fun f xs = Fun g
      (map (\<lambda>z. z \<cdot> \<sigma>) (gm04_vars n))"
    and u: "u = snd (gm04_proper_rule proper ok (g,n)) \<cdot> \<sigma>" .
  from x have fg: "g = f" and n: "n = length xs"
    and xs: "xs = map (\<lambda>z. z \<cdot> \<sigma>) (gm04_vars n)"
    by auto
  have source_root: "(f,length xs) \<in> set F" using fn fg n by simp
  show ?case
  proof (cases "xs = []")
    case True
    have u_ok: "u = Fun ok [Fun f xs]"
      using u fg n True
      by (simp add: gm04_proper_rule_def Let_def)
    have lhs_fun: "\<forall>(l,r)\<in>S. is_Fun l"
      using wf unfolding wf_trs_def by blast
    have undef_ok: "\<not> defined S (ok,1)"
      unfolding S
      by (rule gm04_non_top_role_not_defined[OF fresh], simp)
    have inner: "(Fun f xs,y) \<in> (qrstep True (lhss S) S)\<^sup>*"
      using suffix u_ok gm04_q_top_wrapper_rsteps_iff[
        OF lhs_fun undef_ok, of "Fun f xs" y True "lhss S"] by simp
    show ?thesis by (rule gm04_NF_qsteps_eq[OF Fun.prems(1) inner])
  next
    case nonempty: False
    have n_nonzero: "n \<noteq> 0" using n nonempty by auto
    have u_expand: "u = Fun f (map (\<lambda>z. Fun proper [z]) xs)"
      by (rule gm04_proper_rule_rhs_nonzero_instance[
        OF n_nonzero u fg xs])
    from qrsteps_rqrstep_cases_nrqrstep[OF suffix[unfolded u_expand]]
    consider
      (same_root) zs where "length zs = length xs"
        "Fun ok [y] = Fun f zs"
    | (root) "(Fun f (map (\<lambda>z. Fun proper [z]) xs),
          Fun ok [y])
        \<in> (nrqrstep True (lhss S) S)\<^sup>* O
          rqrstep True (lhss S) S O
          (qrstep True (lhss S) S)\<^sup>*"
      by auto
    then show ?thesis
    proof cases
      case same_root
      from fresh source_root same_root show ?thesis
        unfolding gm04_roles_fresh_def by auto
    next
      case root
      then obtain v w where pre:
          "(Fun f (map (\<lambda>z. Fun proper [z]) xs),v)
            \<in> (nrqrstep True (lhss S) S)\<^sup>*"
        and root_step: "(v,w) \<in> rqrstep True (lhss S) S"
        and post: "(w,Fun ok [y])
            \<in> (qrstep True (lhss S) S)\<^sup>*" by auto
      from nrqrsteps_preserve_root_fun[OF pre]
      obtain zs where v: "v = Fun f zs" by blast
      have len_zs: "length zs = length xs"
        using nrqrsteps_num_args[OF pre] unfolding v by simp
      have source_root_zs: "(f,length zs) \<in> set F"
        using source_root len_zs by simp
      have arg_steps: "\<And>i. i < length xs \<Longrightarrow>
          (Fun proper [xs ! i],zs ! i)
            \<in> (qrstep True (lhss S) S)\<^sup>*"
      proof -
        fix i
        assume i: "i < length xs"
        from nrqrsteps_imp_arg_qrsteps[OF pre, of i] i len_zs
        show "(Fun proper [xs ! i],zs ! i)
            \<in> (qrstep True (lhss S) S)\<^sup>*"
          unfolding v by simp
      qed
      from gm04_root_source_step_to_ok_cases[
          OF S fresh source_root_zs root_step[unfolded v] post]
      obtain \<tau> where zs:
          "zs = map (\<lambda>z. Fun ok [z \<cdot> \<tau>])
            (gm04_vars (length zs))"
        and w: "w = Fun ok [Fun f
            (map (\<lambda>z. z \<cdot> \<tau>) (gm04_vars (length zs)))]"
        and normal_us_cond:
          "True \<Longrightarrow>
          set (map (\<lambda>z. z \<cdot> \<tau>) (gm04_vars (length zs)))
            \<subseteq> NF_terms (lhss S)" by blast
      have normal_us:
          "set (map (\<lambda>z. z \<cdot> \<tau>) (gm04_vars (length zs)))
            \<subseteq> NF_terms (lhss S)"
        by (rule normal_us_cond[OF TrueI])
      let ?us = "map (\<lambda>z. z \<cdot> \<tau>) (gm04_vars (length zs))"
      have len_us: "length ?us = length xs" using len_zs by simp
      have eq_args: "\<And>i. i < length xs \<Longrightarrow> xs ! i = ?us ! i"
      proof -
        fix i
        assume i: "i < length xs"
        have mem_x: "xs ! i \<in> set xs" by (rule nth_mem[OF i])
        have nf_xi: "xs ! i \<in> NF_terms (lhss S)"
          by (rule gm04_NF_terms_subterm[OF Fun.prems(1)],
              simp add: i)
        have nf_ui: "?us ! i \<in> NF_terms (lhss S)"
          using normal_us i len_us by auto
        have path: "(Fun proper [xs ! i],Fun ok [?us ! i])
            \<in> (qrstep True (lhss S) S)\<^sup>*"
          using arg_steps[OF i] zs i len_zs len_us by simp
        show "xs ! i = ?us ! i"
          by (rule Fun.hyps[OF mem_x nf_xi nf_ui path])
      qed
      have xs_us: "xs = ?us"
        by (rule nth_equalityI[OF len_us[symmetric]], simp add: eq_args)
      have lhs_fun: "\<forall>(l,r)\<in>S. is_Fun l"
        using wf unfolding wf_trs_def by blast
      have undef_ok: "\<not> defined S (ok,1)"
        unfolding S
        by (rule gm04_non_top_role_not_defined[OF fresh], simp)
      have final_inner: "(Fun f xs,y)
          \<in> (qrstep True (lhss S) S)\<^sup>*"
        using post w xs_us gm04_q_top_wrapper_rsteps_iff[
          OF lhs_fun undef_ok, of "Fun f xs" y True "lhss S"] by simp
      show ?thesis
        by (rule gm04_NF_qsteps_eq[OF Fun.prems(1) final_inner])
    qed
  qed
qed

theorem gm04_finite_exact_top_pairs_q:
  fixes S :: "('f,string) trs"
  assumes source: "SN (csstep \<mu> R)"
    and lhs_fun: "\<forall>(l,r)\<in>S. is_Fun l"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and ok_mark: "ok \<noteq> mark"
    and active_ok_impossible: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun active [x], Fun ok [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      False"
    and proper_mark_impossible: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun proper [x], Fun mark [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      False"
    and active_mark: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun active [x], Fun mark [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      (gm04_erase W x,gm04_erase W y) \<in> (csstep \<mu> R)\<^sup>+"
    and proper_ok: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun proper [x], Fun ok [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      gm04_erase W x = gm04_erase W y"
  shows "finite_dpp (True,m,
      set (gm04_top_pairs active mark proper ok top_sharp),{},Q,S,{})"
proof (rule gm04_finite_qdpp_from_pair_connectors[
    OF SN_imp_SN_trancl[OF source], where
    decode="gm04_decode_top_pair_erased W mark"])
  fix l r l' r'
  assume first: "(l,r) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and second: "(l',r') \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and nf_first: "l \<in> NF_terms Q"
    and nf_second: "l' \<in> NF_terms Q"
    and connector: "(r,l') \<in> (qrstep True Q S)\<^sup>*"
  from gm04_top_pair_instance_cases[OF first]
  consider (first_ok) x where
      "l = Fun top_sharp [Fun ok [x]]"
      "r = Fun top_sharp [Fun active [x]]"
    | (first_mark) x where
      "l = Fun top_sharp [Fun mark [x]]"
      "r = Fun top_sharp [Fun proper [x]]" .
  then show "(gm04_decode_top_pair_erased W mark (l,r),
      gm04_decode_top_pair_erased W mark (l',r'))
      \<in> gm04_phase_rel ((csstep \<mu> R)\<^sup>+)"
  proof cases
    case (first_ok x)
    have nf_x: "x \<in> NF_terms Q"
      by (rule gm04_NF_terms_subterm[OF nf_first],
          simp add: first_ok Fun_supteq)
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 1 Fun_supteq)
      from connector first_ok 1
      have inner: "(Fun active [x], Fun ok [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from active_ok_impossible[OF nf_x nf_y inner]
      show ?thesis by (rule FalseE)
    next
      case (2 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 2 Fun_supteq)
      from connector first_ok 2
      have inner: "(Fun active [x], Fun mark [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from active_mark[OF nf_x nf_y inner] first_ok 2 show ?thesis
        unfolding gm04_decode_top_pair_erased_def gm04_phase_rel_def
        by (simp add: ok_mark)
    qed
  next
    case (first_mark x)
    have nf_x: "x \<in> NF_terms Q"
      by (rule gm04_NF_terms_subterm[OF nf_first],
          simp add: first_mark Fun_supteq)
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 1 Fun_supteq)
      from connector first_mark 1
      have inner: "(Fun proper [x], Fun ok [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from proper_ok[OF nf_x nf_y inner] first_mark 1 show ?thesis
        unfolding gm04_decode_top_pair_erased_def gm04_phase_rel_def
        by (simp add: ok_mark)
    next
      case (2 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 2 Fun_supteq)
      from connector first_mark 2
      have inner: "(Fun proper [x], Fun mark [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from proper_mark_impossible[OF nf_x nf_y inner]
      show ?thesis by (rule FalseE)
    qed
  qed
qed

theorem gm04_finite_exact_top_pairs_q_sig:
  fixes S :: "('f,string) trs"
    and c :: "('f,string) term \<Rightarrow> string"
  assumes cinj: "inj c"
    and source: "SN (sig_step Fsrc ((csstep \<mu> R)\<^sup>+))"
    and lhs_fun: "\<forall>(l,r)\<in>S. is_Fun l"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and ok_mark: "ok \<noteq> mark"
    and inn: "NF_terms Q \<subseteq> NF_trs S"
    and qf: "QF_cond G Q"
    and rules_sig: "funas_trs S \<subseteq> G"
    and pairs_sig: "funas_args_trs
      (set (gm04_top_pairs active mark proper ok top_sharp)) \<subseteq> G"
    and wwf: "wwf_qtrs Q S"
    and erased_sig: "\<And>x :: ('f,string) term. funas_term x \<subseteq> G \<Longrightarrow>
      funas_term (gm04_erase W x) \<subseteq> Fsrc"
    and active_ok_impossible: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun active [x], Fun ok [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      False"
    and proper_mark_impossible: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun proper [x], Fun mark [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      False"
    and active_mark: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun active [x], Fun mark [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      (gm04_erase W x,gm04_erase W y) \<in> (csstep \<mu> R)\<^sup>+"
    and proper_ok: "\<And>x y.
      x \<in> NF_terms Q \<Longrightarrow> y \<in> NF_terms Q \<Longrightarrow>
      (Fun proper [x], Fun ok [y]) \<in> (qrstep True Q S)\<^sup>* \<Longrightarrow>
      gm04_erase W x = gm04_erase W y"
  shows "finite_dpp (True,m,
      set (gm04_top_pairs active mark proper ok top_sharp),{},Q,S,{})"
proof (rule gm04_finite_qdpp_from_pair_connectors_sig[
    OF cinj source inn qf rules_sig pairs_sig wwf, where
      decode="gm04_decode_top_pair_erased W mark"])
  fix s t
  assume pair: "(s,t) \<in>
      set (gm04_top_pairs active mark proper ok top_sharp)"
  have undef_applicable:
      "\<not> defined (applicable_rules Q S) (top_sharp,1)"
    by (rule ndef_applicable_rules[OF fresh_top])
  from pair show "is_Fun s \<and> is_Fun t \<and>
      \<not> defined (applicable_rules Q S) (the (root t))"
    using undef_applicable unfolding gm04_top_pairs_def by auto
next
  fix s t
  assume "(s,t) \<in> set (gm04_top_pairs active mark proper ok top_sharp)"
  then show "vars_term t \<subseteq> vars_term s"
    unfolding gm04_top_pairs_def by auto
next
  fix l r l' r'
  assume first: "(l,r) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and second: "(l',r') \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and nf_first: "l \<in> NF_terms Q"
    and nf_second: "l' \<in> NF_terms Q"
    and connector: "(r,l') \<in> (qrstep True Q S)\<^sup>*"
    and sig_l: "funas_args_term l \<subseteq> G"
    and sig_r: "funas_args_term r \<subseteq> G"
    and sig_l': "funas_args_term l' \<subseteq> G"
    and sig_r': "funas_args_term r' \<subseteq> G"
  from gm04_top_pair_instance_cases[OF first]
  consider (first_ok) x where
      "l = Fun top_sharp [Fun ok [x]]"
      "r = Fun top_sharp [Fun active [x]]"
    | (first_mark) x where
      "l = Fun top_sharp [Fun mark [x]]"
      "r = Fun top_sharp [Fun proper [x]]" .
  then show "(gm04_decode_top_pair_erased W mark (l,r),
      gm04_decode_top_pair_erased W mark (l',r'))
      \<in> gm04_phase_rel (sig_step Fsrc ((csstep \<mu> R)\<^sup>+))"
  proof cases
    case (first_ok x)
    have nf_x: "x \<in> NF_terms Q"
      by (rule gm04_NF_terms_subterm[OF nf_first],
          simp add: first_ok Fun_supteq)
    have sig_x: "funas_term x \<subseteq> G" using sig_l first_ok
      unfolding funas_args_term_def by auto
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 1 Fun_supteq)
      from connector first_ok 1
      have inner: "(Fun active [x], Fun ok [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from active_ok_impossible[OF nf_x nf_y inner]
      show ?thesis by (rule FalseE)
    next
      case (2 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 2 Fun_supteq)
      have sig_y: "funas_term y \<subseteq> G" using sig_l' 2
        unfolding funas_args_term_def by auto
      from connector first_ok 2
      have inner: "(Fun active [x], Fun mark [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      have raw: "(gm04_erase W x,gm04_erase W y)
          \<in> (csstep \<mu> R)\<^sup>+"
        by (rule active_mark[OF nf_x nf_y inner])
      have erased_x: "funas_term (gm04_erase W x) \<subseteq> Fsrc"
        by (rule erased_sig[of x], rule sig_x)
      have erased_y: "funas_term (gm04_erase W y) \<subseteq> Fsrc"
        by (rule erased_sig[of y], rule sig_y)
      have signed: "(gm04_erase W x,gm04_erase W y)
          \<in> sig_step Fsrc ((csstep \<mu> R)\<^sup>+)"
        by (rule sig_stepI[OF raw erased_x erased_y])
      from signed first_ok 2 show ?thesis
        unfolding gm04_decode_top_pair_erased_def gm04_phase_rel_def
        by (simp add: ok_mark)
    qed
  next
    case (first_mark x)
    have nf_x: "x \<in> NF_terms Q"
      by (rule gm04_NF_terms_subterm[OF nf_first],
          simp add: first_mark Fun_supteq)
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 1 Fun_supteq)
      from connector first_mark 1
      have inner: "(Fun proper [x], Fun ok [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from proper_ok[OF nf_x nf_y inner] first_mark 1 show ?thesis
        unfolding gm04_decode_top_pair_erased_def gm04_phase_rel_def
        by (simp add: ok_mark)
    next
      case (2 y)
      have nf_y: "y \<in> NF_terms Q"
        by (rule gm04_NF_terms_subterm[OF nf_second],
            simp add: 2 Fun_supteq)
      from connector first_mark 2
      have inner: "(Fun proper [x], Fun mark [y])
          \<in> (qrstep True Q S)\<^sup>*"
        using gm04_q_top_wrapper_rsteps_iff[OF lhs_fun fresh_top]
        by simp
      from proper_mark_impossible[OF nf_x nf_y inner]
      show ?thesis by (rule FalseE)
    qed
  qed
qed

theorem gm04_finite_schema_top_pairs_q_if_active:
  fixes S :: "('f,string) trs"
  assumes source: "SN (csstep \<mu> (set R))"
    and S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and wf: "wf_trs S"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and active_mark: "\<And>x y.
      x \<in> NF_terms (lhss S) \<Longrightarrow>
      y \<in> NF_terms (lhss S) \<Longrightarrow>
      (Fun active [x],Fun mark [y])
        \<in> (qrstep True (lhss S) S)\<^sup>* \<Longrightarrow>
      (gm04_erase {active,mark,proper,ok} x,
       gm04_erase {active,mark,proper,ok} y)
        \<in> (csstep \<mu> (set R))\<^sup>+"
  shows "finite_dpp (True,m,
      set (gm04_top_pairs active mark proper ok top_sharp),{},
      lhss S,S,{})"
proof (rule gm04_finite_exact_top_pairs_q[
    OF source _ fresh_top, where
      W="{active,mark,proper,ok}"])
  show "\<forall>(l,r)\<in>S. is_Fun l"
    using wf unfolding wf_trs_def by blast
next
  show "ok \<noteq> mark"
    using fresh unfolding gm04_roles_fresh_def by auto
next
  fix x y
  assume "x \<in> NF_terms (lhss S)" "y \<in> NF_terms (lhss S)"
    "(Fun active [x],Fun ok [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  with gm04_non_top_q_cross_phases_impossible(1)[OF S fresh]
  show False by blast
next
  fix x y
  assume "x \<in> NF_terms (lhss S)" "y \<in> NF_terms (lhss S)"
    "(Fun proper [x],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  with gm04_non_top_q_cross_phases_impossible(2)[OF S fresh]
  show False by blast
next
  show "\<And>x y. x \<in> NF_terms (lhss S) \<Longrightarrow>
      y \<in> NF_terms (lhss S) \<Longrightarrow>
      (Fun active [x],Fun mark [y])
        \<in> (qrstep True (lhss S) S)\<^sup>* \<Longrightarrow>
      (gm04_erase {active,mark,proper,ok} x,
       gm04_erase {active,mark,proper,ok} y)
        \<in> (csstep \<mu> (set R))\<^sup>+"
    by (rule active_mark)
next
  fix x y
  assume nx: "x \<in> NF_terms (lhss S)"
    and ny: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun proper [x],Fun ok [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  from gm04_proper_ok_q_converse[OF S fresh wf nx ny steps]
  show "gm04_erase {active,mark,proper,ok} x =
      gm04_erase {active,mark,proper,ok} y" by simp
qed

theorem gm04_finite_schema_top_pairs_q:
  fixes S :: "('f,string) trs"
  assumes source: "SN (csstep \<mu> (set R))"
    and S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and fresh_top: "\<not> defined S (top_sharp,1)"
  shows "finite_dpp (True,m,
      set (gm04_top_pairs active mark proper ok top_sharp),{},
      lhss S,S,{})"
proof (rule gm04_finite_schema_top_pairs_q_if_active[
    OF source S fresh wf fresh_top])
  fix x y
  assume normal_x: "x \<in> NF_terms (lhss S)"
    and normal_y: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun active [x],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  show "(gm04_erase {active,mark,proper,ok} x,
      gm04_erase {active,mark,proper,ok} y)
      \<in> (csstep \<mu> (set R))\<^sup>+"
    by (rule gm04_active_mark_q_converse[
      OF S fresh signature wf_source wf finite_mu normal_x normal_y steps])
qed

theorem gm04_finite_schema_top_pairs_q_sig:
  fixes S :: "('f,string) trs"
    and c :: "('f,string) term \<Rightarrow> string"
  assumes cinj: "inj c"
    and source: "SN (sig_step (set F) (csstep \<mu> (set R)))"
    and S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and pair_args: "funas_args_trs
      (set (gm04_top_pairs active mark proper ok top_sharp))
        \<subseteq> funas_trs S"
    and schema_sig: "funas_trs S \<subseteq> set F \<union>
      {(active,1),(mark,1),(proper,1),(ok,1)}"
  shows "finite_dpp (True,m,
      set (gm04_top_pairs active mark proper ok top_sharp),{},
      lhss S,S,{})"
proof (rule gm04_finite_exact_top_pairs_q_sig[
    OF cinj gm04_SN_sig_csstep_trancl[OF source signature wf_source],
    where G="funas_trs S" and W="{active,mark,proper,ok}"])
  show "\<forall>(l,r)\<in>S. is_Fun l"
    using wf unfolding wf_trs_def by blast
next
  show "\<not> defined S (top_sharp,1)" by (rule fresh_top)
next
  show "ok \<noteq> mark"
    using fresh unfolding gm04_roles_fresh_def by auto
next
  show "NF_terms (lhss S) \<subseteq> NF_trs S" by simp
next
  show "QF_cond (funas_trs S) (lhss S)"
    unfolding QF_cond_def funas_trs_def funas_rule_def by force
next
  show "funas_trs S \<subseteq> funas_trs S" by simp
next
  show "funas_args_trs
      (set (gm04_top_pairs active mark proper ok top_sharp))
      \<subseteq> funas_trs S" by (rule pair_args)
next
  show "wwf_qtrs (lhss S) S" by (rule wf_trs_imp_wwf_qtrs[OF wf])
next
  fix x
  assume xsig: "funas_term x \<subseteq> funas_trs S"
  show "funas_term (gm04_erase {active,mark,proper,ok} x) \<subseteq> set F"
  proof (rule gm04_funas_erase_roles)
    fix w n
    assume "w \<in> {active,mark,proper,ok}"
    with fresh show "(w,n) \<notin> set F"
      unfolding gm04_roles_fresh_def by auto
  next
    from xsig schema_sig show "funas_term x \<subseteq> set F \<union>
        {(w,1) |w. w \<in> {active,mark,proper,ok}}"
      by auto
  qed
next
  fix x y
  assume "x \<in> NF_terms (lhss S)" "y \<in> NF_terms (lhss S)"
    "(Fun active [x],Fun ok [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  with gm04_non_top_q_cross_phases_impossible(1)[OF S fresh]
  show False by blast
next
  fix x y
  assume "x \<in> NF_terms (lhss S)" "y \<in> NF_terms (lhss S)"
    "(Fun proper [x],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  with gm04_non_top_q_cross_phases_impossible(2)[OF S fresh]
  show False by blast
next
  fix x y
  assume normal_x: "x \<in> NF_terms (lhss S)"
    and normal_y: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun active [x],Fun mark [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  show "(gm04_erase {active,mark,proper,ok} x,
      gm04_erase {active,mark,proper,ok} y)
      \<in> (csstep \<mu> (set R))\<^sup>+"
    by (rule gm04_active_mark_q_converse[
      OF S fresh signature wf_source wf finite_mu normal_x normal_y steps])
next
  fix x y
  assume nx: "x \<in> NF_terms (lhss S)"
    and ny: "y \<in> NF_terms (lhss S)"
    and steps: "(Fun proper [x],Fun ok [y])
      \<in> (qrstep True (lhss S) S)\<^sup>*"
  from gm04_proper_ok_q_converse[OF S fresh wf nx ny steps]
  show "gm04_erase {active,mark,proper,ok} x =
      gm04_erase {active,mark,proper,ok} y" by simp
qed

theorem gm04_finite_exact_top_pairs:
  fixes S :: "('f,string) trs"
  assumes source: "SN (csstep \<mu> R)"
    and wf: "wf_trs S"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and ok_mark: "ok \<noteq> mark"
    and active_ok_impossible: "\<And>x y.
      (Fun active [x], Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and proper_mark_impossible: "\<And>x y.
      (Fun proper [x], Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and active_mark: "\<And>x y.
      (Fun active [x], Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow>
      (x,y) \<in> csstep \<mu> R"
    and proper_ok: "\<And>x y.
      (Fun proper [x], Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> x = y"
  shows "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
proof (rule gm04_finite_dpp_from_pair_connectors[
    OF source, where decode="gm04_decode_top_pair mark"])
  fix l r l' r'
  assume first: "(l,r) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and second: "(l',r') \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and connector: "(r,l') \<in> (rstep S)\<^sup>*"
  from gm04_top_pair_instance_cases[OF first]
  consider (first_ok) x where
      "l = Fun top_sharp [Fun ok [x]]"
      "r = Fun top_sharp [Fun active [x]]"
    | (first_mark) x where
      "l = Fun top_sharp [Fun mark [x]]"
      "r = Fun top_sharp [Fun proper [x]]" .
  then show "(gm04_decode_top_pair mark (l,r),
      gm04_decode_top_pair mark (l',r'))
      \<in> gm04_phase_rel (csstep \<mu> R)"
  proof cases
    case (first_ok x)
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      from connector first_ok 1
      have inner: "(Fun active [x], Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from active_ok_impossible[OF inner]
      show ?thesis by (rule FalseE)
    next
      case (2 y)
      from connector first_ok 2
      have inner: "(Fun active [x], Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from active_mark[OF inner] first_ok 2 show ?thesis
        unfolding gm04_decode_top_pair_def gm04_phase_rel_def
        by (simp add: ok_mark)
    qed
  next
    case (first_mark x)
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      from connector first_mark 1
      have inner: "(Fun proper [x], Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from proper_ok[OF inner] first_mark 1 show ?thesis
        unfolding gm04_decode_top_pair_def gm04_phase_rel_def
        by (simp add: ok_mark)
    next
      case (2 y)
      from connector first_mark 2
      have inner: "(Fun proper [x], Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from proper_mark_impossible[OF inner]
      show ?thesis by (rule FalseE)
    qed
  qed
qed

lemma gm04_complete_rules_set:
  "set (gm04_complete_rules \<mu> active mark proper ok top_sym F R) =
    set (gm04_non_top_rules \<mu> active mark proper ok F R) \<union>
    set (gm04_top_rules active mark proper ok top_sym)"
  by (simp add: gm04_complete_rules_def)

theorem gm04_complete_SN_from_relative:
  assumes relative: "SN_rel
      (rstep (set (gm04_top_rules active mark proper ok top_sym)))
      (rstep (set (gm04_non_top_rules \<mu> active mark proper ok F R)))"
    and administrative: "SN
      (rstep (set (gm04_non_top_rules \<mu> active mark proper ok F R)))"
  shows "SN (rstep (set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)))"
proof -
  from gm04_SN_rel_and_SN_imp_SN_union[OF relative administrative]
  have combined: "SN
      (rstep (set (gm04_top_rules active mark proper ok top_sym)) \<union>
       rstep (set (gm04_non_top_rules \<mu> active mark proper ok F R)))" .
  show ?thesis
    unfolding gm04_complete_rules_set rstep_union
    using combined by (simp add: Un_commute)
qed

end
