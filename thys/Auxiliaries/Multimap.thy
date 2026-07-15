(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Mappings associating keys with lists of values\<close>

theory Multimap
imports
  Util
  "Transitive-Closure.RBT_Map_Set_Extension"
begin

section \<open>Abstract Multimaps\<close>

text \<open>A multi-map is disjoint if value lists resulting from different keys do
not have any common elements.\<close>
definition disjoint :: "('k \<Rightarrow> 'v list option) \<Rightarrow> bool" where
  "disjoint m \<equiv> \<forall>k l vs ws. k \<noteq> l \<and> m k = Some vs \<and> m l = Some ws \<longrightarrow> (set vs \<inter> set ws) = {}"

lemma ran_map_upd_Some':
  assumes "m a = Some b" and "disjoint m" and "set c \<subseteq> set b"
  shows "ran (m(a \<mapsto> c)) \<subseteq> insert c (ran m - {b})"
proof
  fix x assume "x \<in> ran (m(a \<mapsto> c))"
  then obtain k where upd: "(m(a \<mapsto> c)) k = Some x" by (auto simp: ran_def)
  show "x \<in> insert c (ran m - {b})"
  proof (cases "a = k")
    case True
    from assms and upd have x: "x = c" by (simp add: True)
    then show ?thesis by simp
  next
    case False
    then have m_upd: "(m(a \<mapsto> c)) k = m k" by simp
    from upd[unfolded m_upd] have "m k = Some x" by simp
    then have "x \<in> ran m" by (auto simp: ran_def)
    from \<open>m k = Some x\<close> and assms(2)[unfolded disjoint_def] and False and assms(1)
      have 1: "(set b \<inter> set x) = {}" by blast
    show ?thesis
    proof (cases "set b = {}")
      case True with assms(3) have 2: "b = c" by simp
      from assms(1) have "b \<in> ran m" by (auto simp: ran_def)
      then have "insert c (ran m - {b}) = ran m" unfolding 2 by auto
      then show ?thesis using \<open>x \<in> ran m\<close> by simp
    next
      case False
      with 1 have "b \<noteq> x" by auto
      with \<open>x \<in> ran m\<close> show ?thesis by simp
    qed
  qed
qed

lemma UNION_ran_disjoint:
  assumes "m k = Some v" and "disjoint m" and "set w \<subseteq> set v"
  shows "\<Union> (set ` (ran (m(k \<mapsto> w)))) = \<Union> (set ` (insert w (ran m - {v})))" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix x assume "x \<in> ?l"
    then obtain vs where vs: "vs \<in> ran (m(k \<mapsto> w))" and x: "x \<in> set vs" by auto
    from ran_map_upd_Some'[of m k v, OF assms] and vs
      have "vs \<in> insert w (ran m - {v})" by blast
    with x show "x \<in> ?r" by blast
  qed
next
  show "?r \<subseteq> ?l"
  proof
    fix x assume "x \<in> ?r"
    then obtain vs where "vs \<in> insert w (ran m - {v})" and x: "x \<in> set vs" by auto
    then have "w = vs \<or> vs \<in> ran m - {v}" by auto
    then show "x \<in> ?l"
    proof
      assume w: "w = vs"
      show ?thesis unfolding w using x by (auto simp: ran_def)
    next
      assume "vs \<in> ran m - {v}"
      then obtain l where ml: "m l = Some vs" and ne: "vs \<noteq> v" by (auto simp: ran_def)
      show ?thesis
      proof (cases "k = l")
        case True
        from assms(1) and ml and ne show ?thesis by (simp add: True)
      next
        case False
        with ml have "vs \<in> ran (m(k \<mapsto> w))" by (auto simp: ran_def)
        with x show ?thesis by blast
      qed
    qed
  qed
qed

text \<open>Mult-maps whose elements are positioned according to their keys, somehow
correspond to injective mappings.\<close>
definition mmap_inj :: "('v \<Rightarrow> 'k option) \<Rightarrow> ('k \<Rightarrow> 'v list option) \<Rightarrow> bool" where
  "mmap_inj key m \<equiv> (\<forall>k vs. m k = Some vs \<longrightarrow> (\<forall>v\<in>set vs. key v = Some k))"

lemma mmap_inj_empty[simp]: "mmap_inj key Map.empty" by (simp add: mmap_inj_def)

lemma mmap_inj_map_upd:
  assumes "\<And>v. v \<in> set vs \<Longrightarrow> key v = Some k"
    and "mmap_inj key m"
  shows "mmap_inj key (m(k \<mapsto> vs))"
  unfolding mmap_inj_def
proof (intro allI impI)
  fix l ws assume 1: "(m(k \<mapsto> vs)) l = Some ws"
  show "\<forall>v \<in> set ws. key v = Some l"
  proof (cases "k = l")
    assume 2: "k = l"
    with 1 have "vs = ws" by simp
    from assms(1)[unfolded this] show ?thesis by (simp add: 2)
  next
    assume "k \<noteq> l"
    then have 2: "(m(k \<mapsto> vs)) l = m l" by simp
    from 1 have "m l = Some ws" unfolding 2 .
    with assms(2) show ?thesis by (simp add: mmap_inj_def)
  qed
qed


section \<open>Multimap implementation by Red-Black Trees\<close>
lemma mmap_inj_rm_empty[simp]: "mmap_inj key (RBT.lookup RBT.empty)"
  by (simp add: mmap_inj_def)

text \<open>All values contained in a multimap.\<close>
definition "values" :: "('k::linorder, 'v list) RBT.rbt \<Rightarrow> 'v list" where
  "values m \<equiv> concat (map snd (RBT.entries m))"
 
lemma values_rm_empty[simp]: "values RBT.empty = []" 
  by (simp add: values_def)
    (metis empty_iff empty_set keys_def_alt keys_empty_eq zip_Nil
      zip_map_fst_snd)


lemma values_ran: "set (values m) = (\<Union>rs\<in>ran (RBT.lookup m). set rs)"
  using ran_distinct[of "RBT.entries m"]
  by (auto simp: values_def distinct_entries)

definition
  insert_value ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> 'v \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> ('k, 'v list) RBT.rbt"
where
  "insert_value key v m \<equiv> case key v of
    None \<Rightarrow> m
  | Some k \<Rightarrow> (case RBT.lookup m k of
      None \<Rightarrow> RBT.insert k [v] m
    | Some vs \<Rightarrow> RBT.insert k (List.insert v vs) m)"

lemma rm_lookup_dom: "RBT.lookup m k = None \<longleftrightarrow> k \<notin> dom (RBT.lookup m)"
  by (simp add: domIff)

lemma insert_value_None[simp]:
  "key v = None \<Longrightarrow> insert_value key v m = m"
  by (simp add: insert_value_def)

lemma rm_\<alpha>_insert_value_Some[simp]:
  assumes "key v = Some k" and "RBT.lookup m k = None"
  shows "RBT.lookup (insert_value key v m) = (RBT.lookup m)(k \<mapsto> [v])"
  unfolding insert_value_def assms option.simps
  using assms by simp


lemma rm_\<alpha>_insert_value_Some'[simp]:
  assumes "key v = Some k" and "RBT.lookup m k = Some vs"
  shows "RBT.lookup (insert_value key v m) = (RBT.lookup m)(k \<mapsto> List.insert v vs)"
  using assms by (simp add: insert_value_def)

lemma mmap_inj_insert_value:
  assumes "mmap_inj key (RBT.lookup m)"
  shows "mmap_inj key (RBT.lookup (insert_value key v m))"
proof (cases "key v")
  case None with assms show ?thesis by simp
next
  case (Some k)
  note Some' = this
  show ?thesis
  proof (cases "RBT.lookup m k")
    case None
    with Some' and mmap_inj_map_upd[OF _ assms]
      show ?thesis by force
  next
    case (Some vs)
    with assms have "\<forall>v\<in>set (List.insert v vs). key v = Some k"
      using Some' by (simp add: mmap_inj_def)
    with Some Some' show ?thesis by (force intro: mmap_inj_map_upd[OF _ assms])
  qed
qed

lemma Some_in_values:
  assumes "RBT.lookup m k = Some vs"
  shows "set vs \<subseteq> set (values m)"
  using assms unfolding values_ran ran_def
  by auto

lemma values_insert_value_Some[simp]:
  assumes "key v = Some k"
  shows "set (values (insert_value key v m)) = insert v (set (values m))"
proof (cases "RBT.lookup m k")
  case None
  show ?thesis
    unfolding values_ran
    unfolding rm_\<alpha>_insert_value_Some[of key v k, OF assms None]
    using ran_map_upd[of "RBT.lookup m" k] None
    by simp
next
  case (Some vs)
  show ?thesis
    unfolding values_ran
    unfolding rm_\<alpha>_insert_value_Some'[of key v k, OF assms Some]
    using subset_UNION_ran[of "RBT.lookup m" k,
      OF _ set_subset_insertI] Some
    using Some_in_values[OF Some, simplified values_ran]
    by auto
qed

fun
  insert_values ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> 'v list \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> ('k, 'v list) RBT.rbt"
where
  "insert_values _ [] m = m"
| "insert_values key (v#vs) m = insert_value key v (insert_values key vs m)"

lemma mmap_inj_insert_values:
  "mmap_inj key (RBT.lookup m) \<Longrightarrow> mmap_inj key (RBT.lookup (insert_values key vs m))"
  by (induct vs arbitrary: m) (simp_all add: mmap_inj_insert_value)

lemma values_insert_values[simp]:
  "set (values (insert_values key vs m)) = set [v\<leftarrow>vs. key v \<noteq> None] \<union> set (values m)"
proof (induct vs)
  case Nil show ?case by simp
next
  case (Cons v vs) then show ?case by (cases "key v") simp_all
qed

(*could be imporved by using remove1*)
definition
  delete_value ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> 'v \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> ('k, 'v list) RBT.rbt"
where
  "delete_value key v m \<equiv> case key v of
    None \<Rightarrow> m
  | Some k \<Rightarrow> (case RBT.lookup m k of
      None \<Rightarrow> m
    | Some vs \<Rightarrow> RBT.insert k (removeAll v vs) m)"

lemma delete_value_None[simp]:
  "key v = None \<Longrightarrow> delete_value key v m = m"
  by (simp add: delete_value_def)

lemma delete_value_None'[simp]:
  "key v = Some k \<Longrightarrow> RBT.lookup m k = None \<Longrightarrow> delete_value key v m = m"
  by (simp add: delete_value_def)

lemma rm_\<alpha>_delete_value_Some[simp]:
  assumes "key v = Some k" and "RBT.lookup m k = Some vs"
  shows "RBT.lookup (delete_value key v m) = (RBT.lookup m)(k \<mapsto> removeAll v vs)"
  using assms by (simp add: delete_value_def)

lemma mmap_inj_delete_value:
  assumes "mmap_inj key (RBT.lookup m)"
  shows "mmap_inj key (RBT.lookup (delete_value key v m))"
proof (cases "key v")
  case None
  from assms show ?thesis unfolding delete_value_None[of key v, OF None] .
next
  case (Some k)
  note Some' = this
  show ?thesis
  proof (cases "RBT.lookup m k")
    case None
    show ?thesis
      unfolding delete_value_None'[of key v k, OF Some' None]
      by fact
  next
    case (Some vs)
    with assms have 1: "\<forall>v\<in>set (removeAll v vs). key v = Some k"
      by (simp add: mmap_inj_def)
    then show ?thesis
      unfolding rm_\<alpha>_delete_value_Some[of key v k, OF Some' Some]
      using mmap_inj_map_upd[OF _ assms]
      by force
  qed
qed

lemma UNION_insert_removeAll:
  assumes "\<forall>ws\<in>ran m. ws \<noteq> vs \<longrightarrow> v \<notin> set ws"
    and "set vs \<subseteq> \<Union> (set ` ran m)"
  shows "\<Union> (set ` (insert (removeAll v vs) (ran m - {vs}))) = \<Union> (set ` ran m) - {v}"
    (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then have "x \<in> \<Union> (set ` ran m)" and "x \<noteq> v" by auto
    then show "x \<in> ?A" by auto
  qed
next
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain ws where "ws \<in> insert (removeAll v vs) (ran m - {vs})"
      and x: "x \<in> set ws" by blast
    then have "ws = removeAll v vs \<or> ws \<in> ran m - {vs}" by auto
    then show "x \<in> ?B"
    proof
      assume 1: "ws = removeAll v vs"
      with x have "x \<noteq> v" by auto
      with x[unfolded 1] show ?thesis using assms(2) by auto
    next
      assume "ws \<in> ran m - {vs}"
      with assms have "ws \<in> ran m" and "v \<notin> set ws" by auto
      with x have "v \<noteq> x" by auto
      then show ?thesis using \<open>ws \<in> ran m\<close> and x by auto
    qed
  qed
qed

lemma Some_ran:
  "m k = Some vs \<Longrightarrow> set vs \<subseteq> \<Union> (set ` ran m)"
  unfolding ran_def by auto

lemma mmap_inj_ran:
  assumes "key v = Some k" and "mmap_inj key m" and "m k = Some vs"
  shows "\<forall>ws\<in>ran m. ws \<noteq> vs \<longrightarrow> v \<notin> set ws"
  using assms unfolding mmap_inj_def ran_def by auto

lemma mmap_inj_imp_disjoint:
  assumes "mmap_inj key m"
  shows "disjoint m"
proof (rule ccontr)
  assume "\<not> disjoint m"
  then obtain k l vs ws where kl: "k \<noteq> l" and mk: "m k = Some vs"
    and ml: "m l = Some ws" and ne: "set vs \<inter> set ws \<noteq> {}"
    unfolding disjoint_def by blast
  from ne obtain v where "v \<in> set vs" and "v \<in> set ws" by auto
  from \<open>v \<in> set vs\<close> and mk and assms have "key v = Some k"
    by (auto simp: mmap_inj_def)
  moreover from \<open>v \<in> set ws\<close> and ml and assms have "key v = Some l"
    by (auto simp: mmap_inj_def)
  ultimately show False using \<open>k \<noteq> l\<close> by simp
qed

lemma values_delete_value_Some[simp]:
  assumes "key v = Some k" and "RBT.lookup m k = Some vs" and "mmap_inj key (RBT.lookup m)"
  shows "set (values (delete_value key v m)) = set (values m) - {v}"
  unfolding values_ran
  unfolding rm_\<alpha>_delete_value_Some[of key v k, OF assms(1-2)]
  using UNION_ran_disjoint[of "RBT.lookup m" k,
    OF _ mmap_inj_imp_disjoint[OF assms(3)] set_removeAll_subset]
    assms(2)
    UNION_insert_removeAll[OF _ Some_ran[of "RBT.lookup m"]]
    mmap_inj_ran[of key v k, OF assms(1) assms(3), of vs] 
  by simp

fun
  delete_values ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> 'v list \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> ('k , 'v list) RBT.rbt"
where
  "delete_values _ [] m = m"
| "delete_values key (v#vs) m = delete_value key v (delete_values key vs m)"

lemma not_in_values_Some:
  assumes key: "key v = Some k"
    and notin: "RBT.lookup m k = None"
    and mmap_inj: "mmap_inj key (RBT.lookup m)"
  shows "v \<notin> set (values m)"
proof (rule ccontr)
  presume "v \<in> set (values m)"
  from this[unfolded values_ran]
    obtain vs where "vs \<in> ran (RBT.lookup m)" and "v \<in> set vs" by blast
  then obtain l where "RBT.lookup m l = Some vs" by (auto simp: ran_def)
  with mmap_inj and \<open>v \<in> set vs\<close> have "key v = Some l" by (auto simp: mmap_inj_def)
  with key have "k = l" by simp
  with notin[unfolded this]
    and \<open>RBT.lookup m l = Some vs\<close> show False by simp
qed simp

lemma not_in_values_None:
  assumes key: "key v = None"
    and mmap_inj: "mmap_inj key (RBT.lookup m)"
  shows "v \<notin> set (values m)"
proof (rule ccontr)
  presume "v \<in> set (values m)"
  from this[unfolded values_ran]
    obtain vs where "vs \<in> ran (RBT.lookup m)" and "v \<in> set vs" by blast
  then obtain l where "RBT.lookup m l = Some vs" by (auto simp: ran_def)
  with mmap_inj and \<open>v \<in> set vs\<close> have "key v = Some l" by (auto simp: mmap_inj_def)
  with key show False by simp
qed simp

lemma mmap_inj_delete_values:
  "mmap_inj key (RBT.lookup m) \<Longrightarrow> mmap_inj key (RBT.lookup (delete_values key vs m))"
  by (induct vs arbitrary: m) (auto simp: mmap_inj_delete_value)

lemma values_delete_values[simp]:
  assumes "mmap_inj key (RBT.lookup m)"
  shows "set (values (delete_values key vs m)) = set (values m) - set vs"
using assms
proof (induct vs arbitrary: m)
  case Nil show ?case by simp
next
  case (Cons v vs)
  show ?case
  proof (cases "key v")
    case None
    from not_in_values_None[of key v, OF None Cons(2)]
    show ?thesis
      using Cons by (simp add: delete_value_None[of key v, OF None])
  next
    case (Some k)
    note Some' = this
    show ?thesis
    proof (cases "RBT.lookup (delete_values key vs m) k")
      case None
      from not_in_values_Some[of key v, OF Some None
        mmap_inj_delete_values[OF Cons(2)]]
        show ?thesis
        using Cons
        using delete_value_None'[of key v, OF Some' None]
        by auto
    next
      case (Some ws)
      show ?thesis
        using Cons
        using values_delete_value_Some[of key v k,
          OF Some' Some mmap_inj_delete_values[OF Cons(2)]]
        by auto
    qed
  qed
qed

definition
  aux ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> 'v \<Rightarrow> ('k, 'v list) RBT.rbt
    \<Rightarrow> ('k, 'v list) RBT.rbt"
where
  "aux key m v m' \<equiv> case key v of
    Some k \<Rightarrow> (case RBT.lookup m k of
      Some ws \<Rightarrow> (if v \<in> set ws then insert_value key v m' else m')
    | None \<Rightarrow> m')
  | None \<Rightarrow> m'"

(*do not compute key twice in generated code*)
lemma [code]: "aux key m v m' = (case key v of
    Some k \<Rightarrow> (case RBT.lookup m k of
      Some ws \<Rightarrow> (if v \<in> set ws
        then (case RBT.lookup m' k of
          Some vs \<Rightarrow> RBT.insert k (List.insert v vs) m'
        | None \<Rightarrow> RBT.insert k [v] m')
        else m')
      | None \<Rightarrow> m')
    | None \<Rightarrow> m')"
  unfolding aux_def insert_value_def
  by (simp split: option.splits)

lemma not_in_values:
  assumes inj: "mmap_inj key (RBT.lookup m)"
    and "key x = Some k"
    and "RBT.lookup m k = Some vs"
    and "x \<notin> set vs"
  shows "x \<notin> set (values m)"
proof (rule ccontr)
  presume "x \<in> set (values m)"
  then obtain ws l where 1: "x \<in> set ws" and "ws \<in> ran (RBT.lookup m)"
    and 2: "RBT.lookup m l = Some ws"
    unfolding values_ran ran_def by auto
  with inj[unfolded mmap_inj_def] 1 2 have "key x = Some l" by simp
  with assms have "k = l" by simp
  then show False using assms 1 2 by simp
qed simp

lemma set_aux:
  assumes inj: "mmap_inj key (RBT.lookup m)"
  shows "set (values (aux key m v m')) = (set (values m) \<inter> {v}) \<union> set (values m')"
proof (cases "key v")
  case None then show ?thesis by (auto simp: aux_def not_in_values_None[OF None inj])
next
  case (Some k)
  note key = this
  show ?thesis
  proof (cases "RBT.lookup m k")
    case None then show ?thesis by (simp add: aux_def key not_in_values_Some[OF key None inj])
  next
    case (Some vs)
    show ?thesis
    proof (cases "v \<in> set vs")
      case True then show ?thesis using key Some Some_in_values[OF Some]
        by (simp add: aux_def) blast
    next
      case False
      from not_in_values[OF inj key] False Some
      have "v \<notin> set (values m)" by simp
      then show ?thesis unfolding aux_def key Some option.cases if_not_P[OF False] by simp
    qed
  qed
qed

definition
  intersect_values ::
    "('v \<Rightarrow> 'k::linorder option) \<Rightarrow> 'v list \<Rightarrow> ('k, 'v list) RBT.rbt \<Rightarrow> ('k, 'v list) RBT.rbt"
where
  "intersect_values key vs m \<equiv> foldr (aux key m) vs RBT.empty"

lemma foldr_invariant:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> Q x"
    and "P s"
    and "\<And>x s. \<lbrakk>Q x; P s\<rbrakk> \<Longrightarrow> P (f x s)"
  shows" P (foldr f xs s)"
  using assms by (induct xs) simp_all

lemma mmap_inj_intersect_values:
  "mmap_inj key (RBT.lookup m) \<Longrightarrow> mmap_inj key (RBT.lookup (intersect_values key vs m))"
  unfolding intersect_values_def
  by (frule foldr_invariant)
     (auto simp: aux_def split: option.split intro: mmap_inj_insert_value[of key])

lemma values_intersect_values_subset:
  "set (values (intersect_values key vs m)) \<subseteq> set (values m) \<inter> set vs"
  unfolding intersect_values_def
  by (rule foldr_invariant[of _ "\<lambda>v. v \<in> set vs"])
     (insert Some_in_values, auto simp: aux_def split: option.split)

lemma values_intersect_values[simp]:
  assumes "mmap_inj key (RBT.lookup m)"
  shows "set (values (intersect_values key vs m)) = set (values m) \<inter> set vs"
  using assms by (induct vs arbitrary: m) (auto simp: intersect_values_def set_aux)

hide_const aux

end
