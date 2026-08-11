theory Finite_Branching_Dichotomy
  imports "HOL-Library.Infinite_Set"
begin

definition reachable_events ::
  "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "reachable_events E event x = {y. (x,y) \<in> E\<^sup>* \<and> event y}"

definition heavy_node ::
  "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "heavy_node E event x \<longleftrightarrow> infinite (reachable_events E event x)"

lemma reachable_event_at_or_below_successor:
  assumes reachable: "z \<in> reachable_events E event x"
  obtains "z = x" | y where "(x,y) \<in> E" "z \<in> reachable_events E event y"
proof -
  from reachable have steps: "(x,z) \<in> E\<^sup>*" and event: "event z"
    unfolding reachable_events_def by auto
  from converse_rtranclE[OF steps]
  consider (base) "x = z"
    | (step) first where "(x,first) \<in> E" "(first,z) \<in> E\<^sup>*"
    by blast
  then show thesis
  proof cases
    case base
    show thesis by (rule that(1)) (use base in simp)
  next
    case (step first)
    have first: "(x,first) \<in> E" "(first,z) \<in> E\<^sup>*"
      by (rule step)+
    have "z \<in> reachable_events E event first"
      using first(2) event unfolding reachable_events_def by simp
    then show thesis by (rule that(2)[OF first(1)])
  qed
qed

lemma heavy_node_has_heavy_successor:
  assumes heavy: "heavy_node E event x"
    and finite_successors: "finite {y. (x,y) \<in> E}"
  obtains y where "(x,y) \<in> E" "heavy_node E event y"
proof (rule ccontr)
  assume no_successor: "\<not> thesis"
  have no_heavy_successor:
    "\<And>y. (x,y) \<in> E \<Longrightarrow> \<not> heavy_node E event y"
    using no_successor that by blast
  then have finite_below:
    "\<And>y. (x,y) \<in> E \<Longrightarrow> finite (reachable_events E event y)"
    unfolding heavy_node_def by simp
  have subset: "reachable_events E event x \<subseteq>
      {x} \<union> \<Union>(reachable_events E event ` {y. (x,y) \<in> E})"
  proof
    fix z
    assume z: "z \<in> reachable_events E event x"
    from reachable_event_at_or_below_successor[OF z]
    show "z \<in> {x} \<union>
        \<Union>(reachable_events E event ` {y. (x,y) \<in> E})"
      by cases auto
  qed
  have finite_union:
      "finite (\<Union>(reachable_events E event ` {y. (x,y) \<in> E}))"
    using finite_successors finite_below by simp
  have finite_superset:
      "finite ({x} \<union> \<Union>(reachable_events E event ` {y. (x,y) \<in> E}))"
    using finite_union by simp
  have "finite (reachable_events E event x)"
    by (rule finite_subset[OF subset finite_superset])
  with heavy show False unfolding heavy_node_def by simp
qed

definition heavy_successor ::
  "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "heavy_successor E event x =
    (SOME y. (x,y) \<in> E \<and> heavy_node E event y)"

lemma heavy_successor:
  assumes heavy: "heavy_node E event x"
    and finite_successors: "finite {y. (x,y) \<in> E}"
  shows "(x, heavy_successor E event x) \<in> E"
    and "heavy_node E event (heavy_successor E event x)"
proof -
  from heavy_node_has_heavy_successor[OF heavy finite_successors]
  obtain y where "(x,y) \<in> E \<and> heavy_node E event y" by blast
  then have selected:
    "(x, heavy_successor E event x) \<in> E \<and>
      heavy_node E event (heavy_successor E event x)"
    unfolding heavy_successor_def by (rule someI)
  then show "(x, heavy_successor E event x) \<in> E" by simp
  from selected show "heavy_node E event (heavy_successor E event x)" by simp
qed

primrec heavy_path ::
  "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "heavy_path E event root 0 = root"
| "heavy_path E event root (Suc n) =
    heavy_successor E event (heavy_path E event root n)"

lemma heavy_path_heavy:
  assumes root: "heavy_node E event x"
    and finite_successors: "\<And>y. heavy_node E event y \<Longrightarrow>
      finite {z. (y,z) \<in> E}"
  shows "heavy_node E event (heavy_path E event x n)"
proof (induction n)
  case 0
  show ?case using root by simp
next
  case (Suc n)
  have next_heavy: "heavy_node E event
      (heavy_successor E event (heavy_path E event x n))"
    by (rule heavy_successor(2)[OF Suc.IH finite_successors[OF Suc.IH]])
  show ?case by (simp add: next_heavy)
qed

lemma heavy_path_step:
  assumes root: "heavy_node E event x"
    and finite_successors: "\<And>y. heavy_node E event y \<Longrightarrow>
      finite {z. (y,z) \<in> E}"
  shows "(heavy_path E event x n, heavy_path E event x (Suc n)) \<in> E"
proof -
  have heavy: "heavy_node E event (heavy_path E event x n)"
    by (rule heavy_path_heavy[OF root finite_successors])
  have finite: "finite {z. (heavy_path E event x n,z) \<in> E}"
    by (rule finite_successors[OF heavy])
  show ?thesis
    using heavy_successor(1)[OF heavy finite] by simp
qed

definition event_offshoot ::
  "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> bool" where
  "event_offshoot E event path n \<longleftrightarrow>
    (\<exists>y. (path n,y) \<in> E \<and> y \<noteq> path (Suc n) \<and>
      reachable_events E event y \<noteq> {})"

lemma no_offshoot_forces_reachable_event_onto_path:
  assumes path: "\<And>n. (p n, p (Suc n)) \<in> E"
    and no_offshoot: "\<And>n. N \<le> n \<Longrightarrow> \<not> event_offshoot E event p n"
    and reachable: "z \<in> reachable_events E event (p N)"
  shows "\<exists>k. z = p (N+k) \<and> event z"
proof -
  from reachable have steps: "(p N,z) \<in> E\<^sup>*" and event: "event z"
    unfolding reachable_events_def by auto
  have forced: "\<And>k i z. N \<le> i \<Longrightarrow> (p i,z) \<in> E ^^ k \<Longrightarrow>
      event z \<Longrightarrow> z = p (i+k)"
  proof -
    fix k i z
    assume Ni: "N \<le> i" and power: "(p i,z) \<in> E ^^ k" and event_z: "event z"
    from power Ni show "z = p (i+k)"
    proof (induction k arbitrary: i)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      from relpow_Suc_D2[OF Suc.prems(1)]
      obtain y where first: "(p i,y) \<in> E" and rest: "(y,z) \<in> E ^^ k"
        by blast
      have reachable_y: "reachable_events E event y \<noteq> {}"
        using relpow_imp_rtrancl[OF rest] event_z
        unfolding reachable_events_def by auto
      have y: "y = p (Suc i)"
      proof (rule ccontr)
        assume "y \<noteq> p (Suc i)"
        then have "event_offshoot E event p i"
          unfolding event_offshoot_def using first reachable_y by blast
        moreover have "\<not> event_offshoot E event p i"
          by (rule no_offshoot[OF Suc.prems(2)])
        ultimately show False by contradiction
      qed
      have rest': "(p (Suc i),z) \<in> E ^^ k" using rest y by simp
      have "z = p (Suc i + k)"
        by (rule Suc.IH[OF rest']) (use Suc.prems(2) in simp)
      then show ?case by simp
    qed
  qed
  from rtrancl_imp_relpow[OF steps]
  obtain k where power: "(p N,z) \<in> E ^^ k" by blast
  have "z = p (N+k)" by (rule forced[OF order_refl power event])
  then show ?thesis using event by blast
qed

theorem finite_branching_event_dichotomy:
  assumes root: "heavy_node E event x"
    and finite_successors: "\<And>y. heavy_node E event y \<Longrightarrow>
      finite {z. (y,z) \<in> E}"
  defines "p \<equiv> heavy_path E event x"
  shows "(\<forall>n. (p n, p (Suc n)) \<in> E) \<and>
    ((INFM n. event (p n)) \<or>
      (INFM n. event_offshoot E event p n))"
proof (intro conjI)
  show "\<forall>n. (p n, p (Suc n)) \<in> E"
    unfolding p_def by (rule allI, rule heavy_path_step[OF root finite_successors])
  show "(INFM n. event (p n)) \<or>
      (INFM n. event_offshoot E event p n)"
  proof (rule ccontr)
    assume neither: "\<not> ((INFM n. event (p n)) \<or>
      (INFM n. event_offshoot E event p n))"
    have not_event: "\<not> (INFM n. event (p n))" using neither by blast
    have not_offshoot: "\<not> (INFM n. event_offshoot E event p n)"
      using neither by blast
    from not_event[unfolded not_INFM MOST_nat_le]
      not_offshoot[unfolded not_INFM MOST_nat_le]
    obtain N1 N2 where
      no_event: "\<And>n. N1 \<le> n \<Longrightarrow> \<not> event (p n)"
      and no_offshoot:
        "\<And>n. N2 \<le> n \<Longrightarrow> \<not> event_offshoot E event p n"
      by blast
    let ?N = "max N1 N2"
    have heavy: "heavy_node E event (p ?N)"
      unfolding p_def by (rule heavy_path_heavy[OF root finite_successors])
    have empty: "reachable_events E event (p ?N) = {}"
    proof (rule ccontr)
      assume "reachable_events E event (p ?N) \<noteq> {}"
      then obtain z where z: "z \<in> reachable_events E event (p ?N)" by blast
      have path: "\<And>n. (p n, p (Suc n)) \<in> E"
        unfolding p_def by (rule heavy_path_step[OF root finite_successors])
      have no_offshoot_N:
          "\<And>n. ?N \<le> n \<Longrightarrow> \<not> event_offshoot E event p n"
        by (rule no_offshoot) simp
      from no_offshoot_forces_reachable_event_onto_path[
          OF path no_offshoot_N z]
      obtain k where zk: "z = p (?N+k)" and event: "event z"
        by blast
      have "\<not> event (p (?N+k))" by (rule no_event) simp
      with event zk show False by simp
    qed
    with heavy show False unfolding heavy_node_def by simp
  qed
qed

lemma ipath_interval_rtrancl:
  assumes path: "\<And>n. (p n, p (Suc n)) \<in> E"
    and order: "i \<le> j"
  shows "(p i, p j) \<in> E\<^sup>*"
proof -
  obtain d where j: "j = i + d" using order by (auto simp: le_iff_add)
  show ?thesis unfolding j
  proof (induction d)
    case 0
    show ?case by simp
  next
    case (Suc d)
    have edge: "(p (i+d), p (Suc (i+d))) \<in> E" by (rule path)
    show ?case
      by (rule rtrancl_into_rtrancl[OF Suc.IH])
         (use edge in simp)
  qed
qed

lemma ipath_interval_restricted_rtrancl:
  assumes path: "\<And>n. (p n, p (Suc n)) \<in> E"
    and order: "i \<le> j"
    and allowed: "\<And>k. i \<le> k \<Longrightarrow> k < j \<Longrightarrow> allowed (p k)"
  shows "(p i, p j) \<in> {(x,y). (x,y) \<in> E \<and> allowed x}\<^sup>*"
proof -
  obtain d where j: "j = i + d" using order by (auto simp: le_iff_add)
  have segment: "\<And>d. (\<And>k. k < d \<Longrightarrow> allowed (p (i+k))) \<Longrightarrow>
      (p i, p (i+d)) \<in> {(x,y). (x,y) \<in> E \<and> allowed x}\<^sup>*"
  proof -
    fix d
    assume permitted: "\<And>k. k < d \<Longrightarrow> allowed (p (i+k))"
    show "(p i, p (i+d)) \<in>
        {(x,y). (x,y) \<in> E \<and> allowed x}\<^sup>*"
    using permitted
  proof (induction d)
    case 0
    show ?case by simp
  next
    case (Suc d)
    have edge: "(p (i+d), p (Suc (i+d))) \<in> E" by (rule path)
    have permitted: "allowed (p (i+d))"
      by (rule Suc.prems) simp
    have prefix: "(p i, p (i+d)) \<in>
        {(x,y). (x,y) \<in> E \<and> allowed x}\<^sup>*"
      by (rule Suc.IH) (use Suc.prems in auto)
    show ?case
      by (rule rtrancl_into_rtrancl[OF prefix])
         (use edge permitted in auto)
  qed
  qed
  show ?thesis unfolding j
    by (rule segment) (use allowed j in auto)
qed

lemma between_consecutive_enumerated_events:
  fixes p :: "nat \<Rightarrow> 'a"
    and event :: "'a \<Rightarrow> bool"
  defines "I \<equiv> {n. event (p n)}"
  assumes infinite: "infinite I"
    and lower: "enumerate I n < k"
    and upper: "k < enumerate I (Suc n)"
  shows "\<not> event (p k)"
proof
  assume event: "event (p k)"
  then have kI: "k \<in> I" unfolding I_def by simp
  from range_enumerate[OF infinite] kI obtain m where k: "k = enumerate I m"
    by blast
  have mono: "strict_mono (enumerate I)" by (rule strict_mono_enumerate[OF infinite])
  consider "m \<le> n" | "Suc n \<le> m" by arith
  then show False
  proof cases
    case 1
    have "enumerate I m \<le> enumerate I n"
      by (rule monoD[OF strict_mono_mono[OF mono] 1])
    with lower k show False by simp
  next
    case 2
    have "enumerate I (Suc n) \<le> enumerate I m"
      by (rule monoD[OF strict_mono_mono[OF mono] 2])
    with upper k show False by simp
  qed
qed

lemma enumerate_nat_lower_bound:
  assumes "infinite (I :: nat set)"
  shows "n \<le> enumerate I n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "enumerate I n < enumerate I (Suc n)"
    by (rule enumerate_mono[OF _ assms]) simp
  with Suc.IH show ?case by simp
qed

lemma finite_ipath_has_eventual_mutual_anchor:
  assumes finite_nodes: "finite V"
    and nodes: "range p \<subseteq> V"
    and path: "\<And>n. (p n, p (Suc n)) \<in> E"
  obtains x N where
    "x \<in> V"
    "\<And>n. N \<le> n \<Longrightarrow> (x, p n) \<in> E\<^sup>*"
    "\<And>n. N \<le> n \<Longrightarrow> (p n, x) \<in> E\<^sup>*"
proof -
  have recurring: "\<exists>x \<in> V. infinite {n. p n = x}"
  proof (rule ccontr)
    assume none: "\<not> (\<exists>x \<in> V. infinite {n. p n = x})"
    have finite_each: "\<And>x. x \<in> V \<Longrightarrow> finite {n. p n = x}"
      using none by blast
    have finite_union: "finite (\<Union>x\<in>V. {n. p n = x})"
      using finite_nodes finite_each by simp
    have cover: "(UNIV :: nat set) = (\<Union>x\<in>V. {n. p n = x})"
      using nodes by auto
    from finite_union have "finite (UNIV :: nat set)" unfolding cover .
    then show False by simp
  qed
  from recurring obtain x where xV: "x \<in> V"
    and often: "infinite {n. p n = x}" by blast
  have "{n. p n = x} \<noteq> {}" by (rule infinite_imp_nonempty[OF often])
  then obtain N where at_N: "p N = x" by blast
  have forward: "\<And>n. N \<le> n \<Longrightarrow> (x, p n) \<in> E\<^sup>*"
  proof -
    fix n
    assume "N \<le> n"
    have "(p N, p n) \<in> E\<^sup>*"
      by (rule ipath_interval_rtrancl[
          where p=p and E=E and i=N and j=n, OF path `N \<le> n`])
    then show "(x, p n) \<in> E\<^sup>*" unfolding at_N .
  qed
  have backward: "\<And>n. N \<le> n \<Longrightarrow> (p n, x) \<in> E\<^sup>*"
  proof -
    fix n
    assume "N \<le> n"
    from often[unfolded infinite_nat_iff_unbounded]
    obtain m where nm: "n < m" and at_m: "p m = x" by blast
    have "(p n, p m) \<in> E\<^sup>*"
      by (rule ipath_interval_rtrancl[
          where p=p and E=E and i=n and j=m,
          OF path less_imp_le[OF nm]])
    then show "(p n, x) \<in> E\<^sup>*" unfolding at_m .
  qed
  show thesis by (rule that[OF xV forward backward])
qed

end
