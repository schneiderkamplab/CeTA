theory Outermost_RZ_Transformation
  imports
    TRS.Outermost_Rewriting
    "Abstract-Rewriting.Relative_Rewriting"
    Auxx.Name
    TA.Exact_Tree_Automata_Completion
    TA.Tree_Automata_Containment_Impl
    TA.Tree_Automata_Wit_Impl
begin

text \<open>
  Relation-level soundness core for the Raffelsieper-Zantema transformation.
  The concrete transformation will discharge the grounding and simulation premises.
\<close>

lemma adapt_vars_ground_transitive:
  fixes t :: "('f,'a) term"
  assumes "ground t"
  shows "(adapt_vars (adapt_vars t :: ('f,'b) term) :: ('f,'c) term) =
    adapt_vars t"
  using assms by (induct t) auto

lemma ta_lang_containment_variable_type:
  fixes A :: "('q,'f) ta"
    and B :: "('p,'f) ta"
  assumes containment: "(ta_lang A :: ('f,'v) terms) \<subseteq> ta_lang B"
  shows "(ta_lang A :: ('f,'w) terms) \<subseteq> ta_lang B"
proof
  fix t :: "('f,'w) term"
  assume in_A: "t \<in> ta_lang A"
  from ta_langE2[OF in_A] obtain q where g: "ground t"
    and qf: "q \<in> ta_final A" and qr: "q \<in> ta_res A (adapt_vars t)" by blast
  let ?u = "adapt_vars t :: ('f,'v) term"
  have u_A: "?u \<in> ta_lang A"
    by (rule ta_langI2[OF ground_adapt_vars[THEN iffD2, OF g] qf])
       (use qr adapt_vars_ground_transitive[OF g, where 'b='v and 'c='q] in auto)
  from subsetD[OF containment u_A] ta_langE2
  obtain p where ug: "ground ?u" and pf: "p \<in> ta_final B"
    and pr: "p \<in> ta_res B (adapt_vars ?u)" by blast
  show "t \<in> ta_lang B"
    by (rule ta_langI2[OF g pf])
       (use pr adapt_vars_ground_transitive[OF g, where 'b='v and 'c='p] in auto)
qed

lemma lang_containment_variable_type:
  fixes A :: "('q,'f) ta"
    and B :: "('p,'f) ta"
    and anchor :: 'v
    and output_anchor :: 'w
  assumes anchor_refl: "anchor = anchor"
    and output_anchor_refl: "output_anchor = output_anchor"
    and containment: "(lang A :: ('f,'v) terms) \<subseteq> lang B"
  shows "(lang A :: ('f,'w) terms) \<subseteq> lang B"
  using ta_lang_containment_variable_type[of A B, OF containment[folded ta_lang_lang_eq]]
  unfolding ta_lang_lang_eq .

lemma linear_pattern_ground_instances_ta_exact:
  fixes t :: "('f,'v) term"
    and F :: "'f sig"
  assumes const_in: "(a,0) \<in> F"
    and marker: "(d,0) \<notin> F"
    and finite: "finite F"
    and linear: "linear_term t"
    and sig: "funas_term t \<subseteq> F"
  shows "lang (ground_instances_ta F d t) = ground_instances F t"
proof -
  interpret E: etac d F "{} :: ('f,'v) trs" a
      "empty_ta :: ((('f,'v) term),'f) ta"
    apply unfold_locales
    using const_in marker finite
    by (auto simp: funas_ta_def growing_def ta_states_def r_states_def accessible_def)
  show ?thesis
  proof (intro equalityI subsetI)
    fix s :: "('f,'v) term"
    assume accepted: "s \<in> lang (ground_instances_ta F d t)"
    from accepted have ground: "ground s"
      and reach: "star d t \<in> reachable_states
        (ground_instances_ta F d t) (fterm s)"
      unfolding lang_def by auto
    have state: "star d t \<in> ta_states (ground_instances_ta F d t)"
      by (simp add: ta_states_def)
    from E.reachable_states_ground_instances_ta_gi[OF state sig, of s]
      reach have gi: "E.gi (star d t) s" by blast
    from E.gi_ground_instances[OF linear sig, of s] gi
    show "s \<in> ground_instances F t" by blast
  next
    fix s :: "('f,'v) term"
    assume inst_mem: "s \<in> ground_instances F t"
    from E.gi_ground_instances[OF linear sig, of s] inst_mem
    have gi: "E.gi (star d t) s" by blast
    have state: "star d t \<in> ta_states (ground_instances_ta F d t)"
      by (simp add: ta_states_def)
    from E.reachable_states_ground_instances_ta_gi[OF state sig, of s] gi
    have reach: "star d t \<in> reachable_states
      (ground_instances_ta F d t) (fterm s)" by blast
    from inst_mem have "ground s" unfolding ground_instances_def by auto
    with reach show "s \<in> lang (ground_instances_ta F d t)"
      unfolding lang_def by auto
  qed
qed

definition rz_pattern_ta where
  "rz_pattern_ta F d i t =
    fmap_states_ta (Pair i) (ground_instances_ta F d t)"

fun rz_patterns_ta_from where
  "rz_patterns_ta_from F d i [] = empty_ta"
| "rz_patterns_ta_from F d i (t # ts) =
    ta_union (rz_pattern_ta F d i t)
      (rz_patterns_ta_from F d (Suc i) ts)"

definition rz_patterns_ta where
  "rz_patterns_ta F d ts = rz_patterns_ta_from F d 0 ts"

lemma rz_patterns_ta_from_eps [simp]:
  "ta_eps (rz_patterns_ta_from F d i ts) = {}"
  by (induct ts arbitrary: i)
     (simp_all add: rz_pattern_ta_def fmap_states_ta_def ta_union_def)

lemma rz_pattern_ta_states:
  "ta_states (rz_pattern_ta F d i t) \<subseteq> {i} \<times> UNIV"
  unfolding rz_pattern_ta_def fmap_states_ta_def ta_states_def r_states_def
  by (auto split: ta_rule.splits)

lemma rz_patterns_ta_from_states:
  "ta_states (rz_patterns_ta_from F d i ts) \<subseteq>
    {i ..< i + length ts} \<times> UNIV"
proof (induct ts arbitrary: i)
  case Nil
  then show ?case
    by (simp add: ta_states_def r_states_def)
next
  case (Cons t ts)
  have left: "ta_states (rz_pattern_ta F d i t) \<subseteq> {i} \<times> UNIV"
    by (rule rz_pattern_ta_states)
  have right: "ta_states (rz_patterns_ta_from F d (Suc i) ts) \<subseteq>
      {Suc i ..< Suc i + length ts} \<times> UNIV"
    by (rule Cons.hyps)
  show ?case using left right
    by (auto simp: ta_states_ta_union_iff)
qed

lemma rz_pattern_ta_lang:
  "lang (rz_pattern_ta F d i t) = lang (ground_instances_ta F d t)"
proof -
  have inj: "inj_on (Pair i) (ta_states (ground_instances_ta F d t))"
    by (auto simp: inj_on_def)
  from fmap_ta(2)[OF inj]
  show ?thesis unfolding rz_pattern_ta_def ta_lang_lang_eq by simp
qed

definition rz_sig_rules_list where
  "rz_sig_rules_list F d =
    map (\<lambda>fn. TA_rule (fst fn) (replicate (snd fn) (Fun d [])) (Fun d [])) F"

fun rz_ground_instances_rules_list where
  "rz_ground_instances_rules_list F d (Var x) = rz_sig_rules_list F d"
| "rz_ground_instances_rules_list F d (Fun f ts) =
    TA_rule f (map (star d) ts) (star d (Fun f ts)) #
      concat (map (rz_ground_instances_rules_list F d) ts)"

fun rz_map_ta_rule where
  "rz_map_ta_rule h (TA_rule f qs q) = TA_rule f (map h qs) (h q)"

definition rz_pattern_final_list where
  "rz_pattern_final_list d i t = [(i, star d t)]"

definition rz_pattern_rules_list where
  "rz_pattern_rules_list F d i t =
    map (rz_map_ta_rule (Pair i)) (rz_ground_instances_rules_list F d t)"

fun rz_patterns_final_list_from where
  "rz_patterns_final_list_from d i [] = []"
| "rz_patterns_final_list_from d i (t # ts) =
    rz_pattern_final_list d i t @ rz_patterns_final_list_from d (Suc i) ts"

fun rz_patterns_rules_list_from where
  "rz_patterns_rules_list_from F d i [] = []"
| "rz_patterns_rules_list_from F d i (t # ts) =
    rz_pattern_rules_list F d i t @ rz_patterns_rules_list_from F d (Suc i) ts"

lemma set_rz_sig_rules_list:
  "set (rz_sig_rules_list F d) = sig_rules (set F) (Fun d [])"
  unfolding rz_sig_rules_list_def sig_rules_def by force

lemma set_rz_ground_instances_rules_list:
  "set (rz_ground_instances_rules_list F d t) =
    ground_instances_rules (set F) d t"
  by (induct t) (auto simp: set_rz_sig_rules_list)

lemma set_rz_pattern_final_list:
  "set (rz_pattern_final_list d i t) =
    ta_final (rz_pattern_ta (set F) d i t)"
  unfolding rz_pattern_final_list_def rz_pattern_ta_def fmap_states_ta_def
    ground_instances_ta_def by auto

lemma set_rz_pattern_rules_list:
  "set (rz_pattern_rules_list F d i t) =
    ta_rules (rz_pattern_ta (set F) d i t)"
proof -
  have rules: "set (rz_ground_instances_rules_list F d t) =
      ground_instances_rules (set F) d t"
    by (rule set_rz_ground_instances_rules_list)
  show ?thesis
    unfolding rz_pattern_rules_list_def rz_pattern_ta_def fmap_states_ta_def
      ground_instances_ta_def
    apply (simp only: set_map rules Let_def ta.simps)
    apply (rule image_cong[OF refl])
    subgoal for r by (cases r) simp
    done
qed

lemma set_rz_patterns_final_list_from:
  "set (rz_patterns_final_list_from d i ts) =
    ta_final (rz_patterns_ta_from (set F) d i ts)"
proof (induct ts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using set_rz_pattern_final_list[of d i t F] Cons.hyps[of "Suc i"] by simp
qed

lemma set_rz_patterns_rules_list_from:
  "set (rz_patterns_rules_list_from F d i ts) =
    ta_rules (rz_patterns_ta_from (set F) d i ts)"
proof (induct ts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  show ?case
    using set_rz_pattern_rules_list[of F d i t] Cons.hyps[of "Suc i"] by simp
qed

definition rz_pattern_ta_code where
  "rz_pattern_ta_code F d i t = ta_make_ls_code
    (rz_pattern_final_list d i t) (rz_pattern_rules_list F d i t) []"

definition rz_patterns_ta_code where
  "rz_patterns_ta_code F d ts = ta_make_ls_code
    (rz_patterns_final_list_from d 0 ts)
    (rz_patterns_rules_list_from F d 0 ts) []"

lemma rz_pattern_ta_code_refine:
  "(rz_pattern_ta_code F d i t, rz_pattern_ta (set F) d i t) \<in> dflt_ta_rel"
proof -
  have rel: "(ta_make_ls_code (rz_pattern_final_list d i t)
      (rz_pattern_rules_list F d i t) [],
      ta_make_ls (rz_pattern_final_list d i t)
        (rz_pattern_rules_list F d i t) []) \<in> dflt_ta_rel"
    by (rule ta_make_ls_code.refine[THEN fun_relD3']) auto
  have eq: "ta_make_ls (rz_pattern_final_list d i t)
      (rz_pattern_rules_list F d i t) [] = rz_pattern_ta (set F) d i t"
    unfolding ta_make_ls_def
    by (rule ta.equality)
       (simp_all add: set_rz_pattern_final_list set_rz_pattern_rules_list
         rz_pattern_final_list_def rz_pattern_ta_def fmap_states_ta_def
         ground_instances_ta_def ta.make_def)
  show ?thesis
    using rel eq by (simp add: rz_pattern_ta_code_def)
qed

lemma rz_patterns_ta_code_refine:
  "(rz_patterns_ta_code F d ts, rz_patterns_ta (set F) d ts) \<in> dflt_ta_rel"
proof -
  have rel: "(ta_make_ls_code (rz_patterns_final_list_from d 0 ts)
      (rz_patterns_rules_list_from F d 0 ts) [],
      ta_make_ls (rz_patterns_final_list_from d 0 ts)
        (rz_patterns_rules_list_from F d 0 ts) []) \<in> dflt_ta_rel"
    by (rule ta_make_ls_code.refine[THEN fun_relD3']) auto
  have eq: "ta_make_ls (rz_patterns_final_list_from d 0 ts)
      (rz_patterns_rules_list_from F d 0 ts) [] = rz_patterns_ta (set F) d ts"
    unfolding rz_patterns_ta_def ta_make_ls_def
    by (rule ta.equality)
       (simp_all add: set_rz_patterns_final_list_from
         set_rz_patterns_rules_list_from rz_patterns_ta_from.simps ta.make_def)
  show ?thesis
    using rel eq by (simp add: rz_patterns_ta_code_def)
qed

lemma ta_lang_containment_impl_XNone_sound:
  fixes A :: "('q::compare_order,'f::compare_order) ta"
    and B :: "('q,'f) ta"
  assumes A: "(A', A) \<in> dflt_ta_rel"
    and B: "(B', B) \<in> dflt_ta_rel"
    and result: "ta_lang_containment_impl A' B' =
      (XNone :: ('f,unit) term xoption)"
  shows "(ta_lang A :: ('f,unit) terms) \<subseteq> ta_lang B"
proof -
  have impl_ref: "RETURN (ta_lang_containment_impl A' B' ::
      ('f,unit) term xoption) \<le>
      \<Down>(\<langle>\<langle>Id, Id\<rangle>term_rel\<rangle>xoption_rel)
        (ta_lang_containment A B)"
    by (rule ta_lang_containment_impl.refine[OF A B])
  note impl_ref
  also note ta_lang_containment[OF dflt_TA_rel_finite[OF A]
    dflt_TA_rel_finite[OF B], where 'v=unit]
  finally obtain y where rel: "((ta_lang_containment_impl A' B' ::
      ('f,unit) term xoption), y) \<in>
      \<langle>\<langle>Id, Id\<rangle>term_rel\<rangle>xoption_rel"
    and valid: "case y of
      XNone \<Rightarrow> (ta_lang A :: ('f,unit) terms) \<subseteq> ta_lang B
    | XSome t \<Rightarrow> t \<in> ta_lang A - ta_lang B"
    apply (rule RETURN_ref_SPECD)
    subgoal for a
      apply (rule that[of a])
     apply assumption+
      done
    done
  have "y = XNone" using rel result by simp
  with valid show ?thesis by simp
qed

definition rz_cover_check ::
  "('f::compare_order \<times> nat) list \<Rightarrow> 'f \<Rightarrow> 'v::compare_order \<Rightarrow>
    ('f,'v) term list \<Rightarrow> bool" where
  "rz_cover_check F d cover_var patterns =
    (ta_lang_containment_impl
      (rz_pattern_ta_code F d (0::nat) (Var cover_var))
      (rz_patterns_ta_code F d patterns) =
      (XNone :: ('f,unit) term xoption))"

lemma rz_cover_check_sound:
  fixes F :: "('f::compare_order \<times> nat) list"
    and cover_var :: "'x::compare_order"
  assumes "rz_cover_check F d cover_var patterns"
  shows "(lang (rz_pattern_ta (set F) d (0::nat) (Var cover_var)) ::
      ('f,'v) terms) \<subseteq> lang (rz_patterns_ta (set F) d patterns)"
proof -
  have base: "(lang (rz_pattern_ta (set F) d (0::nat) (Var cover_var)) ::
      ('f,unit) terms) \<subseteq> lang (rz_patterns_ta (set F) d patterns)"
    using ta_lang_containment_impl_XNone_sound[
        OF rz_pattern_ta_code_refine rz_patterns_ta_code_refine]
      assms
    unfolding rz_cover_check_def ta_lang_lang_eq by blast
  show ?thesis
    by (rule lang_containment_variable_type[
      where anchor="()" and output_anchor="undefined :: 'v", OF refl refl base])
qed

lemma rz_patterns_ta_from_lang:
  "lang (rz_patterns_ta_from F d i ts) =
    (\<Union>t\<in>set ts. lang (ground_instances_ta F d t))"
proof (induct ts arbitrary: i)
  case Nil
  then show ?case by (auto simp: lang_def)
next
  case (Cons t ts)
  have left: "ta_states (rz_pattern_ta F d i t) \<subseteq> {i} \<times> UNIV"
    by (rule rz_pattern_ta_states)
  have right: "ta_states (rz_patterns_ta_from F d (Suc i) ts) \<subseteq>
      {Suc i ..< Suc i + length ts} \<times> UNIV"
    by (rule rz_patterns_ta_from_states)
  have disjoint: "ta_states (rz_pattern_ta F d i t) \<inter>
      ta_states (rz_patterns_ta_from F d (Suc i) ts) = {}"
    using left right by auto
  from lang_disj_union_eq_union_lang[OF disjoint]
  show ?case using Cons.hyps rz_pattern_ta_lang[of F d i t] by auto
qed

lemma rz_patterns_ta_lang:
  "lang (rz_patterns_ta F d ts) =
    (\<Union>t\<in>set ts. lang (ground_instances_ta F d t))"
  unfolding rz_patterns_ta_def by (rule rz_patterns_ta_from_lang)

lemma rz_linear_patterns_ta_exact:
  assumes const_in: "(a,0) \<in> F"
    and marker: "(d,0) \<notin> F"
    and finite: "finite F"
    and linear: "\<And>t. t \<in> set ts \<Longrightarrow> linear_term t"
    and sig: "\<And>t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> F"
  shows "lang (rz_patterns_ta F d ts) =
    (\<Union>t\<in>set ts. ground_instances F t)"
proof -
  have exact: "\<And>t. t \<in> set ts \<Longrightarrow>
      lang (ground_instances_ta F d t) = ground_instances F t"
    by (intro linear_pattern_ground_instances_ta_exact[OF const_in marker finite]
        linear sig)
  show ?thesis
    unfolding rz_patterns_ta_lang using exact by blast
qed

lemma rz_ta_containment_imp_ground_cover:
  fixes patterns :: "('f,'v) term list"
    and x :: 'v
    and s :: "('f,'v) term"
  assumes const_in: "(a,0) \<in> F"
    and marker: "(d,0) \<notin> F"
    and finite: "finite F"
    and linear: "\<And>t. t \<in> set patterns \<Longrightarrow> linear_term t"
    and sig: "\<And>t. t \<in> set patterns \<Longrightarrow> funas_term t \<subseteq> F"
    and containment: "(lang (rz_pattern_ta F d (0::nat) (Var x)) :: ('f,'v) terms) \<subseteq>
      lang (rz_patterns_ta F d patterns)"
    and ground: "ground s"
    and source_sig: "funas_term s \<subseteq> F"
  shows "\<exists>p\<in>set patterns. \<exists>\<sigma>. p \<cdot> \<sigma> = s"
proof -
  have fg: "fground F s" using ground source_sig by simp
  have universe: "s \<in> (lang (rz_pattern_ta F d (0::nat) (Var x)) :: ('f,'v) terms)"
    using fg unfolding rz_pattern_ta_lang
    by (simp only: ground_instances_ta_Var mem_Collect_eq)
  have accepted: "s \<in> (lang (rz_patterns_ta F d patterns) :: ('f,'v) terms)"
    using containment universe by blast
  have exact: "(lang (rz_patterns_ta F d patterns) :: ('f,'v) terms) =
      (\<Union>p\<in>set patterns. ground_instances F p)"
    by (rule rz_linear_patterns_ta_exact[OF const_in marker finite linear sig])
  from accepted exact have "s \<in> (\<Union>p\<in>set patterns. ground_instances F p)"
    by simp
  then obtain p where p: "p \<in> set patterns" and inst: "s \<in> ground_instances F p"
    by blast
  from inst obtain \<sigma> where "s = p \<cdot> \<sigma>"
    unfolding ground_instances_def by blast
  with p show ?thesis by blast
qed

definition rz_linear_lhss where
  "rz_linear_lhss R = filter linear_term (map fst R)"

lemma rz_ta_nonredex_cover:
  fixes R :: "('f,'v) rules"
    and patterns :: "('f,'v) term list"
    and F :: "'f sig"
    and x :: 'v
    and s :: "('f,'v) term"
  defines "basis \<equiv> rz_linear_lhss R"
  assumes const_in: "(a,0) \<in> F"
    and marker: "(d,0) \<notin> F"
    and finite: "finite F"
    and source_sig: "funas_trs (set R) \<subseteq> F"
    and pattern_linear: "\<And>p. p \<in> set patterns \<Longrightarrow> linear_term p"
    and pattern_sig: "\<And>p. p \<in> set patterns \<Longrightarrow> funas_term p \<subseteq> F"
    and containment: "(lang (rz_pattern_ta F d (0::nat) (Var x)) :: ('f,'v) terms) \<subseteq>
      lang (rz_patterns_ta F d (basis @ patterns))"
    and ground: "ground s"
    and sig: "funas_term s \<subseteq> F"
    and nonredex: "\<And>l. l \<in> fst ` set R \<Longrightarrow>
      \<not> (\<exists>\<sigma>. s = l \<cdot> \<sigma>)"
  shows "\<exists>p\<in>set patterns. \<exists>\<sigma>. p \<cdot> \<sigma> = s"
proof -
  have basis_linear: "\<And>p. p \<in> set basis \<Longrightarrow> linear_term p"
    unfolding basis_def rz_linear_lhss_def by auto
  have basis_sig: "\<And>p. p \<in> set basis \<Longrightarrow> funas_term p \<subseteq> F"
    using source_sig unfolding basis_def rz_linear_lhss_def funas_trs_def funas_rule_def
    by auto
  have combined_linear: "\<And>p. p \<in> set (basis @ patterns) \<Longrightarrow> linear_term p"
    using basis_linear pattern_linear by auto
  have combined_sig: "\<And>p. p \<in> set (basis @ patterns) \<Longrightarrow> funas_term p \<subseteq> F"
    using basis_sig pattern_sig by auto
  from rz_ta_containment_imp_ground_cover[
      OF const_in marker finite combined_linear combined_sig containment ground sig]
  obtain p \<sigma> where p: "p \<in> set (basis @ patterns)" and inst: "p \<cdot> \<sigma> = s"
    by blast
  show ?thesis
  proof (cases "p \<in> set patterns")
    case True
    with inst show ?thesis by blast
  next
    case False
    with p have pb: "p \<in> set basis" by simp
    from pb have lhs: "p \<in> fst ` set R"
      unfolding basis_def rz_linear_lhss_def by auto
    from nonredex[OF lhs] inst show ?thesis by blast
  qed
qed

lemma linear_fresh_constant_ground_match:
  fixes l t :: "('f,'v) term"
    and c :: 'f
  defines "\<gamma> \<equiv> \<lambda>_. Fun c []"
  assumes linear: "linear_term l"
    and fresh: "(c,0) \<notin> funas_term l"
    and match: "l \<cdot> \<sigma> = t \<cdot> \<gamma>"
  shows "\<exists>\<tau>. l \<cdot> \<tau> = t"
  using linear fresh match
proof (induction l arbitrary: t \<sigma>)
  case (Var x)
  then show ?case
    by (intro exI[of _ "\<lambda>y. if y = x then t else Var y"]) simp
next
  case (Fun f ls)
  show ?case
  proof (cases t)
    case (Var x)
    with Fun.prems have "f = c" and "ls = []"
      unfolding \<gamma>_def by auto
    with Fun.prems show ?thesis by simp
  next
    case (Fun g ts)
    have term_eq:
      "Fun f (map (\<lambda>s. s \<cdot> \<sigma>) ls) =
        Fun g (map (\<lambda>s. s \<cdot> \<gamma>) ts)"
      using Fun.prems Fun unfolding \<gamma>_def by simp
    from term_eq have fg: "f = g" and args_eq:
      "map (\<lambda>s. s \<cdot> \<sigma>) ls = map (\<lambda>s. s \<cdot> \<gamma>) ts"
      by auto
    from arg_cong[OF args_eq, of length]
    have len: "length ls = length ts" by simp
    from Fun.prems have part: "is_partition (map vars_term ls)"
      by simp
    have local: "\<And>i. i < length ls \<Longrightarrow>
      \<exists>\<tau>. ls ! i \<cdot> \<tau> = ts ! i"
    proof -
      fix i
      assume i: "i < length ls"
      from Fun.prems have lin_i: "linear_term (ls ! i)"
        using i by simp
      from Fun.prems have fresh_i: "(c,0) \<notin> funas_term (ls ! i)"
        using i by auto
      from arg_cong[OF args_eq, of "\<lambda>xs. xs ! i"] len i have eq_i:
        "ls ! i \<cdot> \<sigma> = ts ! i \<cdot> \<gamma>"
        by simp
      show "\<exists>\<tau>. ls ! i \<cdot> \<tau> = ts ! i"
        by (rule Fun.IH[OF nth_mem[OF i] lin_i fresh_i eq_i])
    qed
    have choices: "\<forall>i. \<exists>\<tau>. i < length ls \<longrightarrow>
      ls ! i \<cdot> \<tau> = ts ! i"
      using local by blast
    from choice[OF choices] obtain \<tau> where tau:
      "\<And>i. i < length ls \<Longrightarrow> ls ! i \<cdot> \<tau> i = ts ! i"
      by blast
    from subst_merge[OF part, of \<tau>] obtain \<delta> where delta:
      "\<And>i x. i < length ls \<Longrightarrow> x \<in> vars_term (ls ! i) \<Longrightarrow>
        \<delta> x = \<tau> i x"
      by blast
    have "map (\<lambda>s. s \<cdot> \<delta>) ls = ts"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>s. s \<cdot> \<delta>) ls) = length ts"
        by (simp add: len)
      fix i
      assume i: "i < length (map (\<lambda>s. s \<cdot> \<delta>) ls)"
      have ii: "i < length ls" using i by simp
      have subst_eq: "ls ! i \<cdot> \<delta> = ls ! i \<cdot> \<tau> i"
        by (rule term_subst_eq, insert delta[OF ii], auto)
      with tau[OF ii] show "map (\<lambda>s. s \<cdot> \<delta>) ls ! i = ts ! i"
        using ii by simp
    qed
    with fg Fun show ?thesis
      by (intro exI[of _ \<delta>]) simp
  qed
qed

definition quasi_left_linear_lhss :: "('f,'v) terms \<Rightarrow> bool" where
  "quasi_left_linear_lhss Q \<longleftrightarrow>
    (\<forall>l\<in>Q. \<exists>k\<in>Q. linear_term k \<and> (\<exists>\<rho>. k \<cdot> \<rho> = l))"

lemma quasi_left_linear_ostep_cond_ground:
  fixes s :: "('f,'v) term"
    and c :: 'f
  defines "\<gamma> \<equiv> \<lambda>_. Fun c []"
  assumes quasi: "quasi_left_linear_lhss Q"
    and fresh: "\<And>l. l \<in> Q \<Longrightarrow> (c,0) \<notin> funas_term l"
    and poss: "p \<in> poss s"
    and cond: "ostep_cond Q p s"
  shows "ostep_cond Q p (s \<cdot> \<gamma>)"
  unfolding ostep_cond_def ostep_cond_single_def
proof (intro ballI allI impI notI)
  fix l q
  assume l: "l \<in> Q" and qp: "q <\<^sub>p p"
    and redex: "\<exists>\<sigma>. s \<cdot> \<gamma> |_ q = l \<cdot> \<sigma>"
  from qp obtain r where p: "p = q @ r" and r: "r \<noteq> []"
    unfolding less_pos_def' by blast
  have qposs: "q \<in> poss s"
    using poss p poss_append_poss by blast
  from redex obtain \<sigma> where redex: "s \<cdot> \<gamma> |_ q = l \<cdot> \<sigma>"
    by blast
  from quasi l obtain k \<rho> where k: "k \<in> Q" and linear: "linear_term k"
    and inst: "k \<cdot> \<rho> = l"
    unfolding quasi_left_linear_lhss_def by blast
  have grounded_match: "k \<cdot> (\<rho> \<circ>\<^sub>s \<sigma>) = (s |_ q) \<cdot> \<gamma>"
  proof -
    have compose: "k \<cdot> (\<rho> \<circ>\<^sub>s \<sigma>) = (k \<cdot> \<rho>) \<cdot> \<sigma>"
      by (induct k) (auto simp: subst_compose_def)
    have subterm: "s \<cdot> \<gamma> |_ q = (s |_ q) \<cdot> \<gamma>"
      by (rule subt_at_subst[OF qposs])
    show ?thesis using compose inst redex subterm by simp
  qed
  from linear_fresh_constant_ground_match[
      OF linear fresh[OF k] grounded_match[unfolded \<gamma>_def]]
  obtain \<tau> where match: "k \<cdot> \<tau> = s |_ q" by blast
  from cond[unfolded ostep_cond_def ostep_cond_single_def,
      rule_format, OF k qp]
  show False using match[symmetric] by blast
qed

lemma quasi_left_linear_ostep_ground:
  fixes R :: "('f,'v) trs"
    and c :: 'f
  defines "\<gamma> \<equiv> \<lambda>_. Fun c []"
  assumes quasi: "quasi_left_linear_lhss Q"
    and fresh: "\<And>l. l \<in> Q \<Longrightarrow> (c,0) \<notin> funas_term l"
    and step: "(s,t) \<in> ostep Q R"
  shows "(s \<cdot> \<gamma>, t \<cdot> \<gamma>) \<in> ostep Q R"
proof -
  from step obtain p lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "ostep_cond Q p s"
    unfolding ostep_def ostep_p_def by blast
  from raw have poss: "p \<in> poss s"
    unfolding rstep_r_p_s_def' by auto
  have raw_ground: "(s \<cdot> \<gamma>, t \<cdot> \<gamma>) \<in>
      rstep_r_p_s R lr p (\<sigma> \<circ>\<^sub>s \<gamma>)"
    using raw unfolding rstep_r_p_s_def'
    by (auto simp: ctxt_of_pos_term_subst)
  have cond_ground: "ostep_cond Q p (s \<cdot> \<gamma>)"
    by (rule quasi_left_linear_ostep_cond_ground[
        OF quasi fresh poss cond, folded \<gamma>_def])
  show ?thesis
    unfolding ostep_def ostep_p_def using raw_ground cond_ground by blast
qed

abbreviation rz_wrap where
  "rz_wrap f t \<equiv> Fun f [t]"

definition rz_blocked_args where
  "rz_blocked_args block ts = map (\<lambda>t. rz_wrap block t) ts"

lemma rz_ground_position_simulation:
  fixes R R1 :: "('f,'v) trs"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and F :: "'f sig"
  assumes root_step: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (rz_wrap down (fst lr \<cdot> \<sigma>),
        rz_wrap up (snd lr \<cdot> \<sigma>)) \<in> rstep R1"
    and descent: "\<And>f ts i. ground (Fun f ts) \<Longrightarrow>
      funas_term (Fun f ts) \<subseteq> F \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)) \<Longrightarrow>
      (rz_wrap down (Fun f ts),
        Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
    and ascent: "\<And>f ts i. funas_term (Fun f ts) \<subseteq> F \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
        rz_wrap up (Fun f ts)) \<in> rstep R1"
    and raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "ostep_cond Q p s"
    and gs: "ground s"
    and gt: "ground t"
    and fs: "funas_term s \<subseteq> F"
    and ft: "funas_term t \<subseteq> F"
  shows "(rz_wrap down s, rz_wrap up t) \<in> (rstep R1)\<^sup>+"
  using raw cond gs gt fs ft
proof (induct p arbitrary: s t)
  case Nil
  from Nil.prems(1) have lr: "lr \<in> R"
    and s: "s = fst lr \<cdot> \<sigma>" and t: "t = snd lr \<cdot> \<sigma>"
    unfolding rstep_r_p_s_def' by auto
  from root_step[OF lr, of \<sigma>] s t show ?case
    by (intro r_into_trancl) simp
next
  case (Cons i q)
  show ?case
  proof (cases s)
    case (Var x)
    with Cons.prems(1) show ?thesis
      unfolding rstep_r_p_s_def' by auto
  next
    case (Fun f ss)
    from Cons.prems(1)[unfolded Fun rstep_r_p_s_def' Cons]
    have i: "i < length ss" and q: "q \<in> poss (ss ! i)"
      and lr: "lr \<in> R"
      and at: "ss ! i |_ q = fst lr \<cdot> \<sigma>"
      and t: "t = Fun f (ss[i := replace_at (ss ! i) q
        (snd lr \<cdot> \<sigma>)])"
      by (auto simp: upd_conv_take_nth_drop)
    let ?u = "replace_at (ss ! i) q (snd lr \<cdot> \<sigma>)"
    have local_raw: "(ss ! i, ?u) \<in> rstep_r_p_s R lr q \<sigma>"
      unfolding rstep_r_p_s_def' using q lr at by auto
    have local_cond: "ostep_cond Q q (ss ! i)"
      unfolding ostep_cond_def ostep_cond_single_def
    proof (intro ballI allI impI)
      fix l p'
      assume l: "l \<in> Q" and less: "p' <\<^sub>p q"
      have lifted_less: "i # p' <\<^sub>p i # q"
        using less unfolding less_pos_def' by auto
      from Cons.prems(2)[unfolded Fun ostep_cond_def ostep_cond_single_def,
          rule_format, OF l lifted_less]
      show "\<not> (\<exists>\<tau>. ss ! i |_ p' = l \<cdot> \<tau>)"
        using i by simp
    qed
    have gss: "ground (ss ! i)"
      using Cons.prems(3)[unfolded Fun] i by auto
    have gu: "ground ?u"
    proof -
      from Cons.prems(4)[unfolded t]
      have all: "\<forall>x\<in>set (ss[i := ?u]). ground x" by simp
      have index: "i < length (ss[i := ?u])" using i by simp
      from all nth_mem[OF index]
      have "ground ((ss[i := ?u]) ! i)" by blast
      with i show ?thesis by simp
    qed
    have fss: "funas_term (ss ! i) \<subseteq> F"
    proof -
      have member: "ss ! i \<in> set ss" using i by simp
      have sub: "funas_term (ss ! i) \<subseteq> \<Union>(funas_term ` set ss)"
        using member by blast
      from sub Cons.prems(5)[unfolded Fun] show ?thesis by auto
    qed
    have fu: "funas_term ?u \<subseteq> F"
    proof -
      from Cons.prems(6)[unfolded t]
      have all: "\<forall>x\<in>set (ss[i := ?u]). funas_term x \<subseteq> F" by auto
      have index: "i < length (ss[i := ?u])" using i by simp
      from all nth_mem[OF index]
      have "funas_term ((ss[i := ?u]) ! i) \<subseteq> F" by blast
      with i show ?thesis by simp
    qed
    from Cons.hyps[OF local_raw local_cond gss gu fss fu]
    have local_sim:
      "(rz_wrap down (ss ! i), rz_wrap up ?u) \<in> (rstep R1)\<^sup>+" .
    have nonredex: "\<And>l. l \<in> Q \<Longrightarrow>
      \<not> (\<exists>\<tau>. Fun f ss = l \<cdot> \<tau>)"
    proof -
      fix l
      assume l: "l \<in> Q"
      have root_prefix: "[] <\<^sub>p i # q"
        unfolding less_pos_def' by auto
      from Cons.prems(2)[unfolded Fun ostep_cond_def ostep_cond_single_def,
          rule_format, OF l root_prefix]
      show "\<not> (\<exists>\<tau>. Fun f ss = l \<cdot> \<tau>)" by simp
    qed
    let ?blocked = "rz_blocked_args block ss"
    let ?before = "Fun (flat (f,length ss))
      (?blocked[i := rz_wrap down (ss ! i)])"
    let ?after = "Fun (flat (f,length ss))
      (?blocked[i := rz_wrap up ?u])"
    have descend: "(rz_wrap down (Fun f ss), ?before) \<in> rstep R1"
      by (rule descent[OF Cons.prems(3)[unfolded Fun]
          Cons.prems(5)[unfolded Fun] i nonredex])
    have pos: "[i] \<in> poss ?before" using i
      unfolding rz_blocked_args_def by simp
    let ?C = "ctxt_of_pos_term [i] ?before"
    from trancl_rstep_ctxt[OF local_sim, of ?C]
    have lifted: "(?C\<langle>rz_wrap down (ss ! i)\<rangle>,
        ?C\<langle>rz_wrap up ?u\<rangle>) \<in> (rstep R1)\<^sup>+" .
    have before: "?C\<langle>rz_wrap down (ss ! i)\<rangle> = ?before"
      using ctxt_supt_id[OF pos] i unfolding rz_blocked_args_def by simp
    have blocked_i: "i < length ?blocked"
      using i unfolding rz_blocked_args_def by (simp add: map_update)
    have update_after:
      "?blocked[i := rz_wrap up ?u] =
        take i ?blocked @ rz_wrap up ?u # drop (Suc i) ?blocked"
      by (rule upd_conv_take_nth_drop[OF blocked_i])
    have update_before:
      "?blocked[i := rz_wrap down (ss ! i)] =
        take i ?blocked @ rz_wrap down (ss ! i) # drop (Suc i) ?blocked"
      by (rule upd_conv_take_nth_drop[OF blocked_i])
    have replace: "replace_at ?before [i] (rz_wrap up ?u) = ?after"
      using i update_after update_before unfolding rz_blocked_args_def by simp
    have after: "?C\<langle>rz_wrap up ?u\<rangle> = ?after"
      using ctxt_supt_id[OF pos] replace i update_after by simp
    from lifted before after have middle: "(?before,?after) \<in> (rstep R1)\<^sup>+"
      by simp
    let ?ts = "ss[i := ?u]"
    have len: "length ?ts = length ss" by simp
    have blocked_update:
      "rz_blocked_args block ?ts = ?blocked[i := rz_wrap block ?u]"
      unfolding rz_blocked_args_def by (rule map_update)
    have after_ascent_lhs:
      "?after = Fun (flat (f,length ?ts))
        ((rz_blocked_args block ?ts)[i := rz_wrap up (?ts ! i)])"
      using i blocked_update by simp
    have target: "Fun f ?ts = t" using t by simp
    have target_sig: "funas_term (Fun f ?ts) \<subseteq> F"
      using Cons.prems(6) target by simp
    have ascend: "(?after, rz_wrap up (Fun f ?ts)) \<in> rstep R1"
      using ascent[of f ?ts i] target_sig i len after_ascent_lhs by simp
    from descend middle have prefix:
      "(rz_wrap down (Fun f ss),?after) \<in> (rstep R1)\<^sup>+"
      by (meson r_into_trancl trancl_trans)
    from prefix ascend target Fun show ?thesis
      by (meson trancl_into_trancl)
  qed
qed

lemma rz_ground_step_top_simulation:
  fixes R R1 :: "('f,'v) trs"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and top up down block :: 'f
    and F :: "'f sig"
  assumes root_step: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (rz_wrap down (fst lr \<cdot> \<sigma>),
        rz_wrap up (snd lr \<cdot> \<sigma>)) \<in> rstep R1"
    and descent: "\<And>f ts i. ground (Fun f ts) \<Longrightarrow>
      funas_term (Fun f ts) \<subseteq> F \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)) \<Longrightarrow>
      (rz_wrap down (Fun f ts),
        Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
    and ascent: "\<And>f ts i. funas_term (Fun f ts) \<subseteq> F \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
        rz_wrap up (Fun f ts)) \<in> rstep R1"
    and reset: "\<And>u. (rz_wrap top (rz_wrap up u),
      rz_wrap top (rz_wrap down u)) \<in> rstep R1"
    and gs: "ground s"
    and gt: "ground t"
    and fs: "funas_term s \<subseteq> F"
    and ft: "funas_term t \<subseteq> F"
    and step: "(s,t) \<in> ostep Q R"
  shows "(rz_wrap top (rz_wrap down s), rz_wrap top (rz_wrap down t))
    \<in> (rstep R1)\<^sup>+"
proof -
  from step obtain p lr \<sigma> where raw: "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "ostep_cond Q p s"
    unfolding ostep_def ostep_p_def by blast
  from rz_ground_position_simulation[
      OF root_step descent ascent raw cond gs gt fs ft]
  have core: "(rz_wrap down s, rz_wrap up t) \<in> (rstep R1)\<^sup>+" .
  let ?source = "rz_wrap top (rz_wrap down s)"
  let ?C = "ctxt_of_pos_term [0] ?source"
  from trancl_rstep_ctxt[OF core, of ?C]
  have lifted: "(?C\<langle>rz_wrap down s\<rangle>,
      ?C\<langle>rz_wrap up t\<rangle>) \<in> (rstep R1)\<^sup>+" .
  have source_pos: "[0] \<in> poss ?source" by simp
  have source: "?C\<langle>rz_wrap down s\<rangle> = ?source"
    using ctxt_supt_id[OF source_pos] by simp
  have target: "?C\<langle>rz_wrap up t\<rangle> = rz_wrap top (rz_wrap up t)"
    by simp
  from lifted source target
  have prefix: "(?source,rz_wrap top (rz_wrap up t)) \<in> (rstep R1)\<^sup>+"
    by simp
  from prefix reset[of t] show ?thesis
    by (rule trancl_into_trancl)
qed

theorem rz_ground_simulation_imp_SN_ostep:
  fixes R :: "('f,'v) trs"
    and R1 :: "('f,'v) trs"
    and Q :: "('f,'v) terms"
    and ground_subst :: "('f,'v) subst"
    and encode :: "('f,'v) term \<Rightarrow> ('f,'v) term"
  assumes transformed_SN: "SN (rstep R1)"
    and grounding: "\<And>s t. (s,t) \<in> ostep Q R \<Longrightarrow>
      (s \<cdot> ground_subst, t \<cdot> ground_subst) \<in> ostep Q R"
    and ground_after: "\<And>t. ground (t \<cdot> ground_subst)"
    and simulation: "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow>
      (s,t) \<in> ostep Q R \<Longrightarrow>
      (encode s, encode t) \<in> (rstep R1)\<^sup>+"
  shows "SN (ostep Q R)"
proof -
  let ?encode = "\<lambda>t. encode (t \<cdot> ground_subst)"
  have target: "SN_rel (rstep R1) {}"
    using transformed_SN by simp
  have source: "SN_rel (ostep Q R) {}"
  proof (rule SN_rel_map[OF target, where R = "ostep Q R" and Rw = "{}" and f = ?encode])
    fix s t
    assume step: "(s,t) \<in> ostep Q R"
    have grounded: "(s \<cdot> ground_subst, t \<cdot> ground_subst) \<in> ostep Q R"
      by (rule grounding[OF step])
    from simulation[OF ground_after ground_after grounded]
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
  then show ?thesis by simp
qed

theorem rz_ground_simulation_imp_SN_sig_ostep:
  fixes R :: "('f,'v) trs"
    and R1 :: "('f,'v) trs"
    and Q :: "('f,'v) terms"
    and F F1 :: "'f sig"
    and ground_subst :: "('f,'v) subst"
    and encode :: "('f,'v) term \<Rightarrow> ('f,'v) term"
  assumes transformed_SN: "SN (rstep R1)"
    and grounding: "\<And>s t. (s,t) \<in> ostep Q R \<Longrightarrow>
      (s \<cdot> ground_subst, t \<cdot> ground_subst) \<in> ostep Q R"
    and ground_after: "\<And>t. ground (t \<cdot> ground_subst)"
    and sig_after: "\<And>t. funas_term t \<subseteq> F \<Longrightarrow>
      funas_term (t \<cdot> ground_subst) \<subseteq> F1"
    and simulation: "\<And>s t. ground s \<Longrightarrow> ground t \<Longrightarrow>
      funas_term s \<subseteq> F1 \<Longrightarrow> funas_term t \<subseteq> F1 \<Longrightarrow>
      (s,t) \<in> ostep Q R \<Longrightarrow>
      (encode s, encode t) \<in> (rstep R1)\<^sup>+"
  shows "SN (sig_step F (ostep Q R))"
proof -
  let ?encode = "\<lambda>t. encode (t \<cdot> ground_subst)"
  have target: "SN_rel (rstep R1) {}" using transformed_SN by simp
  have source: "SN_rel (sig_step F (ostep Q R)) {}"
  proof (rule SN_rel_map[OF target, of _ ?encode])
    fix s t :: "('f,'v) term"
    assume step: "(s,t) \<in> sig_step F (ostep Q R)"
    from step have outer: "(s,t) \<in> ostep Q R"
      and fs: "funas_term s \<subseteq> F" and ft: "funas_term t \<subseteq> F"
      unfolding sig_step_def by auto
    have grounded: "(s \<cdot> ground_subst, t \<cdot> ground_subst) \<in> ostep Q R"
      by (rule grounding[OF outer])
    from simulation[OF ground_after ground_after sig_after[OF fs] sig_after[OF ft]
        grounded]
    have "(?encode s, ?encode t) \<in> rstep R1 O (rstep R1)\<^sup>*"
      unfolding trancl_unfold_left .
    then show "(?encode s, ?encode t) \<in>
      (rstep R1 \<union> {})\<^sup>* O rstep R1 O (rstep R1 \<union> {})\<^sup>*"
      by regexp
  next
    fix s t :: "('f,'v) term"
    assume "(s,t) \<in> {}"
    then show "(?encode s, ?encode t) \<in> (rstep R1 \<union> {})\<^sup>*" by simp
  qed
  then show ?thesis by simp
qed

theorem rz_abstract_transformation_sound:
  fixes R R1 :: "('f,'v) trs"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and top up down block c :: 'f
  assumes transformed_SN: "SN (rstep R1)"
    and quasi: "quasi_left_linear_lhss Q"
    and fresh: "\<And>l. l \<in> Q \<Longrightarrow> (c,0) \<notin> funas_term l"
    and root_step: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (rz_wrap down (fst lr \<cdot> \<sigma>),
        rz_wrap up (snd lr \<cdot> \<sigma>)) \<in> rstep R1"
    and descent: "\<And>f ts i. ground (Fun f ts) \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)) \<Longrightarrow>
      (rz_wrap down (Fun f ts),
        Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
    and ascent: "\<And>f ts i. funas_term (Fun f ts) \<subseteq> UNIV \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
        rz_wrap up (Fun f ts)) \<in> rstep R1"
    and reset: "\<And>u. (rz_wrap top (rz_wrap up u),
      rz_wrap top (rz_wrap down u)) \<in> rstep R1"
  shows "SN (ostep Q R)"
proof (rule rz_ground_simulation_imp_SN_ostep[
    OF transformed_SN,
    where ground_subst = "\<lambda>(_::'v). Fun c []"
      and encode = "\<lambda>t. rz_wrap top (rz_wrap down t)"])
  fix s t
  assume step: "(s,t) \<in> ostep Q R"
  show "(s \<cdot> (\<lambda>_. Fun c []), t \<cdot> (\<lambda>_. Fun c [])) \<in> ostep Q R"
    by (rule quasi_left_linear_ostep_ground[OF quasi fresh step])
next
  fix t :: "('f,'v) term"
  show "ground (t \<cdot> (\<lambda>_. Fun c []))" by auto
next
  fix s t
  assume gs: "ground s" and gt: "ground t" and step: "(s,t) \<in> ostep Q R"
  show "(rz_wrap top (rz_wrap down s), rz_wrap top (rz_wrap down t))
      \<in> (rstep R1)\<^sup>+"
  proof (rule rz_ground_step_top_simulation[
      where F=UNIV, OF root_step _ ascent reset gs gt _ _ step])
    fix f and ts :: "('f,'v) term list" and i
    assume g: "ground (Fun f ts)" and "funas_term (Fun f ts) \<subseteq> UNIV"
      and i: "i < length ts"
      and nr: "\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)"
    show "(rz_wrap down (Fun f ts),
      Fun (flat (f, length ts))
       ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
      by (rule descent[OF g i nr])
  qed simp_all
qed

theorem rz_abstract_transformation_sound_sig:
  fixes R R1 :: "('f,'v) trs"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and F F1 :: "'f sig"
    and top up down block c :: 'f
  assumes transformed_SN: "SN (rstep R1)"
    and quasi: "quasi_left_linear_lhss Q"
    and fresh: "\<And>l. l \<in> Q \<Longrightarrow> (c,0) \<notin> funas_term l"
    and sig_extension: "F \<subseteq> F1"
    and ground_const: "(c,0) \<in> F1"
    and root_step: "\<And>lr \<sigma>. lr \<in> R \<Longrightarrow>
      (rz_wrap down (fst lr \<cdot> \<sigma>),
        rz_wrap up (snd lr \<cdot> \<sigma>)) \<in> rstep R1"
    and descent: "\<And>f ts i. ground (Fun f ts) \<Longrightarrow>
      funas_term (Fun f ts) \<subseteq> F1 \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)) \<Longrightarrow>
      (rz_wrap down (Fun f ts),
        Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
    and ascent: "\<And>f ts i. funas_term (Fun f ts) \<subseteq> F1 \<Longrightarrow>
      i < length ts \<Longrightarrow>
      (Fun (flat (f,length ts))
          ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
        rz_wrap up (Fun f ts)) \<in> rstep R1"
    and reset: "\<And>u. (rz_wrap top (rz_wrap up u),
      rz_wrap top (rz_wrap down u)) \<in> rstep R1"
  shows "SN (sig_step F (ostep Q R))"
proof (rule rz_ground_simulation_imp_SN_sig_ostep[
    OF transformed_SN,
    where ground_subst = "\<lambda>(_::'v). Fun c []"
      and encode = "\<lambda>t. rz_wrap top (rz_wrap down t)"])
  fix s t
  assume step: "(s,t) \<in> ostep Q R"
  show "(s \<cdot> (\<lambda>_. Fun c []), t \<cdot> (\<lambda>_. Fun c [])) \<in> ostep Q R"
    by (rule quasi_left_linear_ostep_ground[OF quasi fresh step])
next
  fix t :: "('f,'v) term"
  show "ground (t \<cdot> (\<lambda>_. Fun c []))" by auto
next
  fix t :: "('f,'v) term"
  assume "funas_term t \<subseteq> F"
  with sig_extension ground_const show
    "funas_term (t \<cdot> (\<lambda>_. Fun c [])) \<subseteq> F1"
    unfolding funas_term_subst by auto
next
  fix s t
  assume gs: "ground s" and gt: "ground t"
    and fs: "funas_term s \<subseteq> F1" and ft: "funas_term t \<subseteq> F1"
    and step: "(s,t) \<in> ostep Q R"
  show "(rz_wrap top (rz_wrap down s), rz_wrap top (rz_wrap down t))
      \<in> (rstep R1)\<^sup>+"
    by (rule rz_ground_step_top_simulation[
        OF root_step descent ascent reset gs gt fs ft step])
qed

fun rz_descent_rule where
  "rz_descent_rule down block flat (Var x) i = (Var x, Var x)"
| "rz_descent_rule down block flat (Fun f ts) i =
    (rz_wrap down (Fun f ts),
      Fun (flat (f,length ts))
        ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)]))"

definition rz_source_rule where
  "rz_source_rule down up lr =
    (rz_wrap down (fst lr), rz_wrap up (snd lr))"

definition rz_reset_rule where
  "rz_reset_rule top_sym up down x =
    (rz_wrap top_sym (rz_wrap up (Var x)),
      rz_wrap top_sym (rz_wrap down (Var x)))"

definition rz_vars where
  "rz_vars n = map Var (x\<^sub>1_to_x\<^sub>n n)"

definition rz_ascent_rule where
  "rz_ascent_rule up block flat fn i =
    (let f = fst fn; n = snd fn; xs = rz_vars n
     in (Fun (flat fn)
          ((rz_blocked_args block xs)[i := rz_wrap up (xs ! i)]),
        rz_wrap up (Fun f xs)))"

definition rz_descent_rules_list where
  "rz_descent_rules_list down block flat patterns =
    concat (map (\<lambda>s. map (rz_descent_rule down block flat s)
      [0..<length (args s)]) patterns)"

definition rz_ascent_rules_list where
  "rz_ascent_rules_list up block flat F =
    concat (map (\<lambda>fn. map (rz_ascent_rule up block flat fn)
      [0..<snd fn]) F)"

definition rz_transformed_rules_list where
  "rz_transformed_rules_list top_sym up down block flat reset_var F R patterns =
    map (rz_source_rule down up) R @
    [rz_reset_rule top_sym up down reset_var] @
    rz_descent_rules_list down block flat patterns @
    rz_ascent_rules_list up block flat F"

lemma rz_rule_instance_rstep:
  assumes "(l,r) \<in> R"
  shows "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rstep R"
proof -
  have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rrstep R"
    using assms unfolding rrstep_def' by blast
  then show ?thesis unfolding rstep_iff_rrstep_or_nrrstep by auto
qed

lemma rz_source_rule_instance:
  assumes "rz_source_rule down up lr \<in> R1"
  shows "(rz_wrap down (fst lr \<cdot> \<sigma>),
      rz_wrap up (snd lr \<cdot> \<sigma>)) \<in> rstep R1"
proof -
  have rule: "(rz_wrap down (fst lr), rz_wrap up (snd lr)) \<in> R1"
    using assms unfolding rz_source_rule_def by simp
  from rz_rule_instance_rstep[OF rule, of \<sigma>]
  show ?thesis by simp
qed

lemma rz_reset_rule_instance:
  fixes R1 :: "('f,string) trs"
  assumes "rz_reset_rule top_sym up down x \<in> R1"
  shows "(rz_wrap top_sym (rz_wrap up u),
      rz_wrap top_sym (rz_wrap down u)) \<in> rstep R1"
proof -
  let ?\<sigma> = "\<lambda>y. if y = x then u else Var y"
  have rule: "(rz_wrap top_sym (rz_wrap up (Var x)),
      rz_wrap top_sym (rz_wrap down (Var x))) \<in> R1"
    using assms unfolding rz_reset_rule_def by simp
  from rz_rule_instance_rstep[OF rule, of ?\<sigma>]
  show ?thesis unfolding rz_reset_rule_def by simp
qed

lemma rz_vars_length[simp]: "length (rz_vars n) = n"
  unfolding rz_vars_def by simp

lemma rz_ascent_rule_instance:
  fixes R1 :: "('f,string) trs"
  assumes rule: "rz_ascent_rule up block flat (f,n) i \<in> R1"
    and i: "i < n"
    and len: "length ts = n"
  shows "(Fun (flat (f,n))
      ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
    rz_wrap up (Fun f ts)) \<in> rstep R1"
proof -
  let ?vs = "x\<^sub>1_to_x\<^sub>n n"
  let ?xs = "map Var ?vs"
  let ?\<sigma> = "subst_extend Var (zip ?vs ts)"
  have fresh: "length ?vs = n" "distinct ?vs" by simp_all
  have inst: "map (\<lambda>t. t \<cdot> ?\<sigma>) ?xs = ts"
    using subst_extend_absorb[OF fresh(2), of ts Var] fresh(1) len by simp
  have rule': "(Fun (flat (f,n))
      ((rz_blocked_args block ?xs)[i := rz_wrap up (?xs ! i)]),
      rz_wrap up (Fun f ?xs)) \<in> R1"
    using rule i unfolding rz_ascent_rule_def rz_vars_def Let_def by simp
  have blocked_inst:
      "map ((\<lambda>s. s \<cdot> ?\<sigma>) \<circ> rz_wrap block) ?xs =
        rz_blocked_args block ts"
    using arg_cong[OF inst, of "map (rz_wrap block)"]
    unfolding rz_blocked_args_def by (simp add: o_def)
  have active_inst: "?xs ! i \<cdot> ?\<sigma> = ts ! i"
    using arg_cong[OF inst, of "\<lambda>xs. xs ! i"] i len by simp
  from rz_rule_instance_rstep[OF rule', of ?\<sigma>]
  show ?thesis
    using inst blocked_inst active_inst i len
    unfolding rz_blocked_args_def by (simp add: map_update o_def)
qed

lemma rz_cover_generated_descent:
  fixes S Q :: "('f,'v) terms"
    and R1 :: "('f,'v) trs"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
  assumes cover: "\<And>t :: ('f,'v) term. ground t \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. t = l \<cdot> \<sigma>)) \<Longrightarrow>
      \<exists>s\<in>S. \<exists>\<tau>. s \<cdot> \<tau> = t"
    and source_sig: "funas_term (Fun f ts) \<subseteq> F"
    and patterns: "\<And>s. s \<in> S \<Longrightarrow> is_Fun s"
    and generated: "\<And>s i. s \<in> S \<Longrightarrow> i < length (args s) \<Longrightarrow>
      rz_descent_rule down block flat s i \<in> R1"
    and ground: "ground (Fun f ts)"
    and i: "i < length ts"
    and nonredex: "\<And>l. l \<in> Q \<Longrightarrow>
      \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)"
  shows "(rz_wrap down (Fun f ts),
      Fun (flat (f,length ts))
        ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep R1"
proof -
  have covered: "\<exists>s\<in>S. \<exists>\<tau>. s \<cdot> \<tau> = Fun f ts"
  proof (rule cover[where t = "Fun f ts", OF ground source_sig])
    fix l
    assume "l \<in> Q"
    then show "\<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)"
      by (rule nonredex)
  qed
  from covered obtain s \<tau> where s: "s \<in> S"
    and inst: "s \<cdot> \<tau> = Fun f ts" by blast
  from patterns[OF s] obtain g ss where shape: "s = Fun g ss"
    by (cases s, auto)
  from inst[unfolded shape]
  have gf: "g = f" and len: "length ss = length ts"
    and args_inst: "map (\<lambda>t. t \<cdot> \<tau>) ss = ts"
    by auto
  have ii: "i < length ss" using i len by simp
  have rule: "rz_descent_rule down block flat s i \<in> R1"
    by (rule generated[OF s], unfold shape, simp add: ii)
  have rule': "(rz_wrap down (Fun g ss),
      Fun (flat (g,length ss))
        ((rz_blocked_args block ss)[i := rz_wrap down (ss ! i)])) \<in> R1"
    using rule unfolding shape by simp
  have blocked_inst:
      "map ((\<lambda>s. s \<cdot> \<tau>) \<circ> rz_wrap block) ss =
        map (rz_wrap block) ts"
    using arg_cong[OF args_inst, of "map (rz_wrap block)"]
    by (simp add: o_def)
  have active_inst: "ss ! i \<cdot> \<tau> = ts ! i"
    using arg_cong[OF args_inst, of "\<lambda>xs. xs ! i"] ii i len by simp
  from rz_rule_instance_rstep[OF rule', of \<tau>]
  show ?thesis
    unfolding shape rz_blocked_args_def
    using gf len args_inst blocked_inst active_inst i ii
    by (simp add: map_update o_def)
qed

theorem rz_transformed_rules_list_sound:
  fixes R T :: "('f,string) rules"
    and F0 F1 :: "('f \<times> nat) list"
    and patterns :: "('f,string) term list"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
  defines "Q \<equiv> fst ` set R"
  assumes quasi: "quasi_left_linear_lhss Q"
    and signature: "set F1 = insert (c,0) (set F0)"
    and fresh: "(c,0) \<notin> funas_trs (set R)"
    and pattern_fun: "\<And>s. s \<in> set patterns \<Longrightarrow> is_Fun s"
    and cover: "\<And>t :: ('f,string) term. ground t \<Longrightarrow>
      funas_term t \<subseteq> set F1 \<Longrightarrow>
      (\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. t = l \<cdot> \<sigma>)) \<Longrightarrow>
      \<exists>s\<in>set patterns. \<exists>\<tau>. s \<cdot> \<tau> = t"
    and transformed: "set (rz_transformed_rules_list top_sym up down block flat
      reset_var F1 R patterns) \<subseteq> set T"
    and transformed_SN: "SN (rstep (set T))"
  shows "SN (sig_step (set F0) (ostep Q (set R)))"
proof (rule rz_abstract_transformation_sound_sig[
    OF transformed_SN quasi _ _ _ _ _ _])
  fix l
  assume l: "l \<in> Q"
  from l obtain r where lr: "(l,r) \<in> set R" unfolding Q_def by auto
  from fresh lr show "(c,0) \<notin> funas_term l"
    unfolding funas_trs_def funas_rule_def by auto
next
  show "set F0 \<subseteq> set F1" using signature by auto
next
  show "(c,0) \<in> set F1" using signature by auto
next
  fix lr \<sigma>
  assume lr: "lr \<in> set R"
  have generated: "rz_source_rule down up lr \<in>
      set (rz_transformed_rules_list top_sym up down block flat
        reset_var F1 R patterns)"
    using lr unfolding rz_transformed_rules_list_def by auto
  from subsetD[OF transformed generated]
  show "(rz_wrap down (fst lr \<cdot> \<sigma>), rz_wrap up (snd lr \<cdot> \<sigma>))
      \<in> rstep (set T)"
    by (rule rz_source_rule_instance)
next
  fix f and ts :: "('f,string) term list" and i
  assume g: "ground (Fun f ts)" and fs: "funas_term (Fun f ts) \<subseteq> set F1"
    and i: "i < length ts"
    and nr: "\<And>l. l \<in> Q \<Longrightarrow> \<not> (\<exists>\<sigma>. Fun f ts = l \<cdot> \<sigma>)"
  show "(rz_wrap down (Fun f ts),
      Fun (flat (f, length ts))
       ((rz_blocked_args block ts)[i := rz_wrap down (ts ! i)])) \<in> rstep (set T)"
  proof (rule rz_cover_generated_descent[
      OF cover fs pattern_fun _ g i nr])
    fix s j
    assume s: "s \<in> set patterns" and j: "j < length (args s)"
    have descent_mem: "rz_descent_rule down block flat s j \<in>
        set (rz_descent_rules_list down block flat patterns)"
      using s j unfolding rz_descent_rules_list_def by force
    have generated: "rz_descent_rule down block flat s j \<in>
        set (rz_transformed_rules_list top_sym up down block flat
          reset_var F1 R patterns)"
      using descent_mem unfolding rz_transformed_rules_list_def by auto
    show "rz_descent_rule down block flat s j \<in> set T"
      by (rule subsetD[OF transformed generated])
  qed
next
  fix f and ts :: "('f,string) term list" and i
  assume fs: "funas_term (Fun f ts) \<subseteq> set F1"
    and i: "i < length ts"
  have fn: "(f,length ts) \<in> set F1" using fs by simp
  have ascent_mem: "rz_ascent_rule up block flat (f,length ts) i \<in>
      set (rz_ascent_rules_list up block flat F1)"
    using fn i unfolding rz_ascent_rules_list_def by force
  have generated: "rz_ascent_rule up block flat (f,length ts) i \<in>
      set (rz_transformed_rules_list top_sym up down block flat
        reset_var F1 R patterns)"
    using ascent_mem unfolding rz_transformed_rules_list_def by auto
  from rz_ascent_rule_instance[OF subsetD[OF transformed generated] i refl]
  show "(Fun (flat (f, length ts))
      ((rz_blocked_args block ts)[i := rz_wrap up (ts ! i)]),
    rz_wrap up (Fun f ts)) \<in> rstep (set T)" .
next
  fix u :: "('f,string) term"
  have generated: "rz_reset_rule top_sym up down reset_var \<in>
      set (rz_transformed_rules_list top_sym up down block flat
        reset_var F1 R patterns)"
    unfolding rz_transformed_rules_list_def by simp
  from rz_reset_rule_instance[OF subsetD[OF transformed generated], of u]
  show "(rz_wrap top_sym (rz_wrap up u), rz_wrap top_sym (rz_wrap down u))
      \<in> rstep (set T)" .
qed

theorem rz_ta_transformed_rules_list_sound:
  fixes R T :: "('f,string) rules"
    and F0 F1 :: "('f \<times> nat) list"
    and patterns :: "('f,string) term list"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and cover_var :: string
  defines "Q \<equiv> fst ` set R"
    and "basis \<equiv> rz_linear_lhss R"
  assumes quasi: "quasi_left_linear_lhss Q"
    and source_sig: "funas_trs (set R) \<subseteq> set F0"
    and signature: "set F1 = insert (c,0) (set F0)"
    and fresh: "(c,0) \<notin> funas_trs (set R)"
    and marker: "(d,0) \<notin> set F1"
    and pattern_fun: "\<And>s. s \<in> set patterns \<Longrightarrow> is_Fun s"
    and pattern_linear: "\<And>s. s \<in> set patterns \<Longrightarrow> linear_term s"
    and pattern_sig: "\<And>s. s \<in> set patterns \<Longrightarrow> funas_term s \<subseteq> set F1"
    and containment: "(lang (rz_pattern_ta (set F1) d (0::nat) (Var cover_var)) ::
        ('f,string) terms) \<subseteq>
      lang (rz_patterns_ta (set F1) d (basis @ patterns))"
    and transformed: "set (rz_transformed_rules_list top_sym up down block flat
      reset_var F1 R patterns) \<subseteq> set T"
    and transformed_SN: "SN (rstep (set T))"
  shows "SN (sig_step (set F0) (ostep Q (set R)))"
proof -
  have c_in: "(c,0) \<in> set F1" using signature by auto
  have finite: "finite (set F1)" by simp
  have source_sig1: "funas_trs (set R) \<subseteq> set F1"
    using source_sig signature by auto
  have cover: "\<And>t :: ('f,string) term. ground t \<Longrightarrow>
      funas_term t \<subseteq> set F1 \<Longrightarrow>
      (\<And>l. l \<in> fst ` set R \<Longrightarrow> \<not> (\<exists>\<sigma>. t = l \<cdot> \<sigma>)) \<Longrightarrow>
      \<exists>s\<in>set patterns. \<exists>\<tau>. s \<cdot> \<tau> = t"
  proof -
    fix t :: "('f,string) term"
    assume g: "ground t" and tsig: "funas_term t \<subseteq> set F1"
      and nr: "\<And>l. l \<in> fst ` set R \<Longrightarrow>
        \<not> (\<exists>\<sigma>. t = l \<cdot> \<sigma>)"
    show "\<exists>s\<in>set patterns. \<exists>\<tau>. s \<cdot> \<tau> = t"
      apply (rule rz_ta_nonredex_cover[
        where F="set F1" and R=R and patterns=patterns and a=c and d=d
          and x=cover_var and s=t])
      subgoal by (rule c_in)
      subgoal by (rule marker)
      subgoal by (rule finite)
      subgoal by (rule source_sig1)
      subgoal by (rule pattern_linear)
      subgoal by (rule pattern_sig)
      subgoal
        apply (rule lang_containment_variable_type[
          where A="rz_pattern_ta (set F1) d (0::nat) (Var cover_var)"
            and B="rz_patterns_ta (set F1) d (rz_linear_lhss R @ patterns)"
            and anchor=cover_var and output_anchor=cover_var, OF refl refl])
        using containment unfolding basis_def by assumption
      subgoal by (rule g)
      subgoal by (rule tsig)
      subgoal by (rule nr)
      done
  qed
  show ?thesis
    unfolding Q_def
    by (rule rz_transformed_rules_list_sound[
      OF quasi[unfolded Q_def] signature fresh pattern_fun cover
        transformed transformed_SN])
qed

theorem rz_cover_check_transformed_rules_list_sound:
  fixes R T :: "('f::compare_order,string) rules"
    and F0 F1 :: "('f \<times> nat) list"
    and patterns :: "('f,string) term list"
    and flat :: "'f \<times> nat \<Rightarrow> 'f"
    and cover_var :: string
  assumes quasi: "quasi_left_linear_lhss (fst ` set R)"
    and source_sig: "funas_trs (set R) \<subseteq> set F0"
    and signature: "set F1 = insert (c,0) (set F0)"
    and fresh: "(c,0) \<notin> funas_trs (set R)"
    and marker: "(d,0) \<notin> set F1"
    and pattern_fun: "\<And>s. s \<in> set patterns \<Longrightarrow> is_Fun s"
    and pattern_linear: "\<And>s. s \<in> set patterns \<Longrightarrow> linear_term s"
    and pattern_sig: "\<And>s. s \<in> set patterns \<Longrightarrow>
      funas_term s \<subseteq> set F1"
    and cover_check: "rz_cover_check F1 d cover_var
      (rz_linear_lhss R @ patterns)"
    and transformed: "set (rz_transformed_rules_list top_sym up down block flat
      reset_var F1 R patterns) \<subseteq> set T"
    and transformed_SN: "SN (rstep (set T))"
  shows "SN (sig_step (set F0) (ostep (fst ` set R) (set R)))"
proof -
  have containment: "(lang (rz_pattern_ta (set F1) d (0::nat)
      (Var cover_var)) :: ('f,string) terms) \<subseteq>
      lang (rz_patterns_ta (set F1) d (rz_linear_lhss R @ patterns))"
    by (rule rz_cover_check_sound[OF cover_check])
  show ?thesis
    by (rule rz_ta_transformed_rules_list_sound)
       (use quasi source_sig signature fresh marker pattern_fun pattern_linear
          pattern_sig containment transformed transformed_SN in auto)
qed

lemma rz_cover_check_single_constant_test:
  "rz_cover_check [((0::nat),0)] 1 (0::nat) [Fun 0 []]"
  by eval

lemma rz_cover_check_rejects_empty_cover_test:
  "\<not> rz_cover_check [((0::nat),0)] 1 (0::nat) []"
  by eval

lemma rz_cover_check_rejects_wrong_arity_test:
  "\<not> rz_cover_check [((0::nat),0)] 1 (0::nat) [Fun 0 [Var 0]]"
  by eval

end
