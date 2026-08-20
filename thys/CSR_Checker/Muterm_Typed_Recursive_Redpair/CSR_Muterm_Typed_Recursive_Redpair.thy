(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Typed_Recursive_Redpair
  imports CSR_Muterm_Typed_General_Redpair.CSR_Muterm_Typed_General_Redpair
begin

text \<open>
  The ordinary reduction-pair lifting theorem treats every dependency-pair
  event in isolation.  That is too early for typed MU-TERM chains: a call
  hidden in the right-hand side of one event can be certified nonterminating
  by the exact unhiding bridge of the following event.  The following
  look-ahead variant therefore orients a complete block from one pair source
  to the next pair source.  Its residual premise still removes the current
  pair, so it proves the usual reduction-pair processor rather than a
  two-pair processor.
\<close>

lemma SN_rel_interpreted_redpair_lookahead:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and target_SN: "\<And>s t. (s,t) \<in> B \<Longrightarrow> SN_on A {t}"
    and block_order: "\<And>s t s' t'.
      SN_on A {s'} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (t,s') \<in> A\<^sup>* \<Longrightarrow> (s',t') \<in> B \<Longrightarrow>
      (I s,I s') \<in> Rgt \<union> Rge"
    and block_residual: "\<And>s t s' t'.
      SN_on A {s'} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (t,s') \<in> A\<^sup>* \<Longrightarrow> (s',t') \<in> B \<Longrightarrow>
      (I s,I s') \<notin> Rgt \<Longrightarrow> (s,t) \<in> C"
    and fin: "SN_rel C A"
  shows "SN_rel B A"
proof (rule ccontr)
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?PB = "A\<^sup>* O B O A\<^sup>*"
  let ?PC = "A\<^sup>* O C O A\<^sup>*"
  assume not_fin: "\<not> SN_rel B A"
  then obtain f where chain: "chain ?PB f"
    unfolding SN_rel_on_def SN_defs by auto
  have ex_mid: "\<forall>i. \<exists>a b. (f i,a) \<in> A\<^sup>* \<and>
      (a,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*"
  proof
    fix i
    from chain[rule_format, of i] obtain a b where
      pre: "(f i,a) \<in> A\<^sup>*" and pair: "(a,b) \<in> B"
      and post: "(b,f (Suc i)) \<in> A\<^sup>*" by auto
    show "\<exists>a b. (f i,a) \<in> A\<^sup>* \<and> (a,b) \<in> B \<and>
      (b,f (Suc i)) \<in> A\<^sup>*" using pre pair post by auto
  qed
  from choice[OF ex_mid] obtain a where choose_a:
      "\<forall>i. \<exists>b. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*" by auto
  from choice[OF choose_a] obtain b where chosen:
      "\<forall>i. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b i) \<in> B \<and> (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  from chosen have pre: "\<And>i. (f i,a i) \<in> A\<^sup>*"
    and pair: "\<And>i. (a i,b i) \<in> B"
    and post: "\<And>i. (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  have between: "(b i,a (Suc i)) \<in> A\<^sup>*" for i
    by (rule rtrancl_trans[OF post[of i] pre[of "Suc i"]])
  have b_sn: "SN_on A {b i}" for i by (rule target_SN[OF pair])
  have a_sn: "SN_on A {a (Suc i)}" for i
  proof (rule ccontr)
    assume not_sn: "\<not> SN_on A {a (Suc i)}"
    from steps_notSN_on_source[OF between[of i] not_sn]
      b_sn[of i] show False by contradiction
  qed
  let ?x = "\<lambda>i. I (a i)"
  have xstep: "(?x i,?x (Suc i)) \<in> Rge \<union> Rgt" for i
    using block_order[OF a_sn pair between pair] by blast
  have xchain: "chain (Rge \<union> Rgt) ?x" using xstep by simp
  have sn0: "SN_on Rgt {?x 0}" using rp.SN unfolding SN_on_def by auto
  from non_strict_ending[OF xchain rp.compat_NS_S sn0]
  obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?x k,?x (Suc k)) \<in> Rge - Rgt" by auto
  have tail_pair: "(a (k+j),b (k+j)) \<in> C" for k
  proof -
    have not_strict: "(I (a (k+j)),I (a (Suc (k+j)))) \<notin> Rgt"
      using tail[of "k+j"] by auto
    show ?thesis by (rule block_residual[
      OF a_sn pair between pair not_strict])
  qed
  let ?h = "shift f j"
  have residual_chain: "chain ?PC ?h"
  proof
    fix k
    have member: "(f (k+j),f (Suc (k+j))) \<in> ?PC"
      using pre[of "k+j"] tail_pair[of k] post[of "k+j"] by auto
    show "(?h k,?h (Suc k)) \<in> ?PC" using member by simp
  qed
  from fin have "SN_on ?PC UNIV" unfolding SN_rel_on_def .
  moreover have "\<not> SN_on ?PC UNIV"
    by (rule not_SN_onI[OF _ residual_chain], simp)
  ultimately show False by contradiction
qed

lemma SN_rel_source_invariant:
  assumes target_good: "\<And>s t. (s,t) \<in> B \<Longrightarrow> G t"
    and steps_good: "\<And>s t. G s \<Longrightarrow> (s,t) \<in> A\<^sup>* \<Longrightarrow> G t"
    and fin: "SN_rel {(s,t). (s,t) \<in> B \<and> G s} A"
  shows "SN_rel B A"
proof (rule ccontr)
  let ?PB = "A\<^sup>* O B O A\<^sup>*"
  let ?BG = "{(s,t). (s,t) \<in> B \<and> G s}"
  let ?PG = "A\<^sup>* O ?BG O A\<^sup>*"
  assume not_fin: "\<not> SN_rel B A"
  then obtain f where chain: "chain ?PB f"
    unfolding SN_rel_on_def SN_defs by auto
  have ex_mid: "\<forall>i. \<exists>a b. (f i,a) \<in> A\<^sup>* \<and>
      (a,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*"
  proof
    fix i
    from chain[rule_format, of i] show "\<exists>a b. (f i,a) \<in> A\<^sup>* \<and>
        (a,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*" by auto
  qed
  from choice[OF ex_mid] obtain a where choose_a:
      "\<forall>i. \<exists>b. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b) \<in> B \<and> (b,f (Suc i)) \<in> A\<^sup>*" by auto
  from choice[OF choose_a] obtain b where chosen:
      "\<forall>i. (f i,a i) \<in> A\<^sup>* \<and>
        (a i,b i) \<in> B \<and> (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  from chosen have pre: "\<And>i. (f i,a i) \<in> A\<^sup>*"
    and pair: "\<And>i. (a i,b i) \<in> B"
    and post: "\<And>i. (b i,f (Suc i)) \<in> A\<^sup>*" by auto
  have good_f: "G (f (Suc i))" for i
    by (rule steps_good[OF target_good[OF pair] post])
  have good_a: "G (a (Suc i))" for i
    by (rule steps_good[OF good_f pre])
  let ?h = "shift f 1"
  have good_chain: "chain ?PG ?h"
  proof
    fix i
    have member: "(f (Suc i),f (Suc (Suc i))) \<in> ?PG"
      using pre[of "Suc i"] pair[of "Suc i"] post[of "Suc i"]
        good_a[of i] by auto
    show "(?h i,?h (Suc i)) \<in> ?PG" using member by simp
  qed
  from fin have "SN_on ?PG UNIV" unfolding SN_rel_on_def .
  moreover have "\<not> SN_on ?PG UNIV"
    by (rule not_SN_onI[OF _ good_chain], simp)
  ultimately show False by contradiction
qed

lemma SN_rel_interpreted_redpair_lookahead_invariant:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and target_SN: "\<And>s t. (s,t) \<in> B \<Longrightarrow> SN_on A {t}"
    and target_good: "\<And>s t. (s,t) \<in> B \<Longrightarrow> G t"
    and steps_good: "\<And>s t. G s \<Longrightarrow> (s,t) \<in> A\<^sup>* \<Longrightarrow> G t"
    and block_order: "\<And>s t s' t'.
      G s \<Longrightarrow> SN_on A {s'} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (t,s') \<in> A\<^sup>* \<Longrightarrow> (s',t') \<in> B \<Longrightarrow>
      (I s,I s') \<in> Rgt \<union> Rge"
    and block_residual: "\<And>s t s' t'.
      G s \<Longrightarrow> SN_on A {s'} \<Longrightarrow> (s,t) \<in> B \<Longrightarrow>
      (t,s') \<in> A\<^sup>* \<Longrightarrow> (s',t') \<in> B \<Longrightarrow>
      (I s,I s') \<notin> Rgt \<Longrightarrow> (s,t) \<in> C"
    and fin: "SN_rel C A"
  shows "SN_rel B A"
proof -
  let ?BG = "{(s,t). (s,t) \<in> B \<and> G s}"
  have fin_good: "SN_rel ?BG A"
  proof (rule SN_rel_interpreted_redpair_lookahead[
      OF redpair _ _ _ fin, where I=I])
    fix s t
    assume event: "(s,t) \<in> ?BG"
    from event have event': "(s,t) \<in> B" by auto
    show "SN_on A {t}" by (rule target_SN[OF event'])
  next
    fix s t s' t'
    assume sn: "SN_on A {s'}" and event: "(s,t) \<in> ?BG"
      and steps: "(t,s') \<in> A\<^sup>*" and next_event: "(s',t') \<in> ?BG"
    from event have good: "G s" and event': "(s,t) \<in> B" by auto
    from next_event have next': "(s',t') \<in> B" by auto
    show "(I s,I s') \<in> Rgt \<union> Rge"
      by (rule block_order[OF good sn event' steps next'])
  next
    fix s t s' t'
    assume sn: "SN_on A {s'}" and event: "(s,t) \<in> ?BG"
      and steps: "(t,s') \<in> A\<^sup>*" and next_event: "(s',t') \<in> ?BG"
      and nonstrict: "(I s,I s') \<notin> Rgt"
    from event have good: "G s" and event': "(s,t) \<in> B" by auto
    from next_event have next': "(s',t') \<in> B" by auto
    show "(s,t) \<in> C"
      by (rule block_residual[OF good sn event' steps next' nonstrict])
  qed
  show ?thesis by (rule SN_rel_source_invariant[
    OF target_good steps_good fin_good])
qed

text \<open>
  A marked MU-TERM call is a description of a selected call, rather than a
  symbol rewritten by the source TRS.  In particular, all of its arguments
  belong to the description.  This interpretation therefore descends through
  every argument of a marked call.  Below unmarked symbols it retains the
  already proved arbitrary-term interpretation: terminating calls use the
  RTA'08 list interpretation, while nonterminating calls preserve their root
  and interpret active arguments recursively.

  The extra marked descent is the invariant needed when a collapsing pair
  selects a variable from an inactive argument and an exact unhiding rule
  exposes a call below it.  It does not enable rewriting below inactive source
  positions; it only gives the pair and its bridge one common interpreted
  substitution.
\<close>

locale muterm_i4 =
  fixes Rs :: "((('f::{showl,compare_order},'l::{showl,compare_order}) lab),string) rules"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "((('f,'l) lab) \<times> nat) set"
    and cn :: "(('f,'l) lab) \<times> nat"
  assumes wf: "wf_trs (set Rs)"
begin

interpretation base: muterm_i3 Rs \<mu> \<Delta> cn
  by (unfold_locales, rule wf)

interpretation old4: muterm_i2 Rs \<mu> \<Delta> cn
  by (unfold_locales, rule wf)

function i4 :: "((('f,'l) lab),string) term \<Rightarrow> ((('f,'l) lab),string) term"
where
  "i4 (Var x) = Var x"
| "i4 (Fun f ts) =
    (if is_sharp_lab f then Fun f (map i4 ts)
     else if SN_on (csstep \<mu> (set Rs)) {Fun f ts}
     then base.i3 (Fun f ts)
     else Fun f (map (\<lambda>(i,t).
       if i \<in> \<mu> (f,length ts) then i4 t else t)
       (zip [0..<length ts] ts)))"
  by pat_completeness auto

termination
  by (relation "measure size", auto simp: set_zip intro: size_simp1)

lemma i4_Var [simp]: "i4 (Var x) = Var x"
  by simp

lemma i4_Sharp [simp]:
  "i4 (Fun (Sharp f) ts) = Fun (Sharp f) (map i4 ts)"
  by simp

lemma i4_Sharp_nth:
  assumes i: "i < length ts"
  shows "args (i4 (Fun (Sharp f) ts)) ! i = i4 (ts ! i)"
  using i by simp

lemma i4_unmarked_SN:
  assumes unmarked: "\<not> is_sharp_lab f"
    and SN: "SN_on (csstep \<mu> (set Rs)) {Fun f ts}"
  shows "i4 (Fun f ts) = base.i3 (Fun f ts)"
  using unmarked SN by simp

lemma i4_unmarked_not_SN:
  assumes unmarked: "\<not> is_sharp_lab f"
    and not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts}"
  shows "i4 (Fun f ts) = Fun f (map (\<lambda>(i,t).
    if i \<in> \<mu> (f,length ts) then i4 t else t)
    (zip [0..<length ts] ts))"
  using unmarked not_SN by simp

definition unmarked_term where
  "unmarked_term t \<longleftrightarrow>
    (\<forall>fn\<in>funas_term t. \<not> is_sharp_lab (fst fn))"

lemma unmarked_term_Var [simp]: "unmarked_term (Var x)"
  unfolding unmarked_term_def by simp

lemma unmarked_term_Fun:
  "unmarked_term (Fun f ts) \<longleftrightarrow>
    \<not> is_sharp_lab f \<and> (\<forall>t\<in>set ts. unmarked_term t)"
  unfolding unmarked_term_def by auto

text \<open>
  The recursive interpretation is deliberately a conservative extension of
  the already verified arbitrary-term interpretation: it differs only at a
  marked root.  This fact is also the boundary needed later to reuse the
  existing simulation of source rewriting below every unmarked argument.
\<close>

lemma i4_eq_i3_if_unmarked:
  assumes "unmarked_term t"
  shows "i4 t = base.i3 t"
  using assms
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems have root: "\<not> is_sharp_lab f"
    and children: "\<forall>t\<in>set ts. unmarked_term t"
    unfolding unmarked_term_Fun by auto
  show ?case
  proof (cases "SN_on (csstep \<mu> (set Rs)) {Fun f ts}")
    case True
    then show ?thesis using root by simp
  next
    case False
    have child_eq: "\<And>t. t \<in> set ts \<Longrightarrow> i4 t = base.i3 t"
      by (rule Fun.hyps, use children in auto)
    have args_eq:
      "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts) then i4 t else t)
          (zip [0..<length ts] ts) =
       map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts) then base.i3 t else t)
          (zip [0..<length ts] ts)"
    proof (rule map_cong)
      show "zip [0..<length ts] ts = zip [0..<length ts] ts" by simp
      fix z
      assume z: "z \<in> set (zip [0..<length ts] ts)"
      obtain i t where z_def: "z = (i,t)" by (cases z)
      have pair: "(i,t) \<in> set (zip [0..<length ts] ts)"
        using z unfolding z_def .
      from pair obtain j where j:
          "j < length (zip [0..<length ts] ts)"
        and at: "zip [0..<length ts] ts ! j = (i,t)"
        unfolding in_set_conv_nth by blast
      have jts: "j < length ts" using j by simp
      have t_eq: "t = ts ! j" using at jts by (auto simp add: nth_zip)
      have t: "t \<in> set ts" unfolding t_eq by (rule nth_mem[OF jts])
      show "(case z of (i,t) \<Rightarrow>
          if i \<in> \<mu> (f,length ts) then i4 t else t) =
        (case z of (i,t) \<Rightarrow>
          if i \<in> \<mu> (f,length ts) then base.i3 t else t)"
        unfolding z_def using child_eq[OF t] by simp
    qed
    show ?thesis using root False args_eq
      by (simp add: base.i3_Fun base.i3_args_def)
  qed
qed

lemma i4_Sharp_subst:
  "i4 (Fun (Sharp f) ts \<cdot> \<sigma>) =
    Fun (Sharp f) (map (\<lambda>t. i4 (t \<cdot> \<sigma>)) ts)"
  by simp

definition i4_mu where
  "i4_mu fn = (if is_sharp_lab (fst fn) then {0..<snd fn} else \<mu> fn)"

lemma i4_mu_Sharp [simp]:
  "i4_mu (Sharp f,n) = {0..<n}"
  unfolding i4_mu_def by simp

lemma i4_mu_unmarked:
  assumes "\<not> is_sharp_lab f"
  shows "i4_mu (f,n) = \<mu> (f,n)"
  using assms unfolding i4_mu_def by simp

definition i4_subst where
  "i4_subst t \<sigma> x =
    (if x \<in> mu_vars_term i4_mu t then i4 (\<sigma> x) else \<sigma> x)"

fun i4_bracket ::
  "((('f,'l) lab),string) term \<Rightarrow>
   ((('f,'l) lab),string) subst \<Rightarrow> ((('f,'l) lab),string) term"
where
  "i4_bracket (Var x) \<sigma> = i4 (\<sigma> x)"
| "i4_bracket (Fun f ts) \<sigma> = Fun f
    (map (\<lambda>(i,t). if i \<in> i4_mu (f,length ts)
          then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"

lemma i4_bracket_Fun_nth:
  assumes i: "i < length ts"
  shows "args (i4_bracket (Fun f ts) \<sigma>) ! i =
    (if i \<in> i4_mu (f,length ts) then i4_bracket (ts ! i) \<sigma>
     else (ts ! i) \<cdot> \<sigma>)"
  using i by (simp add: nth_zip)

lemma i4_bracket_Sharp [simp]:
  "i4_bracket (Fun (Sharp f) ts) \<sigma> =
    Fun (Sharp f) (map (\<lambda>t. i4_bracket t \<sigma>) ts)"
proof -
  have indices: "map (\<lambda>(i,t). if i \<in> {0..<length ts}
        then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts) = map (\<lambda>t. i4_bracket t \<sigma>) ts"
    by (rule nth_equalityI, auto simp: nth_zip)
  show ?thesis using indices by simp
qed

text \<open>
  Variables below a marked call are description variables and are therefore
  all interpreted.  Below an unmarked source symbol, activity remains exactly
  the original replacement map.  The usual active/inactive disjointness
  condition then gives one substitution for the whole bracket.
\<close>

lemma i4_bracket_as_subst:
  assumes disj: "mu_vars_term i4_mu t \<inter>
      non_mu_vars_term i4_mu t = {}"
  shows "i4_bracket t \<sigma> = t \<cdot> i4_subst t \<sigma>"
  using disj
proof (induct t)
  case (Var x)
  then show ?case unfolding i4_subst_def mu_vars_term_def by simp
next
  case (Fun f ts)
  have lists: "map (\<lambda>(i,t). if i \<in> i4_mu (f,length ts)
          then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) =
      map (\<lambda>t. t \<cdot> i4_subst (Fun f ts) \<sigma>) ts"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(i,t). if i \<in> i4_mu (f,length ts)
          then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts)) =
        length (map (\<lambda>t. t \<cdot> i4_subst (Fun f ts) \<sigma>) ts)"
      by simp
    fix i
    assume imap: "i < length (map (\<lambda>(i,t).
      if i \<in> i4_mu (f,length ts) then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"
    then have i: "i < length ts" by simp
    show "map (\<lambda>(i,t). if i \<in> i4_mu (f,length ts)
        then i4_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) ! i =
      map (\<lambda>t. t \<cdot> i4_subst (Fun f ts) \<sigma>) ts ! i"
    proof (cases "i \<in> i4_mu (f,length ts)")
      case True
      have child_disj: "mu_vars_term i4_mu (ts ! i) \<inter>
          non_mu_vars_term i4_mu (ts ! i) = {}"
      proof (rule ccontr)
        assume "mu_vars_term i4_mu (ts ! i) \<inter>
            non_mu_vars_term i4_mu (ts ! i) \<noteq> {}"
        then obtain x where xa: "x \<in> mu_vars_term i4_mu (ts ! i)"
          and xn: "x \<in> non_mu_vars_term i4_mu (ts ! i)" by blast
        have "x \<in> mu_vars_term i4_mu (Fun f ts)"
          by (rule mu_vars_term_active_argI[OF i True xa])
        moreover have "x \<in> non_mu_vars_term i4_mu (Fun f ts)"
          by (rule non_mu_vars_term_active_argI[OF i True xn])
        ultimately show False using Fun.prems by blast
      qed
      have IH: "i4_bracket (ts ! i) \<sigma> =
          (ts ! i) \<cdot> i4_subst (ts ! i) \<sigma>"
        by (rule Fun.hyps[OF nth_mem[OF i] child_disj])
      have subst_eq: "(ts ! i) \<cdot> i4_subst (ts ! i) \<sigma> =
          (ts ! i) \<cdot> i4_subst (Fun f ts) \<sigma>"
      proof (rule term_subst_eq)
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        show "i4_subst (ts ! i) \<sigma> x =
            i4_subst (Fun f ts) \<sigma> x"
        proof (cases "x \<in> mu_vars_term i4_mu (ts ! i)")
          case True
          have parent: "x \<in> mu_vars_term i4_mu (Fun f ts)"
            by (rule mu_vars_term_active_argI[OF i
              `i \<in> i4_mu (f,length ts)` True])
          show ?thesis unfolding i4_subst_def using True parent by simp
        next
          case False
          from vars_term_active_or_inactive[OF x] False
          have child_inactive:
              "x \<in> non_mu_vars_term i4_mu (ts ! i)" by blast
          have parent_inactive:
              "x \<in> non_mu_vars_term i4_mu (Fun f ts)"
            by (rule non_mu_vars_term_active_argI[OF i
              `i \<in> i4_mu (f,length ts)` child_inactive])
          have parent_not_active:
              "x \<notin> mu_vars_term i4_mu (Fun f ts)"
            using Fun.prems parent_inactive by blast
          show ?thesis unfolding i4_subst_def
            using False parent_not_active by simp
        qed
      qed
      show ?thesis using i True IH subst_eq by (simp add: nth_zip)
    next
      case False
      have inactive: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
          x \<notin> mu_vars_term i4_mu (Fun f ts)"
      proof -
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        have parent_inactive:
            "x \<in> non_mu_vars_term i4_mu (Fun f ts)"
          by (rule non_mu_vars_term_inactive_argI[
            where \<mu>=i4_mu and f=f and ts=ts and i=i, OF i False x])
        show "x \<notin> mu_vars_term i4_mu (Fun f ts)"
          using Fun.prems parent_inactive by blast
      qed
      have subst_eq: "(ts ! i) \<cdot> \<sigma> =
          (ts ! i) \<cdot> i4_subst (Fun f ts) \<sigma>"
        by (rule term_subst_eq, simp add: i4_subst_def inactive)
      show ?thesis using i False subst_eq by (simp add: nth_zip)
    qed
  qed
  show ?case using lists by simp
qed

fun i4_safe ::
  "((('f,'l) lab),string) term \<Rightarrow> ((('f,'l) lab),string) subst \<Rightarrow> bool"
where
  "i4_safe (Var x) \<sigma> = unmarked_term (\<sigma> x)"
| "i4_safe (Fun f ts) \<sigma> =
    ((is_sharp_lab f \<or>
        (unmarked_term (Fun f ts \<cdot> \<sigma>) \<and>
         ((f,length ts) \<in> \<Delta> \<or>
          \<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts \<cdot> \<sigma>}))) \<and>
     (\<forall>i<length ts. i \<in> i4_mu (f,length ts) \<longrightarrow>
        i4_safe (ts ! i) \<sigma>))"

text \<open>
  An unmarked call may escape the usable-rule closure only when its concrete
  instance is nonterminating.  In that case @{const i4} preserves the call;
  otherwise membership in @{term \<Delta>} makes the existing RTA'08 list
  interpretation preserve its root.  Marked calls need no such premise and
  recurse through all arguments.
\<close>

lemma i4_equals_bracket:
  assumes safe: "i4_safe t \<sigma>"
  shows "i4 (t \<cdot> \<sigma>) = i4_bracket t \<sigma>"
  using safe
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
  have len [simp]: "length ?ss = length ts" by simp
  show ?case
  proof (cases "is_sharp_lab f")
    case True
    then obtain g where f: "f = Sharp g" by (cases f, auto)
    have child_safe: "\<And>i. i < length ts \<Longrightarrow>
        i4_safe (ts ! i) \<sigma>"
      using Fun.prems unfolding f by simp
    have children: "map (\<lambda>t. i4 (t \<cdot> \<sigma>)) ts =
        map (\<lambda>t. i4_bracket t \<sigma>) ts"
    proof (rule map_cong)
      show "ts = ts" by simp
      fix t
      assume t: "t \<in> set ts"
      from t obtain i where i: "i < length ts" and ti: "ts ! i = t"
        unfolding in_set_conv_nth by blast
      show "i4 (t \<cdot> \<sigma>) = i4_bracket t \<sigma>"
        unfolding ti[symmetric] by (rule Fun.hyps[OF nth_mem[OF i]
          child_safe[OF i]])
    qed
    have lhs: "i4 (Fun (Sharp g) ts \<cdot> \<sigma>) =
        Fun (Sharp g) (map (\<lambda>t. i4 (t \<cdot> \<sigma>)) ts)" by simp
    have rhs: "i4_bracket (Fun (Sharp g) ts) \<sigma> =
        Fun (Sharp g) (map (\<lambda>t. i4_bracket t \<sigma>) ts)"
      by (rule i4_bracket_Sharp)
    show ?thesis unfolding f lhs rhs using children by simp
  next
    case unmarked: False
    have mu_eq: "i4_mu (f,length ts) = \<mu> (f,length ts)"
      by (rule i4_mu_unmarked[OF unmarked])
    have instance_unmarked: "unmarked_term (Fun f ?ss)"
      using Fun.prems unmarked by simp
    show ?thesis
    proof (cases "SN_on (csstep \<mu> (set Rs)) {Fun f ?ss}")
      case not_SN: False
      have child_safe: "\<And>i. i < length ts \<Longrightarrow>
          i \<in> \<mu> (f,length ts) \<Longrightarrow>
          i4_safe (ts ! i) \<sigma>"
        using Fun.prems unfolding mu_eq[symmetric] by simp
      have args: "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
              then i4 t else t)
            (zip [0..<length ts] ?ss) =
          args (i4_bracket (Fun f ts) \<sigma>)"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
              then i4 t else t)
            (zip [0..<length ts] ?ss)) =
            length (args (i4_bracket (Fun f ts) \<sigma>))" by simp
        fix i
        assume il: "i < length (map (\<lambda>(i,t).
          if i \<in> \<mu> (f,length ts) then i4 t else t)
          (zip [0..<length ts] ?ss))"
        then have i: "i < length ts" by simp
        show "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
            then i4 t else t)
            (zip [0..<length ts] ?ss) ! i =
          args (i4_bracket (Fun f ts) \<sigma>) ! i"
        proof (cases "i \<in> \<mu> (f,length ts)")
          case True
          have IH: "i4 ((ts ! i) \<cdot> \<sigma>) =
              i4_bracket (ts ! i) \<sigma>"
            by (rule Fun.hyps[OF nth_mem[OF i] child_safe[OF i True]])
          show ?thesis using i True IH mu_eq
            by (simp add: nth_zip i4_bracket_Fun_nth)
        next
          case False
          show ?thesis using i False mu_eq
            by (simp add: nth_zip i4_bracket_Fun_nth)
        qed
      qed
      show ?thesis using unmarked not_SN args
        by (simp add: i4_unmarked_not_SN)
    next
      case SN: True
      have root_delta: "(f,length ts) \<in> \<Delta>"
        using Fun.prems unmarked SN by simp
      have child_safe: "\<And>i. i < length ts \<Longrightarrow>
          i \<in> \<mu> (f,length ts) \<Longrightarrow>
          i4_safe (ts ! i) \<sigma>"
        using Fun.prems unfolding mu_eq[symmetric] by simp
      have child_SN: "\<And>i. i < length ts \<Longrightarrow>
          i \<in> \<mu> (f,length ts) \<Longrightarrow>
          SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
      proof -
        fix i
        assume i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
        have empty: "[] \<in> mu_poss \<mu> ((ts ! i) \<cdot> \<sigma>)"
          by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
        have pos: "i # [] \<in> mu_poss \<mu> (Fun f ?ss)"
          using i active empty by auto
        from SN_on_mu_pos[OF wf pos SN]
        show "SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
          using i by simp
      qed
      have args_eq: "old4.i2_args f ?ss =
          args (i4_bracket (Fun f ts) \<sigma>)"
      proof (rule nth_equalityI)
        show "length (old4.i2_args f ?ss) =
            length (args (i4_bracket (Fun f ts) \<sigma>))" by simp
        fix i
        assume il: "i < length (old4.i2_args f ?ss)"
        then have i: "i < length ts" by simp
        show "old4.i2_args f ?ss ! i =
            args (i4_bracket (Fun f ts) \<sigma>) ! i"
        proof (cases "i \<in> \<mu> (f,length ts)")
          case True
          have IH: "i4 ((ts ! i) \<cdot> \<sigma>) =
              i4_bracket (ts ! i) \<sigma>"
            by (rule Fun.hyps[OF nth_mem[OF i] child_safe[OF i True]])
          have i4_i3: "i4 ((ts ! i) \<cdot> \<sigma>) =
              base.i3 ((ts ! i) \<cdot> \<sigma>)"
          proof (rule i4_eq_i3_if_unmarked)
            from instance_unmarked have children_unmarked:
                "\<forall>t\<in>set ?ss. unmarked_term t"
              unfolding unmarked_term_Fun by blast
            have "(ts ! i) \<cdot> \<sigma> \<in> set ?ss"
              using i by simp
            with children_unmarked show
              "unmarked_term ((ts ! i) \<cdot> \<sigma>)" by blast
          qed
          have i3_i2: "base.i3 ((ts ! i) \<cdot> \<sigma>) =
              old4.i2 ((ts ! i) \<cdot> \<sigma>)"
            by (rule base.i3_SN_eq_i2[OF child_SN[OF i True]])
          show ?thesis using i True IH i4_i3 i3_i2 mu_eq
            by (simp add: old4.i2_args_nth i4_bracket_Fun_nth)
        next
          case False
          show ?thesis using i False mu_eq
            by (simp add: old4.i2_args_nth i4_bracket_Fun_nth)
        qed
      qed
      have interpreted_root: "base.i3 (Fun f ?ss) =
          Fun f (old4.i2_args f ?ss)"
        using SN root_delta
        by (simp add: base.i3_Fun old4.i2_Fun old4.i2_args_def)
      show ?thesis using unmarked SN interpreted_root args_eq by simp
    qed
  qed
qed

lemma i4_subst_uniform_on_full_active:
  assumes full: "vars_term t \<subseteq> mu_vars_term i4_mu t"
  shows "t \<cdot> i4_subst t \<sigma> = t \<cdot> (\<lambda>x. i4 (\<sigma> x))"
proof (rule term_subst_eq)
  fix x
  assume x: "x \<in> vars_term t"
  with full have active: "x \<in> mu_vars_term i4_mu t" by blast
  show "i4_subst t \<sigma> x = i4 (\<sigma> x)"
    unfolding i4_subst_def using active by simp
qed

lemma i4_full_active_commutes:
  assumes safe: "i4_safe t \<sigma>"
    and partition: "mu_vars_term i4_mu t \<inter>
      non_mu_vars_term i4_mu t = {}"
    and full: "vars_term t \<subseteq> mu_vars_term i4_mu t"
  shows "i4 (t \<cdot> \<sigma>) = t \<cdot> (\<lambda>x. i4 (\<sigma> x))"
  using i4_equals_bracket[OF safe]
    i4_bracket_as_subst[OF partition]
    i4_subst_uniform_on_full_active[OF full] by simp

text \<open>
  The reduction-pair argument itself only needs a common interpreted
  substitution.  Keeping that fact separate is useful: the next lemmas can
  establish the common substitution from the checked exact-unhiding shape,
  without baking an unjustified activity condition into the order argument.
\<close>

lemma i4_noncollapsing_redpair_order_from_common_subst:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order: "(l,r) \<in> Rgt \<union> Rge"
    and source_i4: "i4 (l \<cdot> \<sigma>) = l \<cdot> \<tau>"
    and target_i4: "i4 (r \<cdot> \<sigma>) = r \<cdot> \<tau>"
  shows "(i4 (l \<cdot> \<sigma>),i4 (r \<cdot> \<sigma>)) \<in> Rgt \<union> Rge \<and>
    ((i4 (l \<cdot> \<sigma>),i4 (r \<cdot> \<sigma>)) \<notin> Rgt \<longrightarrow>
      (l,r) \<notin> Rgt)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  show ?thesis
  proof (cases "(l,r) \<in> Rgt")
    case True
    have "(l \<cdot> \<tau>,r \<cdot> \<tau>) \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    then show ?thesis unfolding source_i4 target_i4 by auto
  next
    case False
    with pair_order have weak: "(l,r) \<in> Rge" by auto
    have "(l \<cdot> \<tau>,r \<cdot> \<tau>) \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak])
    then show ?thesis unfolding source_i4 target_i4 using False by auto
  qed
qed

lemma i4_collapsing_bridge_redpair_order_from_common_substs:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order: "(l,Var y) \<in> Rgt \<union> Rge"
    and bridge_order: "(a,b) \<in> Rge"
    and source_i4: "i4 (l \<cdot> \<sigma>) = l \<cdot> \<sigma>'"
    and hidden_i4: "\<sigma>' y = a \<cdot> \<theta>'"
    and target_i4: "i4 (b \<cdot> \<theta>) = b \<cdot> \<theta>'"
  shows "(i4 (l \<cdot> \<sigma>),i4 (b \<cdot> \<theta>)) \<in> Rgt \<union> Rge \<and>
    ((i4 (l \<cdot> \<sigma>),i4 (b \<cdot> \<theta>)) \<notin> Rgt \<longrightarrow>
      (l,Var y) \<notin> Rgt)"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have bridge: "(a \<cdot> \<theta>',b \<cdot> \<theta>') \<in> Rge"
    by (rule subst.closedD[OF rp.subst_NS bridge_order])
  show ?thesis
  proof (cases "(l,Var y) \<in> Rgt")
    case True
    have pair: "(l \<cdot> \<sigma>',Var y \<cdot> \<sigma>') \<in> Rgt"
      by (rule subst.closedD[OF rp.subst_S True])
    have pair': "(l \<cdot> \<sigma>',a \<cdot> \<theta>') \<in> Rgt"
      using pair hidden_i4 by simp
    have strict: "(l \<cdot> \<sigma>',b \<cdot> \<theta>') \<in> Rgt"
      using rp.compat_S_NS pair' bridge by auto
    show ?thesis unfolding source_i4 target_i4 using strict by auto
  next
    case False
    with pair_order have weak0: "(l,Var y) \<in> Rge" by auto
    have pair: "(l \<cdot> \<sigma>',Var y \<cdot> \<sigma>') \<in> Rge"
      by (rule subst.closedD[OF rp.subst_NS weak0])
    have pair': "(l \<cdot> \<sigma>',a \<cdot> \<theta>') \<in> Rge"
      using pair hidden_i4 by simp
    have weak: "(l \<cdot> \<sigma>',b \<cdot> \<theta>') \<in> Rge"
      by (rule rp.trans_NS_point[OF pair' bridge])
    show ?thesis unfolding source_i4 target_i4 using weak False by auto
  qed
qed

lemma i4_noncollapsing_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order: "(l,r) \<in> Rgt \<union> Rge"
    and source_safe: "i4_safe l \<sigma>"
    and target_safe: "i4_safe r \<sigma>"
    and source_partition: "mu_vars_term i4_mu l \<inter>
      non_mu_vars_term i4_mu l = {}"
    and target_partition: "mu_vars_term i4_mu r \<inter>
      non_mu_vars_term i4_mu r = {}"
    and source_full: "vars_term l \<subseteq> mu_vars_term i4_mu l"
    and target_full: "vars_term r \<subseteq> mu_vars_term i4_mu r"
  shows "(i4 (l \<cdot> \<sigma>),i4 (r \<cdot> \<sigma>)) \<in> Rgt \<union> Rge \<and>
    ((i4 (l \<cdot> \<sigma>),i4 (r \<cdot> \<sigma>)) \<notin> Rgt \<longrightarrow>
      (l,r) \<notin> Rgt)"
proof (rule i4_noncollapsing_redpair_order_from_common_subst)
  show "compat_redpair_order Rgt Rge" by (rule redpair)
  show "(l,r) \<in> Rgt \<union> Rge" by (rule pair_order)
  show "i4 (l \<cdot> \<sigma>) = l \<cdot> (\<lambda>x. i4 (\<sigma> x))"
    by (rule i4_full_active_commutes[
      OF source_safe source_partition source_full])
  show "i4 (r \<cdot> \<sigma>) = r \<cdot> (\<lambda>x. i4 (\<sigma> x))"
    by (rule i4_full_active_commutes[
      OF target_safe target_partition target_full])
qed

lemma i4_subst_target_from_active_sub:
  assumes target_full: "vars_term b \<subseteq> mu_vars_term i4_mu b"
    and active_sub: "mu_vars_term i4_mu b \<subseteq>
      mu_vars_term i4_mu a"
  shows "b \<cdot> i4_subst a \<theta> = b \<cdot> i4_subst b \<theta>"
proof (rule term_subst_eq)
  fix x
  assume x: "x \<in> vars_term b"
  with target_full have xb: "x \<in> mu_vars_term i4_mu b" by blast
  with active_sub have xa: "x \<in> mu_vars_term i4_mu a" by blast
  show "i4_subst a \<theta> x = i4_subst b \<theta> x"
    unfolding i4_subst_def using xa xb by simp
qed

lemma i4_collapsing_bridge_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pair_order: "(l,Var y) \<in> Rgt \<union> Rge"
    and bridge_order: "(a,b) \<in> Rge"
    and source_safe: "i4_safe l \<sigma>"
    and bridge_safe: "i4_safe a \<theta>"
    and target_safe: "i4_safe b \<theta>"
    and source_partition: "mu_vars_term i4_mu l \<inter>
      non_mu_vars_term i4_mu l = {}"
    and bridge_partition: "mu_vars_term i4_mu a \<inter>
      non_mu_vars_term i4_mu a = {}"
    and target_partition: "mu_vars_term i4_mu b \<inter>
      non_mu_vars_term i4_mu b = {}"
    and source_full: "vars_term l \<subseteq> mu_vars_term i4_mu l"
    and target_full: "vars_term b \<subseteq> mu_vars_term i4_mu b"
    and bridge_active: "mu_vars_term i4_mu b \<subseteq>
      mu_vars_term i4_mu a"
    and hidden: "\<sigma> y = a \<cdot> \<theta>"
  shows "(i4 (l \<cdot> \<sigma>),i4 (b \<cdot> \<theta>)) \<in> Rgt \<union> Rge \<and>
    ((i4 (l \<cdot> \<sigma>),i4 (b \<cdot> \<theta>)) \<notin> Rgt \<longrightarrow>
      (l,Var y) \<notin> Rgt)"
proof (rule i4_collapsing_bridge_redpair_order_from_common_substs[
    where \<sigma>'="\<lambda>x. i4 (\<sigma> x)" and \<theta>'="i4_subst a \<theta>"])
  show "compat_redpair_order Rgt Rge" by (rule redpair)
  show "(l,Var y) \<in> Rgt \<union> Rge" by (rule pair_order)
  show "(a,b) \<in> Rge" by (rule bridge_order)
  show "i4 (l \<cdot> \<sigma>) = l \<cdot> (\<lambda>x. i4 (\<sigma> x))"
    by (rule i4_full_active_commutes[
      OF source_safe source_partition source_full])
  have bridge_i4: "i4 (a \<cdot> \<theta>) = a \<cdot> i4_subst a \<theta>"
    using i4_equals_bracket[OF bridge_safe]
      i4_bracket_as_subst[OF bridge_partition] by simp
  show "i4 (\<sigma> y) = a \<cdot> i4_subst a \<theta>"
    unfolding hidden by (rule bridge_i4)
  have target_i4: "i4 (b \<cdot> \<theta>) = b \<cdot> i4_subst b \<theta>"
    using i4_equals_bracket[OF target_safe]
      i4_bracket_as_subst[OF target_partition] by simp
  show "i4 (b \<cdot> \<theta>) = b \<cdot> i4_subst a \<theta>"
    unfolding target_i4
    by (rule i4_subst_target_from_active_sub[
      OF target_full bridge_active, symmetric])
qed

lemma i4_typed_pair_redpair_order:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_source_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {}"
    and pair_target_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {}"
    and bridge_source_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {}"
    and bridge_target_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {}"
    and pair_source_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      vars_term l \<subseteq> mu_vars_term i4_mu l"
    and pair_target_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow> vars_term r \<subseteq> mu_vars_term i4_mu r"
    and bridge_target_full: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      vars_term b \<subseteq> mu_vars_term i4_mu b"
    and bridge_active: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a"
    and noncoll_safe: "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
    and coll_safe: "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
      (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
      \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
    and pair_step: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "(i4 s,i4 t) \<in> Rgt \<union> Rge \<and>
    ((i4 s,i4 t) \<notin> Rgt \<longrightarrow>
      (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
proof -
  from pair_step have cases:
      "muterm_noncollapsing_rrstep P s t \<or>
       (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rfun: "is_Fun r"
      and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from noncoll_safe[OF pair rfun s t]
    have lsafe: "i4_safe l \<sigma>" and rsafe: "i4_safe r \<sigma>" by auto
    from i4_noncollapsing_redpair_order[
      OF redpair pairs_order[THEN subsetD, OF pair] lsafe rsafe
        pair_source_partition[OF pair] pair_target_partition[OF pair rfun]
        pair_source_full[OF pair] pair_target_full[OF pair rfun]]
    have ordered: "(i4 s,i4 t) \<in> Rgt \<union> Rge"
      and residual: "(i4 s,i4 t) \<notin> Rgt \<Longrightarrow> (l,r) \<notin> Rgt"
      unfolding s t by auto
    have residual_step: "(i4 s,i4 t) \<notin> Rgt \<Longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
        rrstep_def' using pair rfun s t residual by blast
    show ?thesis using ordered residual_step by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> a b \<theta> where pair: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and hidden: "\<sigma> y = a \<cdot> \<theta>"
      and bridge: "(a,b) \<in> B" and t: "t = b \<cdot> \<theta>"
      unfolding muterm_collapsing_rrstep_def rrstep_def' by auto
    from coll_safe[OF pair bridge s hidden t]
    have lsafe: "i4_safe l \<sigma>" and asafe: "i4_safe a \<theta>"
      and bsafe: "i4_safe b \<theta>" by auto
    from i4_collapsing_bridge_redpair_order[
      OF redpair pairs_order[THEN subsetD, OF pair]
        bridges_order[THEN subsetD, OF bridge] lsafe asafe bsafe
        pair_source_partition[OF pair] bridge_source_partition[OF bridge]
        bridge_target_partition[OF bridge] pair_source_full[OF pair]
        bridge_target_full[OF bridge] bridge_active[OF bridge] hidden]
    have ordered: "(i4 s,i4 t) \<in> Rgt \<union> Rge"
      and residual: "(i4 s,i4 t) \<notin> Rgt \<Longrightarrow>
        (l,Var y) \<notin> Rgt"
      unfolding s t by auto
    have residual_step: "(i4 s,i4 t) \<notin> Rgt \<Longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      unfolding muterm_typed_pair_step_def muterm_collapsing_rrstep_def
        rrstep_def' using pair s hidden bridge t residual by blast
    show ?thesis using ordered residual_step by blast
  qed
qed

definition i4_typed_step_safe where
  "i4_typed_step_safe P B s t \<longleftrightarrow>
    (\<forall>l r \<sigma>. (l,r) \<in> P \<longrightarrow> is_Fun r \<longrightarrow>
      s = l \<cdot> \<sigma> \<longrightarrow> t = r \<cdot> \<sigma> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>) \<and>
    (\<forall>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<longrightarrow> (a,b) \<in> B \<longrightarrow>
      s = l \<cdot> \<sigma> \<longrightarrow> \<sigma> y = a \<cdot> \<theta> \<longrightarrow>
      t = b \<cdot> \<theta> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>)"

lemma i4_typed_step_safe_noncollD:
  assumes safe: "i4_typed_step_safe P B s t"
    and pair: "(l,r) \<in> P" and rfun: "is_Fun r"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
  shows "i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
proof -
  from safe have all: "\<forall>l r \<sigma>. (l,r) \<in> P \<longrightarrow> is_Fun r \<longrightarrow>
      s = l \<cdot> \<sigma> \<longrightarrow> t = r \<cdot> \<sigma> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
    unfolding i4_typed_step_safe_def by (rule conjunct1)
  show ?thesis by (rule all[rule_format, OF pair rfun s t])
qed

lemma i4_typed_step_safe_collD:
  assumes safe: "i4_typed_step_safe P B s t"
    and pair: "(l,Var y) \<in> P" and bridge: "(a,b) \<in> B"
    and s: "s = l \<cdot> \<sigma>" and hidden: "\<sigma> y = a \<cdot> \<theta>"
    and t: "t = b \<cdot> \<theta>"
  shows "i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
proof -
  from safe have all: "\<forall>l y \<sigma> a b \<theta>.
      (l,Var y) \<in> P \<longrightarrow> (a,b) \<in> B \<longrightarrow>
      s = l \<cdot> \<sigma> \<longrightarrow> \<sigma> y = a \<cdot> \<theta> \<longrightarrow>
      t = b \<cdot> \<theta> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
    unfolding i4_typed_step_safe_def by (rule conjunct2)
  show ?thesis by (rule all[rule_format, OF pair bridge s hidden t])
qed

(* DIAGNOSTIC WRAPPER START
lemma i4_typed_pair_redpair_order_safe:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_source_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {}"
    and pair_target_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {}"
    and bridge_source_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {}"
    and bridge_target_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {}"
    and pair_source_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      vars_term l \<subseteq> mu_vars_term i4_mu l"
    and pair_target_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow> vars_term r \<subseteq> mu_vars_term i4_mu r"
    and bridge_target_full: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      vars_term b \<subseteq> mu_vars_term i4_mu b"
    and bridge_active: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a"
    and safe: "i4_typed_step_safe P B s t"
    and pair_step: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "(i4 s,i4 t) \<in> Rgt \<union> Rge \<and>
    ((i4 s,i4 t) \<notin> Rgt \<longrightarrow>
      (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
proof (rule i4_typed_pair_redpair_order)
  show "compat_redpair_order Rgt Rge" by (rule redpair)
  show "P \<subseteq> Rgt \<union> Rge" by (rule pairs_order)
  show "B \<subseteq> Rge" by (rule bridges_order)
  show "\<And>l r. (l,r) \<in> P \<Longrightarrow>
    mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {}"
    by (rule pair_source_partition)
  show "\<And>l r. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
    mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {}"
    by (rule pair_target_partition)
  show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
    mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {}"
    by (rule bridge_source_partition)
  show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
    mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {}"
    by (rule bridge_target_partition)
  show "\<And>l r. (l,r) \<in> P \<Longrightarrow>
    vars_term l \<subseteq> mu_vars_term i4_mu l"
    by (rule pair_source_full)
  show "\<And>l r. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
    vars_term r \<subseteq> mu_vars_term i4_mu r"
    by (rule pair_target_full)
  show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
    vars_term b \<subseteq> mu_vars_term i4_mu b"
    by (rule bridge_target_full)
  show "\<And>a b. (a,b) \<in> B \<Longrightarrow>
    mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a"
    by (rule bridge_active)
  show "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
    s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
    i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
    using safe unfolding i4_typed_step_safe_def by blast
  show "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
    (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
    \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
    i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
    using safe unfolding i4_typed_step_safe_def by blast
  show "(s,t) \<in> muterm_typed_pair_step P B" by (rule pair_step)
qed
DIAGNOSTIC WRAPPER END *)

lemma i4_next_collapsing_hidden_not_SN:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>u. u \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s' x"
    and bridge: "(x,t') \<in> rrstep B"
  shows "\<not> SN_on (csstep \<mu> (set Rs)) {x}"
proof -
  from next_event obtain u where target: "t' = sharp_term Sharp u"
    and uT_inner: "u \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs))"
    unfolding muterm_innermost_min_typed_pair_step_def by auto
  have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    by (rule lift_minimal[OF uT_inner])
  show ?thesis
    by (rule exact_unhiding_bridge_hidden_not_SN[
      where \<mu>=m and R="set Rs" and B=B and u=u,
      unfolded mu[symmetric], OF wf exact bridge[unfolded target] uT])
qed

fun i4_covered_or_exposed ::
  "((('f,'l) lab),string) term set \<Rightarrow>
   ((('f,'l) lab),string) term \<Rightarrow> ((('f,'l) lab),string) subst \<Rightarrow> bool"
where
  "i4_covered_or_exposed X (Var x) \<sigma> = unmarked_term (\<sigma> x)"
| "i4_covered_or_exposed X (Fun f ts) \<sigma> =
    ((is_sharp_lab f \<or>
      (unmarked_term (Fun f ts \<cdot> \<sigma>) \<and>
       ((f,length ts) \<in> \<Delta> \<or> Fun f ts \<cdot> \<sigma> \<in> X))) \<and>
     (\<forall>i<length ts. i \<in> i4_mu (f,length ts) \<longrightarrow>
       i4_covered_or_exposed X (ts ! i) \<sigma>))"

text \<open>
  This predicate is the executable half of recursive target safety.  Every
  unmarked call is either covered by the local usable-rule root set or is
  listed among calls exposed by the following exact unhiding event.  The
  latter set is semantic only in this lemma; the chain theorem above proves
  its members nonterminating.
\<close>

lemma i4_covered_or_exposed_imp_safe:
  assumes covered: "i4_covered_or_exposed X t \<sigma>"
    and exposed: "\<And>u. u \<in> X \<Longrightarrow>
      \<not> SN_on (csstep \<mu> (set Rs)) {u}"
  shows "i4_safe t \<sigma>"
  using covered
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have root: "is_sharp_lab f \<or>
      (unmarked_term (Fun f ts \<cdot> \<sigma>) \<and>
       ((f,length ts) \<in> \<Delta> \<or>
        \<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts \<cdot> \<sigma>}))"
  proof (cases "is_sharp_lab f")
    case True
    then show ?thesis by simp
  next
    case False
    from Fun.prems False have unmarked:
        "unmarked_term (Fun f ts \<cdot> \<sigma>)"
      and covered_root: "(f,length ts) \<in> \<Delta> \<or>
        Fun f ts \<cdot> \<sigma> \<in> X" by auto
    show ?thesis
    proof (cases "(f,length ts) \<in> \<Delta>")
      case True
      then show ?thesis using unmarked by auto
    next
      case False
      with covered_root have member: "Fun f ts \<cdot> \<sigma> \<in> X" by auto
      show ?thesis using unmarked exposed[OF member] by auto
    qed
  qed
  have children: "\<And>i. i < length ts \<Longrightarrow>
      i \<in> i4_mu (f,length ts) \<Longrightarrow> i4_safe (ts ! i) \<sigma>"
  proof -
    fix i
    assume i: "i < length ts" and active: "i \<in> i4_mu (f,length ts)"
    have child_covered: "i4_covered_or_exposed X (ts ! i) \<sigma>"
      using Fun.prems i active by simp
    show "i4_safe (ts ! i) \<sigma>"
      by (rule Fun.hyps[OF nth_mem[OF i] child_covered])
  qed
  show ?case using root children by simp
qed

lemma i4_covered_by_next_collapsing_imp_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>u. u \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s' x"
    and bridge: "(x,t') \<in> rrstep B"
    and covered: "i4_covered_or_exposed {x} t \<sigma>"
  shows "i4_safe t \<sigma>"
proof (rule i4_covered_or_exposed_imp_safe[OF covered])
  fix u
  assume "u \<in> {x}"
  then have u: "u = x" by simp
  show "\<not> SN_on (csstep \<mu> (set Rs)) {u}"
    unfolding u by (rule i4_next_collapsing_hidden_not_SN[
      OF mu lift_minimal exact next_event collapsing bridge])
qed

lemma i4_unary_active_hidden_not_SN:
  assumes undef: "\<not> defined (set Rs) (f,1)"
    and not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun f [u]}"
  shows "\<not> SN_on (csstep \<mu> (set Rs)) {u}"
proof -
  have undef': "\<not> defined (set Rs) (f,length [u])"
    using undef by simp
  have ex: "\<exists>i<length [u]. i \<in> \<mu> (f,length [u]) \<and>
      \<not> SN_on (csstep \<mu> (set Rs)) {[u] ! i}"
    by (rule csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[
      OF wf undef' not_SN])
  then obtain i where i: "i < length [u]"
    and child: "\<not> SN_on (csstep \<mu> (set Rs)) {[u] ! i}"
    by auto
  from i have "i = 0" by simp
  with child show ?thesis by simp
qed

lemma i4_covered_by_next_unary_hidden_imp_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>v. v \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      v \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s' x"
    and bridge: "(x,t') \<in> rrstep B"
    and x: "x = Fun f [u]"
    and undef: "\<not> defined (set Rs) (f,1)"
    and covered: "i4_covered_or_exposed {u} t \<sigma>"
  shows "i4_safe t \<sigma>"
proof (rule i4_covered_or_exposed_imp_safe[OF covered])
  fix v
  assume "v \<in> {u}"
  then have v: "v = u" by simp
  have x_not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {x}"
    by (rule i4_next_collapsing_hidden_not_SN[
      OF mu lift_minimal exact next_event collapsing bridge])
  have u_not_SN: "\<not> SN_on (csstep \<mu> (set Rs)) {u}"
    by (rule i4_unary_active_hidden_not_SN[
      OF undef x_not_SN[unfolded x]])
  show "\<not> SN_on (csstep \<mu> (set Rs)) {v}"
    unfolding v by (rule u_not_SN)
qed

lemma i4_innermost_steps_inactive_marked_arg_preserved:
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and i: "i < length ts"
    and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
    and steps: "(Fun (Sharp f) ts,v) \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
  shows "\<exists>us. v = Fun (Sharp f) us \<and> length us = length ts \<and>
    us ! i = ts ! i"
proof -
  have full_steps: "(Fun (Sharp f) ts,v) \<in>
      (csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    by (rule rtrancl_mono[OF innermost_csdp_step_subset_csdp_step,
      THEN subsetD, OF steps])
  show ?thesis by (rule cssteps_Fun_inactive_arg_preserved[
    OF wf fresh i inactive full_steps])
qed

lemma i4_frozen_unary_next_exposure_imp_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>w. w \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      w \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and fresh: "\<And>h n. \<not> defined (set Rs) (Sharp h,n)"
    and current: "t = Fun (Sharp f) ts"
    and following: "s' = Fun (Sharp f) us"
    and i: "i < length ts"
    and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
    and steps: "(t,s') \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and frozen_arg: "ts ! i = Fun g [u]"
    and selected: "x = us ! i"
    and undef: "\<not> defined (set Rs) (g,1)"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s' x"
    and bridge: "(x,t') \<in> rrstep B"
    and covered: "i4_covered_or_exposed {u} q \<sigma>"
  shows "i4_safe q \<sigma>"
proof -
  from i4_innermost_steps_inactive_marked_arg_preserved[
    OF fresh i inactive steps[unfolded current following]]
  obtain vs where s'_vs: "Fun (Sharp f) us = Fun (Sharp f) vs"
    and len: "length vs = length ts" and same: "vs ! i = ts ! i"
    unfolding following by blast
  have us_vs: "us = vs" using s'_vs by simp
  have x_shape: "x = Fun g [u]"
    using selected us_vs same frozen_arg by simp
  show ?thesis by (rule i4_covered_by_next_unary_hidden_imp_safe[
    OF mu lift_minimal exact next_event collapsing bridge x_shape undef covered])
qed

lemma unmarked_term_subst:
  assumes unmarked: "unmarked_term t"
    and subst: "\<And>x. x \<in> vars_term t \<Longrightarrow> unmarked_term (\<sigma> x)"
  shows "unmarked_term (t \<cdot> \<sigma>)"
  using unmarked subst
proof (induct t)
  case (Var x)
  show ?case using Var.prems by simp
next
  case (Fun f ts)
  from Fun.prems have root: "\<not> is_sharp_lab f"
    and children: "\<forall>u\<in>set ts. unmarked_term u"
    unfolding unmarked_term_Fun by auto
  have "\<forall>u\<in>set ts. unmarked_term (u \<cdot> \<sigma>)"
  proof (intro ballI)
    fix u
    assume u: "u \<in> set ts"
    have local_subst: "\<And>x. x \<in> vars_term u \<Longrightarrow>
        unmarked_term (\<sigma> x)"
      using Fun.prems(2) u by auto
    show "unmarked_term (u \<cdot> \<sigma>)"
      by (rule Fun.hyps[OF u children[rule_format, OF u] local_subst])
  qed
  then show ?case using root by (simp add: unmarked_term_Fun)
qed

lemma unmarked_term_subst_varD:
  assumes unmarked: "unmarked_term (t \<cdot> \<sigma>)"
    and x: "x \<in> vars_term t"
  shows "unmarked_term (\<sigma> x)"
  using unmarked x
proof (induct t)
  case (Var y)
  then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems obtain q where q: "q \<in> set ts"
    and xq: "x \<in> vars_term q" by auto
  have uq: "unmarked_term (q \<cdot> \<sigma>)"
  proof (unfold unmarked_term_def, intro ballI)
    fix fn
    assume fn: "fn \<in> funas_term (q \<cdot> \<sigma>)"
    have fn_parent: "fn \<in> funas_term (Fun f ts \<cdot> \<sigma>)"
      using q fn by auto
    from Fun.prems(1) show "\<not> is_sharp_lab (fst fn)"
      unfolding unmarked_term_def using fn_parent by auto
  qed
  show ?case by (rule Fun.hyps[OF q uq xq])
qed

lemma csstep_preserves_unmarked_term:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and source: "unmarked_term s"
    and step: "(s,t) \<in> csstep \<mu> (set Rs)"
  shows "unmarked_term t"
proof -
  let ?F = "{fn. \<not> is_sharp_lab (fst fn)}"
  have rules_F: "funas_trs (set Rs) \<subseteq> ?F"
    using rules_unmarked by auto
  have source_F: "funas_term s \<subseteq> ?F"
    using source unfolding unmarked_term_def by auto
  have raw: "(s,t) \<in> rstep (set Rs)"
    by (rule csstep_subset_rstep[THEN subsetD, OF step])
  have target_F: "funas_term t \<subseteq> ?F"
    by (rule rstep_preserves_funas_terms[OF rules_F source_F raw wf])
  show ?thesis using target_F unfolding unmarked_term_def by auto
qed

definition i4_chain_good where
  "i4_chain_good t \<longleftrightarrow> (\<exists>f ss.
    t = Fun (Sharp f) ss \<and> \<not> is_sharp_lab f \<and>
    (\<forall>i<length ss. unmarked_term (ss ! i)))"

text \<open>
  Internal marked symbols are introduced by the dependency-pair
  transformation and are not part of source substitutions.  We record that
  signature invariant explicitly instead of silently strengthening the
  unrestricted semantic DPP.  The residual checker may still establish the
  stronger unrestricted problem; the recursive interpretation only needs the
  well-formed subrelation generated from source CSR chains.
\<close>

definition muterm_i4_good_pair_step where
  "muterm_i4_good_pair_step P B =
    muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B \<inter>
      {(s,t). i4_chain_good s \<and> i4_chain_good t}"

definition finite_muterm_i4_good_typed_dpp where
  "finite_muterm_i4_good_typed_dpp P B \<longleftrightarrow>
    SN_rel (muterm_i4_good_pair_step P B)
      (innermost_csdp_step Sharp \<mu> (set Rs))"

lemma finite_muterm_innermost_min_typed_dpp_imp_i4_good:
  assumes "finite_muterm_innermost_min_typed_dpp Sharp \<mu> (set Rs) P B"
  shows "finite_muterm_i4_good_typed_dpp P B"
proof -
  from assms have fin:
      "SN_rel (muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) P B)
        (innermost_csdp_step Sharp \<mu> (set Rs))"
    unfolding finite_muterm_innermost_min_typed_dpp_def .
  show ?thesis unfolding finite_muterm_i4_good_typed_dpp_def
  proof (rule SN_rel_mono[OF _ subset_refl fin])
    show "muterm_i4_good_pair_step P B \<subseteq>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      unfolding muterm_i4_good_pair_step_def by auto
  qed
qed

lemma i4_chain_good_marked_instance_varD:
  assumes good: "i4_chain_good s"
    and shape: "l = Fun (Sharp f) ls"
    and source: "s = l \<cdot> \<sigma>"
    and x: "x \<in> vars_term l"
  shows "unmarked_term (\<sigma> x)"
proof -
  from good obtain g us where s: "s = Fun (Sharp g) us"
    and args: "\<And>i. i < length us \<Longrightarrow> unmarked_term (us ! i)"
    unfolding i4_chain_good_def by blast
  have g: "g = f" and us: "us = map (\<lambda>q. q \<cdot> \<sigma>) ls"
    using s source unfolding shape by auto
  from x obtain q where q: "q \<in> set ls" and xq: "x \<in> vars_term q"
    unfolding shape by auto
  from q obtain i where i: "i < length ls" and qi: "ls ! i = q"
    unfolding in_set_conv_nth by blast
  have ius: "i < length us" using i unfolding us by simp
  have ith_unmarked: "unmarked_term ((ls ! i) \<cdot> \<sigma>)"
    using args[OF ius] i unfolding us by simp
  have q_unmarked: "unmarked_term (q \<cdot> \<sigma>)"
    using ith_unmarked qi by simp
  show ?thesis by (rule unmarked_term_subst_varD[OF q_unmarked xq])
qed

lemma i4_chain_good_innermost_steps:
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and good: "i4_chain_good s"
    and steps: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
  shows "i4_chain_good t"
  using steps good
proof (induct rule: rtrancl_induct)
  case base
  then show ?case .
next
  case (step y z)
  from step.hyps(3)[OF step.prems]
  obtain f us where y: "y = Fun (Sharp f) us"
    and root: "\<not> is_sharp_lab f"
    and args: "\<And>i. i < length us \<Longrightarrow> unmarked_term (us ! i)"
    unfolding i4_chain_good_def by blast
  have full_step: "(Fun (Sharp f) us,z) \<in>
      csdp_step Sharp \<mu> (set Rs)"
    by (rule innermost_csdp_step_subset_csdp_step[THEN subsetD,
      OF step.hyps(2)[unfolded y]])
  have sharp_step: "(sharp_term Sharp (Fun f us),z) \<in>
      csdp_step Sharp \<mu> (set Rs)" using full_step by simp
  from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp sharp_step]
  obtain u where z: "z = sharp_term Sharp u"
    and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
  from nonroot obtain vs where u: "u = Fun f vs"
    and len: "length vs = length us" by (elim csnrstep_FunE, blast)
  have source_plain: "unmarked_term (Fun f us)"
    unfolding unmarked_term_Fun using root args
    by (auto simp: in_set_conv_nth)
  have local_plain: "(Fun f us,u) \<in> csstep \<mu> (set Rs)"
    using nonroot unfolding csstep_root_nonroot by auto
  have target_plain: "unmarked_term u"
    by (rule csstep_preserves_unmarked_term[
      OF rules_unmarked source_plain local_plain])
  have target_args: "\<forall>i<length vs. unmarked_term (vs ! i)"
    using target_plain unfolding u unmarked_term_Fun by auto
  show ?case unfolding i4_chain_good_def z u
    using root target_args by auto
qed

fun i4_symbolically_covered ::
  "((('f,'l) lab),string) term set \<Rightarrow> ((('f,'l) lab),string) term \<Rightarrow> bool"
where
  "i4_symbolically_covered E (Var x) = True"
| "i4_symbolically_covered E (Fun f ts) =
    ((is_sharp_lab f \<or>
      (unmarked_term (Fun f ts) \<and>
       ((f,length ts) \<in> \<Delta> \<or> Fun f ts \<in> E))) \<and>
     (\<forall>i<length ts. i \<in> i4_mu (f,length ts) \<longrightarrow>
       i4_symbolically_covered E (ts ! i)))"

lemma i4_symbolically_covered_subst:
  assumes symbolic: "i4_symbolically_covered E t"
    and unmarked_subst: "\<And>x. x \<in> vars_term t \<Longrightarrow>
      unmarked_term (\<sigma> x)"
  shows "i4_covered_or_exposed ((\<lambda>e. e \<cdot> \<sigma>) ` E) t \<sigma>"
  using symbolic unmarked_subst
proof (induct t)
  case (Var x)
    then show ?case by simp
next
  case (Fun f ts)
  have root: "is_sharp_lab f \<or>
      (unmarked_term (Fun f ts \<cdot> \<sigma>) \<and>
       ((f,length ts) \<in> \<Delta> \<or>
        Fun f ts \<cdot> \<sigma> \<in> (\<lambda>e. e \<cdot> \<sigma>) ` E))"
  proof (cases "is_sharp_lab f")
    case True
    then show ?thesis by simp
  next
    case False
    from Fun.prems False have unmarked: "unmarked_term (Fun f ts)"
      and covered_root: "(f,length ts) \<in> \<Delta> \<or> Fun f ts \<in> E"
      by auto
    have instance_unmarked: "unmarked_term (Fun f ts \<cdot> \<sigma>)"
      by (rule unmarked_term_subst[OF unmarked Fun.prems(2)])
    show ?thesis
    proof (cases "(f,length ts) \<in> \<Delta>")
      case True
      show ?thesis using False True instance_unmarked by auto
    next
      case False
      with covered_root have "Fun f ts \<in> E" by auto
      then have "Fun f ts \<cdot> \<sigma> \<in> (\<lambda>e. e \<cdot> \<sigma>) ` E"
        by blast
      then show ?thesis using instance_unmarked by auto
    qed
  qed
  have children: "\<And>i. i < length ts \<Longrightarrow>
      i \<in> i4_mu (f,length ts) \<Longrightarrow>
      i4_covered_or_exposed ((\<lambda>e. e \<cdot> \<sigma>) ` E) (ts ! i) \<sigma>"
  proof -
    fix i
    assume i: "i < length ts" and active: "i \<in> i4_mu (f,length ts)"
    have child_symbolic: "i4_symbolically_covered E (ts ! i)"
      using Fun.prems i active by simp
    have child_subst: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
        unmarked_term (\<sigma> x)"
    proof -
      fix x
      assume x: "x \<in> vars_term (ts ! i)"
      have "x \<in> vars_term (Fun f ts)"
        using nth_mem[OF i] x by auto
      then show "unmarked_term (\<sigma> x)"
        by (rule Fun.prems(2))
    qed
    show "i4_covered_or_exposed ((\<lambda>e. e \<cdot> \<sigma>) ` E)
      (ts ! i) \<sigma>"
      by (rule Fun.hyps[OF nth_mem[OF i] child_symbolic child_subst])
  qed
  show ?case using root children by simp
qed

lemma i4_symbolically_covered_empty_safe:
  assumes symbolic: "i4_symbolically_covered {} t"
    and unmarked_subst: "\<And>x. x \<in> vars_term t \<Longrightarrow>
      unmarked_term (\<sigma> x)"
  shows "i4_safe t \<sigma>"
proof (rule i4_covered_or_exposed_imp_safe)
  show "i4_covered_or_exposed {} t \<sigma>"
    using i4_symbolically_covered_subst[
      OF symbolic unmarked_subst] by simp
next
  show "\<And>u. u \<in> {} \<Longrightarrow>
      \<not> SN_on (csstep \<mu> (set Rs)) {u}" by simp
qed

lemma i4_exact_bridge_symbolic_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>u. u \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and event: "(s,t) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s x"
    and bridge: "(a,b) \<in> B"
    and hidden: "x = a \<cdot> \<theta>"
    and source_symbolic: "i4_symbolically_covered {a} a"
    and target_symbolic: "i4_symbolically_covered {} b"
    and source_subst: "\<And>z. z \<in> vars_term a \<Longrightarrow>
      unmarked_term (\<theta> z)"
    and target_subst: "\<And>z. z \<in> vars_term b \<Longrightarrow>
      unmarked_term (\<theta> z)"
    and event_bridge: "(x,t) \<in> rrstep B"
  shows "i4_safe a \<theta> \<and> i4_safe b \<theta>"
proof
  have covered: "i4_covered_or_exposed {x} a \<theta>"
    using i4_symbolically_covered_subst[
      OF source_symbolic source_subst] hidden by simp
  show "i4_safe a \<theta>"
    by (rule i4_covered_by_next_collapsing_imp_safe[
      OF mu lift_minimal exact event collapsing event_bridge covered])
  show "i4_safe b \<theta>"
    by (rule i4_symbolically_covered_empty_safe[
      OF target_symbolic target_subst])
qed

lemma i4_exact_bridge_unary_symbolic_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>v. v \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      v \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and event: "(s,t) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and collapsing: "muterm_collapsing_rrstep P s x"
    and bridge: "(a,b) \<in> B"
    and hidden: "x = a \<cdot> \<theta>"
    and source: "a = Fun f [u]"
    and undef: "\<not> defined (set Rs) (f,1)"
    and source_symbolic: "i4_symbolically_covered {u} a"
    and target_symbolic: "i4_symbolically_covered {} b"
    and source_subst: "\<And>z. z \<in> vars_term a \<Longrightarrow>
      unmarked_term (\<theta> z)"
    and target_subst: "\<And>z. z \<in> vars_term b \<Longrightarrow>
      unmarked_term (\<theta> z)"
    and event_bridge: "(x,t) \<in> rrstep B"
  shows "i4_safe a \<theta> \<and> i4_safe b \<theta>"
proof
  have covered: "i4_covered_or_exposed {u \<cdot> \<theta>} a \<theta>"
    using i4_symbolically_covered_subst[
      OF source_symbolic source_subst] by simp
  have x_shape: "x = Fun f [u \<cdot> \<theta>]"
    using hidden source by simp
  show "i4_safe a \<theta>"
    by (rule i4_covered_by_next_unary_hidden_imp_safe[
      OF mu lift_minimal exact event collapsing event_bridge
        x_shape undef covered])
  show "i4_safe b \<theta>"
    by (rule i4_symbolically_covered_empty_safe[
      OF target_symbolic target_subst])
qed

lemma i4_frozen_unary_symbolic_target_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>w. w \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      w \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "B = set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and fresh: "\<And>h n. \<not> defined (set Rs) (Sharp h,n)"
    and rhs: "r = Fun (Sharp f) ts"
    and i: "i < length ts"
    and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
    and frozen: "ts ! i = Fun g [u]"
    and undef: "\<not> defined (set Rs) (g,1)"
    and steps: "(r \<cdot> \<sigma>,s') \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and next_selects: "\<And>us. s' = Fun (Sharp f) us \<Longrightarrow>
      muterm_collapsing_rrstep P s' (us ! i) \<and>
      ((us ! i),t') \<in> rrstep B"
    and symbolic: "i4_symbolically_covered {u} r"
    and unmarked_subst: "\<And>x. x \<in> vars_term r \<Longrightarrow>
      unmarked_term (\<sigma> x)"
  shows "i4_safe r \<sigma>"
proof -
  have current: "r \<cdot> \<sigma> =
      Fun (Sharp f) (map (\<lambda>q. q \<cdot> \<sigma>) ts)"
    unfolding rhs by simp
  have ci: "i < length (map (\<lambda>q. q \<cdot> \<sigma>) ts)" using i by simp
  have cinactive: "i \<notin> csr_dp_root_mu \<mu>
      (Sharp f,length (map (\<lambda>q. q \<cdot> \<sigma>) ts))"
    using inactive by simp
  from i4_innermost_steps_inactive_marked_arg_preserved[
    OF fresh ci cinactive steps[unfolded current]]
  obtain us where following: "s' = Fun (Sharp f) us"
    and len: "length us = length ts"
    and same: "us ! i = (map (\<lambda>q. q \<cdot> \<sigma>) ts) ! i"
    by auto
  from next_selects[OF following]
  have collapsing: "muterm_collapsing_rrstep P s' (us ! i)"
    and bridge: "((us ! i),t') \<in> rrstep B" by auto
  have frozen_instance:
      "(map (\<lambda>q. q \<cdot> \<sigma>) ts) ! i = Fun g [u \<cdot> \<sigma>]"
    using i frozen by simp
  have covered: "i4_covered_or_exposed {u \<cdot> \<sigma>} r \<sigma>"
    using i4_symbolically_covered_subst[OF symbolic unmarked_subst] by simp
  show ?thesis
  proof (rule i4_frozen_unary_next_exposure_imp_safe[
      OF mu lift_minimal exact fresh current following ci cinactive
        steps frozen_instance _ undef next_event collapsing bridge covered])
    show "us ! i = us ! i" by simp
  qed
qed

definition muterm_root_pairs_select_arg where
  "muterm_root_pairs_select_arg P f i \<longleftrightarrow>
    (\<forall>l r ls. (l,r) \<in> P \<longrightarrow> l = Fun (Sharp f) ls \<longrightarrow>
      i < length ls \<and> is_Var r \<and> r = ls ! i)"

lemma muterm_root_pairs_select_arg_sound:
  assumes lhs_shape: "\<forall>(l,r)\<in>P. \<exists>g ls. l = Fun (Sharp g) ls"
    and select: "muterm_root_pairs_select_arg P f i"
    and source: "s = Fun (Sharp f) us"
    and event: "(s,t) \<in> muterm_typed_pair_step P B"
  shows "muterm_collapsing_rrstep P s (us ! i) \<and>
    ((us ! i),t) \<in> rrstep B"
proof -
  from event have cases: "muterm_noncollapsing_rrstep P s t \<or>
      (\<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P s t"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rfun: "is_Fun r"
      and se: "s = l \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from lhs_shape pair obtain g ls where l: "l = Fun (Sharp g) ls" by auto
    have g: "g = f" using source se unfolding l by simp
    from select pair have "is_Var r"
      unfolding muterm_root_pairs_select_arg_def l g by blast
    with rfun show ?thesis by (cases r, auto)
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P s x \<and>
      (x,t) \<in> rrstep B"
    then obtain x l y \<sigma> where pair: "(l,Var y) \<in> P"
      and se: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      and bridge: "(x,t) \<in> rrstep B"
      unfolding muterm_collapsing_rrstep_def by auto
    from lhs_shape pair obtain g ls where l: "l = Fun (Sharp g) ls" by auto
    have g: "g = f" using source se unfolding l by simp
    from select pair have il: "i < length ls" and ri: "Var y = ls ! i"
      unfolding muterm_root_pairs_select_arg_def l g by blast+
    have us: "us = map (\<lambda>q. q \<cdot> \<sigma>) ls"
      using source se unfolding l g by simp
    have usi: "us ! i = \<sigma> y" using il ri unfolding us by simp
    have collapse_i: "muterm_collapsing_rrstep P s (us ! i)"
      unfolding muterm_collapsing_rrstep_def
      using pair se x usi coll by auto
    show ?thesis using collapse_i bridge x usi by simp
  qed
qed

lemma muterm_root_pairs_select_arg_next_event:
  assumes lhs_shape: "\<forall>(l,r)\<in>P. \<exists>g ls. l = Fun (Sharp g) ls"
    and select: "muterm_root_pairs_select_arg P f i"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> R P B"
    and source: "s' = Fun (Sharp f) us"
  shows "muterm_collapsing_rrstep P s' (us ! i) \<and>
    ((us ! i),t') \<in> rrstep B"
proof -
  from next_event have typed: "(s',t') \<in> muterm_typed_pair_step P B"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def by auto
  show ?thesis by (rule muterm_root_pairs_select_arg_sound[
    OF lhs_shape select source typed])
qed

definition muterm_root_pairs_select_arg_check where
  "muterm_root_pairs_select_arg_check P f i = list_all (\<lambda>lr.
    case fst lr of
      Var x \<Rightarrow> False
    | Fun h ls \<Rightarrow> (case h of
        Sharp g \<Rightarrow> if g = f then
          i < length ls \<and> is_Var (snd lr) \<and> snd lr = ls ! i
        else True
      | _ \<Rightarrow> False)) P"

lemma muterm_root_pairs_select_arg_check_sound:
  assumes check: "muterm_root_pairs_select_arg_check P f i"
  shows "(\<forall>(l,r)\<in>set P. \<exists>g ls. l = Fun (Sharp g) ls) \<and>
    muterm_root_pairs_select_arg (set P) f i"
proof -
  have each: "\<And>l r. (l,r) \<in> set P \<Longrightarrow>
      (\<exists>g ls. l = Fun (Sharp g) ls) \<and>
      (\<forall>ls. l = Fun (Sharp f) ls \<longrightarrow>
        i < length ls \<and> is_Var r \<and> r = ls ! i)"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set P"
    from check have all: "\<forall>lr\<in>set P. (case fst lr of
        Var x \<Rightarrow> False
      | Fun h ls \<Rightarrow> (case h of
          Sharp g \<Rightarrow> if g = f then
            i < length ls \<and> is_Var (snd lr) \<and> snd lr = ls ! i
          else True
        | _ \<Rightarrow> False))"
      unfolding muterm_root_pairs_select_arg_check_def list_all_iff .
    from all[rule_format, OF lr] have raw: "(case l of
        Var x \<Rightarrow> False
      | Fun h ls \<Rightarrow> (case h of
          Sharp g \<Rightarrow> if g = f then
            i < length ls \<and> is_Var r \<and> r = ls ! i
          else True
        | _ \<Rightarrow> False))"
      by (cases l; auto split: lab.splits if_splits)
    show "(\<exists>g ls. l = Fun (Sharp g) ls) \<and>
      (\<forall>ls. l = Fun (Sharp f) ls \<longrightarrow>
        i < length ls \<and> is_Var r \<and> r = ls ! i)"
      using raw by (cases l; auto split: lab.splits if_splits)
  qed
  have shape: "\<forall>(l,r)\<in>set P. \<exists>g ls. l = Fun (Sharp g) ls"
    using each by auto
  have select: "muterm_root_pairs_select_arg (set P) f i"
    unfolding muterm_root_pairs_select_arg_def using each by blast
  show ?thesis using shape select by simp
qed

definition muterm_no_bridge_matches where
  "muterm_no_bridge_matches B q \<longleftrightarrow>
    (\<forall>(a,b)\<in>set B. \<not> matches q a)"

lemma muterm_no_bridge_matches_sound:
  assumes no_match: "muterm_no_bridge_matches B q"
    and bridge: "(a,b) \<in> set B"
  shows "a \<cdot> \<theta> \<noteq> q"
proof
  assume eq: "a \<cdot> \<theta> = q"
  have "matches q a" unfolding matches_iff using eq by blast
  moreover from no_match bridge have "\<not> matches q a"
    unfolding muterm_no_bridge_matches_def by auto
  ultimately show False by contradiction
qed

definition muterm_root_pair_selects_or_ground_blocked where
  "muterm_root_pair_selects_or_ground_blocked B f i ts lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow> case l of
      Var x \<Rightarrow> False
    | Fun h ls \<Rightarrow> (case h of
        Sharp g \<Rightarrow> if g \<noteq> f then True else
          (case r of
            Fun k rs \<Rightarrow> False
          | Var y \<Rightarrow>
              (i < length ls \<and> ls ! i = Var y) \<or>
              (\<exists>j<length ls. j < length ts \<and>
                j \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                ls ! j = Var y \<and> ground (ts ! j) \<and>
                muterm_no_bridge_matches B (ts ! j)))
      | _ \<Rightarrow> False))"

definition muterm_root_successors_select_or_block_check where
  "muterm_root_successors_select_or_block_check P B f i ts =
    list_all (muterm_root_pair_selects_or_ground_blocked B f i ts) P"

definition muterm_recursive_pair_safe_check where
  "muterm_recursive_pair_safe_check P B lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow> case l of
      Var x \<Rightarrow> False
    | Fun h ls \<Rightarrow> (case h of
        Sharp k \<Rightarrow>
          i4_symbolically_covered {} l \<and>
          vars_term r \<subseteq> vars_term l \<and>
          (case r of
            Var y \<Rightarrow> True
          | Fun q ts \<Rightarrow> (case q of
              Sharp f \<Rightarrow>
                i4_symbolically_covered {} r \<or>
                list_ex (\<lambda>(i,v). case v of
                    Var z \<Rightarrow> False
                  | Fun g us \<Rightarrow> (case us of
                      [u] \<Rightarrow>
                        i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                        \<not> defined (set Rs) (g,1) \<and>
                        i4_symbolically_covered {u} r \<and>
                        muterm_root_successors_select_or_block_check
                          P B f i ts
                    | _ \<Rightarrow> False))
                  (zip [0..<length ts] ts)
            | _ \<Rightarrow> False))
      | _ \<Rightarrow> False))"

definition muterm_recursive_pairs_safe_check where
  "muterm_recursive_pairs_safe_check P B =
    list_all (muterm_recursive_pair_safe_check P B) P"

definition muterm_recursive_bridges_safe_check where
  "muterm_recursive_bridges_safe_check B = list_all (\<lambda>lr.
    vars_term (snd lr) \<subseteq> vars_term (fst lr) \<and>
    (i4_symbolically_covered {fst lr} (fst lr) \<or>
      (case fst lr of
        Var x \<Rightarrow> False
      | Fun f ts \<Rightarrow> (case ts of
          [u] \<Rightarrow> \<not> defined (set Rs) (f,1) \<and>
            i4_symbolically_covered {u} (fst lr)
        | _ \<Rightarrow> False))) \<and>
    i4_symbolically_covered {} (snd lr)) B"

fun muterm_unmarked_term_check where
  "muterm_unmarked_term_check (Var x) = True"
| "muterm_unmarked_term_check (Fun f ts) =
    (\<not> is_sharp_lab f \<and> list_all muterm_unmarked_term_check ts)"

definition muterm_recursive_target_shape_check where
  "muterm_recursive_target_shape_check P B =
    (list_all (\<lambda>lr. case snd lr of
        Var x \<Rightarrow> True
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False)) P \<and>
     list_all (\<lambda>lr. case snd lr of
        Var x \<Rightarrow> False
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False)) B)"

fun muterm_i4_mu_vars_term_list ::
  "(((('f,'l) lab),string) term) \<Rightarrow> string list"
where
  "muterm_i4_mu_vars_term_list (Var x) = [x]"
| "muterm_i4_mu_vars_term_list (Fun f ts) = concat (map
    (\<lambda>i. muterm_i4_mu_vars_term_list (ts ! i))
    [i <- [0..<length ts]. is_sharp_lab f \<or>
      i \<in> \<mu> (f,length ts)])"

fun muterm_i4_non_mu_vars_term_list ::
  "(((('f,'l) lab),string) term) \<Rightarrow> string list"
where
  "muterm_i4_non_mu_vars_term_list (Var x) = []"
| "muterm_i4_non_mu_vars_term_list (Fun f ts) = concat (map
    (\<lambda>i. if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
      then muterm_i4_non_mu_vars_term_list (ts ! i)
      else vars_term_list (ts ! i)) [0..<length ts])"

definition muterm_i4_partition_check where
  "muterm_i4_partition_check t =
    (set (muterm_i4_mu_vars_term_list t) \<inter>
      set (muterm_i4_non_mu_vars_term_list t) = {})"

definition muterm_i4_full_check where
  "muterm_i4_full_check t = list_all
    (\<lambda>x. x \<in> set (muterm_i4_mu_vars_term_list t))
    (vars_term_list t)"

definition muterm_recursive_i4_shape_check where
  "muterm_recursive_i4_shape_check P B =
    (list_all (\<lambda>lr.
       muterm_i4_partition_check (fst lr) \<and>
       muterm_i4_full_check (fst lr) \<and>
       (is_Var (snd lr) \<or>
        (muterm_i4_partition_check (snd lr) \<and>
         muterm_i4_full_check (snd lr)))) P \<and>
     list_all (\<lambda>lr.
       muterm_i4_partition_check (fst lr) \<and>
       muterm_i4_partition_check (snd lr) \<and>
       muterm_i4_full_check (snd lr) \<and>
       list_all (\<lambda>x. x \<in>
          set (muterm_i4_mu_vars_term_list (fst lr)))
         (muterm_i4_mu_vars_term_list (snd lr))) B)"

lemma muterm_unmarked_term_check_sound:
  "muterm_unmarked_term_check t \<longleftrightarrow> unmarked_term t"
  by (induct t; auto simp: unmarked_term_Fun list_all_iff)

lemma set_muterm_i4_mu_vars_term_list [simp]:
  "set (muterm_i4_mu_vars_term_list t) = mu_vars_term i4_mu t"
proof (induct t)
  case (Var x)
  then show ?case unfolding mu_vars_term_def by simp
next
  case (Fun f ts)
  show ?case
  proof
    show "set (muterm_i4_mu_vars_term_list (Fun f ts)) \<subseteq>
        mu_vars_term i4_mu (Fun f ts)"
    proof
      fix x
      assume x: "x \<in> set (muterm_i4_mu_vars_term_list (Fun f ts))"
      then obtain i where i: "i < length ts"
        and active: "is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)"
        and child: "x \<in> set (muterm_i4_mu_vars_term_list (ts ! i))"
        by auto
      have ih: "set (muterm_i4_mu_vars_term_list (ts ! i)) =
          mu_vars_term i4_mu (ts ! i)"
        by (rule Fun.hyps[OF nth_mem[OF i]])
      have child': "x \<in> mu_vars_term i4_mu (ts ! i)"
        using child unfolding ih .
      have active': "i \<in> i4_mu (f,length ts)"
        using active i unfolding i4_mu_def by auto
      show "x \<in> mu_vars_term i4_mu (Fun f ts)"
        by (rule mu_vars_term_active_argI[OF i active' child'])
    qed
  next
    show "mu_vars_term i4_mu (Fun f ts) \<subseteq>
        set (muterm_i4_mu_vars_term_list (Fun f ts))"
    proof
      fix x
      assume x: "x \<in> mu_vars_term i4_mu (Fun f ts)"
      from mu_vars_term_FunE[OF x] obtain i where i: "i < length ts"
        and active: "i \<in> i4_mu (f,length ts)"
        and child: "x \<in> mu_vars_term i4_mu (ts ! i)" .
      have active': "is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)"
        using active i unfolding i4_mu_def
        by (cases "is_sharp_lab f"; auto)
      have ih: "set (muterm_i4_mu_vars_term_list (ts ! i)) =
          mu_vars_term i4_mu (ts ! i)"
        by (rule Fun.hyps[OF nth_mem[OF i]])
      show "x \<in> set (muterm_i4_mu_vars_term_list (Fun f ts))"
        using i active' child unfolding ih[symmetric] by auto
    qed
  qed
qed

lemma set_muterm_i4_non_mu_vars_term_list [simp]:
  "set (muterm_i4_non_mu_vars_term_list t) = non_mu_vars_term i4_mu t"
proof (induct t)
  case (Var x)
  then show ?case unfolding non_mu_vars_term_def by simp
next
  case (Fun f ts)
  show ?case
  proof
    show "set (muterm_i4_non_mu_vars_term_list (Fun f ts)) \<subseteq>
        non_mu_vars_term i4_mu (Fun f ts)"
    proof
      fix x
      assume x: "x \<in> set (muterm_i4_non_mu_vars_term_list (Fun f ts))"
      then obtain i where i: "i < length ts" and child:
        "x \<in> (if is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)
          then set (muterm_i4_non_mu_vars_term_list (ts ! i))
          else vars_term (ts ! i))"
        by (auto simp: set_vars_term_list)
      show "x \<in> non_mu_vars_term i4_mu (Fun f ts)"
      proof (cases "is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)")
        case True
        have active: "i \<in> i4_mu (f,length ts)"
          using True i unfolding i4_mu_def by auto
        have child': "x \<in> non_mu_vars_term i4_mu (ts ! i)"
          using child True Fun.hyps[OF nth_mem[OF i]] by simp
        show ?thesis by (rule non_mu_vars_term_active_argI[
          OF i active child'])
      next
        case False
        have inactive: "i \<notin> i4_mu (f,length ts)"
          using False unfolding i4_mu_def by auto
        have child': "x \<in> vars_term (ts ! i)" using child False by simp
        show ?thesis by (rule non_mu_vars_term_inactive_argI[
          where \<mu>=i4_mu and f=f and ts=ts and i=i,
          OF i inactive child'])
      qed
    qed
  next
    show "non_mu_vars_term i4_mu (Fun f ts) \<subseteq>
        set (muterm_i4_non_mu_vars_term_list (Fun f ts))"
    proof
      fix x
      assume x: "x \<in> non_mu_vars_term i4_mu (Fun f ts)"
      from x obtain p where pos: "p \<in> poss (Fun f ts)"
        and inactive: "p \<notin> mu_poss i4_mu (Fun f ts)"
        and at: "Fun f ts |_ p = Var x"
        unfolding non_mu_vars_term_def by blast
      from at pos obtain i q where p: "p = i # q" and i: "i < length ts"
        by (cases p; auto)
      show "x \<in> set (muterm_i4_non_mu_vars_term_list (Fun f ts))"
      proof (cases "is_sharp_lab f \<or> i \<in> \<mu> (f,length ts)")
        case True
        have active: "i \<in> i4_mu (f,length ts)"
          using True i unfolding i4_mu_def by auto
        have qpos: "q \<in> poss (ts ! i)" using pos p i by auto
        have qat: "ts ! i |_ q = Var x" using at p i by simp
        have qnot: "q \<notin> mu_poss i4_mu (ts ! i)"
        proof
          assume qin: "q \<in> mu_poss i4_mu (ts ! i)"
          have "i # q \<in> mu_poss i4_mu (Fun f ts)"
            using i active qin by auto
          moreover have "i # q \<notin> mu_poss i4_mu (Fun f ts)"
            using inactive unfolding p .
          ultimately show False by contradiction
        qed
        have child_inactive: "x \<in>
            non_mu_vars_term i4_mu (ts ! i)"
          unfolding non_mu_vars_term_def using qpos qnot qat by blast
        show ?thesis using Fun.hyps[OF nth_mem[OF i]] child_inactive i True
          by auto
      next
        case False
        have qpos: "q \<in> poss (ts ! i)" using pos p i by auto
        have qat: "ts ! i |_ q = Var x" using at p i by simp
        have child_var: "x \<in> vars_term (ts ! i)"
          using vars_term_subt_at[OF qpos] unfolding qat by auto
        show ?thesis using i False child_var by (auto simp: set_vars_term_list)
      qed
    qed
  qed
qed

lemma muterm_recursive_target_shape_check_sound:
  assumes check: "muterm_recursive_target_shape_check P B"
  shows "(\<forall>(l,r)\<in>set P. is_Var r \<or> (\<exists>f ts.
      r = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
      (\<forall>i<length ts. unmarked_term (ts ! i)))) \<and>
    (\<forall>(a,b)\<in>set B. \<exists>f ts.
      b = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
      (\<forall>i<length ts. unmarked_term (ts ! i)))"
proof
  from check have pc: "\<forall>lr\<in>set P. (case snd lr of
        Var x \<Rightarrow> True
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False))"
    unfolding muterm_recursive_target_shape_check_def list_all_iff by blast
  show "\<forall>(l,r)\<in>set P. is_Var r \<or> (\<exists>f ts.
      r = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
      (\<forall>i<length ts. unmarked_term (ts ! i)))"
  proof (intro ballI)
    fix dp
    assume dp: "dp \<in> set P"
    obtain l r where dp_pair: "dp = (l,r)" by (cases dp)
    from pc[rule_format, OF dp] have raw: "case r of
        Var x \<Rightarrow> True
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False)" unfolding dp_pair by simp
    show "case dp of (l,r) \<Rightarrow> is_Var r \<or> (\<exists>f ts.
        r = Fun (Sharp f) ts \<and>
        \<not> is_sharp_lab f \<and>
        (\<forall>i<length ts. unmarked_term (ts ! i)))"
      unfolding dp_pair using raw
      by (cases r; auto simp: list_all_iff
        muterm_unmarked_term_check_sound in_set_conv_nth
        dest: nth_mem split: lab.splits)
  qed
next
  from check have bc: "\<forall>lr\<in>set B. (case snd lr of
        Var x \<Rightarrow> False
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False))"
    unfolding muterm_recursive_target_shape_check_def list_all_iff by blast
  show "\<forall>(a,b)\<in>set B. \<exists>f ts.
      b = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
      (\<forall>i<length ts. unmarked_term (ts ! i))"
  proof (intro ballI)
    fix lr
    assume lr: "lr \<in> set B"
    obtain a b where lr_pair: "lr = (a,b)" by (cases lr)
    from bc[rule_format, OF lr] have raw: "case b of
        Var x \<Rightarrow> False
      | Fun h ts \<Rightarrow> (case h of
          Sharp f \<Rightarrow> \<not> is_sharp_lab f \<and>
            list_all muterm_unmarked_term_check ts
        | _ \<Rightarrow> False)" unfolding lr_pair by simp
    show "case lr of (a,b) \<Rightarrow> \<exists>f ts.
        b = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
        (\<forall>i<length ts. unmarked_term (ts ! i))"
      unfolding lr_pair using raw
      by (cases b; auto simp: list_all_iff
        muterm_unmarked_term_check_sound in_set_conv_nth
        dest: nth_mem split: lab.splits)
  qed
qed

lemma muterm_recursive_i4_shape_check_sound:
  assumes check: "muterm_recursive_i4_shape_check P B"
  shows "(\<forall>(l,r)\<in>set P.
      mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {} \<and>
      vars_term l \<subseteq> mu_vars_term i4_mu l \<and>
      (is_Var r \<or>
       (mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {} \<and>
        vars_term r \<subseteq> mu_vars_term i4_mu r))) \<and>
    (\<forall>(a,b)\<in>set B.
      mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {} \<and>
      mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {} \<and>
      vars_term b \<subseteq> mu_vars_term i4_mu b \<and>
      mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a)"
  using check
  unfolding muterm_recursive_i4_shape_check_def
    muterm_i4_partition_check_def muterm_i4_full_check_def
  by (fastforce simp: list_all_iff set_vars_term_list split: prod.splits)

lemma muterm_recursive_pairs_safe_check_member:
  assumes check: "muterm_recursive_pairs_safe_check P B"
    and member: "lr \<in> set P"
  shows "muterm_recursive_pair_safe_check P B lr"
  using check member unfolding muterm_recursive_pairs_safe_check_def
    list_all_iff by auto

lemma muterm_recursive_pair_safe_check_sound:
  assumes check: "muterm_recursive_pair_safe_check P B (l,r)"
  shows "\<exists>k ls. l = Fun (Sharp k) ls \<and>
    i4_symbolically_covered {} l \<and>
    vars_term r \<subseteq> vars_term l \<and>
    (is_Var r \<or> (\<exists>f ts. r = Fun (Sharp f) ts \<and>
      (i4_symbolically_covered {} r \<or>
       (\<exists>i g u. i < length ts \<and> ts ! i = Fun g [u] \<and>
         i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
         \<not> defined (set Rs) (g,1) \<and>
         i4_symbolically_covered {u} r \<and>
         muterm_root_successors_select_or_block_check P B f i ts))))"
proof -
  from check obtain k ls where l: "l = Fun (Sharp k) ls"
    and lhs_symbolic: "i4_symbolically_covered {} l"
    and vars: "vars_term r \<subseteq> vars_term l"
    and target_raw: "(case r of
        Var y \<Rightarrow> True
      | Fun q ts \<Rightarrow> (case q of
          Sharp f \<Rightarrow>
            i4_symbolically_covered {} r \<or>
            list_ex (\<lambda>(i,v). case v of
                Var z \<Rightarrow> False
              | Fun g us \<Rightarrow> (case us of
                  [u] \<Rightarrow>
                    i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                    \<not> defined (set Rs) (g,1) \<and>
                    i4_symbolically_covered {u} r \<and>
                    muterm_root_successors_select_or_block_check
                      P B f i ts
                | _ \<Rightarrow> False))
              (zip [0..<length ts] ts)
        | _ \<Rightarrow> False))"
    unfolding muterm_recursive_pair_safe_check_def
    by (cases l; auto split: lab.splits)
  have target: "is_Var r \<or> (\<exists>f ts. r = Fun (Sharp f) ts \<and>
      (i4_symbolically_covered {} r \<or>
       (\<exists>i g u. i < length ts \<and> ts ! i = Fun g [u] \<and>
         i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
         \<not> defined (set Rs) (g,1) \<and>
         i4_symbolically_covered {u} r \<and>
         muterm_root_successors_select_or_block_check P B f i ts)))"
  proof (cases r)
    case (Var y)
    then show ?thesis by simp
  next
    case (Fun q ts)
    from target_raw[unfolded Fun]
    obtain f where q: "q = Sharp f" by (cases q; auto)
    from target_raw have alt: "i4_symbolically_covered {} r \<or>
        list_ex (\<lambda>(i,v). case v of
            Var z \<Rightarrow> False
          | Fun g us \<Rightarrow> (case us of
              [u] \<Rightarrow>
                i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                \<not> defined (set Rs) (g,1) \<and>
                i4_symbolically_covered {u} r \<and>
                muterm_root_successors_select_or_block_check P B f i ts
            | _ \<Rightarrow> False))
          (zip [0..<length ts] ts)"
      using target_raw unfolding Fun q
      by (simp only: term.simps lab.simps)
    from alt show ?thesis
    proof
      assume direct: "i4_symbolically_covered {} r"
      show ?thesis using Fun q direct by auto
    next
      assume listed: "list_ex (\<lambda>(i,v). case v of
            Var z \<Rightarrow> False
          | Fun g us \<Rightarrow> (case us of
              [u] \<Rightarrow>
                i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                \<not> defined (set Rs) (g,1) \<and>
                i4_symbolically_covered {u} r \<and>
                muterm_root_successors_select_or_block_check P B f i ts
            | _ \<Rightarrow> False))
          (zip [0..<length ts] ts)"
      then obtain iv where iv: "iv \<in> set (zip [0..<length ts] ts)"
        and valid: "(case iv of (i,v) \<Rightarrow> case v of
            Var z \<Rightarrow> False
          | Fun g us \<Rightarrow> (case us of
              [u] \<Rightarrow>
                i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
                \<not> defined (set Rs) (g,1) \<and>
                i4_symbolically_covered {u} r \<and>
                muterm_root_successors_select_or_block_check P B f i ts
            | _ \<Rightarrow> False))"
        unfolding list_ex_iff by blast
      obtain i v where iv_pair: "iv = (i,v)" by (cases iv)
      from iv iv_pair have i: "i < length ts" and v: "v = ts ! i"
        by (auto simp: in_set_conv_nth)
      from valid[unfolded iv_pair] obtain g u where vu: "v = Fun g [u]"
        and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
        and undef: "\<not> defined (set Rs) (g,1)"
        and symbolic: "i4_symbolically_covered {u} r"
        and successors:
          "muterm_root_successors_select_or_block_check P B f i ts"
        by (cases v; auto split: list.splits)
      show ?thesis using Fun q i v vu inactive undef symbolic successors
        by auto
    qed
  qed
  show ?thesis using l lhs_symbolic vars target by blast
qed

lemma muterm_recursive_pair_safe_check_lhs_vars:
  assumes check: "muterm_recursive_pair_safe_check P B (l,r)"
  shows "\<exists>k ls. l = Fun (Sharp k) ls \<and>
    vars_term r \<subseteq> vars_term l"
  using check
  unfolding muterm_recursive_pair_safe_check_def
  by (cases l; auto split: lab.splits)

lemma muterm_recursive_pair_safe_check_lhs:
  assumes check: "muterm_recursive_pair_safe_check P B (l,r)"
  obtains k ls where "l = Fun (Sharp k) ls"
  using check
  unfolding muterm_recursive_pair_safe_check_def
  by (cases l; auto split: lab.splits)

lemma muterm_recursive_pair_safe_check_vars:
  assumes check: "muterm_recursive_pair_safe_check P B (l,r)"
  shows "vars_term r \<subseteq> vars_term l"
  using check
  unfolding muterm_recursive_pair_safe_check_def
  by (cases l; auto split: lab.splits)

lemma muterm_recursive_bridges_safe_check_member:
  assumes check: "muterm_recursive_bridges_safe_check B"
    and member: "(a,b) \<in> set B"
  shows "vars_term b \<subseteq> vars_term a \<and>
    (i4_symbolically_covered {a} a \<or>
      (\<exists>f u. a = Fun f [u] \<and> \<not> defined (set Rs) (f,1) \<and>
        i4_symbolically_covered {u} a)) \<and>
    i4_symbolically_covered {} b"
proof -
  from check have all: "\<forall>lr\<in>set B.
      vars_term (snd lr) \<subseteq> vars_term (fst lr) \<and>
      (i4_symbolically_covered {fst lr} (fst lr) \<or>
        (case fst lr of
          Var x \<Rightarrow> False
        | Fun f ts \<Rightarrow> (case ts of
            [u] \<Rightarrow> \<not> defined (set Rs) (f,1) \<and>
              i4_symbolically_covered {u} (fst lr)
          | _ \<Rightarrow> False))) \<and>
      i4_symbolically_covered {} (snd lr)"
    unfolding muterm_recursive_bridges_safe_check_def list_all_iff .
  note raw = all[THEN bspec, OF member]
  show ?thesis using raw
    by (cases a; auto split: list.splits)
qed

lemma muterm_recursive_event_target_good:
  assumes pairs_check: "muterm_recursive_pairs_safe_check P B"
    and bridges_check: "muterm_recursive_bridges_safe_check B"
    and target_check: "muterm_recursive_target_shape_check P B"
    and good: "i4_chain_good s"
    and event: "(s,t) \<in> muterm_typed_pair_step (set P) (set B)"
  shows "i4_chain_good t"
proof -
  from muterm_recursive_target_shape_check_sound[OF target_check]
  have pair_shape: "\<And>l r. (l,r) \<in> set P \<Longrightarrow> is_Fun r \<Longrightarrow>
      \<exists>f ts. r = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
        (\<forall>i<length ts. unmarked_term (ts ! i))"
    and bridge_shape: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      \<exists>f ts. b = Fun (Sharp f) ts \<and> \<not> is_sharp_lab f \<and>
        (\<forall>i<length ts. unmarked_term (ts ! i))"
    by auto
  from event[unfolded muterm_typed_pair_step_def] show ?thesis
  proof
    assume nc: "(s,t) \<in> {(s,t). muterm_noncollapsing_rrstep (set P) s t}"
    then obtain l r \<sigma> where pair: "(l,r) \<in> set P"
      and rfun: "is_Fun r" and se: "s = l \<cdot> \<sigma>"
      and te: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by auto
    note safe = muterm_recursive_pairs_safe_check_member[OF pairs_check pair]
    from muterm_recursive_pair_safe_check_lhs[OF safe]
    obtain k ls where l: "l = Fun (Sharp k) ls" .
    have vars: "vars_term r \<subseteq> vars_term l"
      by (rule muterm_recursive_pair_safe_check_vars[OF safe])
    have subst_l: "\<And>x. x \<in> vars_term l \<Longrightarrow>
        unmarked_term (\<sigma> x)"
      by (rule i4_chain_good_marked_instance_varD[OF good l se])
    have subst_r: "\<And>x. x \<in> vars_term r \<Longrightarrow>
        unmarked_term (\<sigma> x)" using vars subst_l by blast
    from pair_shape[OF pair rfun]
    obtain f ts where r: "r = Fun (Sharp f) ts"
      and root: "\<not> is_sharp_lab f"
      and args: "\<And>i. i < length ts \<Longrightarrow>
        unmarked_term (ts ! i)" by blast
    have inst_args: "\<And>i. i < length ts \<Longrightarrow>
        unmarked_term ((ts ! i) \<cdot> \<sigma>)"
    proof -
      fix i
      assume i: "i < length ts"
      show "unmarked_term ((ts ! i) \<cdot> \<sigma>)"
      proof (rule unmarked_term_subst[OF args[OF i]])
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        have "x \<in> vars_term r" using i x unfolding r by auto
        then show "unmarked_term (\<sigma> x)" by (rule subst_r)
      qed
    qed
    show ?thesis unfolding i4_chain_good_def te r
      using root inst_args by auto
  next
    assume coll: "(s,t) \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep (set P) s x \<and> (x,t) \<in> rrstep (set B)}"
    then obtain x l y \<sigma> a b \<theta> where pair: "(l,Var y) \<in> set P"
      and se: "s = l \<cdot> \<sigma>" and hidden0: "x = \<sigma> y"
      and bridge: "(a,b) \<in> set B" and hidden1: "x = a \<cdot> \<theta>"
      and te: "t = b \<cdot> \<theta>"
      unfolding muterm_collapsing_rrstep_def rrstep_def' by auto
    note safe = muterm_recursive_pairs_safe_check_member[OF pairs_check pair]
    from muterm_recursive_pair_safe_check_lhs[OF safe]
    obtain k ls where l: "l = Fun (Sharp k) ls" .
    have vars_y: "vars_term (Var y) \<subseteq> vars_term l"
      using safe unfolding muterm_recursive_pair_safe_check_def l by simp
    have subst_l: "\<And>z. z \<in> vars_term l \<Longrightarrow>
        unmarked_term (\<sigma> z)"
      by (rule i4_chain_good_marked_instance_varD[OF good l se])
    have hidden_unmarked: "unmarked_term (a \<cdot> \<theta>)"
      using subst_l vars_y hidden0 hidden1 by auto
    from muterm_recursive_bridges_safe_check_member[
        OF bridges_check bridge]
    have vars_ba: "vars_term b \<subseteq> vars_term a" by blast
    have subst_b: "\<And>z. z \<in> vars_term b \<Longrightarrow>
        unmarked_term (\<theta> z)"
    proof -
      fix z
      assume z: "z \<in> vars_term b"
      from vars_ba z have za: "z \<in> vars_term a" by blast
      show "unmarked_term (\<theta> z)"
        by (rule unmarked_term_subst_varD[OF hidden_unmarked za])
    qed
    from bridge_shape[OF bridge]
    obtain f ts where b: "b = Fun (Sharp f) ts"
      and root: "\<not> is_sharp_lab f"
      and args: "\<And>i. i < length ts \<Longrightarrow>
        unmarked_term (ts ! i)" by blast
    have inst_args: "\<And>i. i < length ts \<Longrightarrow>
        unmarked_term ((ts ! i) \<cdot> \<theta>)"
    proof -
      fix i
      assume i: "i < length ts"
      show "unmarked_term ((ts ! i) \<cdot> \<theta>)"
      proof (rule unmarked_term_subst[OF args[OF i]])
        fix z
        assume z: "z \<in> vars_term (ts ! i)"
        have "z \<in> vars_term b" using i z unfolding b by auto
        then show "unmarked_term (\<theta> z)" by (rule subst_b)
      qed
    qed
    show ?thesis unfolding i4_chain_good_def te b
      using root inst_args by auto
  qed
qed

lemma unmarked_term_subt_at:
  assumes plain: "unmarked_term t" and p: "p \<in> poss t"
  shows "unmarked_term (t |_ p)"
proof -
  have "funas_term (t |_ p) \<subseteq> funas_term t"
    by (rule supteq_imp_funas_term_subset[OF subt_at_imp_supteq[OF p]])
  with plain show ?thesis unfolding unmarked_term_def by blast
qed

theorem finite_muterm_i4_good_typed_dpp_imp_SN_on_unmarked_innermost:
  fixes P B :: "(((('f,'l) lab),string) rules)"
  assumes defs: "{f. defined (set Rs) f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D (set Rs)
      (set P) (set B)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and pairs_check: "muterm_recursive_pairs_safe_check P B"
    and bridges_check: "muterm_recursive_bridges_safe_check B"
    and target_check: "muterm_recursive_target_shape_check P B"
    and fin: "finite_muterm_i4_good_typed_dpp (set P) (set B)"
    and plain: "unmarked_term t0"
  shows "SN_on (innermost_csstep \<mu> (set Rs)) {t0}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (innermost_csstep \<mu> (set Rs)) {t0}"
  from not_SN_imp_subt_Tinf[OF notSN]
  obtain t where subt: "t \<unlhd> t0"
    and tT: "t \<in> Tinf (innermost_csstep \<mu> (set Rs))" by blast
  have sub_plain: "unmarked_term t"
  proof -
    have "funas_term t \<subseteq> funas_term t0"
      by (rule supteq_imp_funas_term_subset[OF subt])
    with plain show ?thesis unfolding unmarked_term_def by blast
  qed
  obtain f us where sub: "t = Fun f us"
  proof (cases t)
    case (Var x)
    have full: "SN_on (csstep \<mu> (set Rs)) {Var x}"
      by (rule SN_on_csstep_Var[OF wf])
    have inner: "SN_on (innermost_csstep \<mu> (set Rs)) {Var x}"
      by (rule SN_on_subset1[OF full innermost_csstep_subset_csstep])
    from tT have not_inner:
        "\<not> SN_on (innermost_csstep \<mu> (set Rs)) {Var x}"
      unfolding Tinf_def Var by auto
    from not_inner inner have False by contradiction
    then show ?thesis by blast
  next
    case (Fun g ss)
    show ?thesis by (rule that[OF Fun])
  qed
  let ?t = t
  have hp0: "has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) ?t"
    by (rule Tinf_has_muterm_unhiding_property[OF tT])
  let ?S = "innermost_csdp_step Sharp \<mu> (set Rs)"
  let ?Q = "muterm_innermost_min_typed_pair_step
    Sharp \<mu> (set Rs) (set P) (set B)"
  let ?G = "muterm_i4_good_pair_step (set P) (set B)"
  let ?A = "?S\<^sup>* O ?G O ?S\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) t \<Longrightarrow>
    \<exists>u. has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in>
        ?S\<^sup>* O ?Q O ?S\<^sup>*"
    by (rule innermost_muterm_unhiding_relstep_min_typed[OF wf _ defs cover])
  have all_ex: "\<forall>t. \<exists>u. has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) t \<longrightarrow>
    has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in>
        ?S\<^sup>* O ?Q O ?S\<^sup>*"
    using step_ex by blast
  from choice[OF all_ex]
  obtain nxt where nxt: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) t \<Longrightarrow>
    has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) (nxt t) \<and>
      (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in>
        ?S\<^sup>* O ?Q O ?S\<^sup>*" by blast
  define ts where "ts = rec_nat ?t (\<lambda>n t. nxt t)"
  have ts_hp: "has_muterm_unhiding_property Sharp \<mu>
      (innermost_csstep \<mu> (set Rs)) (set B) (ts n)" for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp0 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps] show ?case unfolding ts_def by simp
  qed
  have ts_raw: "(sharp_term Sharp (ts n),
      sharp_term Sharp (ts (Suc n))) \<in> ?S\<^sup>* O ?Q O ?S\<^sup>*" for n
    using nxt[OF ts_hp[of n]] unfolding ts_def by simp
  define h where "h n = sharp_term Sharp (ts n)" for n
  have h0_good: "i4_chain_good (h 0)"
  proof -
    from sub_plain have root: "\<not> is_sharp_lab f"
      and args: "\<And>i. i < length us \<Longrightarrow> unmarked_term (us ! i)"
      unfolding sub unmarked_term_Fun by auto
    show ?thesis unfolding h_def ts_def sub i4_chain_good_def
      using root args by auto
  qed
  have h_good: "i4_chain_good (h n)" for n
  proof (induct n)
    case 0
    show ?case by (rule h0_good)
  next
    case (Suc n)
    from ts_raw[of n] obtain a b where pre: "(h n,a) \<in> ?S\<^sup>*"
      and event: "(a,b) \<in> ?Q"
      and post: "(b,h (Suc n)) \<in> ?S\<^sup>*"
      unfolding h_def by auto
    have a_good: "i4_chain_good a"
      by (rule i4_chain_good_innermost_steps[
        OF fresh rules_unmarked Suc.hyps pre])
    have typed: "(a,b) \<in> muterm_typed_pair_step (set P) (set B)"
      using event unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    have b_good: "i4_chain_good b"
      by (rule muterm_recursive_event_target_good[
        OF pairs_check bridges_check target_check a_good typed])
    show ?case by (rule i4_chain_good_innermost_steps[
      OF fresh rules_unmarked b_good post])
  qed
  have hstep: "(h n,h (Suc n)) \<in> ?A" for n
  proof -
    from ts_raw[of n] obtain a b where pre: "(h n,a) \<in> ?S\<^sup>*"
      and event: "(a,b) \<in> ?Q"
      and post: "(b,h (Suc n)) \<in> ?S\<^sup>*"
      unfolding h_def by auto
    have a_good: "i4_chain_good a"
      by (rule i4_chain_good_innermost_steps[
        OF fresh rules_unmarked h_good pre])
    have typed: "(a,b) \<in> muterm_typed_pair_step (set P) (set B)"
      using event unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    have b_good: "i4_chain_good b"
      by (rule muterm_recursive_event_target_good[
        OF pairs_check bridges_check target_check a_good typed])
    have good_event: "(a,b) \<in> ?G"
      unfolding muterm_i4_good_pair_step_def
      using event a_good b_good by auto
    show ?thesis using pre good_event post by auto
  qed
  have "\<not> SN ?A" unfolding SN_defs using hstep by blast
  moreover from fin have "SN_rel ?G ?S"
    unfolding finite_muterm_i4_good_typed_dpp_def .
  then have "SN ?A" unfolding SN_rel_on_def .
  ultimately show False by contradiction
qed

lemma cssteps_preserve_unmarked_term:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and source: "unmarked_term s"
    and steps: "(s,t) \<in> (csstep \<mu> (set Rs))\<^sup>*"
  shows "unmarked_term t"
  using steps source
proof (induct rule: rtrancl_induct)
  case base
  show ?case by (rule base)
next
  case (step y z)
  show ?case by (rule csstep_preserves_unmarked_term[
    OF rules_unmarked step.hyps(3)[OF step.prems] step.hyps(2)])
qed

lemma innermost_csnf_preserves_unmarked_term:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and source: "unmarked_term s"
    and sn: "SN_on (innermost_csstep \<mu> (set Rs)) {s}"
  shows "unmarked_term (innermost_csnf \<mu> (set Rs) s)"
proof -
  from innermost_csnf_from_SN[OF wf sn]
  have steps: "(s,innermost_csnf \<mu> (set Rs) s) \<in>
      (innermost_csstep \<mu> (set Rs))\<^sup>*" by blast
  have full: "(s,innermost_csnf \<mu> (set Rs) s) \<in>
      (csstep \<mu> (set Rs))\<^sup>*"
    by (rule rtrancl_mono[OF innermost_csstep_subset_csstep,
      THEN subsetD, OF steps])
  show ?thesis by (rule cssteps_preserve_unmarked_term[
    OF rules_unmarked source full])
qed

lemma csr_innermost_variants_preserve_unmarked_term:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and source: "unmarked_term s"
    and member: "u \<in> csr_innermost_variants \<mu> (set Rs) s"
  shows "unmarked_term u"
  using source member
proof (induct s arbitrary: u)
  case (Var x)
  from Var.prems(2)[unfolded csr_innermost_variants_cases]
  show ?case
  proof
    assume "u \<in> csr_innermost_variants0 \<mu> (set Rs) (Var x)"
    then show ?thesis by simp
  next
    assume normalized: "SN_on (csstep \<mu> (set Rs)) {Var x} \<and>
      (\<exists>v. v \<in> csr_innermost_variants0 \<mu> (set Rs) (Var x) \<and>
        SN_on (innermost_csstep \<mu> (set Rs)) {v} \<and>
        u = innermost_csnf \<mu> (set Rs) v)"
    then obtain v where v: "v = Var x"
      and sn: "SN_on (innermost_csstep \<mu> (set Rs)) {v}"
      and u: "u = innermost_csnf \<mu> (set Rs) v" by auto
    have plain_v: "unmarked_term v" unfolding v by simp
    show ?thesis unfolding u
      by (rule innermost_csnf_preserves_unmarked_term[
        OF rules_unmarked plain_v sn])
  qed
next
  case (Fun f ss)
  from Fun.prems(1) have root: "\<not> is_sharp_lab f"
    and all_args: "\<forall>q\<in>set ss. unmarked_term q"
    unfolding unmarked_term_Fun by auto
  have args: "\<And>i. i < length ss \<Longrightarrow> unmarked_term (ss ! i)"
    using all_args nth_mem by blast
  have base_plain: "\<And>v. v \<in>
      csr_innermost_variants0 \<mu> (set Rs) (Fun f ss) \<Longrightarrow>
      unmarked_term v"
  proof -
    fix v
    assume base: "v \<in>
      csr_innermost_variants0 \<mu> (set Rs) (Fun f ss)"
    then obtain us where v: "v = Fun f us"
      and len: "length us = length ss"
      and children: "\<And>i. i < length ss \<Longrightarrow>
        us ! i \<in> csr_innermost_variants \<mu> (set Rs) (ss ! i)"
      by auto
    have children_plain: "\<And>i. i < length us \<Longrightarrow>
        unmarked_term (us ! i)"
    proof -
      fix i
      assume i: "i < length us"
      have iss: "i < length ss" using i len by simp
      show "unmarked_term (us ! i)"
        by (rule Fun.hyps[OF nth_mem[OF iss] args[OF iss]
          children[OF iss]])
    qed
    show "unmarked_term v" unfolding v unmarked_term_Fun
      using root children_plain by (auto simp: in_set_conv_nth)
  qed
  from Fun.prems(2)[unfolded csr_innermost_variants_cases]
  show ?case
  proof
    assume base: "u \<in>
      csr_innermost_variants0 \<mu> (set Rs) (Fun f ss)"
    show ?thesis by (rule base_plain[OF base])
  next
    assume normalized: "SN_on (csstep \<mu> (set Rs)) {Fun f ss} \<and>
      (\<exists>v. v \<in>
        csr_innermost_variants0 \<mu> (set Rs) (Fun f ss) \<and>
        SN_on (innermost_csstep \<mu> (set Rs)) {v} \<and>
        u = innermost_csnf \<mu> (set Rs) v)"
    then obtain v where base: "v \<in>
        csr_innermost_variants0 \<mu> (set Rs) (Fun f ss)"
      and sn: "SN_on (innermost_csstep \<mu> (set Rs)) {v}"
      and u: "u = innermost_csnf \<mu> (set Rs) v" by blast
    show ?thesis unfolding u
      by (rule innermost_csnf_preserves_unmarked_term[
        OF rules_unmarked base_plain[OF base] sn])
  qed
qed

lemma csr_switch_selected_steps_variants_simulation_unmarked:
  assumes ortho: "csr_switch_overlay (set Rs)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and inner_plain: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (innermost_csstep \<mu> (set Rs)) {x}"
    and steps: "(s,t) \<in>
      (csr_switch_selected_step \<mu> (set Rs))\<^sup>*"
    and source_plain: "unmarked_term s"
    and member: "s' \<in> csr_innermost_variants \<mu> (set Rs) s"
  shows "\<exists>t'. t' \<in> csr_innermost_variants \<mu> (set Rs) t \<and>
    (s',t') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>* \<and>
    unmarked_term t'"
  using steps member source_plain
proof (induct rule: rtrancl_induct)
  case base
  have plain: "unmarked_term s'"
    by (rule csr_innermost_variants_preserve_unmarked_term[
      OF rules_unmarked base.prems(2) base.prems(1)])
  show ?case by (intro exI[of _ s'], use base plain in auto)
next
  case (step x y)
  from step.hyps(3)[OF step.prems(1) step.prems(2)]
  obtain x' where x'_member:
      "x' \<in> csr_innermost_variants \<mu> (set Rs) x"
    and prefix: "(s',x') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>*"
    and x'_plain: "unmarked_term x'" by blast
  have selected_full: "(s,x) \<in> (csstep \<mu> (set Rs))\<^sup>*"
  proof (rule rtrancl_mono[THEN subsetD, OF _ step.hyps(1)])
    show "csr_switch_selected_step \<mu> (set Rs) \<subseteq>
        csstep \<mu> (set Rs)"
      by (rule csr_switch_selected_step_subset)
  qed
  have x_plain: "unmarked_term x"
    by (rule cssteps_preserve_unmarked_term[
      OF rules_unmarked step.prems(2) selected_full])
  have x'_SN: "SN_on (innermost_csstep \<mu> (set Rs)) {x'}"
    by (rule inner_plain[OF x'_plain])
  from csr_switch_selected_step_variants_simulation[
      OF ortho wf step.hyps(2) x'_member x'_SN]
  obtain y' where y'_member:
      "y' \<in> csr_innermost_variants \<mu> (set Rs) y"
    and suffix: "(x',y') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>*"
    by blast
  have xy: "(x,y) \<in> csstep \<mu> (set Rs)"
    by (rule csr_switch_selected_step_subset[THEN subsetD, OF step.hyps(2)])
  have y_plain: "unmarked_term y"
    by (rule csstep_preserves_unmarked_term[
      OF rules_unmarked x_plain xy])
  have y'_plain: "unmarked_term y'"
    by (rule csr_innermost_variants_preserve_unmarked_term[
      OF rules_unmarked y_plain y'_member])
  have path: "(s',y') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>*"
    by (rule rtrancl_trans[OF prefix suffix])
  show ?case using y'_member path y'_plain by blast
qed

lemma csr_switch_block_variants_simulation_unmarked:
  assumes ortho: "csr_switch_overlay (set Rs)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and inner_plain: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (innermost_csstep \<mu> (set Rs)) {x}"
    and block: "(s,t) \<in> csr_switch_block \<mu> (set Rs)"
    and source_plain: "unmarked_term s"
    and member: "s' \<in> csr_innermost_variants \<mu> (set Rs) s"
  shows "\<exists>t'. t' \<in> csr_innermost_variants \<mu> (set Rs) t \<and>
    (s',t') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>+ \<and>
    unmarked_term t'"
proof -
  from block obtain u where selected:
      "(s,u) \<in> (csr_switch_selected_step \<mu> (set Rs))\<^sup>*"
    and minimal: "(u,t) \<in> csr_switch_minimal_step \<mu> (set Rs)"
    unfolding csr_switch_block_def by blast
  from csr_switch_selected_steps_variants_simulation_unmarked[
      OF ortho rules_unmarked inner_plain selected source_plain member]
  obtain u' where u'_member:
      "u' \<in> csr_innermost_variants \<mu> (set Rs) u"
    and prefix: "(s',u') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>*"
    and u'_plain: "unmarked_term u'" by blast
  have selected_full: "(s,u) \<in> (csstep \<mu> (set Rs))\<^sup>*"
  proof (rule rtrancl_mono[THEN subsetD, OF _ selected])
    show "csr_switch_selected_step \<mu> (set Rs) \<subseteq>
        csstep \<mu> (set Rs)"
      by (rule csr_switch_selected_step_subset)
  qed
  have u_plain: "unmarked_term u"
    by (rule cssteps_preserve_unmarked_term[
      OF rules_unmarked source_plain selected_full])
  have minimal_selected: "(u,t) \<in>
      csr_switch_selected_step \<mu> (set Rs)"
    by (rule csr_switch_minimal_step_subset_selected[THEN subsetD, OF minimal])
  have u'_SN: "SN_on (innermost_csstep \<mu> (set Rs)) {u'}"
    by (rule inner_plain[OF u'_plain])
  from csr_switch_selected_step_variants_simulation[
      OF ortho wf minimal_selected u'_member u'_SN]
  obtain t' where t'_member:
      "t' \<in> csr_innermost_variants \<mu> (set Rs) t"
    and suffix: "(u',t') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>+"
    using minimal by blast
  have ut: "(u,t) \<in> csstep \<mu> (set Rs)"
    by (rule csr_switch_selected_step_subset[THEN subsetD,
      OF minimal_selected])
  have t_plain: "unmarked_term t"
    by (rule csstep_preserves_unmarked_term[
      OF rules_unmarked u_plain ut])
  have t'_plain: "unmarked_term t'"
    by (rule csr_innermost_variants_preserve_unmarked_term[
      OF rules_unmarked t_plain t'_member])
  have path: "(s',t') \<in> (innermost_csstep \<mu> (set Rs))\<^sup>+"
    by (rule rtrancl_trancl_trancl[OF prefix suffix])
  show ?thesis using t'_member path t'_plain by blast
qed

theorem csr_switch_overlay_innermost_termination_unmarked:
  assumes ortho: "csr_switch_overlay (set Rs)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and inner_plain: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (innermost_csstep \<mu> (set Rs)) {x}"
    and source_plain: "unmarked_term s0"
  shows "SN_on (csstep \<mu> (set Rs)) {s0}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {s0}"
  let ?P = "\<lambda>(_ :: nat) t.
    \<not> SN_on (csstep \<mu> (set Rs)) {t} \<and> unmarked_term t"
  let ?Q = "\<lambda>(_ :: nat) s t.
    (s,t) \<in> csr_switch_block \<mu> (set Rs)"
  have initial: "\<exists>t. ?P 0 t" using notSN source_plain by blast
  have successor: "\<And>t n. ?P n t \<Longrightarrow>
      \<exists>u. ?P (Suc n) u \<and> ?Q n t u"
  proof -
    fix t n
    assume pt: "?P n t"
    from notSN_has_csr_switch_block_successor[OF wf conjunct1[OF pt]]
    obtain u where block: "(t,u) \<in> csr_switch_block \<mu> (set Rs)"
      and u_notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {u}" by blast
    from block obtain v where selected:
        "(t,v) \<in> (csr_switch_selected_step \<mu> (set Rs))\<^sup>*"
      and minimal: "(v,u) \<in> csr_switch_minimal_step \<mu> (set Rs)"
      unfolding csr_switch_block_def by blast
    have tv: "(t,v) \<in> (csstep \<mu> (set Rs))\<^sup>*"
    proof (rule rtrancl_mono[THEN subsetD, OF _ selected])
      show "csr_switch_selected_step \<mu> (set Rs) \<subseteq>
          csstep \<mu> (set Rs)"
        by (rule csr_switch_selected_step_subset)
    qed
    have v_plain: "unmarked_term v"
      by (rule cssteps_preserve_unmarked_term[
        OF rules_unmarked conjunct2[OF pt] tv])
    have vu: "(v,u) \<in> csstep \<mu> (set Rs)"
      by (rule csr_switch_selected_step_subset[THEN subsetD],
        rule csr_switch_minimal_step_subset_selected[THEN subsetD, OF minimal])
    have u_plain: "unmarked_term u"
      by (rule csstep_preserves_unmarked_term[
        OF rules_unmarked v_plain vu])
    show "\<exists>u. ?P (Suc n) u \<and> ?Q n t u"
      using block u_notSN u_plain by blast
  qed
  from dependent_nat_choice[OF initial successor]
  obtain ts where ts_choice:
      "\<forall>n. ?P n (ts n) \<and> ?Q n (ts n) (ts (Suc n))" ..
  have ts_plain: "\<And>n. unmarked_term (ts n)"
    using ts_choice by auto
  have blocks: "\<And>n. (ts n,ts (Suc n)) \<in>
      csr_switch_block \<mu> (set Rs)"
    using ts_choice by auto
  let ?PV = "\<lambda>n u. u \<in>
    csr_innermost_variants \<mu> (set Rs) (ts n) \<and> unmarked_term u"
  let ?QV = "\<lambda>(_ :: nat) u v.
    (u,v) \<in> (innermost_csstep \<mu> (set Rs))\<^sup>+"
  have variants_initial: "\<exists>u. ?PV 0 u"
  proof (intro exI[of _ "ts 0"] conjI)
    show "ts 0 \<in> csr_innermost_variants \<mu> (set Rs) (ts 0)"
      by (rule csr_innermost_variants_self)
    show "unmarked_term (ts 0)" by (rule ts_plain)
  qed
  have variants_successor: "\<And>u n. ?PV n u \<Longrightarrow>
      \<exists>v. ?PV (Suc n) v \<and> ?QV n u v"
  proof -
    fix u n
    assume member: "?PV n u"
    from csr_switch_block_variants_simulation_unmarked[
      OF ortho rules_unmarked inner_plain blocks[of n]
        ts_plain conjunct1[OF member]]
    show "\<exists>v. ?PV (Suc n) v \<and> ?QV n u v" by blast
  qed
  from dependent_nat_choice[OF variants_initial variants_successor]
  obtain us where us_choice:
      "\<forall>n. ?PV n (us n) \<and> ?QV n (us n) (us (Suc n))" ..
  have us_plain: "unmarked_term (us 0)" using us_choice by auto
  have us_steps: "\<And>n. (us n,us (Suc n)) \<in>
      (innermost_csstep \<mu> (set Rs))\<^sup>+"
    using us_choice by auto
  have inner0: "SN_on (innermost_csstep \<mu> (set Rs)) {us 0}"
    by (rule inner_plain[OF us_plain])
  have inner_plus: "SN_on ((innermost_csstep \<mu> (set Rs))\<^sup>+) {us 0}"
    by (rule SN_on_trancl[OF inner0])
  from inner_plus[unfolded SN_on_def]
  show False using us_steps by blast
qed

fun muterm_strip_outer_sharp :: "('f,'l) lab \<Rightarrow> ('f,'l) lab" where
  "muterm_strip_outer_sharp (Sharp f) = muterm_strip_outer_sharp f"
| "muterm_strip_outer_sharp (UnLab f) = UnLab f"
| "muterm_strip_outer_sharp (Lab f l) = Lab f l"
| "muterm_strip_outer_sharp (FunLab f ls) = FunLab f ls"

lemma muterm_strip_outer_sharp_unmarked [simp]:
  "\<not> is_sharp_lab (muterm_strip_outer_sharp f)"
  by (induct f rule: muterm_strip_outer_sharp.induct, auto)

lemma muterm_strip_outer_sharp_id [simp]:
  assumes "\<not> is_sharp_lab f"
  shows "muterm_strip_outer_sharp f = f"
  using assms by (cases f, auto)

lemma muterm_strip_outer_sharp_mu:
  assumes marked: "\<And>f n. \<mu> (Sharp f,n) = \<mu> (f,n)"
  shows "\<mu> (muterm_strip_outer_sharp f,n) = \<mu> (f,n)"
  by (induct f rule: muterm_strip_outer_sharp.induct,
      auto simp: marked)

lemma muterm_strip_term_unmarked:
  "unmarked_term (map_funs_term muterm_strip_outer_sharp t)"
  unfolding unmarked_term_def
  by (induct t, auto)

lemma muterm_strip_rule_symbols_id:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and f: "f \<in> funs_trs (set Rs)"
  shows "muterm_strip_outer_sharp f = f"
proof (rule muterm_strip_outer_sharp_id)
  from f[unfolded funs_trs_funas_trs]
  obtain fn where fn: "fn \<in> funas_trs (set Rs)" and "fst fn = f"
    by blast
  from rules_unmarked[OF fn] show "\<not> is_sharp_lab f"
    unfolding \<open>fst fn = f\<close> .
qed

lemma poss_map_funs_term [simp]:
  "poss (map_funs_term h t) = poss t"
  by (induct t, auto)

lemma subt_at_map_funs_term:
  assumes p: "p \<in> poss t"
  shows "map_funs_term h t |_ p = map_funs_term h (t |_ p)"
  using p
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  show ?case unfolding t using Cons.hyps[OF pp] i by simp
qed

lemma replace_at_map_funs_term:
  assumes p: "p \<in> poss t"
  shows "map_funs_term h (replace_at t p u) =
    replace_at (map_funs_term h t) p (map_funs_term h u)"
  using p
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  show ?case unfolding t using Cons.hyps[OF pp] i
    by (simp add: upd_conv_take_nth_drop take_map drop_map)
qed

lemma csstep_cond_strip_outer_sharp:
  assumes marked: "\<And>f n. \<mu> (Sharp f,n) = \<mu> (f,n)"
    and cond: "csstep_cond \<mu> p s"
  shows "csstep_cond \<mu> p
    (map_funs_term muterm_strip_outer_sharp s)"
proof -
  show ?thesis unfolding csstep_cond_def
  proof (intro allI impI)
    fix p1 i p2
    assume at: "p = p1 @ i # p2 \<and>
      p \<in> poss (map_funs_term muterm_strip_outer_sharp s)"
    from at have eq: "p = p1 @ i # p2" and pposs: "p \<in> poss s"
      by auto
    from cond[unfolded csstep_cond_def, rule_format, OF conjI[OF eq pposs]]
    obtain f ts where sub: "s |_ p1 = Fun f ts"
      and active: "i \<in> \<mu> (f,length ts)" by blast
    have p1poss: "p1 \<in> poss s"
      using pposs eq poss_append_poss by blast
    show "\<exists>f ts.
      map_funs_term muterm_strip_outer_sharp s |_ p1 = Fun f ts \<and>
      i \<in> \<mu> (f,length ts)"
    proof (intro exI[of _ "muterm_strip_outer_sharp f"]
        exI[of _ "map (map_funs_term muterm_strip_outer_sharp) ts"] conjI)
      show "map_funs_term muterm_strip_outer_sharp s |_ p1 =
          Fun (muterm_strip_outer_sharp f)
            (map (map_funs_term muterm_strip_outer_sharp) ts)"
        unfolding subt_at_map_funs_term[OF p1poss] sub by simp
      show "i \<in> \<mu> (muterm_strip_outer_sharp f,
          length (map (map_funs_term muterm_strip_outer_sharp) ts))"
        using active muterm_strip_outer_sharp_mu[OF marked, of f "length ts"]
        by simp
    qed
  qed
qed

lemma rstep_r_p_s_strip_outer_sharp:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and step: "(s,t) \<in> rstep_r_p_s (set Rs) lr p \<sigma>"
  shows "(map_funs_term muterm_strip_outer_sharp s,
      map_funs_term muterm_strip_outer_sharp t) \<in>
    rstep_r_p_s (set Rs) lr p
      (map_funs_subst muterm_strip_outer_sharp \<sigma>)"
proof -
  from step have p: "p \<in> poss s" and lr: "lr \<in> set Rs"
    and at: "s |_ p = fst lr \<cdot> \<sigma>"
    and t: "t = replace_at s p (snd lr \<cdot> \<sigma>)"
    unfolding rstep_r_p_s_def' by auto
  have fixed: "\<And>f. f \<in> funs_trs (set Rs) \<Longrightarrow>
      muterm_strip_outer_sharp f = f"
    by (rule muterm_strip_rule_symbols_id[OF rules_unmarked])
  have lhs: "map_funs_term muterm_strip_outer_sharp (fst lr) = fst lr"
  proof (rule funs_term_map_funs_term_id)
    fix f
    assume f: "f \<in> funs_term (fst lr)"
    show "muterm_strip_outer_sharp f = f"
      by (rule fixed, use lr f in
        \<open>auto simp: funs_trs_def funs_rule_def\<close>)
  qed
  have rhs: "map_funs_term muterm_strip_outer_sharp (snd lr) = snd lr"
  proof (rule funs_term_map_funs_term_id)
    fix f
    assume f: "f \<in> funs_term (snd lr)"
    show "muterm_strip_outer_sharp f = f"
      by (rule fixed, use lr f in
        \<open>auto simp: funs_trs_def funs_rule_def\<close>)
  qed
  have mapped_at: "map_funs_term muterm_strip_outer_sharp s |_ p =
      fst lr \<cdot> map_funs_subst muterm_strip_outer_sharp \<sigma>"
    by (simp only: subt_at_map_funs_term[OF p] at
      map_funs_subst_distrib lhs)
  have mapped_t: "map_funs_term muterm_strip_outer_sharp t =
    replace_at (map_funs_term muterm_strip_outer_sharp s) p
      (snd lr \<cdot> map_funs_subst muterm_strip_outer_sharp \<sigma>)"
    by (simp only: t replace_at_map_funs_term[OF p]
      map_funs_subst_distrib rhs)
  show ?thesis using p lr mapped_at mapped_t
    unfolding rstep_r_p_s_def' by auto
qed

lemma csstep_strip_outer_sharp:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<mu> (Sharp f,n) = \<mu> (f,n)"
    and step: "(s,t) \<in> csstep \<mu> (set Rs)"
  shows "(map_funs_term muterm_strip_outer_sharp s,
      map_funs_term muterm_strip_outer_sharp t) \<in>
    csstep \<mu> (set Rs)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s (set Rs) lr p \<sigma>"
    and cond: "csstep_cond \<mu> p s"
    unfolding csstep_def csstep_p_def by blast
  have mapped_raw: "(map_funs_term muterm_strip_outer_sharp s,
      map_funs_term muterm_strip_outer_sharp t) \<in>
    rstep_r_p_s (set Rs) lr p
      (map_funs_subst muterm_strip_outer_sharp \<sigma>)"
    by (rule rstep_r_p_s_strip_outer_sharp[OF rules_unmarked raw])
  have mapped_cond: "csstep_cond \<mu> p
      (map_funs_term muterm_strip_outer_sharp s)"
    by (rule csstep_cond_strip_outer_sharp[OF marked cond])
  show ?thesis unfolding csstep_def csstep_p_def
    using mapped_raw mapped_cond by blast
qed

theorem SN_on_unmarked_imp_SN_full_signature:
  assumes rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<mu> (Sharp f,n) = \<mu> (f,n)"
    and source_SN: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (csstep \<mu> (set Rs)) {x}"
  shows "SN (csstep \<mu> (set Rs))"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> (set Rs))"
  then obtain f where chain: "\<And>n. (f n,f (Suc n)) \<in>
      csstep \<mu> (set Rs)"
    unfolding SN_defs by blast
  define g where "g n = map_funs_term muterm_strip_outer_sharp (f n)" for n
  have g_plain: "unmarked_term (g 0)"
    unfolding g_def by (rule muterm_strip_term_unmarked)
  have g_step: "(g n,g (Suc n)) \<in> csstep \<mu> (set Rs)" for n
    unfolding g_def by (rule csstep_strip_outer_sharp[
      OF rules_unmarked marked chain])
  from source_SN[OF g_plain, unfolded SN_on_def]
  show False using g_step by blast
qed

theorem finite_muterm_i4_good_typed_dpp_imp_SN:
  fixes P B :: "(((('f,'l) lab),string) rules)"
  assumes defs: "{f. defined (set Rs) f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D (set Rs)
      (set P) (set B)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and pairs_check: "muterm_recursive_pairs_safe_check P B"
    and bridges_check: "muterm_recursive_bridges_safe_check B"
    and target_check: "muterm_recursive_target_shape_check P B"
    and overlay: "csr_switch_overlay (set Rs)"
    and marked: "\<And>f n. \<mu> (Sharp f,n) = \<mu> (f,n)"
    and fin: "finite_muterm_i4_good_typed_dpp (set P) (set B)"
  shows "SN (csstep \<mu> (set Rs))"
proof -
  have inner_plain: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (innermost_csstep \<mu> (set Rs)) {x}"
    by (rule finite_muterm_i4_good_typed_dpp_imp_SN_on_unmarked_innermost[
      OF defs cover fresh rules_unmarked pairs_check bridges_check
        target_check fin])
  have full_plain: "\<And>x. unmarked_term x \<Longrightarrow>
      SN_on (csstep \<mu> (set Rs)) {x}"
    by (rule csr_switch_overlay_innermost_termination_unmarked[
      OF overlay rules_unmarked inner_plain])
  show ?thesis by (rule SN_on_unmarked_imp_SN_full_signature[
    OF rules_unmarked marked full_plain])
qed

lemma muterm_root_successors_select_or_block_sound:
  assumes check: "muterm_root_successors_select_or_block_check P B f i ts"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and current: "r = Fun (Sharp f) ts"
    and inactive: "i < length ts \<Longrightarrow>
      i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
    and steps: "(r \<cdot> \<sigma>,s') \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) (set P) (set B)"
  shows "\<exists>us. s' = Fun (Sharp f) us \<and>
    muterm_collapsing_rrstep (set P) s' (us ! i) \<and>
    ((us ! i),t') \<in> rrstep (set B)"
proof -
  from next_event have typed: "(s',t') \<in>
      muterm_typed_pair_step (set P) (set B)"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def by auto
  from typed have cases: "muterm_noncollapsing_rrstep (set P) s' t' \<or>
      (\<exists>x. muterm_collapsing_rrstep (set P) s' x \<and>
        (x,t') \<in> rrstep (set B))"
    unfolding muterm_typed_pair_step_def by auto
  have current_shape: "r \<cdot> \<sigma> =
      Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
    unfolding current by simp
  have full_steps: "(Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<sigma>) ts),s') \<in>
      (csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    by (rule rtrancl_mono[OF innermost_csdp_step_subset_csdp_step,
      THEN subsetD, OF steps[unfolded current_shape]])
  from cssteps_Fun_undefined_root_preserved[OF wf fresh full_steps]
  obtain us where sshape: "s' = Fun (Sharp f) us"
    and us_length: "length us = length ts" by auto
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep (set P) s' t'"
    then obtain l q \<tau> where pair: "(l,q) \<in> set P"
      and qfun: "is_Fun q" and source: "s' = l \<cdot> \<tau>"
      unfolding muterm_noncollapsing_rrstep_def rrstep_def' by auto
    from check pair have valid:
      "muterm_root_pair_selects_or_ground_blocked B f i ts (l,q)"
      unfolding muterm_root_successors_select_or_block_check_def list_all_iff
      by auto
    from valid obtain g ls where l: "l = Fun (Sharp g) ls"
      unfolding muterm_root_pair_selects_or_ground_blocked_def
      by (cases l; auto split: lab.splits)
    have g: "g = f" using source sshape unfolding l by simp
    from valid qfun show ?thesis
      unfolding muterm_root_pair_selects_or_ground_blocked_def l g
      by (cases q, auto)
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep (set P) s' x \<and>
      (x,t') \<in> rrstep (set B)"
    then obtain x l y \<tau> where pair: "(l,Var y) \<in> set P"
      and source: "s' = l \<cdot> \<tau>" and x: "x = \<tau> y"
      and bridge: "(x,t') \<in> rrstep (set B)"
      unfolding muterm_collapsing_rrstep_def by auto
    have coll_x: "muterm_collapsing_rrstep (set P) s' x"
      unfolding muterm_collapsing_rrstep_def
      using pair source x by auto
    from check have valid_all: "\<forall>lr\<in>set P.
        muterm_root_pair_selects_or_ground_blocked B f i ts lr"
      unfolding muterm_root_successors_select_or_block_check_def list_all_iff .
    note valid_raw = valid_all[THEN bspec, OF pair]
    from valid_raw obtain g ls where l: "l = Fun (Sharp g) ls"
      unfolding muterm_root_pair_selects_or_ground_blocked_def
      by (cases l; auto split: lab.splits if_splits term.splits)
    have g: "g = f" using source sshape unfolding l by simp
    from valid_raw have alternatives:
      "(i < length ls \<and> ls ! i = Var y) \<or>
       (\<exists>j<length ls. j < length ts \<and>
          j \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
          ls ! j = Var y \<and> ground (ts ! j) \<and>
          muterm_no_bridge_matches B (ts ! j))"
      unfolding muterm_root_pair_selects_or_ground_blocked_def l g by simp
    from alternatives show ?thesis
    proof
      assume selected_i: "i < length ls \<and> ls ! i = Var y"
      then have il: "i < length ls" and li: "ls ! i = Var y" by auto
      have sshape: "s' = Fun (Sharp f) (map (\<lambda>u. u \<cdot> \<tau>) ls)"
        unfolding source l g by simp
      have selected: "map (\<lambda>u. u \<cdot> \<tau>) ls ! i = x"
        using il li x by simp
      show ?thesis using coll_x bridge sshape selected by auto
    next
      assume blocked: "\<exists>j<length ls. j < length ts \<and>
          j \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
          ls ! j = Var y \<and> ground (ts ! j) \<and>
          muterm_no_bridge_matches B (ts ! j)"
      then obtain j where jl: "j < length ls" and jt: "j < length ts"
        and jinactive: "j \<notin> csr_dp_root_mu \<mu>
          (Sharp f,length ts)" and lj: "ls ! j = Var y"
        and ground: "ground (ts ! j)"
        and no_match: "muterm_no_bridge_matches B (ts ! j)" by blast
      have jt_map: "j < length (map (\<lambda>u. u \<cdot> \<sigma>) ts)"
        using jt by simp
      have jinactive_map: "j \<notin> csr_dp_root_mu \<mu>
          (Sharp f,length (map (\<lambda>u. u \<cdot> \<sigma>) ts))"
        using jinactive by simp
      from i4_innermost_steps_inactive_marked_arg_preserved[
        OF fresh jt_map jinactive_map steps[unfolded current_shape]]
      obtain us where sshape: "s' = Fun (Sharp f) us"
        and same: "us ! j = map (\<lambda>u. u \<cdot> \<sigma>) ts ! j" by auto
      have next_args: "us = map (\<lambda>u. u \<cdot> \<tau>) ls"
        using source sshape unfolding l g by simp
      have selected_j: "us ! j = x" using jl lj x unfolding next_args by simp
      from bridge obtain a b \<theta> where ab: "(a,b) \<in> set B"
        and xa: "x = a \<cdot> \<theta>"
        unfolding rrstep_def' by auto
      have instantiated: "a \<cdot> \<theta> = (ts ! j) \<cdot> \<sigma>"
        using same selected_j xa jt by simp
      have mapped: "map_vars_term (\<lambda>_. undefined) (a \<cdot> \<theta>) =
          map_vars_term (\<lambda>_. undefined) ((ts ! j) \<cdot> \<sigma>)"
        using instantiated by simp
      from mapped have converted:
          "a \<cdot> (\<lambda>z. map_vars_term (\<lambda>_. undefined) (\<theta> z)) =
           (ts ! j) \<cdot> (\<lambda>z. map_vars_term (\<lambda>_. undefined) (\<sigma> z))"
        by simp
      have ground_id:
          "(ts ! j) \<cdot> (\<lambda>z. map_vars_term (\<lambda>_. undefined) (\<sigma> z)) =
           ts ! j"
        by (rule ground_subst_apply[OF ground])
      have witness: "a \<cdot> (\<lambda>z. map_vars_term (\<lambda>_. undefined) (\<theta> z)) =
          ts ! j"
        by (rule HOL.trans[OF converted ground_id])
      have "matches (ts ! j) a"
        unfolding matches_iff using witness by blast
      moreover from no_match ab have "\<not> matches (ts ! j) a"
        unfolding muterm_no_bridge_matches_def by auto
      ultimately show ?thesis by contradiction
    qed
  qed
qed

lemma i4_frozen_unary_symbolic_target_check_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>w. w \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      w \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "set B =
      set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and fresh: "\<And>h n. \<not> defined (set Rs) (Sharp h,n)"
    and rhs: "r = Fun (Sharp f) ts"
    and i: "i < length ts"
    and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
    and frozen: "ts ! i = Fun g [u]"
    and undef: "\<not> defined (set Rs) (g,1)"
    and steps: "(r \<cdot> \<sigma>,s') \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and next_event: "(s',t') \<in>
      muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) (set P) (set B)"
    and successors:
      "muterm_root_successors_select_or_block_check P B f i ts"
    and symbolic: "i4_symbolically_covered {u} r"
    and unmarked_subst: "\<And>x. x \<in> vars_term r \<Longrightarrow>
      unmarked_term (\<sigma> x)"
  shows "i4_safe r \<sigma>"
proof -
  from muterm_root_successors_select_or_block_sound[
    OF successors fresh rhs inactive steps next_event]
  obtain us where following: "s' = Fun (Sharp f) us"
    and collapsing: "muterm_collapsing_rrstep (set P) s' (us ! i)"
    and bridge: "(us ! i,t') \<in> rrstep (set B)" by blast
  show ?thesis
  proof (rule i4_frozen_unary_symbolic_target_safe[
      OF mu lift_minimal exact fresh rhs i inactive frozen undef steps
        next_event _ symbolic unmarked_subst])
    fix vs
    assume following': "s' = Fun (Sharp f) vs"
    have "vs = us" using following following' by simp
    then show "muterm_collapsing_rrstep (set P) s' (vs ! i) \<and>
        (vs ! i,t') \<in> rrstep (set B)"
      using collapsing bridge by simp
  qed
qed

theorem muterm_recursive_checks_block_safe:
  fixes m :: "((('f,'l) lab) muL)"
  assumes mu: "\<mu> = mu_of m"
    and lift_minimal: "\<And>w. w \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      w \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and exact: "set B =
      set (muterm_exact_unhiding_rules_list Sharp m D Rs)"
    and fresh: "\<And>h n. \<not> defined (set Rs) (Sharp h,n)"
    and pairs_check: "muterm_recursive_pairs_safe_check P B"
    and bridges_check: "muterm_recursive_bridges_safe_check B"
    and good: "i4_chain_good s"
    and event: "(s,t) \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) (set P) (set B)"
    and steps: "(t,s') \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and next_event: "(s',t') \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) (set P) (set B)"
  shows "i4_typed_step_safe (set P) (set B) s t"
  unfolding i4_typed_step_safe_def
proof (rule conjI)
  show "\<forall>l r \<sigma>. (l,r) \<in> set P \<longrightarrow> is_Fun r \<longrightarrow>
      s = l \<cdot> \<sigma> \<longrightarrow> t = r \<cdot> \<sigma> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
  proof (intro allI impI)
  fix l r \<sigma>
  assume pair: "(l,r) \<in> set P" and rfun: "is_Fun r"
    and se: "s = l \<cdot> \<sigma>" and te: "t = r \<cdot> \<sigma>"
  from muterm_recursive_pair_safe_check_sound[
      OF muterm_recursive_pairs_safe_check_member[OF pairs_check pair]]
  obtain k ls where l: "l = Fun (Sharp k) ls"
    and lhs_symbolic: "i4_symbolically_covered {} l"
    and vars: "vars_term r \<subseteq> vars_term l"
    and target: "is_Var r \<or> (\<exists>f ts. r = Fun (Sharp f) ts \<and>
      (i4_symbolically_covered {} r \<or>
       (\<exists>i g u. i < length ts \<and> ts ! i = Fun g [u] \<and>
         i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
         \<not> defined (set Rs) (g,1) \<and>
         i4_symbolically_covered {u} r \<and>
         muterm_root_successors_select_or_block_check P B f i ts)))"
    by blast
  have subst_l: "\<And>x. x \<in> vars_term l \<Longrightarrow>
      unmarked_term (\<sigma> x)"
    by (rule i4_chain_good_marked_instance_varD[OF good l se])
  have lsafe: "i4_safe l \<sigma>"
    by (rule i4_symbolically_covered_empty_safe[
      OF lhs_symbolic subst_l])
  have subst_r: "\<And>x. x \<in> vars_term r \<Longrightarrow>
      unmarked_term (\<sigma> x)"
    using vars subst_l by blast
  from rfun obtain q ts where r0: "r = Fun q ts" by (cases r; auto)
  from target[unfolded r0] obtain f where q: "q = Sharp f"
    by (cases q; auto)
  have r: "r = Fun (Sharp f) ts" unfolding r0 q ..
  have target_cases: "i4_symbolically_covered {} r \<or>
       (\<exists>i g u. i < length ts \<and> ts ! i = Fun g [u] \<and>
         i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
         \<not> defined (set Rs) (g,1) \<and>
         i4_symbolically_covered {u} r \<and>
         muterm_root_successors_select_or_block_check P B f i ts)"
    using target unfolding r by blast
  have rsafe: "i4_safe r \<sigma>"
  using target_cases
  proof
    assume direct: "i4_symbolically_covered {} r"
    show ?thesis by (rule i4_symbolically_covered_empty_safe[
      OF direct subst_r])
  next
    assume exceptional: "\<exists>i g u. i < length ts \<and>
        ts ! i = Fun g [u] \<and>
        i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts) \<and>
        \<not> defined (set Rs) (g,1) \<and>
        i4_symbolically_covered {u} r \<and>
        muterm_root_successors_select_or_block_check P B f i ts"
    then obtain i g u where i: "i < length ts"
      and frozen: "ts ! i = Fun g [u]"
      and inactive: "i \<notin> csr_dp_root_mu \<mu> (Sharp f,length ts)"
      and undef: "\<not> defined (set Rs) (g,1)"
      and symbolic: "i4_symbolically_covered {u} r"
      and successors:
        "muterm_root_successors_select_or_block_check P B f i ts"
      by blast
    show ?thesis
      by (rule i4_frozen_unary_symbolic_target_check_safe[
        OF mu lift_minimal exact fresh r i inactive frozen undef
          steps[unfolded te] next_event successors symbolic subst_r])
  qed
    show "i4_safe l \<sigma> \<and> i4_safe r \<sigma>" using lsafe rsafe by simp
  qed
next
  show "\<forall>l y \<sigma> a b \<theta>. (l,Var y) \<in> set P \<longrightarrow>
      (a,b) \<in> set B \<longrightarrow> s = l \<cdot> \<sigma> \<longrightarrow>
      \<sigma> y = a \<cdot> \<theta> \<longrightarrow> t = b \<cdot> \<theta> \<longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
  proof (intro allI impI)
  fix l y \<sigma> a b \<theta>
  assume pair: "(l,Var y) \<in> set P" and bridge: "(a,b) \<in> set B"
    and se: "s = l \<cdot> \<sigma>" and hidden: "\<sigma> y = a \<cdot> \<theta>"
    and te: "t = b \<cdot> \<theta>"
  have checked: "muterm_recursive_pair_safe_check P B (l,Var y)"
    by (rule muterm_recursive_pairs_safe_check_member[OF pairs_check pair])
  from checked
  obtain k ls where l: "l = Fun (Sharp k) ls"
    and lhs_symbolic: "i4_symbolically_covered {} l"
    and vars: "vars_term (Var y) \<subseteq> vars_term l"
    unfolding muterm_recursive_pair_safe_check_def
    by (cases l; auto split: lab.splits)
  have subst_l: "\<And>x. x \<in> vars_term l \<Longrightarrow>
      unmarked_term (\<sigma> x)"
    by (rule i4_chain_good_marked_instance_varD[OF good l se])
  have lsafe: "i4_safe l \<sigma>"
    by (rule i4_symbolically_covered_empty_safe[
      OF lhs_symbolic subst_l])
  have hidden_unmarked: "unmarked_term (a \<cdot> \<theta>)"
    using subst_l vars unfolding hidden[symmetric] by auto
  from muterm_recursive_bridges_safe_check_member[
      OF bridges_check bridge]
  have bridge_vars: "vars_term b \<subseteq> vars_term a"
    and source_cases: "i4_symbolically_covered {a} a \<or>
      (\<exists>f u. a = Fun f [u] \<and> \<not> defined (set Rs) (f,1) \<and>
        i4_symbolically_covered {u} a)"
    and target_symbolic: "i4_symbolically_covered {} b" by auto
  have source_subst: "\<And>z. z \<in> vars_term a \<Longrightarrow>
      unmarked_term (\<theta> z)"
    by (rule unmarked_term_subst_varD[OF hidden_unmarked])
  have target_subst: "\<And>z. z \<in> vars_term b \<Longrightarrow>
      unmarked_term (\<theta> z)"
    using bridge_vars source_subst by blast
  have collapsing: "muterm_collapsing_rrstep (set P) s (a \<cdot> \<theta>)"
    unfolding muterm_collapsing_rrstep_def using pair se hidden[symmetric] by blast
  have event_bridge: "(a \<cdot> \<theta>,t) \<in> rrstep (set B)"
    unfolding te using bridge by auto
  have safe_bridge: "i4_safe a \<theta> \<and> i4_safe b \<theta>"
  using source_cases
  proof
    assume source_symbolic: "i4_symbolically_covered {a} a"
    show ?thesis by (rule i4_exact_bridge_symbolic_safe[
      OF mu lift_minimal exact event collapsing bridge refl
        source_symbolic target_symbolic source_subst target_subst event_bridge])
  next
    assume "\<exists>f u. a = Fun f [u] \<and>
        \<not> defined (set Rs) (f,1) \<and> i4_symbolically_covered {u} a"
    then obtain f u where source: "a = Fun f [u]"
      and undef: "\<not> defined (set Rs) (f,1)"
      and source_symbolic: "i4_symbolically_covered {u} a" by blast
    show ?thesis by (rule i4_exact_bridge_unary_symbolic_safe[
      OF mu lift_minimal exact event collapsing bridge refl source undef
        source_symbolic target_symbolic source_subst target_subst event_bridge])
  qed
    show "i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
      using lsafe safe_bridge by simp
  qed
qed

lemma i4_strong_interpretation_available:
  fixes U T :: "(((('f,'l) lab),string) trs)"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> T"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
  shows True
proof -
  interpret S: muterm_i2_strong Rs \<mu> \<Delta> cn U T
  proof
    show "\<Delta> = csr_u3_delta (set Rs) U" by (rule delta)
    show "muterm_innermost_ur_closed (set Rs) U \<mu> T" by (rule closed)
    show "muterm_strongly_conservative \<mu> T" by (rule strong)
    show "U \<subseteq> T" by (rule usable_in)
    show "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l" by (rule lhs_T)
  qed
  show True by simp
qed

lemma i4_local_terminating_step_weak:
  fixes U T Rge Rgt :: "(((('f,'l) lab),string) trs)"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> U"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and source_SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s,t) \<in> csstep \<mu> (set Rs)"
    and source_unmarked: "unmarked_term s"
    and target_unmarked: "unmarked_term t"
  shows "(i4 s,i4 t) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  from closed have U_R: "U \<subseteq> set Rs"
    and U_closed: "\<forall>lr\<in>U. csr_u3_root_rules_closed (set Rs) U
      (snd lr) (mu_fun_poss \<mu> (snd lr))"
    unfolding muterm_innermost_ur_closed_def by auto
  have closed_U: "muterm_innermost_ur_closed (set Rs) U \<mu> U"
    unfolding muterm_innermost_ur_closed_def
    using U_R U_closed by auto
  interpret S: muterm_i2_strong Rs \<mu> \<Delta> cn U U
  proof
    show "\<Delta> = csr_u3_delta (set Rs) U" by (rule delta)
    show "muterm_innermost_ur_closed (set Rs) U \<mu> U" by (rule closed_U)
    show "muterm_strongly_conservative \<mu> U" by (rule strong)
    show "U \<subseteq> U" by simp
    show "\<And>l r. (l,r) \<in> U \<Longrightarrow> is_Fun l"
      by (rule lhs_T, use usable_in in blast)
  qed
  have target_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
    by (rule step_SN_on_target[OF source_SN step])
  have sim: "(old4.i2 s,old4.i2 t) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    by (rule S.i2_csstep[OF source_SN step])
  have sim_Rge_star: "(old4.i2 s,old4.i2 t) \<in> Rge\<^sup>*"
    by (rule rtrancl_mono[OF rewrite_weak, THEN subsetD, OF sim])
  have sim_Rge: "(old4.i2 s,old4.i2 t) \<in> Rge"
    using sim_Rge_star rp.refl_NS rp.trans_NS
    by (simp add: trans_refl_imp_rtrancl_id)
  have source_i4_i2: "i4 s = old4.i2 s"
    using i4_eq_i3_if_unmarked[OF source_unmarked]
      base.i3_SN_eq_i2[OF source_SN] by simp
  have target_i4_i2: "i4 t = old4.i2 t"
    using i4_eq_i3_if_unmarked[OF target_unmarked]
      base.i3_SN_eq_i2[OF target_SN] by simp
  show ?thesis using sim_Rge source_i4_i2 target_i4_i2 by simp
qed

(* COMBINED CONTEXT LIFT UNDER ACTIVE REFINEMENT
lemma i4_marked_argument_update_weak:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and i: "i < length ss"
    and len: "length us = length ss"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
    and local: "(i4 (ss ! i),i4 (us ! i)) \<in> Rge"
  shows "(i4 (Fun (Sharp f) ss),i4 (Fun (Sharp f) us)) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have update: "map i4 us = (map i4 ss)[i := i4 (us ! i)]"
  proof (rule nth_equalityI)
    show "length (map i4 us) = length ((map i4 ss)[i := i4 (us ! i)])"
      using len by simp
    fix j
    assume j: "j < length (map i4 us)"
    then have jus: "j < length us" by simp
    have jss: "j < length ss" using jus len by simp
    show "map i4 us ! j = (map i4 ss)[i := i4 (us ! i)] ! j"
    proof (cases "j=i")
      case True
      then show ?thesis using i jus by simp
    next
      case False
      have same_j: "us ! j = ss ! j" by (rule same[OF jss False])
      show ?thesis using False i jus jss same_j by simp
    qed
  qed
  have decomp: "map i4 ss = take i (map i4 ss) @
      i4 (ss ! i) # drop (Suc i) (map i4 ss)"
  proof -
    have il: "i < length (map i4 ss)" using i by simp
    from id_take_nth_drop[OF il]
    show ?thesis using i by simp
  qed
  have upd: "(map i4 ss)[i := i4 (us ! i)] =
      take i (map i4 ss) @ i4 (us ! i) # drop (Suc i) (map i4 ss)"
    by (rule upd_conv_take_nth_drop, use i in simp)
  have lifted: "(Fun (Sharp f) (map i4 ss),
      Fun (Sharp f) ((map i4 ss)[i := i4 (us ! i)])) \<in> Rge"
  proof -
    from ctxt_closed_one[OF rp.ctxt_NS local,
      of "Sharp f" "take i (map i4 ss)" "drop (Suc i) (map i4 ss)"]
    show ?thesis unfolding decomp upd .
  qed
  show ?thesis using lifted by (simp only: i4_Sharp update)
qed
END COMBINED CONTEXT LIFT UNDER ACTIVE REFINEMENT *)

lemma map_single_changed_argument:
  assumes i: "i < length ss"
    and len: "length us = length ss"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
  shows "map h us = (map h ss)[i := h (us ! i)]"
proof (rule nth_equalityI)
  show "length (map h us) = length ((map h ss)[i := h (us ! i)])"
    using len by simp
  fix j
  assume j: "j < length (map h us)"
  then have jus: "j < length us" by simp
  have jss: "j < length ss" using jus len by simp
  show "map h us ! j = (map h ss)[i := h (us ! i)] ! j"
  proof (cases "j=i")
    case True
    then show ?thesis using i jus by simp
  next
    case False
    have same_j: "us ! j = ss ! j" by (rule same[OF jss False])
    show ?thesis using False i jus jss same_j by simp
  qed
qed

lemma ctxt_closed_Fun_list_update:
  assumes closed: "ctxt.closed R"
    and i: "i < length ss"
    and local: "(ss ! i,u) \<in> R"
  shows "(Fun f ss,Fun f (ss[i := u])) \<in> R"
proof -
  have decomp: "ss = take i ss @ ss ! i # drop (Suc i) ss"
    by (rule id_take_nth_drop[OF i])
  have upd: "ss[i := u] = take i ss @ u # drop (Suc i) ss"
    by (rule upd_conv_take_nth_drop[OF i])
  have lifted: "(Fun f (take i ss @ ss ! i # drop (Suc i) ss),
      Fun f (take i ss @ u # drop (Suc i) ss)) \<in> R"
    by (rule ctxt_closed_one[OF closed local])
  show ?thesis
    apply (subst decomp)
    apply (subst upd)
    apply (rule lifted)
    done
qed

lemma i4_marked_argument_update_weak:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and i: "i < length ss"
    and len: "length us = length ss"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
    and local: "(i4 (ss ! i),i4 (us ! i)) \<in> Rge"
  shows "(i4 (Fun (Sharp f) ss),i4 (Fun (Sharp f) us)) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have update: "map i4 us = (map i4 ss)[i := i4 (us ! i)]"
    by (rule map_single_changed_argument[OF i len same])
  have lifted: "(Fun (Sharp f) (map i4 ss),
      Fun (Sharp f) ((map i4 ss)[i := i4 (us ! i)])) \<in> Rge"
    by (rule ctxt_closed_Fun_list_update[OF rp.ctxt_NS], use i local in simp_all)
  show ?thesis using lifted by (simp only: i4_Sharp update)
qed

lemma i4_marked_innermost_step_weak:
  fixes U T Rge Rgt :: "(((('f,'l) lab),string) trs)"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> U"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and marked: "\<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and source_SN: "SN_on (csdp_step Sharp \<mu> (set Rs))
      {Fun (Sharp f) ss}"
    and step: "(Fun (Sharp f) ss,v) \<in>
      innermost_csdp_step Sharp \<mu> (set Rs)"
    and source_unmarked: "\<And>i. i < length ss \<Longrightarrow>
      unmarked_term (ss ! i)"
    and target_unmarked: "\<And>i us. i < length ss \<Longrightarrow>
      (ss ! i,us) \<in> csstep \<mu> (set Rs) \<Longrightarrow>
      unmarked_term us"
  shows "(i4 (Fun (Sharp f) ss),i4 v) \<in> Rge"
proof -
  have full_step: "(Fun (Sharp f) ss,v) \<in>
      csdp_step Sharp \<mu> (set Rs)"
    using step innermost_csdp_step_subset_csdp_step by blast
  have sharp_step: "(sharp_term Sharp (Fun f ss),v) \<in>
      csdp_step Sharp \<mu> (set Rs)" using full_step by simp
  from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp sharp_step]
  obtain u where v: "v = sharp_term Sharp u"
    and nonroot: "(Fun f ss,u) \<in> csnrstep \<mu> (set Rs)" by blast
  from nonroot obtain i us where i: "i < length ss"
    and active: "i \<in> \<mu> (f,length ss)"
    and u: "u = Fun f us" and len: "length us = length ss"
    and local: "(ss ! i,us ! i) \<in> csstep \<mu> (set Rs)"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j" by (elim csnrstep_FunE, blast)
  have arg_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}"
    by (rule SN_sharp_csdp_imp_SN_active_arg[OF i active source_SN])
  have local_weak: "(i4 (ss ! i),i4 (us ! i)) \<in> Rge"
    by (rule i4_local_terminating_step_weak[OF delta closed strong usable_in
          lhs_T redpair rewrite_weak arg_SN local source_unmarked[OF i]
          target_unmarked[OF i local]])
  have lifted: "(i4 (Fun (Sharp f) ss),i4 (Fun (Sharp f) us)) \<in> Rge"
    by (rule i4_marked_argument_update_weak[OF redpair i len same local_weak])
  show ?thesis using lifted v u by simp
qed

lemma compat_redpair_rtrancl_from_SN:
  fixes I :: "'a \<Rightarrow> ('g,'w) term"
  assumes redpair: "compat_redpair_order Rgt Rge"
    and source_SN: "SN_on A {s}"
    and steps: "(s,t) \<in> A\<^sup>*"
    and one: "\<And>x y. SN_on A {x} \<Longrightarrow> (x,y) \<in> A \<Longrightarrow>
      (I x,I y) \<in> Rge"
  shows "(I s,I t) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have "(I s,I t) \<in> Rge \<and> SN_on A {t}"
    using steps source_SN
  proof (induct rule: rtrancl_induct)
    case base
    show ?case using base rp.refl_NS unfolding refl_on_def by blast
  next
    case (step y z)
    from step.hyps(3)[OF step.prems]
    have prefix: "(I s,I y) \<in> Rge" and y_SN: "SN_on A {y}" by auto
    have last: "(I y,I z) \<in> Rge" by (rule one[OF y_SN step.hyps(2)])
    have weak: "(I s,I z) \<in> Rge"
      by (rule rp.trans_NS_point[OF prefix last])
    have z_SN: "SN_on A {z}"
      by (rule step_SN_on_target[OF y_SN step.hyps(2)])
    show ?case using weak z_SN by auto
  qed
  then show ?thesis by blast
qed

lemma i4_marked_innermost_steps_weak:
  fixes U T Rge Rgt :: "(((('f,'l) lab),string) trs)"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> U"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and marked: "\<And>n. \<mu> (Sharp f,n) = \<mu> (f,n)"
    and unmarked_root: "\<not> is_sharp_lab f"
    and source_SN: "SN_on (csdp_step Sharp \<mu> (set Rs))
      {Fun (Sharp f) ss}"
    and steps: "(Fun (Sharp f) ss,v) \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and source_unmarked: "\<And>i. i < length ss \<Longrightarrow>
      unmarked_term (ss ! i)"
  shows "(i4 (Fun (Sharp f) ss),i4 v) \<in> Rge"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  have combined: "(i4 (Fun (Sharp f) ss),i4 v) \<in> Rge \<and>
      SN_on (csdp_step Sharp \<mu> (set Rs)) {v} \<and>
      (\<exists>us. v = Fun (Sharp f) us \<and> length us = length ss \<and>
        (\<forall>i<length us. unmarked_term (us ! i)))"
    using steps source_SN source_unmarked
  proof (induct rule: rtrancl_induct)
    case base
    have refl: "(i4 (Fun (Sharp f) ss),i4 (Fun (Sharp f) ss)) \<in> Rge"
      using rp.refl_NS unfolding refl_on_def by blast
    show ?case using base refl by auto
  next
    case (step y z)
    from step.hyps(3)[OF step.prems(1) step.prems(2)]
    have prefix: "(i4 (Fun (Sharp f) ss),i4 y) \<in> Rge"
      and y_SN: "SN_on (csdp_step Sharp \<mu> (set Rs)) {y}"
      and y_shape: "\<exists>us. y = Fun (Sharp f) us \<and>
        length us = length ss \<and>
        (\<forall>i<length us. unmarked_term (us ! i))" by blast+
    from y_shape obtain us where y: "y = Fun (Sharp f) us"
      and us_len: "length us = length ss"
      and us_unmarked: "\<And>i. i < length us \<Longrightarrow>
        unmarked_term (us ! i)" by blast
    have one: "(i4 y,i4 z) \<in> Rge"
      unfolding y
      apply (rule i4_marked_innermost_step_weak[
        OF delta closed strong usable_in, where Rgt=Rgt])
      subgoal for l r by (rule lhs_T)
            apply (rule redpair)
           apply (rule rewrite_weak)
          apply (rule fresh)
         apply (rule marked)
        using y_SN y apply simp
       using step.hyps(2) y apply simp
      subgoal for i by (rule us_unmarked)
      subgoal for i vs
        by (rule csstep_preserves_unmarked_term[OF rules_unmarked
              us_unmarked])
      done
    have weak: "(i4 (Fun (Sharp f) ss),i4 z) \<in> Rge"
      by (rule rp.trans_NS_point[OF prefix one])
    have yz_full: "(y,z) \<in> csdp_step Sharp \<mu> (set Rs)"
      by (rule innermost_csdp_step_subset_csdp_step[THEN subsetD,
        OF step.hyps(2)])
    have z_SN: "SN_on (csdp_step Sharp \<mu> (set Rs)) {z}"
      by (rule step_SN_on_target[OF y_SN yz_full])
    have z_shape: "\<exists>vs. z = Fun (Sharp f) vs \<and>
        length vs = length ss \<and>
        (\<forall>i<length vs. unmarked_term (vs ! i))"
    proof -
      have full_step: "(Fun (Sharp f) us,z) \<in>
          csdp_step Sharp \<mu> (set Rs)"
        using yz_full y by simp
      have sharp_step: "(sharp_term Sharp (Fun f us),z) \<in>
          csdp_step Sharp \<mu> (set Rs)" using full_step by simp
      from sharp_csdp_step_imp_csnrstep[OF wf fresh inj_Sharp sharp_step]
      obtain u where z: "z = sharp_term Sharp u"
        and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
      from nonroot obtain vs where u: "u = Fun f vs"
        and len: "length vs = length us" by (elim csnrstep_FunE, blast)
      have source_plain: "unmarked_term (Fun f us)"
      proof (unfold unmarked_term_Fun, intro conjI)
        show "\<not> is_sharp_lab f" by (rule unmarked_root)
        show "\<forall>t\<in>set us. unmarked_term t"
        proof (intro ballI)
          fix t
          assume "t \<in> set us"
          then obtain i where i: "i < length us" and t: "t = us ! i"
            unfolding in_set_conv_nth by blast
          show "unmarked_term t" unfolding t by (rule us_unmarked[OF i])
        qed
      qed
      have local_plain: "(Fun f us,u) \<in> csstep \<mu> (set Rs)"
        using nonroot unfolding csstep_root_nonroot by auto
      have target_plain: "unmarked_term u"
        by (rule csstep_preserves_unmarked_term[
          OF rules_unmarked source_plain local_plain])
      have vs_plain: "\<forall>i<length vs. unmarked_term (vs ! i)"
        using target_plain unfolding u unmarked_term_Fun by auto
      show ?thesis using z u len us_len vs_plain by auto
    qed
    show ?case using weak z_SN z_shape by blast
  qed
  then show ?thesis by blast
qed

text \<open>
  This is the finite-DPP reduction-pair theorem at the semantic boundary.
  The two look-ahead premises are intentionally about consecutive concrete
  events.  Subsequent lemmas discharge them from innermost source normality,
  usable-rule closure, and exact unhiding; they are not checker assumptions.
\<close>

theorem finite_muterm_innermost_min_typed_dpp_i4_lookahead:
  fixes P B Rgt Rge ::
    "(((('f,'l) lab),string) trs)"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and redpair: "compat_redpair_order Rgt Rge"
    and steps_good: "\<And>s t. i4_chain_good s \<Longrightarrow>
      (s,t) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* \<Longrightarrow>
      i4_chain_good t"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_source_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {}"
    and pair_target_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {}"
    and bridge_source_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {}"
    and bridge_target_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {}"
    and pair_source_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      vars_term l \<subseteq> mu_vars_term i4_mu l"
    and pair_target_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow> vars_term r \<subseteq> mu_vars_term i4_mu r"
    and bridge_target_full: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      vars_term b \<subseteq> mu_vars_term i4_mu b"
    and bridge_active: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a"
    and block_safe: "\<And>s t s' t'. i4_chain_good s \<Longrightarrow>
      (s,t) \<in> muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B \<Longrightarrow>
      (t,s') \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* \<Longrightarrow>
      (s',t') \<in> muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B \<Longrightarrow>
      i4_typed_step_safe P B s t"
    and block_steps: "\<And>s t s' t'.
      i4_chain_good t \<Longrightarrow>
      (s,t) \<in> muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B \<Longrightarrow>
      (t,s') \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* \<Longrightarrow>
      (s',t') \<in> muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B \<Longrightarrow>
      (i4 t,i4 s') \<in> Rge"
    and fin: "finite_muterm_i4_good_typed_dpp (P - Rgt) B"
  shows "finite_muterm_i4_good_typed_dpp P B"
proof -
  interpret rp: compat_redpair_order Rgt Rge by (rule redpair)
  let ?A = "innermost_csdp_step Sharp \<mu> (set Rs)"
  let ?Q = "muterm_i4_good_pair_step P B"
  let ?C = "muterm_i4_good_pair_step (P - Rgt) B"
  show ?thesis unfolding finite_muterm_i4_good_typed_dpp_def
  proof (rule SN_rel_interpreted_redpair_lookahead_invariant[
      OF redpair, where I=i4])
    fix s t
    assume event: "(s,t) \<in> ?Q"
    from event have event0: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      unfolding muterm_i4_good_pair_step_def by auto
    from event0 obtain u where t: "t = sharp_term Sharp u"
      and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
      unfolding muterm_innermost_min_typed_pair_step_def by auto
    show "SN_on ?A {t}"
      unfolding t by (rule innermost_mu_Tinf_imp_SN_sharp_innermost_csdp[
        OF wf fresh inj_Sharp uT])
  next
    fix s t
    assume event: "(s,t) \<in> ?Q"
    show "i4_chain_good t"
      using event unfolding muterm_i4_good_pair_step_def by auto
  next
    fix s t
    assume good: "i4_chain_good s" and steps: "(s,t) \<in> ?A\<^sup>*"
    show "i4_chain_good t" by (rule steps_good[OF good steps])
  next
    fix s t s' t'
    assume good: "i4_chain_good s" and source_SN: "SN_on ?A {s'}"
      and event: "(s,t) \<in> ?Q"
      and steps: "(t,s') \<in> ?A\<^sup>*" and next_event: "(s',t') \<in> ?Q"
    from event have event0: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      and event_target_good: "i4_chain_good t"
      unfolding muterm_i4_good_pair_step_def by auto
    from next_event have next_event0: "(s',t') \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      unfolding muterm_i4_good_pair_step_def by auto
    from event0 have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    have safe: "i4_typed_step_safe P B s t"
      by (rule block_safe[OF good event0 steps next_event0])
    have nc_safe: "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
      by (rule i4_typed_step_safe_noncollD[OF safe])
    have c_safe: "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
      (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
      \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
    proof -
      fix l y \<sigma> a b \<theta>
      assume pair: "(l,Var y) \<in> P" and bridge: "(a,b) \<in> B"
        and se: "s = l \<cdot> \<sigma>" and hidden: "\<sigma> y = a \<cdot> \<theta>"
        and te: "t = b \<cdot> \<theta>"
      show "i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
        by (rule i4_typed_step_safe_collD[OF safe pair bridge se hidden te])
    qed
    have pair_fact: "(i4 s,i4 t) \<in> Rgt \<union> Rge \<and>
        ((i4 s,i4 t) \<notin> Rgt \<longrightarrow>
          (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
    proof (rule i4_typed_pair_redpair_order[
        OF redpair pairs_order bridges_order pair_source_partition
          pair_target_partition bridge_source_partition bridge_target_partition
          pair_source_full pair_target_full bridge_target_full bridge_active])
      show "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
        s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
        i4_safe l \<sigma> \<and> i4_safe r \<sigma>" by (rule nc_safe)
      show "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
        (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
        \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
        i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
        by (rule c_safe)
      show "(s,t) \<in> muterm_typed_pair_step P B" by (rule typed)
    qed
    have pair_order: "(i4 s,i4 t) \<in> Rgt \<union> Rge"
      by (rule conjunct1[OF pair_fact])
    have weak: "(i4 t,i4 s') \<in> Rge"
      by (rule block_steps[OF event_target_good event0 steps next_event0])
    show "(i4 s,i4 s') \<in> Rgt \<union> Rge"
    proof (cases "(i4 s,i4 t) \<in> Rgt")
      case True
      then show ?thesis using rp.compat_S_NS weak by auto
    next
      case False
      with pair_order have "(i4 s,i4 t) \<in> Rge" by auto
      then show ?thesis using rp.trans_NS_point weak by auto
    qed
  next
    fix s t s' t'
    assume good: "i4_chain_good s" and source_SN: "SN_on ?A {s'}"
      and event: "(s,t) \<in> ?Q"
      and steps: "(t,s') \<in> ?A\<^sup>*" and next_event: "(s',t') \<in> ?Q"
      and block_not_strict: "(i4 s,i4 s') \<notin> Rgt"
    from event have event0: "(s,t) \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      and event_good: "i4_chain_good s \<and> i4_chain_good t"
      unfolding muterm_i4_good_pair_step_def by auto
    from next_event have next_event0: "(s',t') \<in>
        muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
      unfolding muterm_i4_good_pair_step_def by auto
    from event0 have typed: "(s,t) \<in> muterm_typed_pair_step P B"
      and pair_source: "innermost_pair_source Sharp \<mu> (set Rs) s"
      and target_inv: "\<exists>u. t = sharp_term Sharp u \<and>
        u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
      unfolding muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def by auto
    have safe: "i4_typed_step_safe P B s t"
      by (rule block_safe[OF good event0 steps next_event0])
    have nc_safe: "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
      s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe r \<sigma>"
      by (rule i4_typed_step_safe_noncollD[OF safe])
    have c_safe: "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
      (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
      \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
      i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
    proof -
      fix l y \<sigma> a b \<theta>
      assume pair: "(l,Var y) \<in> P" and bridge: "(a,b) \<in> B"
        and se: "s = l \<cdot> \<sigma>" and hidden: "\<sigma> y = a \<cdot> \<theta>"
        and te: "t = b \<cdot> \<theta>"
      show "i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
        by (rule i4_typed_step_safe_collD[OF safe pair bridge se hidden te])
    qed
    have pair_fact: "(i4 s,i4 t) \<in> Rgt \<union> Rge \<and>
        ((i4 s,i4 t) \<notin> Rgt \<longrightarrow>
          (s,t) \<in> muterm_typed_pair_step (P - Rgt) B)"
    proof (rule i4_typed_pair_redpair_order[
        OF redpair pairs_order bridges_order pair_source_partition
          pair_target_partition bridge_source_partition bridge_target_partition
          pair_source_full pair_target_full bridge_target_full bridge_active])
      show "\<And>l r \<sigma>. (l,r) \<in> P \<Longrightarrow> is_Fun r \<Longrightarrow>
        s = l \<cdot> \<sigma> \<Longrightarrow> t = r \<cdot> \<sigma> \<Longrightarrow>
        i4_safe l \<sigma> \<and> i4_safe r \<sigma>" by (rule nc_safe)
      show "\<And>l y \<sigma> a b \<theta>. (l,Var y) \<in> P \<Longrightarrow>
        (a,b) \<in> B \<Longrightarrow> s = l \<cdot> \<sigma> \<Longrightarrow>
        \<sigma> y = a \<cdot> \<theta> \<Longrightarrow> t = b \<cdot> \<theta> \<Longrightarrow>
        i4_safe l \<sigma> \<and> i4_safe a \<theta> \<and> i4_safe b \<theta>"
        by (rule c_safe)
      show "(s,t) \<in> muterm_typed_pair_step P B" by (rule typed)
    qed
    have pair_order: "(i4 s,i4 t) \<in> Rgt \<union> Rge"
      by (rule conjunct1[OF pair_fact])
    have pair_residual: "(i4 s,i4 t) \<notin> Rgt \<Longrightarrow>
        (s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      by (rule conjunct2[OF pair_fact, rule_format])
    have weak: "(i4 t,i4 s') \<in> Rge"
      by (rule block_steps[OF conjunct2[OF event_good] event0 steps next_event0])
    have pair_not_strict: "(i4 s,i4 t) \<notin> Rgt"
    proof
      assume strict: "(i4 s,i4 t) \<in> Rgt"
      from rp.compat_S_NS strict weak have "(i4 s,i4 s') \<in> Rgt" by auto
      with block_not_strict show False by contradiction
    qed
    have residual: "(s,t) \<in> muterm_typed_pair_step (P - Rgt) B"
      by (rule pair_residual[OF pair_not_strict])
    show "(s,t) \<in> ?C"
      unfolding muterm_i4_good_pair_step_def
        muterm_innermost_min_typed_pair_step_def
        muterm_innermost_typed_pair_step_def
      using residual pair_source target_inv event_good by auto
  next
    show "SN_rel ?C ?A"
      using fin unfolding finite_muterm_i4_good_typed_dpp_def .
  qed
qed

theorem finite_muterm_innermost_min_typed_dpp_i4_simulated:
  fixes P B U T Rgt Rge :: "(((('f,'l) lab),string) trs)"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (Sharp g,n)"
    and lift_minimal: "\<And>u. u \<in> mu_Tinf \<mu>
      (innermost_csstep \<mu> (set Rs)) \<Longrightarrow>
      u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    and delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> U"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
    and redpair: "compat_redpair_order Rgt Rge"
    and rewrite_weak: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> Rge"
    and rules_unmarked: "\<And>fn. fn \<in> funas_trs (set Rs) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      \<mu> (Sharp f,n) = \<mu> (f,n)"
    and pairs_order: "P \<subseteq> Rgt \<union> Rge"
    and bridges_order: "B \<subseteq> Rge"
    and pair_source_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      mu_vars_term i4_mu l \<inter> non_mu_vars_term i4_mu l = {}"
    and pair_target_partition: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      mu_vars_term i4_mu r \<inter> non_mu_vars_term i4_mu r = {}"
    and bridge_source_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu a \<inter> non_mu_vars_term i4_mu a = {}"
    and bridge_target_partition: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<inter> non_mu_vars_term i4_mu b = {}"
    and pair_source_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      vars_term l \<subseteq> mu_vars_term i4_mu l"
    and pair_target_full: "\<And>l r. (l,r) \<in> P \<Longrightarrow>
      is_Fun r \<Longrightarrow> vars_term r \<subseteq> mu_vars_term i4_mu r"
    and bridge_target_full: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      vars_term b \<subseteq> mu_vars_term i4_mu b"
    and bridge_active: "\<And>a b. (a,b) \<in> B \<Longrightarrow>
      mu_vars_term i4_mu b \<subseteq> mu_vars_term i4_mu a"
    and block_safe: "\<And>s t s' t'. i4_chain_good s \<Longrightarrow>
      (s,t) \<in> muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) P B \<Longrightarrow>
      (t,s') \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* \<Longrightarrow>
      (s',t') \<in> muterm_innermost_min_typed_pair_step
        Sharp \<mu> (set Rs) P B \<Longrightarrow>
      i4_typed_step_safe P B s t"
    and fin: "finite_muterm_i4_good_typed_dpp (P - Rgt) B"
  shows "finite_muterm_i4_good_typed_dpp P B"
proof -
  have steps_good': "\<And>s t. i4_chain_good s \<Longrightarrow>
      (s,t) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* \<Longrightarrow>
      i4_chain_good t"
    by (rule i4_chain_good_innermost_steps[OF fresh rules_unmarked])
  show ?thesis
  proof (rule finite_muterm_innermost_min_typed_dpp_i4_lookahead[
    OF fresh redpair steps_good' pairs_order bridges_order pair_source_partition
      pair_target_partition bridge_source_partition bridge_target_partition
      pair_source_full pair_target_full bridge_target_full bridge_active
      block_safe])
  fix s t s' t'
  assume target_good: "i4_chain_good t"
    and event: "(s,t) \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) P B"
    and steps: "(t,s') \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and next_event: "(s',t') \<in> muterm_innermost_min_typed_pair_step
      Sharp \<mu> (set Rs) P B"
  from target_good obtain f ss where t: "t = Fun (Sharp f) ss"
    and root: "\<not> is_sharp_lab f"
    and args: "\<And>i. i < length ss \<Longrightarrow> unmarked_term (ss ! i)"
    unfolding i4_chain_good_def by blast
  from event obtain u where target: "t = sharp_term Sharp u"
    and uT: "u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
    unfolding muterm_innermost_min_typed_pair_step_def by auto
  have full_uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> (set Rs))"
    by (rule lift_minimal[OF uT])
  have target_SN: "SN_on (csdp_step Sharp \<mu> (set Rs)) {t}"
    unfolding target by (rule mu_Tinf_imp_SN_sharp_csdp[
      OF wf fresh full_uT])
  show "(i4 t,i4 s') \<in> Rge" unfolding t
    apply (rule i4_marked_innermost_steps_weak[
      OF delta closed strong usable_in, where Rgt=Rgt])
    subgoal for l r by (rule lhs_T)
             apply (rule redpair)
            apply (rule rewrite_weak)
    subgoal for fn by (rule rules_unmarked)
          apply (rule fresh)
         apply (rule marked[OF root])
        apply (rule root)
       using target_SN t apply simp
      using steps t apply simp
    subgoal for i using args[of i] by blast
    done
next
  show "finite_muterm_i4_good_typed_dpp (P - Rgt) B" by (rule fin)
qed
qed

definition muterm_recursive_rta08_ur_redpair_proc where
  "muterm_recursive_rta08_ur_redpair_proc J m rp Premove U B dpp =
    check_return (do {
      rel_impl_redpair rp;
      let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
      let T = dpp_ops.pairs J dpp @ B @ U;
      check (muterm_innermost_ur_closed_check
          (dpp_ops.rules J dpp) U m T)
        (showsl_lit (STR ''recursive MU-TERM usable-rule closure failed''));
      check (muterm_strongly_conservative_check m U)
        (showsl_lit (STR ''recursive MU-TERM strong-conservativity check failed''));
      check (list_all (is_Fun \<circ> fst) T)
        (showsl_lit (STR ''recursive MU-TERM rule has a variable left-hand side''));
      check (muterm_recursive_pairs_safe_check (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM pair safety check failed''));
      check (muterm_recursive_bridges_safe_check B)
        (showsl_lit (STR ''recursive MU-TERM unhiding safety check failed''));
      check (muterm_recursive_target_shape_check (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM target-shape check failed''));
      check (muterm_recursive_i4_shape_check (dpp_ops.pairs J dpp) B)
        (showsl_lit (STR ''recursive MU-TERM interpretation-shape check failed''));
      check (muterm_marked_mu_equal_check m)
        (showsl_lit (STR ''marked replacement-map entries differ from source symbols''));
      rel_impl.ce_compat rp;
      rel_impl_ns rp (U @ B @ pns)
        <+? (\<lambda>s. showsl_lit
          (STR ''problem weakly orienting recursive MU-TERM rules, unhiding rules, or pairs\<newline>'' ) \<circ> s);
      rel_impl_s rp ps
        <+? (\<lambda>s. showsl_lit
          (STR ''problem strictly orienting recursive MU-TERM pairs\<newline>'' ) \<circ> s)
    }) (dpp_spec.delete_pairs J dpp Premove)"

lemma muterm_i4_good_relto_witness:
  assumes step: "(s,t) \<in>
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* O
      muterm_i4_good_pair_step P B O
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>* \<and>
    (s,t) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>* O
      muterm_i4_good_pair_step {(l,r)} B O
      (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
proof -
  from step obtain a b where
    pre: "(s,a) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    and event: "(a,b) \<in> muterm_i4_good_pair_step P B"
    and post: "(b,t) \<in> (innermost_csdp_step Sharp \<mu> (set Rs))\<^sup>*"
    by auto
  from event have min_event: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) P B"
    and good_a: "i4_chain_good a" and good_b: "i4_chain_good b"
    unfolding muterm_i4_good_pair_step_def by auto
  from min_event have typed: "(a,b) \<in> muterm_typed_pair_step P B"
    and source: "innermost_pair_source Sharp \<mu> (set Rs) a"
    and target_inv: "\<exists>u. b = sharp_term Sharp u \<and>
      u \<in> mu_Tinf \<mu> (innermost_csstep \<mu> (set Rs))"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def by auto
  have cs_sub: "csdp_step Sharp \<mu> (set Rs) \<subseteq>
      csdp_step Sharp \<mu> (set Rs \<union> B)"
  proof
    fix st
    assume member: "st \<in> csdp_step Sharp \<mu> (set Rs)"
    then obtain x y p lr \<tau> where st: "st = (x,y)"
      and cond: "csdp_step_cond Sharp \<mu> p x"
      and raw: "(x,y) \<in> rstep_r_p_s (set Rs) lr p \<tau>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lr: "lr \<in> set Rs"
      unfolding rstep_r_p_s_def Let_def by auto
    have raw': "(x,y) \<in> rstep_r_p_s (set Rs \<union> B) lr p \<tau>"
      using raw lr unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (set Rs \<union> B)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have base_sub: "innermost_csdp_step Sharp \<mu> (set Rs) \<subseteq>
      csdp_step Sharp \<mu> (set Rs \<union> B)"
    by (rule subset_trans[OF innermost_csdp_step_subset_csdp_step cs_sub])
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>*"
    using pre rtrancl_mono[OF base_sub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>*"
    using post rtrancl_mono[OF base_sub] by blast
  from typed have cases:
      "muterm_noncollapsing_rrstep P a b \<or>
       (\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep B)"
    unfolding muterm_typed_pair_step_def by blast
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P a b"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P"
      and rfun: "\<not> is_Var r" and a: "a = l \<cdot> \<sigma>"
      and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,r)} B"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
      using rfun a b by auto
    have one_inner: "(a,b) \<in>
      muterm_innermost_typed_pair_step Sharp \<mu> (set Rs) {(l,r)} B"
      unfolding muterm_innermost_typed_pair_step_def using one source by auto
    have one_min: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) {(l,r)} B"
      unfolding muterm_innermost_min_typed_pair_step_def
      using one_inner target_inv by auto
    have one_good: "(a,b) \<in> muterm_i4_good_pair_step {(l,r)} B"
      unfolding muterm_i4_good_pair_step_def
      using one_min good_a good_b by auto
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x=r in exI)
      apply (rule_tac x=\<sigma> in exI)
      using pair pre' post' pre one_good post unfolding a b by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P a x \<and>
      (x,b) \<in> rrstep B"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep B" by blast
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one_coll: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} B"
      unfolding muterm_typed_pair_step_def using one_coll bridge by auto
    have one_inner: "(a,b) \<in>
      muterm_innermost_typed_pair_step Sharp \<mu> (set Rs) {(l,Var y)} B"
      unfolding muterm_innermost_typed_pair_step_def using one source by auto
    have one_min: "(a,b) \<in>
      muterm_innermost_min_typed_pair_step Sharp \<mu> (set Rs) {(l,Var y)} B"
      unfolding muterm_innermost_min_typed_pair_step_def
      using one_inner target_inv by auto
    have one_good: "(a,b) \<in> muterm_i4_good_pair_step {(l,Var y)} B"
      unfolding muterm_i4_good_pair_step_def
      using one_min good_a good_b by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (set Rs \<union> B)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>*"
      using bridge' post' by auto
    have post_var: "(Var y \<cdot> \<sigma>,t) \<in>
        (csdp_step Sharp \<mu> (set Rs \<union> B))\<^sup>*"
      using post'' x by simp
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x="Var y" in exI)
      apply (rule_tac x=\<sigma> in exI)
      using pair pre' post_var pre one_good post unfolding a by blast
  qed
qed

end

locale muterm_i4_label = muterm_i4 Rs \<mu> \<Delta> cn
  for Rs :: "((('f::{showl,compare_order},label_type) lab),string) rules"
    and \<mu> :: "((('f,label_type) lab) \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "((('f,label_type) lab) \<times> nat) set"
    and cn :: "(('f,label_type) lab) \<times> nat"
begin

lemma check_muterm_i4_good_dep_graph_sound:
  fixes m :: "((('f,label_type) lab) muL)"
  assumes mu: "mu_of m = \<mu>"
    and check: "isOK (check_muterm_typed_dep_graph m Rs B P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_i4_good_typed_dpp (set P \<inter> set C) (set B)"
  shows "finite_muterm_i4_good_typed_dpp (set P) (set B)"
proof -
  let ?PS = "set P"
  let ?RB = "set (Rs @ B)"
  let ?S = "innermost_csdp_step Sharp \<mu> (set Rs)"
  let ?Q = "muterm_i4_good_pair_step ?PS (set B)"
  show ?thesis
    unfolding finite_muterm_i4_good_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?S\<^sup>* O ?Q O ?S\<^sup>*)"
    then obtain ch where chain: "\<And>i.
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O ?Q O ?S\<^sup>*" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?PS \<and>
      (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_i4_good_pair_step {(l,r)} (set B) O ?S\<^sup>*"
    proof
      fix i
      from muterm_i4_good_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?PS \<and>
        (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
          muterm_i4_good_pair_step {(l,r)} (set B) O ?S\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_i4_good_pair_step {(s i,r)} (set B) O ?S\<^sup>*" by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_i4_good_pair_step {(s i,t i)} (set B) O ?S\<^sup>*" by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?PS \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> (csdp_step Sharp \<mu> ?RB)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_i4_good_pair_step {(s i,t i)} (set B) O ?S\<^sup>*" by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?PS"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp \<mu> ?RB)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp \<mu> ?RB)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in> ?S\<^sup>* O
        muterm_i4_good_pair_step {(s i,t i)} (set B) O ?S\<^sup>*" by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,
        s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp \<mu> ?RB)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    have selected: "\<exists>prf Cs n. (Some prf,Cs) \<in> set edps \<and>
      (\<forall>k. (s (k+n),t (k+n)) \<in> set P \<inter> set Cs)"
    proof (rule check_muterm_typed_dep_graph_select_component[OF check])
      show "\<And>i. (s i,t i) \<in> set P" by (rule pair)
      show "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
        (csdp_step Sharp (mu_of m) (set (Rs @ B)))\<^sup>*"
        using steps unfolding mu by (simp add: set_append)
    qed
    from selected obtain p0 Cs n where mem: "(Some p0,Cs) \<in> set edps"
      and CP: "\<And>k. (s (k+n),t (k+n)) \<in> ?PS \<inter> set Cs"
      by auto
    let ?tail = "\<lambda>k. ch (k+n)"
    let ?QC = "muterm_i4_good_pair_step (?PS \<inter> set Cs) (set B)"
    have tail_step: "\<And>k. (?tail k,?tail (Suc k)) \<in>
      ?S\<^sup>* O ?QC O ?S\<^sup>*"
    proof -
      fix k
      have singleton: "{(s (k+n),t (k+n))} \<subseteq> ?PS \<inter> set Cs"
        using CP[of k] by auto
      have mono: "muterm_i4_good_pair_step
          {(s (k+n),t (k+n))} (set B) \<subseteq> ?QC"
        unfolding muterm_i4_good_pair_step_def
        using muterm_innermost_min_typed_pair_step_mono_pairs[OF singleton]
        by blast
      have inc: "?S\<^sup>* O muterm_i4_good_pair_step
          {(s (k+n),t (k+n))} (set B) O ?S\<^sup>*
        \<subseteq> ?S\<^sup>* O ?QC O ?S\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      have member: "(ch (k+n),ch (Suc (k+n))) \<in>
          ?S\<^sup>* O ?QC O ?S\<^sup>*"
        by (rule inc[THEN subsetD, OF typed[of "k+n"]])
      show "(?tail k,?tail (Suc k)) \<in> ?S\<^sup>* O ?QC O ?S\<^sup>*"
        using member by simp
    qed
    have tail_sn: "SN (?S\<^sup>* O ?QC O ?S\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_i4_good_typed_dpp_def SN_rel_on_def .
    have tail_chain: "chain (?S\<^sup>* O ?QC O ?S\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN (?S\<^sup>* O ?QC O ?S\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed

end

theorem muterm_recursive_rta08_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and m :: "((('f,'l) lab) muL)"
    and rp :: "((('f,'l) lab),string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_i4.muterm_recursive_rta08_ur_redpair_proc
      (dpp_ops.rules J dpp) (mu_of m)
      (csr_u3_delta (set (dpp_ops.rules J dpp)) (set U))
      J m rp Premove U B dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and overlay: "csr_switch_overlay (set (dpp_ops.rules J dpp))"
    and exact: "set B = set (muterm_exact_unhiding_rules_list
      Sharp m D (dpp_ops.rules J dpp))"
    and fresh: "\<And>h n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp h,n)"
    and rules_unmarked: "\<And>fn. fn \<in>
      funas_trs (set (dpp_ops.rules J dpp)) \<Longrightarrow>
      \<not> is_sharp_lab (fst fn)"
    and marked: "\<And>f n. \<not> is_sharp_lab f \<Longrightarrow>
      mu_of m (Sharp f,n) = mu_of m (f,n)"
    and fin: "muterm_i4.finite_muterm_i4_good_typed_dpp
      (dpp_ops.rules J dpp') (mu_of m)
      (set (dpp_ops.pairs J dpp')) (set B)"
  shows "muterm_i4.finite_muterm_i4_good_typed_dpp
    (dpp_ops.rules J dpp) (mu_of m)
    (set (dpp_ops.pairs J dpp)) (set B)"
proof (cases "dpp_ops.pairs J dpp = []")
  case True
  interpret E: muterm_i4 "dpp_ops.rules J dpp" "mu_of m" "{}"
      "undefined"
    by (unfold_locales, rule wf)
  have empty: "muterm_innermost_min_typed_pair_step Sharp (mu_of m)
      (set (dpp_ops.rules J dpp)) {} (set B) = {}"
    unfolding muterm_innermost_min_typed_pair_step_def
      muterm_innermost_typed_pair_step_def muterm_typed_pair_step_def
      muterm_noncollapsing_rrstep_def muterm_collapsing_rrstep_def
    by auto
  have raw: "finite_muterm_innermost_min_typed_dpp Sharp (mu_of m)
      (set (dpp_ops.rules J dpp)) {} (set B)"
    unfolding finite_muterm_innermost_min_typed_dpp_def empty
    by (rule SN_rel_empty1)
  have good: "E.finite_muterm_i4_good_typed_dpp {} (set B)"
    by (rule E.finite_muterm_innermost_min_typed_dpp_imp_i4_good[OF raw])
  show ?thesis using good True by simp
next
  case False
  interpret dpp_spec J by (rule J)
  interpret M0: muterm_i4 "rules dpp" "mu_of m"
      "csr_u3_delta (set (rules dpp)) (set U)" "undefined"
    by (unfold_locales, rule wf)
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)"
    by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  let ?T = "pairs dpp @ B @ U"
  from proc[unfolded M0.muterm_recursive_rta08_ur_redpair_proc_def
      Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and closed_check: "muterm_innermost_ur_closed_check
      (rules dpp) U m ?T"
    and strong_check: "muterm_strongly_conservative_check m U"
    and lhs_check: "list_all (is_Fun \<circ> fst) ?T"
    and pairs_check: "M0.muterm_recursive_pairs_safe_check (pairs dpp) B"
    and bridges_check: "M0.muterm_recursive_bridges_safe_check B"
    and target_check: "M0.muterm_recursive_target_shape_check (pairs dpp) B"
    and i4_check: "M0.muterm_recursive_i4_shape_check (pairs dpp) B"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp (U @ B @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ B @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST"
    by blast
  have ex_rel: "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using ex_rel by presburger
  from rel_prop strict weak subst sn standard ce
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
    and B_NS: "set B \<subseteq> NS"
    and pns_NS: "set pns \<subseteq> NS"
    and S_NS: "S \<subseteq> NS"
    and S_NS_comp: "S O NS \<subseteq> S"
    and NS_S_comp: "NS O S \<subseteq> S"
    and ctxt_NS: "ctxt.closed NS"
    and trans_NS: "trans NS"
    and refl_NS: "refl NS"
    and subst_NS: "subst.closed NS"
    and trans_S: "trans S"
    and irrefl_S: "irrefl S"
    and subst_S: "subst.closed S"
    and SN_S: "SN S"
    and ce_NS: "ce_compatible NS"
    by (auto simp: rel_impl_list)
  have redpair: "compat_redpair_order S NS" by (unfold_locales; fact)
  have orient: "set (pairs dpp) \<subseteq> S \<union> NS"
    using strict_S pns_NS unfolding ps pns by auto
  have closed: "muterm_innermost_ur_closed
      (set (rules dpp)) (set U) (mu_of m) (set ?T)"
    by (rule muterm_innermost_ur_closed_check_sound[OF closed_check])
  have strong: "muterm_strongly_conservative (mu_of m) (set U)"
    by (rule muterm_strongly_conservative_check_sound[OF strong_check])
  have usable_in: "set U \<subseteq> set ?T" by auto
  have lhs_T: "\<And>l r. (l,r) \<in> set ?T \<Longrightarrow> is_Fun l"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set ?T"
    from lhs_check have all: "\<forall>x\<in>set ?T. is_Fun (fst x)"
      by (simp add: list_all_iff)
    from all[rule_format, OF lr] show "is_Fun l" by simp
  qed
  note shape = M0.muterm_recursive_i4_shape_check_sound[OF i4_check]
  note pair_shape = conjunct1[OF shape]
  note bridge_shape = conjunct2[OF shape]
  have pair_shape_lr: "mu_vars_term M0.i4_mu l \<inter>
        non_mu_vars_term M0.i4_mu l = {} \<and>
      vars_term l \<subseteq> mu_vars_term M0.i4_mu l \<and>
      (is_Var r \<or> (mu_vars_term M0.i4_mu r \<inter>
        non_mu_vars_term M0.i4_mu r = {} \<and>
        vars_term r \<subseteq> mu_vars_term M0.i4_mu r))"
    if lr: "(l,r) \<in> set (pairs dpp)" for l r
  proof -
    have "case (l,r) of (l,r) \<Rightarrow>
      mu_vars_term M0.i4_mu l \<inter> non_mu_vars_term M0.i4_mu l = {} \<and>
      vars_term l \<subseteq> mu_vars_term M0.i4_mu l \<and>
      (is_Var r \<or> (mu_vars_term M0.i4_mu r \<inter>
        non_mu_vars_term M0.i4_mu r = {} \<and>
        vars_term r \<subseteq> mu_vars_term M0.i4_mu r))"
      using pair_shape[rule_format, OF lr] by simp
    then show ?thesis by simp
  qed
  have bridge_shape_lr: "mu_vars_term M0.i4_mu a \<inter>
        non_mu_vars_term M0.i4_mu a = {} \<and>
      mu_vars_term M0.i4_mu b \<inter> non_mu_vars_term M0.i4_mu b = {} \<and>
      vars_term b \<subseteq> mu_vars_term M0.i4_mu b \<and>
      mu_vars_term M0.i4_mu b \<subseteq> mu_vars_term M0.i4_mu a"
    if lr: "(a,b) \<in> set B" for a b
  proof -
    have "case (a,b) of (a,b) \<Rightarrow>
      mu_vars_term M0.i4_mu a \<inter> non_mu_vars_term M0.i4_mu a = {} \<and>
      mu_vars_term M0.i4_mu b \<inter> non_mu_vars_term M0.i4_mu b = {} \<and>
      vars_term b \<subseteq> mu_vars_term M0.i4_mu b \<and>
      mu_vars_term M0.i4_mu b \<subseteq> mu_vars_term M0.i4_mu a"
      using bridge_shape[rule_format, OF lr] by simp
    then show ?thesis by simp
  qed
  have pair_source_partition: "\<And>l r. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      mu_vars_term M0.i4_mu l \<inter> non_mu_vars_term M0.i4_mu l = {}"
    by (rule conjunct1[OF pair_shape_lr])
  have pair_target_partition: "\<And>l r. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      is_Fun r \<Longrightarrow>
      mu_vars_term M0.i4_mu r \<inter> non_mu_vars_term M0.i4_mu r = {}"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set (pairs dpp)" and rfun: "is_Fun r"
    from pair_shape_lr[OF lr] have disj: "is_Var r \<or>
      (mu_vars_term M0.i4_mu r \<inter> non_mu_vars_term M0.i4_mu r = {} \<and>
       vars_term r \<subseteq> mu_vars_term M0.i4_mu r)" by blast
    show "mu_vars_term M0.i4_mu r \<inter>
      non_mu_vars_term M0.i4_mu r = {}" using disj rfun by (cases r; auto)
  qed
  have bridge_source_partition: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      mu_vars_term M0.i4_mu a \<inter> non_mu_vars_term M0.i4_mu a = {}"
    by (rule conjunct1[OF bridge_shape_lr])
  have bridge_target_partition: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      mu_vars_term M0.i4_mu b \<inter> non_mu_vars_term M0.i4_mu b = {}"
    by (rule conjunct1[OF conjunct2[OF bridge_shape_lr]])
  have pair_source_full: "\<And>l r. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      vars_term l \<subseteq> mu_vars_term M0.i4_mu l"
    by (rule conjunct1[OF conjunct2[OF pair_shape_lr]])
  have pair_target_full: "\<And>l r. (l,r) \<in> set (pairs dpp) \<Longrightarrow>
      is_Fun r \<Longrightarrow> vars_term r \<subseteq> mu_vars_term M0.i4_mu r"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set (pairs dpp)" and rfun: "is_Fun r"
    from pair_shape_lr[OF lr] have disj: "is_Var r \<or>
      (mu_vars_term M0.i4_mu r \<inter> non_mu_vars_term M0.i4_mu r = {} \<and>
       vars_term r \<subseteq> mu_vars_term M0.i4_mu r)" by blast
    show "vars_term r \<subseteq> mu_vars_term M0.i4_mu r"
      using disj rfun by (cases r; auto)
  qed
  have bridge_target_full: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      vars_term b \<subseteq> mu_vars_term M0.i4_mu b"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF bridge_shape_lr]]])
  have bridge_active: "\<And>a b. (a,b) \<in> set B \<Longrightarrow>
      mu_vars_term M0.i4_mu b \<subseteq> mu_vars_term M0.i4_mu a"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF bridge_shape_lr]]])
  obtain n where ce_bound: "\<And>c k. k \<ge> n \<Longrightarrow>
      ce_trs (c,k) \<subseteq> NS"
  proof (rule ce_compatibleE[OF ce_NS])
    fix n
    assume bound: "\<And>c k. k \<ge> n \<Longrightarrow> ce_trs (c,k) \<subseteq> NS"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(undefined,n)"
  have ce_weak: "ce_trs ?cn \<subseteq> NS" by (rule ce_bound, simp)
  interpret M: muterm_i4 "rules dpp" "mu_of m"
      "csr_u3_delta (set (rules dpp)) (set U)" ?cn
    by (unfold_locales, rule wf)
  have rewrite_weak: "csstep (mu_of m)
      (set U \<union> ce_trs ?cn) \<subseteq> NS"
  proof -
    interpret O: compat_redpair_order S NS by (rule redpair)
    have rules: "set U \<union> ce_trs ?cn \<subseteq> NS"
      using U_NS ce_weak by auto
    show ?thesis by (rule subset_trans[OF csstep_subset_rstep
      subset_trans[OF rstep_mono[OF rules] O.rstep_NS]])
  qed
  have lift_minimal: "\<And>w. w \<in> mu_Tinf (mu_of m)
      (innermost_csstep (mu_of m) (set (rules dpp))) \<Longrightarrow>
      w \<in> mu_Tinf (mu_of m) (csstep (mu_of m) (set (rules dpp)))"
    by (rule mu_Tinf_innermost_imp_mu_Tinf[OF overlay wf])
  have block_safe: "\<And>s t s' t'. M.i4_chain_good s \<Longrightarrow>
      (s,t) \<in> muterm_innermost_min_typed_pair_step Sharp (mu_of m)
        (set (rules dpp)) (set (pairs dpp)) (set B) \<Longrightarrow>
      (t,s') \<in> (innermost_csdp_step Sharp (mu_of m)
        (set (rules dpp)))\<^sup>* \<Longrightarrow>
      (s',t') \<in> muterm_innermost_min_typed_pair_step Sharp (mu_of m)
        (set (rules dpp)) (set (pairs dpp)) (set B) \<Longrightarrow>
      M.i4_typed_step_safe (set (pairs dpp)) (set B) s t"
    by (rule M.muterm_recursive_checks_block_safe[
      OF refl lift_minimal exact fresh pairs_check bridges_check])
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have wf': "wf_trs (set (rules dpp'))" using wf unfolding rules' .
  interpret M': muterm_i4 "rules dpp'" "mu_of m"
      "csr_u3_delta (set (rules dpp')) (set U)" ?cn
    by (unfold_locales, rule wf')
  have finM': "M'.finite_muterm_i4_good_typed_dpp
      (set (pairs dpp')) (set B)" by (rule fin)
  have fin_base: "M.finite_muterm_i4_good_typed_dpp
      (set (pairs dpp) - set Premove) (set B)"
    using finM' unfolding M'.finite_muterm_i4_good_typed_dpp_def
      M.finite_muterm_i4_good_typed_dpp_def
      M'.muterm_i4_good_pair_step_def M.muterm_i4_good_pair_step_def
      pairs' rules' by simp
  have sub: "set (pairs dpp) - S \<subseteq>
      set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have step_sub: "M.muterm_i4_good_pair_step
      (set (pairs dpp) - S) (set B) \<subseteq>
      M.muterm_i4_good_pair_step
      (set (pairs dpp) - set Premove) (set B)"
    unfolding M.muterm_i4_good_pair_step_def
    using muterm_innermost_min_typed_pair_step_mono_pairs[OF sub]
    by blast
  have fin_S: "M.finite_muterm_i4_good_typed_dpp
      (set (pairs dpp) - S) (set B)"
    unfolding M.finite_muterm_i4_good_typed_dpp_def
    by (rule SN_rel_mono[OF step_sub subset_refl
      fin_base[unfolded M.finite_muterm_i4_good_typed_dpp_def]])
  show ?thesis
    by (rule M.finite_muterm_innermost_min_typed_dpp_i4_simulated[
      OF fresh lift_minimal refl closed strong usable_in lhs_T redpair
        rewrite_weak rules_unmarked marked orient B_NS
        pair_source_partition pair_target_partition bridge_source_partition
        bridge_target_partition pair_source_full pair_target_full
        bridge_target_full bridge_active block_safe fin_S])
qed

end
