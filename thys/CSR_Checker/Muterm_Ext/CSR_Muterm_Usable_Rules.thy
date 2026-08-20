(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Muterm_Usable_Rules
  imports
    CSR_Checker_Extensions.CSR_Minimal_CSDP_Proofs
    CSR_Checker_Extensions.CSR_Innermost_DP_Checker
    CSR_Innermost_Unhiding_Proofs
    Auxx.RenamingN
    Auxx.RenamingN_String
begin

text \<open>
  MU-TERM keeps ordinary context-sensitive steps and unhiding steps in
  different components.  This is essential for the innermost framework:
  minimality/normal-form obligations concern the source rules, whereas an
  unhiding rule is a bounded bridge immediately following a dependency-pair
  step.  In particular, the bridge must not be flattened into the ordinary
  rewrite-rule component of a generic DPP.
\<close>

definition muterm_rename_many where
  "muterm_rename_many ren i = (\<lambda>v. rename_many ren (i,v))"

definition muterm_typed_pair_step where
  "muterm_typed_pair_step P S =
    {(s,t). muterm_noncollapsing_rrstep P s t} \<union>
    {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"

text \<open>
  A collapsing MU-TERM pair followed by its mandatory unhiding step is an
  ordinary root step of a composed pair.  Both input rules are renamed apart
  before composition; this is essential because variables in distinct rules
  are independent even when their printed names coincide.
\<close>

definition muterm_compose_collapsing_pair where
  "muterm_compose_collapsing_pair ren l x a b =
    (let rp = muterm_rename_many ren 0;
         rs = rename_single ren;
         l' = map_vars_term rp l;
         a' = map_vars_term rs a;
         b' = map_vars_term rs b
     in (l' \<cdot> Var(rp x := a'), b'))"

definition muterm_expanded_pairs where
  "muterm_expanded_pairs ren P S =
    {(map_vars_term (muterm_rename_many ren 0) l,
       map_vars_term (muterm_rename_many ren 0) r) | l r.
       (l,r) \<in> P \<and> \<not> is_Var r} \<union>
    {muterm_compose_collapsing_pair ren l x a b | l x a b.
       (l,Var x) \<in> P \<and> (a,b) \<in> S}"

fun muterm_expand_one_pair where
  "muterm_expand_one_pair ren S (l,Var x) =
    map (\<lambda>(a,b). muterm_compose_collapsing_pair ren l x a b) S"
| "muterm_expand_one_pair ren S (l,Fun f ts) =
    [(map_vars_term (muterm_rename_many ren 0) l,
      map_vars_term (muterm_rename_many ren 0) (Fun f ts))]"

definition muterm_expanded_pairs_list where
  "muterm_expanded_pairs_list ren P S =
    concat (map (muterm_expand_one_pair ren S) P)"

lemma set_muterm_expanded_pairs_list:
  "set (muterm_expanded_pairs_list ren P S) =
    muterm_expanded_pairs ren (set P) (set S)"
proof (rule equalityI)
  show "set (muterm_expanded_pairs_list ren P S) \<subseteq>
      muterm_expanded_pairs ren (set P) (set S)"
  proof
    fix q
    assume q: "q \<in> set (muterm_expanded_pairs_list ren P S)"
    then obtain p where p: "p \<in> set P"
      and one: "q \<in> set (muterm_expand_one_pair ren S p)"
      unfolding muterm_expanded_pairs_list_def by auto
    obtain l r where pair: "p = (l,r)" by (cases p)
    show "q \<in> muterm_expanded_pairs ren (set P) (set S)"
    proof (cases r)
      case (Var x)
      from one obtain a b where ab: "(a,b) \<in> set S"
        and qeq: "q = muterm_compose_collapsing_pair ren l x a b"
        unfolding pair Var by auto
      show ?thesis unfolding muterm_expanded_pairs_def
        using p[unfolded pair Var] ab qeq by blast
    next
      case (Fun f ts)
      from one have qeq: "q =
          (map_vars_term (muterm_rename_many ren 0) l,
           map_vars_term (muterm_rename_many ren 0) r)"
        unfolding pair Fun by simp
      have mem: "(map_vars_term (muterm_rename_many ren 0) l,
          map_vars_term (muterm_rename_many ren 0) r) \<in>
          {(map_vars_term (muterm_rename_many ren 0) l,
            map_vars_term (muterm_rename_many ren 0) r) |l r.
            (l,r) \<in> set P \<and> \<not> is_Var r}"
        using p[unfolded pair] Fun by blast
      show ?thesis unfolding muterm_expanded_pairs_def qeq
        by (rule UnI1[OF mem])
    qed
  qed
next
  show "muterm_expanded_pairs ren (set P) (set S) \<subseteq>
      set (muterm_expanded_pairs_list ren P S)"
  proof
    fix q
    assume q: "q \<in> muterm_expanded_pairs ren (set P) (set S)"
    from q show "q \<in> set (muterm_expanded_pairs_list ren P S)"
      unfolding muterm_expanded_pairs_def
    proof
      assume nc: "q \<in> {(map_vars_term (muterm_rename_many ren 0) l,
          map_vars_term (muterm_rename_many ren 0) r) |l r.
          (l,r) \<in> set P \<and> \<not> is_Var r}"
      then obtain l r where lr: "(l,r) \<in> set P" and rv: "\<not> is_Var r"
        and qeq: "q = (map_vars_term (muterm_rename_many ren 0) l,
          map_vars_term (muterm_rename_many ren 0) r)" by blast
      from rv obtain f ts where r: "r = Fun f ts" by (cases r) auto
      have one: "q \<in> set (muterm_expand_one_pair ren S (l,r))"
        using qeq unfolding r by simp
      show ?thesis unfolding muterm_expanded_pairs_list_def
        using lr one by auto
    next
      assume coll: "q \<in> {muterm_compose_collapsing_pair ren l x a b |l x a b.
          (l,Var x) \<in> set P \<and> (a,b) \<in> set S}"
      then obtain l x a b where lx: "(l,Var x) \<in> set P"
        and ab: "(a,b) \<in> set S"
        and qeq: "q = muterm_compose_collapsing_pair ren l x a b" by blast
      have one: "q \<in> set (muterm_expand_one_pair ren S (l,Var x))"
        using ab qeq by auto
      have member_set: "set (muterm_expand_one_pair ren S (l,Var x)) \<in>
          set ` muterm_expand_one_pair ren S ` set P"
        using lx by blast
      show ?thesis unfolding muterm_expanded_pairs_list_def set_concat set_map
        by (rule UnionI[OF member_set one])
    qed
  qed
qed

lemma muterm_typed_pair_step_subset_expanded:
  "muterm_typed_pair_step P S \<subseteq> rrstep (muterm_expanded_pairs ren P S)"
proof
  fix st
  assume step: "st \<in> muterm_typed_pair_step P S"
  obtain s t where st: "st = (s,t)" by (cases st)
  from step[unfolded st muterm_typed_pair_step_def] show
    "st \<in> rrstep (muterm_expanded_pairs ren P S)"
  proof
    assume nc: "(s,t) \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
    then obtain l r \<sigma> where lr: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by auto
    let ?rp = "muterm_rename_many ren 0"
    define \<tau> where "\<tau> z =
      (if z \<in> range ?rp then \<sigma> (the_inv ?rp z) else Var z)" for z
    have inj: "inj ?rp"
      unfolding muterm_rename_many_def inj_def
      using renameN(1)[of ren, unfolded inj_def] by blast
    have tau: "\<tau> (?rp x) = \<sigma> x" for x
      unfolding \<tau>_def by (simp add: inj the_inv_f_f)
    have left: "map_vars_term ?rp l \<cdot> \<tau> = l \<cdot> \<sigma>"
      unfolding apply_subst_map_vars_term
      by (rule term_subst_eq, simp add: tau)
    have right: "map_vars_term ?rp r \<cdot> \<tau> = r \<cdot> \<sigma>"
      unfolding apply_subst_map_vars_term
      by (rule term_subst_eq, simp add: tau)
    have ep: "(map_vars_term ?rp l,map_vars_term ?rp r) \<in>
        muterm_expanded_pairs ren P S"
      unfolding muterm_expanded_pairs_def using lr rv by blast
    show ?thesis unfolding st s t
      by (rule rrstepI[OF ep, where \<sigma> = \<tau>], use left right in auto)
  next
    assume coll: "(s,t) \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    then obtain x where px: "muterm_collapsing_rrstep P s x"
      and xt: "(x,t) \<in> rrstep S" by auto
    from px obtain l y \<sigma> where ly: "(l,Var y) \<in> P"
      and s: "s = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by auto
    from xt obtain a b \<theta> where ab: "(a,b) \<in> S"
      and x': "x = a \<cdot> \<theta>" and t: "t = b \<cdot> \<theta>"
      unfolding rrstep_def' by auto
    let ?rp = "muterm_rename_many ren 0"
    let ?rs = "rename_single ren"
    define \<tau> where "\<tau> z =
      (if z \<in> range ?rp then \<sigma> (the_inv ?rp z)
       else if z \<in> range ?rs then \<theta> (the_inv ?rs z)
       else Var z)" for z
    have injp: "inj ?rp"
      unfolding muterm_rename_many_def inj_def
      using renameN(1)[of ren, unfolded inj_def] by blast
    have injs: "inj ?rs" using renameN(2)[of ren] .
    have disj: "range ?rp \<inter> range ?rs = {}"
      unfolding muterm_rename_many_def using renameN(3)[of ren] by blast
    have taup: "\<tau> (?rp z) = \<sigma> z" for z
      unfolding \<tau>_def by (simp add: injp the_inv_f_f)
    have taus: "\<tau> (?rs z) = \<theta> z" for z
    proof -
      have "?rs z \<notin> range ?rp" using disj by blast
      then show ?thesis unfolding \<tau>_def
        by (simp add: injs the_inv_f_f)
    qed
    have a_tau: "map_vars_term ?rs a \<cdot> \<tau> = a \<cdot> \<theta>"
      unfolding apply_subst_map_vars_term
      by (rule term_subst_eq, simp add: taus)
    have bridge_eq: "a \<cdot> \<theta> = \<sigma> y" using x x' by simp
    let ?\<rho> = "Var(?rp y := map_vars_term ?rs a)"
    have rho_tau: "(?\<rho> \<circ>\<^sub>s \<tau>) (?rp z) = \<sigma> z" for z
    proof (cases "z = y")
      case True
      show ?thesis unfolding True subst_compose_def using x x' a_tau by simp
    next
      case False
      have ne: "?rp z \<noteq> ?rp y" using False injp by (auto simp: inj_def)
      show ?thesis unfolding subst_compose_def using ne taup by simp
    qed
    have left: "(map_vars_term ?rp l \<cdot> ?\<rho>) \<cdot> \<tau> = l \<cdot> \<sigma>"
      by (induct l) (simp_all add: a_tau bridge_eq taup injp inj_eq)
    have right: "map_vars_term ?rs b \<cdot> \<tau> = b \<cdot> \<theta>"
      unfolding apply_subst_map_vars_term
      by (rule term_subst_eq, simp add: taus)
    have ep: "muterm_compose_collapsing_pair ren l y a b \<in>
        muterm_expanded_pairs ren P S"
      unfolding muterm_expanded_pairs_def using ly ab by blast
    obtain cl cr where comp:
      "muterm_compose_collapsing_pair ren l y a b = (cl,cr)"
      by (cases "muterm_compose_collapsing_pair ren l y a b") auto
    have ep': "(cl,cr) \<in> muterm_expanded_pairs ren P S"
      using ep comp by simp
    show ?thesis unfolding st s t
    proof (rule rrstepI[OF ep', where \<sigma> = \<tau>])
      show "l \<cdot> \<sigma> = cl \<cdot> \<tau>"
        using comp left unfolding muterm_compose_collapsing_pair_def Let_def by simp
      show "b \<cdot> \<theta> = cr \<cdot> \<tau>"
        using comp right unfolding muterm_compose_collapsing_pair_def Let_def by simp
    qed
  qed
qed

definition finite_muterm_typed_dpp where
  "finite_muterm_typed_dpp shp \<mu> R P S \<longleftrightarrow>
    SN_rel (muterm_typed_pair_step P S) (csdp_step shp \<mu> R)"

lemma muterm_typed_pair_step_empty[simp]:
  "muterm_typed_pair_step {} S = {}"
  unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
    muterm_collapsing_rrstep_def by auto

lemma muterm_unhiding_relstep_typed:
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and event:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have strict: "(sharp_term Sharp s,sharp_term Sharp u) \<in>
      muterm_typed_pair_step P S"
    using event unfolding muterm_typed_pair_step_def by blast
  have prefix: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref])
  show ?thesis using hp_u prefix strict by blast
qed

theorem finite_muterm_typed_dpp_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and fin: "finite_muterm_typed_dpp Sharp \<mu> R P S"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in>
          (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    by (rule muterm_unhiding_relstep_typed[OF wf _ defs cover preserving])
  have all_ex: "\<forall>t. \<exists>u.
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<longrightarrow>
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
       has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
       (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in>
         (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n)"
    for n
    by (induct n, unfold ts_def, use hp0 nxt in auto)
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "(f n,f (Suc n)) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S O
      (csdp_step Sharp \<mu> R)\<^sup>*" for n
    using nxt[OF inv[of n]] unfolding f_def ts_def by auto
  from fin have sn: "SN ((csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*)"
    unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
  moreover have "\<not> SN ((csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*)"
    unfolding SN_defs using chain by blast
  ultimately show False by contradiction
qed

text \<open>
  MU-TERM's reduction-triple processor exploits the minimality invariant of
  chains extracted from a minimal nonterminating CSR term.  Keep this
  invariant in the semantic problem instead of labelling an unrestricted DPP
  as minimal.  In particular, the target of every typed macro pair must be
  strongly normalizing for the context-sensitive DP rewrite relation.
\<close>

definition muterm_min_typed_pair_step where
  "muterm_min_typed_pair_step shp \<mu> R P S =
    muterm_typed_pair_step P S \<inter>
      {(s,t). SN_on (csdp_step shp \<mu> R) {t}}"

definition finite_muterm_min_typed_dpp where
  "finite_muterm_min_typed_dpp shp \<mu> R P S \<longleftrightarrow>
    SN_rel (muterm_min_typed_pair_step shp \<mu> R P S)
      (csdp_step shp \<mu> R)"

text \<open>
  Reduction-pair removal for the semantic typed MU-TERM problem.  Keeping this
  lemma at the typed boundary is important: the target-normality invariant is
  context-sensitive, so it must not be replaced by an ordinary minimal-DP
  flag.  Concrete usable-rule processors only have to establish the weak
  simulation and the order of the typed macro steps.
\<close>

lemma finite_muterm_min_typed_dpp_redpair:
  assumes redpair: "compat_redpair_order Rgt Rge"
    and weak: "csdp_step shp \<mu> R \<subseteq> Rge"
    and orient:
      "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq> Rgt \<union> Rge"
    and residual:
      "muterm_min_typed_pair_step shp \<mu> R P S - Rgt \<subseteq>
       muterm_min_typed_pair_step shp \<mu> R Q S"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> R Q S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
  unfolding finite_muterm_min_typed_dpp_def
  by (rule SN_rel_compat_redpair_residual[
      OF redpair weak orient residual
        fin[unfolded finite_muterm_min_typed_dpp_def]])

text \<open>
  Interpretation form of the preceding processor.  This is the reusable
  semantic seam needed by usable-rule interpretations: original
  context-sensitive rewrite and typed macro steps need only be weak/strict
  after applying the interpretation.  No assumption that the original rules
  themselves belong to the reduction pair is hidden here.
\<close>

text \<open>
  The general RTA'08 closure is already strong enough to construct the
  interpretation used for weak rewrite steps.  For a selected usable rule,
  its active right-hand-side positions are covered directly by the RTA
  closure; its inactive positions are covered by the global hidden-symbol
  seed.  Hence all right-hand-side function positions of usable rules satisfy
  the older U3 closure.  Pair right-hand sides deliberately do not: their
  treatment is the additional RTA/MU-TERM chain argument.
\<close>

lemma csr_rta08_usable_rules_closed_imp_u3_empty:
  assumes closed: "csr_rta08_usable_rules_closed R U \<mu> P"
  shows "csr_u3_usable_rules_closed R U \<mu> {}"
proof -
  from closed have sub: "U \<subseteq> R"
    and rule_lhs: "\<And>lr. lr \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U (fst lr)
        {p\<in>fun_poss (fst lr). p \<notin> mu_fun_poss \<mu> (fst lr)}"
    and rule_rhs_active: "\<And>lr. lr \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U (snd lr)
        (mu_fun_poss \<mu> (snd lr))"
    and rule_rhs_inactive: "\<And>lr. lr \<in> R \<Longrightarrow>
      csr_u3_root_rules_closed R U (snd lr)
        {p\<in>fun_poss (snd lr). p \<notin> mu_fun_poss \<mu> (snd lr)}"
    unfolding csr_rta08_usable_rules_closed_def by blast+
  have rule_rhs: "\<And>lr. lr \<in> U \<Longrightarrow>
      csr_u3_root_rules_closed R U (snd lr) (fun_poss (snd lr))"
  proof -
    fix lr
    assume lr: "lr \<in> U"
    have active: "csr_u3_root_rules_closed R U (snd lr)
        (mu_fun_poss \<mu> (snd lr))"
      by (rule rule_rhs_active[OF lr])
    have inactive: "csr_u3_root_rules_closed R U (snd lr)
        {p\<in>fun_poss (snd lr). p \<notin> mu_fun_poss \<mu> (snd lr)}"
      by (rule rule_rhs_inactive[OF sub[THEN subsetD, OF lr]])
    show "csr_u3_root_rules_closed R U (snd lr) (fun_poss (snd lr))"
      using active inactive mu_fun_poss_imp_fun_poss
      unfolding csr_u3_root_rules_closed_def by blast
  qed
  show ?thesis
    unfolding csr_u3_usable_rules_closed_def
    using sub rule_lhs rule_rhs rule_rhs_inactive by auto
qed

locale csr_rta08_i1 =
  fixes Rs :: "('f::{showl, compare_order}, 'v) rules"
    and U :: "('f, 'v) trs"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and P :: "('f, 'v) trs"
    and cn :: "'f \<times> nat"
  assumes wf: "wf_trs (set Rs)"
    and closed: "csr_rta08_usable_rules_closed (set Rs) U \<mu> P"
begin

sublocale weak: csr_u3_i1 Rs U \<mu> "{}" cn
  apply unfold_locales
   apply (rule wf)
  apply (rule csr_rta08_usable_rules_closed_imp_u3_empty[OF closed])
  done

end

lemma finite_min_csr_dpp_expanded_imp_finite_muterm_min_typed:
  assumes fin: "finite_min_csr_dpp Sharp \<mu>
      (muterm_expanded_pairs ren P S) R"
  shows "finite_muterm_min_typed_dpp Sharp \<mu> R P S"
proof -
  have strict: "muterm_min_typed_pair_step Sharp \<mu> R P S \<subseteq>
      csr_min_pair_step Sharp \<mu> (muterm_expanded_pairs ren P S) R"
    unfolding muterm_min_typed_pair_step_def csr_min_pair_step_def
    using muterm_typed_pair_step_subset_expanded[of P S ren] by blast
  show ?thesis
    unfolding finite_muterm_min_typed_dpp_def finite_min_csr_dpp_def
    by (rule SN_rel_mono[OF strict subset_refl fin[unfolded finite_min_csr_dpp_def]])
qed

text \<open>
  For the innermost branch of Theorem 21, the exact expanded MU-TERM pairs
  are a conservative strengthening of the ordinary noncollapsing
  context-sensitive dependency pairs.  This observation lets the checker
  reuse the recursive innermost CSR-DP framework (including its
  argument-filtered usable-rule processor) instead of interpreting an
  ordinary minimal-DP proof at the wrong rewrite boundary.
\<close>

lemma rrstep_mu_CSDP_on_subset_muterm_expanded:
  assumes cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
  shows "rrstep (mu_CSDP_on Sharp \<mu> D R) \<subseteq>
    rrstep (muterm_expanded_pairs ren P S)"
proof -
  have pairs: "mu_CSDP_on Sharp \<mu> D R \<subseteq> P"
    by (rule muterm_unhiding_coverage_mu[OF cover])
  have typed: "rrstep (mu_CSDP_on Sharp \<mu> D R) \<subseteq>
      muterm_typed_pair_step P S"
  proof
    fix st
    assume step: "st \<in> rrstep (mu_CSDP_on Sharp \<mu> D R)"
    obtain a b where st: "st = (a,b)" by (cases st)
    from step obtain l r \<sigma> where pair:
        "(l,r) \<in> mu_CSDP_on Sharp \<mu> D R"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding st rrstep_def' by blast
    from pair obtain l0 r0 p f ts where
      shape: "r = sharp_term Sharp (r0 |_ p)"
      and subterm: "r0 |_ p = Fun f ts"
      unfolding mu_CSDP_on_def by blast
    have nonvar: "\<not> is_Var r" unfolding shape subterm by simp
    have "muterm_noncollapsing_rrstep P a b"
      unfolding muterm_noncollapsing_rrstep_def
      using pairs pair nonvar a b by blast
    then show "st \<in> muterm_typed_pair_step P S"
      unfolding st muterm_typed_pair_step_def by blast
  qed
  show ?thesis
    by (rule subset_trans[OF typed
      muterm_typed_pair_step_subset_expanded])
qed

lemma finite_muterm_expanded_innermost_imp_finite_mu_CSDP:
  assumes cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu>
      (muterm_expanded_pairs ren P S) R"
  shows "finite_mode_csr_dpp Sharp CSR_Innermost \<mu>
    (mu_CSDP_on Sharp \<mu> D R) R"
proof -
  have pair_sub: "innermost_rrstep Sharp \<mu> R
      (mu_CSDP_on Sharp \<mu> D R) \<subseteq>
    innermost_rrstep Sharp \<mu> R (muterm_expanded_pairs ren P S)"
    using rrstep_mu_CSDP_on_subset_muterm_expanded[OF cover]
    unfolding innermost_rrstep_def by blast
  from fin have expanded: "SN_rel
      (innermost_rrstep Sharp \<mu> R (muterm_expanded_pairs ren P S))
      (innermost_csdp_step Sharp \<mu> R)"
    unfolding finite_mode_csr_dpp_def by simp
  show ?thesis unfolding finite_mode_csr_dpp_def
    csr_mode_rrstep.simps csr_mode_csdp_step.simps
    by (rule SN_rel_mono[OF pair_sub subset_refl expanded])
qed

theorem muterm_expanded_innermost_imp_SN_csstep:
  assumes overlay: "csr_switch_overlay R"
    and wf: "wf_trs R"
    and vc: "rhs_mu_vars_condition \<mu> R"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and fin: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu>
      (muterm_expanded_pairs ren P S) R"
  shows "SN (csstep \<mu> R)"
proof (rule csr_switch_overlay_innermost_termination[OF overlay wf])
  have base: "finite_mode_csr_dpp Sharp CSR_Innermost \<mu>
      (mu_CSDP_on Sharp \<mu> D R) R"
    by (rule finite_muterm_expanded_innermost_imp_finite_mu_CSDP[
      OF cover fin])
  show "SN (innermost_csstep \<mu> R)"
    by (rule finite_innermost_mu_CSDP_on_imp_SN[OF wf vc defs base])
qed

text \<open>
  Keep the innermost MU problem as a first-class semantic object.  Merely
  setting an ordinary DPP's innermost flag is not equivalent: unhiding rules
  are macro bridges, while normal-form obligations refer only to the original
  context-sensitive rules.
\<close>

definition muterm_innermost_typed_pair_step where
  "muterm_innermost_typed_pair_step shp \<mu> R P S =
    muterm_typed_pair_step P S \<inter>
      {(s,t). innermost_pair_source shp \<mu> R s}"

definition finite_muterm_innermost_typed_dpp where
  "finite_muterm_innermost_typed_dpp shp \<mu> R P S \<longleftrightarrow>
    SN_rel (muterm_innermost_typed_pair_step shp \<mu> R P S)
      (innermost_csdp_step shp \<mu> R)"

lemma muterm_innermost_typed_pair_step_mono_pairs:
  assumes "P \<subseteq> Q"
  shows "muterm_innermost_typed_pair_step shp \<mu> R P S \<subseteq>
    muterm_innermost_typed_pair_step shp \<mu> R Q S"
proof
  fix st
  assume mem: "st \<in> muterm_innermost_typed_pair_step shp \<mu> R P S"
  then have typed: "st \<in> muterm_typed_pair_step P S"
    and source: "st \<in> {(s,t). innermost_pair_source shp \<mu> R s}"
    unfolding muterm_innermost_typed_pair_step_def by auto
  have typed': "st \<in> muterm_typed_pair_step Q S"
  proof -
    obtain a b where st: "st = (a,b)" by (cases st)
    from typed[unfolded st muterm_typed_pair_step_def]
    show ?thesis
    proof
      assume nc: "(a,b) \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
      have "muterm_noncollapsing_rrstep Q a b"
        using nc assms unfolding muterm_noncollapsing_rrstep_def by blast
      then show ?thesis unfolding st muterm_typed_pair_step_def by auto
    next
      assume coll: "(a,b) \<in> {(s,t). \<exists>x.
        muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain x where px: "muterm_collapsing_rrstep P a x"
        and xb: "(x,b) \<in> rrstep S" by auto
      have "muterm_collapsing_rrstep Q a x"
        using px assms unfolding muterm_collapsing_rrstep_def by blast
      with xb show ?thesis unfolding st muterm_typed_pair_step_def by auto
    qed
  qed
  show "st \<in> muterm_innermost_typed_pair_step shp \<mu> R Q S"
    unfolding muterm_innermost_typed_pair_step_def using typed' source by auto
qed

lemma finite_muterm_innermost_typed_dpp_mono_pairs:
  assumes sub: "P \<subseteq> Q"
    and fin: "finite_muterm_innermost_typed_dpp shp \<mu> R Q S"
  shows "finite_muterm_innermost_typed_dpp shp \<mu> R P S"
  unfolding finite_muterm_innermost_typed_dpp_def
  by (rule SN_rel_mono[
      OF muterm_innermost_typed_pair_step_mono_pairs[OF sub]
        subset_refl fin[unfolded finite_muterm_innermost_typed_dpp_def]])

lemma finite_muterm_typed_imp_finite_min_typed:
  assumes "finite_muterm_typed_dpp shp \<mu> R P S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
proof -
  from assms have full: "SN_rel (muterm_typed_pair_step P S)
      (csdp_step shp \<mu> R)"
    unfolding finite_muterm_typed_dpp_def .
  have sub: "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq>
      muterm_typed_pair_step P S"
    unfolding muterm_min_typed_pair_step_def by auto
  show ?thesis unfolding finite_muterm_min_typed_dpp_def
    by (rule SN_rel_mono[OF sub subset_refl full])
qed

lemma muterm_unhiding_relstep_min_typed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R P S"
proof -
  from muterm_unhiding_relstep_typed[OF wf hp defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O muterm_typed_pair_step P S"
    by blast
  from hp_u have uT: "u \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  have target: "SN_on (csdp_step Sharp \<mu> R) {sharp_term Sharp u}"
    by (rule mu_Tinf_imp_SN_sharp_csdp[OF wf fresh uT])
  from step obtain v where prefix:
      "(sharp_term Sharp t,v) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and strict: "(v,sharp_term Sharp u) \<in> muterm_typed_pair_step P S"
    by auto
  have strict': "(v,sharp_term Sharp u) \<in>
      muterm_min_typed_pair_step Sharp \<mu> R P S"
    unfolding muterm_min_typed_pair_step_def using strict target by auto
  show ?thesis using hp_u prefix strict' by blast
qed

theorem finite_muterm_min_typed_dpp_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and fin: "finite_muterm_min_typed_dpp Sharp \<mu> R P S"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_min_typed_pair_step Sharp \<mu> R P S O
    (csdp_step Sharp \<mu> R)\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
  proof -
    fix t
    assume hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    from muterm_unhiding_relstep_min_typed[
      OF wf fresh hp defs cover preserving]
    obtain u where hp_u:
        "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
      and step: "(sharp_term Sharp t,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>* O
        muterm_min_typed_pair_step Sharp \<mu> R P S"
      by blast
    have suffix: "(sharp_term Sharp u,sharp_term Sharp u) \<in>
        (csdp_step Sharp \<mu> R)\<^sup>*" by simp
    show "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
      using hp_u step suffix by blast
  qed
  have all_ex: "\<forall>t. \<exists>u.
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<longrightarrow>
      has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
      (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
       has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
       (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in> ?A" by blast
  define ts where "ts = rec_nat t0 (\<lambda>n t. nxt t)"
  have inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n)"
    for n
    by (induct n, unfold ts_def, use hp0 nxt in auto)
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "(f n,f (Suc n)) \<in> ?A" for n
    using nxt[OF inv[of n]] unfolding f_def ts_def by auto
  from fin have sn: "SN ?A"
    unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def .
  moreover have "\<not> SN ?A" unfolding SN_defs using chain by blast
  ultimately show False by contradiction
qed

text \<open>
  The QCS usable-rule simulation does not intrinsically depend on minimality.
  This full-chain variant is kept in the MU-TERM overlay because its first use
  is the recursive exact-unhiding processor; placing it in the central CSR-DP
  theory would force large checker rebuilds during development.
\<close>

lemma qcs_csr_relto_target_closed_full:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where pair: "(a,b) \<in> rrstep P"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_rrstep_target[OF P_closed pair]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  show ?thesis by auto
qed

lemma qcs_csr_relto_transfer_full:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R U \<mu> s"
    and step: "(s, t) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s, t) \<in>
      (csdp_step Sharp \<mu> U)\<^sup>* O rrstep P O
      (csdp_step Sharp \<mu> U)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R U \<mu> t"
proof -
  from closed have U_closed: "\<And>lr. lr \<in> U \<Longrightarrow>
      qcs_ur_closed_term R U \<mu> (snd lr)"
    and P_closed: "\<And>dp. dp \<in> P \<Longrightarrow>
      qcs_ur_closed_dp_rhs R U \<mu> (snd dp)"
    unfolding qcs_csr_ur_closed_def by auto
  from step obtain a b where prefix:
    "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and pair: "(a,b) \<in> rrstep P"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_s prefix]
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> U)\<^sup>*" by auto
  from qcs_ur_closed_rrstep_target[OF P_closed pair]
  have closed_b: "qcs_ur_closed_dp_rhs R U \<mu> b" .
  from qcs_ur_closed_csdp_steps[OF wf fresh U_closed closed_b suffix]
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> U)\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R U \<mu> t" by auto
  show ?thesis using prefix_U pair suffix_U closed_t by auto
qed

theorem finite_csr_dpp_qcs_usable_rules:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f, n)"
    and closed: "qcs_csr_ur_closed R U \<mu> P"
    and fin: "finite_csr_dpp Sharp \<mu> P U"
  shows "finite_csr_dpp Sharp \<mu> P R"
proof (unfold finite_csr_dpp_def SN_rel_on_def SN_on_def, intro notI)
  let ?PR = "rrstep P"
  let ?SR = "csdp_step Sharp \<mu> R"
  let ?SU = "csdp_step Sharp \<mu> U"
  assume "\<exists>f. f 0 \<in> UNIV \<and>
    (\<forall>n. (f n, f (Suc n)) \<in> ?SR\<^sup>* O ?PR O ?SR\<^sup>*)"
  then obtain f where chain:
    "\<And>n. (f n, f (Suc n)) \<in> ?SR\<^sup>* O ?PR O ?SR\<^sup>*"
    by auto
  from qcs_csr_relto_target_closed_full[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R U \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R U \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from qcs_csr_relto_transfer_full[
      OF wf fresh closed Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n, ?g (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*" for n
    using qcs_csr_relto_transfer_full[
      OF wf fresh closed closed_g[of n] chain[of "Suc n"]] by auto
  from fin have no_U_chain:
    "\<not> (\<exists>h. h 0 \<in> UNIV \<and>
      (\<forall>n. (h n, h (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*))"
    unfolding finite_csr_dpp_def SN_rel_on_def SN_on_def .
  have U_chain: "\<exists>h. h 0 \<in> UNIV \<and>
      (\<forall>n. (h n, h (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*)"
  proof (intro exI[of _ ?g] conjI)
    show "?g 0 \<in> UNIV" by simp
    show "\<forall>n. (?g n, ?g (Suc n)) \<in> ?SU\<^sup>* O ?PR O ?SU\<^sup>*"
      using g_step by simp
  qed
  from no_U_chain U_chain show False by contradiction
qed

text \<open>
  Exact MU-TERM chains differ at one important point from ordinary CS-DP
  chains: a collapsing pair has a variable right-hand side, but that value is
  immediately exposed by one of the checked unhiding rules.  The following
  closure predicate records exactly the rules needed for that macro-step.  It
  deliberately accepts variable pair targets only here; the generic QCS
  usable-rule processor remains unchanged.
\<close>

text \<open>
  The innermost branch uses the smaller U-triangle usable-rule set from
  Definition 18 of the LPAR'08
  framework.  Only defined symbols at active right-hand-side positions seed
  the closure.  This criterion must remain distinct from U3: U3 also follows
  inactive left-hand-side positions and inactive positions in all source-rule
  right-hand sides.  Conflating the two loses precisely the useful rule set in
  examples such as Ex1_GM03.

  We state the predicate independently of a reduction order.  The recursive
  processor below combines it with the innermost-chain invariant and the
  checked reduction pair.
\<close>

definition muterm_innermost_ur_closed where
  "muterm_innermost_ur_closed R U \<mu> P \<longleftrightarrow>
    U \<subseteq> R \<and>
    (\<forall>dp\<in>P. \<not> is_Var (snd dp) \<longrightarrow>
      csr_u3_root_rules_closed R U (snd dp)
        (mu_fun_poss \<mu> (snd dp))) \<and>
    (\<forall>lr\<in>U. csr_u3_root_rules_closed R U (snd lr)
      (mu_fun_poss \<mu> (snd lr)))"

definition muterm_innermost_ur_closed_check where
  "muterm_innermost_ur_closed_check R U \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>dp. is_Var (snd dp) \<or>
       csr_rta08_active_root_rules_check R U \<mu> (snd dp)) P \<and>
     list_all (\<lambda>lr.
       csr_rta08_active_root_rules_check R U \<mu> (snd lr)) U)"

text \<open>
  The full-termination branch of the LPAR'08 U-triangle processor additionally
  requires strong conservativity (Definition 20).  Keep this side condition
  executable and explicit: active variables must be preserved from right to
  left, and no variable may occur both actively and in a frozen position of
  either side.  In particular, this is a property of the exact residual pairs
  together with the supplied usable rules, rather than of the original TRS.
\<close>

definition non_mu_vars_term where
  "non_mu_vars_term \<mu> t =
    {x. \<exists>p. p \<in> poss t - mu_poss \<mu> t \<and> t |_ p = Var x}"

fun var_of_term where
  "var_of_term (Var x) = x"
| "var_of_term (Fun f ts) = undefined"

definition non_mu_vars_term_list where
  "non_mu_vars_term_list \<mu> t = map (\<lambda>p. var_of_term (t |_ p))
    (filter (\<lambda>p. p \<notin> set (mu_poss_list \<mu> t)) (var_poss_list t))"

lemma set_non_mu_vars_term_list [simp]:
  "set (non_mu_vars_term_list \<mu> t) = non_mu_vars_term (mu_of \<mu>) t"
proof
  show "set (non_mu_vars_term_list \<mu> t) \<subseteq>
      non_mu_vars_term (mu_of \<mu>) t"
  proof
    fix x
    assume mem: "x \<in> set (non_mu_vars_term_list \<mu> t)"
    then obtain p where p: "p \<in> set (var_poss_list t)"
      and not_mu: "p \<notin> set (mu_poss_list \<mu> t)"
      and x: "x = var_of_term (t |_ p)"
      unfolding non_mu_vars_term_list_def by auto
    from p obtain y where at: "t |_ p = Var y"
      by (auto simp: var_poss_iff)
    from x at have "x = y" by simp
    moreover have "p \<in> poss t"
      by (rule var_poss_imp_poss, use p in simp)
    moreover have "p \<notin> mu_poss (mu_of \<mu>) t" using not_mu by simp
    ultimately show "x \<in> non_mu_vars_term (mu_of \<mu>) t"
      unfolding non_mu_vars_term_def using at by blast
  qed
next
  show "non_mu_vars_term (mu_of \<mu>) t \<subseteq>
      set (non_mu_vars_term_list \<mu> t)"
  proof
    fix x
    assume mem: "x \<in> non_mu_vars_term (mu_of \<mu>) t"
    then obtain p where p: "p \<in> poss t"
      and not_mu: "p \<notin> mu_poss (mu_of \<mu>) t"
      and at: "t |_ p = Var x"
      unfolding non_mu_vars_term_def by blast
    have var: "p \<in> set (var_poss_list t)"
      using p at by (simp add: var_poss_iff)
    have filtered: "p \<in> set
        (filter (\<lambda>p. p \<notin> set (mu_poss_list \<mu> t)) (var_poss_list t))"
      using var not_mu by simp
    show "x \<in> set (non_mu_vars_term_list \<mu> t)"
      unfolding non_mu_vars_term_list_def
      using filtered at by force
  qed
qed

lemma vars_term_active_or_inactive:
  assumes x: "x \<in> vars_term t"
  shows "x \<in> mu_vars_term \<mu> t \<or> x \<in> non_mu_vars_term \<mu> t"
proof -
  from vars_term_poss_subt_at[OF x] obtain p where
    p: "p \<in> poss t" and at: "t |_ p = Var x" by blast
  show ?thesis
  proof (cases "p \<in> mu_poss \<mu> t")
    case True
    then show ?thesis unfolding mu_vars_term_def using at by blast
  next
    case False
    then show ?thesis unfolding non_mu_vars_term_def using p at by blast
  qed
qed

definition muterm_strongly_conservative where
  "muterm_strongly_conservative \<mu> T \<longleftrightarrow>
    rhs_mu_vars_condition \<mu> T \<and>
    (\<forall>(l,r)\<in>T.
      mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {} \<and>
      mu_vars_term \<mu> r \<inter> non_mu_vars_term \<mu> r = {})"

definition muterm_strongly_conservative_check where
  "muterm_strongly_conservative_check \<mu> T =
    (rhs_mu_vars_condition_list \<mu> T \<and>
     list_all (\<lambda>(l,r).
       set (mu_vars_term_list \<mu> l) \<inter>
         set (non_mu_vars_term_list \<mu> l) = {} \<and>
       set (mu_vars_term_list \<mu> r) \<inter>
         set (non_mu_vars_term_list \<mu> r) = {}) T)"

lemma muterm_strongly_conservative_check_sound:
  assumes "muterm_strongly_conservative_check \<mu> T"
  shows "muterm_strongly_conservative (mu_of \<mu>) (set T)"
  using assms rhs_mu_vars_condition_list_sound[of \<mu> T]
  unfolding muterm_strongly_conservative_check_def
    muterm_strongly_conservative_def list_all_iff
  by auto

lemma muterm_strongly_conservative_rule:
  assumes sc: "muterm_strongly_conservative \<mu> T"
    and lr: "(l,r) \<in> T"
  shows "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
    and "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    and "mu_vars_term \<mu> r \<inter> non_mu_vars_term \<mu> r = {}"
  using sc lr unfolding muterm_strongly_conservative_def
    rhs_mu_vars_condition_def by auto

lemma muterm_strongly_conservative_rhs_active_not_lhs_inactive:
  assumes sc: "muterm_strongly_conservative \<mu> T"
    and lr: "(l,r) \<in> T"
  shows "mu_vars_term \<mu> r \<inter>
    non_mu_vars_term \<mu> l = {}"
proof -
  have sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
    by (rule muterm_strongly_conservative_rule(1)[OF sc lr])
  have disj: "mu_vars_term \<mu> l \<inter>
      non_mu_vars_term \<mu> l = {}"
    by (rule muterm_strongly_conservative_rule(2)[OF sc lr])
  show ?thesis using sub disj by blast
qed

lemma muterm_strongly_conservative_variable_partition:
  assumes sc: "muterm_strongly_conservative \<mu> T"
    and lr: "(l,r) \<in> T"
    and x: "x \<in> vars_term l"
  shows "x \<in> mu_vars_term \<mu> l \<longleftrightarrow>
    x \<notin> non_mu_vars_term \<mu> l"
proof
  assume active: "x \<in> mu_vars_term \<mu> l"
  from muterm_strongly_conservative_rule(2)[OF sc lr]
  show "x \<notin> non_mu_vars_term \<mu> l" using active by blast
next
  assume inactive: "x \<notin> non_mu_vars_term \<mu> l"
  from vars_term_active_or_inactive[OF x] inactive
  show "x \<in> mu_vars_term \<mu> l" by blast
qed

lemma mu_vars_term_active_argI:
  assumes i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
    and x: "x \<in> mu_vars_term \<mu> (ts ! i)"
  shows "x \<in> mu_vars_term \<mu> (Fun f ts)"
proof -
  from x obtain p where p: "p \<in> mu_poss \<mu> (ts ! i)"
    and at: "ts ! i |_ p = Var x"
    unfolding mu_vars_term_def by blast
  have ip: "i # p \<in> mu_poss \<mu> (Fun f ts)"
    using i active p by auto
  have "Fun f ts |_ (i # p) = Var x"
    using i p at mu_poss_imp_poss by simp
  with ip show ?thesis unfolding mu_vars_term_def by blast
qed

lemma non_mu_vars_term_active_argI:
  assumes i: "i < length ts" and active: "i \<in> \<mu> (f,length ts)"
    and x: "x \<in> non_mu_vars_term \<mu> (ts ! i)"
  shows "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
proof -
  from x obtain p where p: "p \<in> poss (ts ! i)"
    and not_mu: "p \<notin> mu_poss \<mu> (ts ! i)"
    and at: "ts ! i |_ p = Var x"
    unfolding non_mu_vars_term_def by blast
  have ip_pos: "i # p \<in> poss (Fun f ts)" using i p by simp
  have ip_not_mu: "i # p \<notin> mu_poss \<mu> (Fun f ts)"
    using i active not_mu by auto
  have "Fun f ts |_ (i # p) = Var x" using i at by simp
  then show ?thesis unfolding non_mu_vars_term_def
    using ip_pos ip_not_mu by blast
qed

lemma non_mu_vars_term_inactive_argI:
  assumes i: "i < length ts" and inactive: "i \<notin> \<mu> (f,length ts)"
    and x: "x \<in> vars_term (ts ! i)"
  shows "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
proof -
  from vars_term_poss_subt_at[OF x] obtain p where p: "p \<in> poss (ts ! i)"
    and at: "ts ! i |_ p = Var x" by blast
  have ip_pos: "i # p \<in> poss (Fun f ts)" using i p by simp
  have ip_not_mu: "i # p \<notin> mu_poss \<mu> (Fun f ts)"
    using i inactive by auto
  have "Fun f ts |_ (i # p) = Var x" using i at by simp
  then show ?thesis unfolding non_mu_vars_term_def
    using ip_pos ip_not_mu by blast
qed

lemma mu_vars_term_FunE:
  assumes "x \<in> mu_vars_term \<mu> (Fun f ts)"
  obtains i where "i < length ts" "i \<in> \<mu> (f,length ts)"
    "x \<in> mu_vars_term \<mu> (ts ! i)"
proof -
  from assms obtain p where p: "p \<in> mu_poss \<mu> (Fun f ts)"
    and at: "Fun f ts |_ p = Var x"
    unfolding mu_vars_term_def by blast
  from at have "p \<noteq> []" by auto
  then obtain i q where pq: "p = i # q" by (cases p, auto)
  from p[unfolded pq] obtain i': "i < length ts"
    and active: "i \<in> \<mu> (f,length ts)"
    and q: "q \<in> mu_poss \<mu> (ts ! i)" by auto
  have "ts ! i |_ q = Var x" using at pq i' by simp
  then have "x \<in> mu_vars_term \<mu> (ts ! i)"
    unfolding mu_vars_term_def using q by blast
  then show thesis by (rule that[OF i' active])
qed

lemma vars_term_arg_subset:
  assumes "i < length ts"
  shows "vars_term (ts ! i) \<subseteq> vars_term (Fun f ts)"
  using nth_mem[OF assms] by auto

lemma muterm_innermost_ur_closed_check_sound:
  assumes "muterm_innermost_ur_closed_check R U \<mu> P"
  shows "muterm_innermost_ur_closed (set R) (set U) (mu_of \<mu>) (set P)"
proof -
  from assms have subset: "set U \<subseteq> set R"
    and pairs: "\<And>dp. dp \<in> set P \<Longrightarrow> \<not> is_Var (snd dp) \<Longrightarrow>
      csr_rta08_active_root_rules_check R U \<mu> (snd dp)"
    and rules: "\<And>lr. lr \<in> set U \<Longrightarrow>
      csr_rta08_active_root_rules_check R U \<mu> (snd lr)"
    unfolding muterm_innermost_ur_closed_check_def
    by (auto simp: list_all_iff)
  have active_sound: "\<And>t. csr_rta08_active_root_rules_check R U \<mu> t \<Longrightarrow>
      csr_u3_root_rules_closed (set R) (set U) t
        (mu_fun_poss (mu_of \<mu>) t)"
  proof -
    fix t
    assume check: "csr_rta08_active_root_rules_check R U \<mu> t"
    have roots: "csr_u3_root_rules_closed (set R) (set U) t
        (set (mu_fun_poss_list \<mu> t))"
      using csr_u3_root_rules_check_sound[OF check[unfolded
        csr_rta08_active_root_rules_check_def]] by simp
    show "csr_u3_root_rules_closed (set R) (set U) t
        (mu_fun_poss (mu_of \<mu>) t)"
      using roots by simp
  qed
  show ?thesis unfolding muterm_innermost_ur_closed_def
  proof (intro conjI ballI impI)
    show "set U \<subseteq> set R" by (rule subset)
  next
    fix dp
    assume dp: "dp \<in> set P" and nonvar: "\<not> is_Var (snd dp)"
    show "csr_u3_root_rules_closed (set R) (set U) (snd dp)
      (mu_fun_poss (mu_of \<mu>) (snd dp))"
      by (rule active_sound[OF pairs[OF dp nonvar]])
  next
    fix lr
    assume lr: "lr \<in> set U"
    show "csr_u3_root_rules_closed (set R) (set U) (snd lr)
      (mu_fun_poss (mu_of \<mu>) (snd lr))"
      by (rule active_sound[OF rules[OF lr]])
  qed
qed

text \<open>
  Strip every outer dependency-pair mark when consulting the original
  replacement map.  On well-formed CPF problems this agrees with
  @{const csr_dp_root_mu}; making the operation idempotent gives the exact
  marked/unmarked equality required by the I2 simulation without imposing a
  spurious condition on syntactically nested marks.
\<close>

fun muterm_dp_root_mu ::
  "(('f,'l) lab) mu \<Rightarrow> ((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
where
  "muterm_dp_root_mu \<mu> (Sharp f,n) = muterm_dp_root_mu \<mu> (f,n)"
| "muterm_dp_root_mu \<mu> (f,n) = \<mu> (f,n)"

fun muterm_dp_mu_fun_poss_list where
  "muterm_dp_mu_fun_poss_list \<mu> (Var x) = []"
| "muterm_dp_mu_fun_poss_list \<mu> (Fun f ts) = [] # concat
    (map (\<lambda>i. map ((#) i) (muterm_dp_mu_fun_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts].
        i \<in> mu_of \<mu> (f,length ts)])"

lemma set_muterm_dp_mu_fun_poss_list [simp]:
  "set (muterm_dp_mu_fun_poss_list \<mu> t) =
    mu_fun_poss (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case by auto
qed

fun muterm_dp_mu_poss_list where
  "muterm_dp_mu_poss_list \<mu> (Var x) = [[]]"
| "muterm_dp_mu_poss_list \<mu> (Fun f ts) = [] # concat
    (map (\<lambda>i. map ((#) i) (muterm_dp_mu_poss_list \<mu> (ts ! i)))
      [i <- [0..<length ts].
        i \<in> mu_of \<mu> (f,length ts)])"

lemma set_muterm_dp_mu_poss_list [simp]:
  "set (muterm_dp_mu_poss_list \<mu> t) =
    mu_poss (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case by auto
qed

fun muterm_dp_mu_vars_term_list where
  "muterm_dp_mu_vars_term_list \<mu> (Var x) = [x]"
| "muterm_dp_mu_vars_term_list \<mu> (Fun f ts) = concat
    (map (\<lambda>i. muterm_dp_mu_vars_term_list \<mu> (ts ! i))
      [i <- [0..<length ts].
        i \<in> mu_of \<mu> (f,length ts)])"

lemma set_muterm_dp_mu_vars_term_list [simp]:
  "set (muterm_dp_mu_vars_term_list \<mu> t) =
    mu_vars_term (mu_of \<mu>) t"
proof (induct t)
  case (Var x)
  then show ?case unfolding mu_vars_term_def by simp
next
  case (Fun f ts)
  show ?case
  proof
    show "set (muterm_dp_mu_vars_term_list \<mu> (Fun f ts)) \<subseteq>
        mu_vars_term (mu_of \<mu>) (Fun f ts)"
    proof
      fix x
      assume x: "x \<in> set (muterm_dp_mu_vars_term_list \<mu> (Fun f ts))"
      then obtain i where i: "i < length ts"
        "i \<in> mu_of \<mu> (f,length ts)"
        and xi: "x \<in> set (muterm_dp_mu_vars_term_list \<mu> (ts ! i))"
        by auto
      from Fun.hyps[OF nth_mem[OF i(1)], unfolded mu_vars_term_def] xi
      obtain p where p: "p \<in> mu_poss (mu_of \<mu>) (ts ! i)"
        and sub: "ts ! i |_ p = Var x" by auto
      have "i # p \<in> mu_poss (mu_of \<mu>) (Fun f ts)"
        using i p by auto
      moreover have "Fun f ts |_ (i # p) = Var x" using i sub by simp
      ultimately show "x \<in> mu_vars_term
          (mu_of \<mu>) (Fun f ts)"
        unfolding mu_vars_term_def by blast
    qed
  next
    show "mu_vars_term (mu_of \<mu>) (Fun f ts) \<subseteq>
        set (muterm_dp_mu_vars_term_list \<mu> (Fun f ts))"
    proof
      fix x
      assume "x \<in> mu_vars_term (mu_of \<mu>) (Fun f ts)"
      then obtain p where p: "p \<in> mu_poss
          (mu_of \<mu>) (Fun f ts)"
        and sub: "Fun f ts |_ p = Var x"
        unfolding mu_vars_term_def by auto
      show "x \<in> set (muterm_dp_mu_vars_term_list \<mu> (Fun f ts))"
      proof (cases p)
        case Nil
        with sub show ?thesis by simp
      next
        case (Cons i q)
        from p Cons have i: "i < length ts"
          "i \<in> mu_of \<mu> (f,length ts)"
          and q: "q \<in> mu_poss (mu_of \<mu>) (ts ! i)"
          by auto
        from sub Cons i have sub_i: "ts ! i |_ q = Var x" by simp
        have "x \<in> set (muterm_dp_mu_vars_term_list \<mu> (ts ! i))"
          using Fun.hyps[OF nth_mem[OF i(1)]] q sub_i
          unfolding mu_vars_term_def by auto
        with i show ?thesis by auto
      qed
    qed
  qed
qed

definition muterm_dp_non_mu_vars_term_list where
  "muterm_dp_non_mu_vars_term_list \<mu> t =
    map (\<lambda>p. var_of_term (t |_ p))
      (filter (\<lambda>p. p \<notin> set (muterm_dp_mu_poss_list \<mu> t))
        (var_poss_list t))"

lemma set_muterm_dp_non_mu_vars_term_list [simp]:
  "set (muterm_dp_non_mu_vars_term_list \<mu> t) =
    non_mu_vars_term (mu_of \<mu>) t"
  unfolding muterm_dp_non_mu_vars_term_list_def non_mu_vars_term_def
  by (auto simp: var_poss_iff, force)

definition muterm_dp_strongly_conservative_check where
  "muterm_dp_strongly_conservative_check \<mu> T =
    (list_all (\<lambda>(l,r). list_all (\<lambda>x.
        x \<in> set (muterm_dp_mu_vars_term_list \<mu> l))
      (muterm_dp_mu_vars_term_list \<mu> r)) T \<and>
     list_all (\<lambda>(l,r).
       set (muterm_dp_mu_vars_term_list \<mu> l) \<inter>
         set (muterm_dp_non_mu_vars_term_list \<mu> l) = {} \<and>
       set (muterm_dp_mu_vars_term_list \<mu> r) \<inter>
         set (muterm_dp_non_mu_vars_term_list \<mu> r) = {}) T)"

lemma muterm_dp_strongly_conservative_check_sound:
  assumes "muterm_dp_strongly_conservative_check \<mu> T"
  shows "muterm_strongly_conservative
    (mu_of \<mu>) (set T)"
  using assms unfolding muterm_dp_strongly_conservative_check_def
    muterm_strongly_conservative_def rhs_mu_vars_condition_def list_all_iff
  by auto

definition muterm_dp_active_ur_closed_check where
  "muterm_dp_active_ur_closed_check R U \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set R) U \<and>
     list_all (\<lambda>dp. is_Var (snd dp) \<or>
       csr_u3_root_rules_check R U (snd dp)
         (muterm_dp_mu_fun_poss_list \<mu> (snd dp))) P \<and>
     list_all (\<lambda>lr. csr_u3_root_rules_check R U (snd lr)
       (muterm_dp_mu_fun_poss_list \<mu> (snd lr))) U)"

lemma muterm_dp_active_ur_closed_check_sound:
  assumes "muterm_dp_active_ur_closed_check R U \<mu> P"
  shows "muterm_innermost_ur_closed (set R) (set U)
    (mu_of \<mu>) (set P)"
proof -
  from assms have subset: "set U \<subseteq> set R"
    and pairs: "\<And>dp. dp \<in> set P \<Longrightarrow> \<not> is_Var (snd dp) \<Longrightarrow>
      csr_u3_root_rules_check R U (snd dp)
        (muterm_dp_mu_fun_poss_list \<mu> (snd dp))"
    and rules: "\<And>lr. lr \<in> set U \<Longrightarrow>
      csr_u3_root_rules_check R U (snd lr)
        (muterm_dp_mu_fun_poss_list \<mu> (snd lr))"
    unfolding muterm_dp_active_ur_closed_check_def
    by (auto simp: list_all_iff)
  show ?thesis unfolding muterm_innermost_ur_closed_def
  proof (intro conjI ballI impI)
    show "set U \<subseteq> set R" by (rule subset)
  next
    fix dp
    assume dp: "dp \<in> set P" and rhs: "\<not> is_Var (snd dp)"
    from csr_u3_root_rules_check_sound[OF pairs[OF dp rhs]]
    show "csr_u3_root_rules_closed (set R) (set U) (snd dp)
      (mu_fun_poss (mu_of \<mu>) (snd dp))" by simp
  next
    fix lr
    assume lr: "lr \<in> set U"
    from csr_u3_root_rules_check_sound[OF rules[OF lr]]
    show "csr_u3_root_rules_closed (set R) (set U) (snd lr)
      (mu_fun_poss (mu_of \<mu>) (snd lr))" by simp
  qed
qed

text \<open>
  The interpretation used by Theorem 21(i) of the improved CS-DP
  framework only descends through active arguments.  This is the essential
  difference from the existing U3 interpretation, which must also inspect
  inactive arguments and therefore needs the larger U3 closure.

  We make the interpretation total by leaving nonterminating inputs
  unchanged.  All recursive calls from a terminating input are either an
  active proper-subterm call or a context-sensitive rewrite call; their
  union is well founded by the existing active-subterm/rewrite result.
\<close>

definition muterm_i2_struct_call where
  "muterm_i2_struct_call \<mu> =
    {(Fun f ts,t) |f ts t. \<exists>i<length ts.
      i \<in> \<mu> (f,length ts) \<and> t = ts ! i}"

definition muterm_i2_call where
  "muterm_i2_call R \<mu> =
    {(t,u). SN_on (csstep \<mu> R) {t} \<and>
      ((t,u) \<in> muterm_i2_struct_call \<mu> \<or>
       (t,u) \<in> csstep \<mu> R)}"

lemma wf_muterm_i2_call:
  assumes wf: "wf_trs R"
  shows "wf ((muterm_i2_call R \<mu>)\<inverse>)"
proof -
  let ?A = "restrict_SN (csstep \<mu> R) (csstep \<mu> R)"
  let ?B = "restrict_SN (mu_supt_rel \<mu>) (csstep \<mu> R)"
  have sn: "SN (?A \<union> ?B)"
    by (rule SN_restrict_SN_mu_supt_csstep[OF wf])
  have call_sn: "SN (muterm_i2_call R \<mu>)"
  proof (rule ccontr)
    assume "\<not> SN (muterm_i2_call R \<mu>)"
    then obtain f where chain:
      "\<And>n. (f n,f (Suc n)) \<in> muterm_i2_call R \<mu>"
      unfolding SN_defs by blast
    have nonvar: "\<not> is_Var (f n)" for n
    proof
      assume var: "is_Var (f n)"
      then obtain x where fx: "f n = Var x" by (cases "f n", auto)
      from chain[of n] have cases:
        "(f n,f (Suc n)) \<in> muterm_i2_struct_call \<mu> \<or>
         (f n,f (Suc n)) \<in> csstep \<mu> R"
        unfolding muterm_i2_call_def by auto
      then show False
      proof
        assume "(f n,f (Suc n)) \<in> muterm_i2_struct_call \<mu>"
        then show False unfolding muterm_i2_struct_call_def fx by auto
      next
        assume "(f n,f (Suc n)) \<in> csstep \<mu> R"
        then show False unfolding fx using csstep_Var_empty_wf[OF wf] by blast
      qed
    qed
    have restricted: "(f n,f (Suc n)) \<in> ?A \<union> ?B" for n
    proof -
      from chain[of n] have source_sn:
          "SN_on (csstep \<mu> R) {f n}"
        and cases:
          "(f n,f (Suc n)) \<in> muterm_i2_struct_call \<mu> \<or>
           (f n,f (Suc n)) \<in> csstep \<mu> R"
        unfolding muterm_i2_call_def by auto
      from cases show ?thesis
      proof
        assume struct: "(f n,f (Suc n)) \<in> muterm_i2_struct_call \<mu>"
        from struct obtain g ts i where src: "f n = Fun g ts"
          and i: "i < length ts" and active: "i \<in> \<mu> (g,length ts)"
          and dst: "f (Suc n) = ts ! i"
          unfolding muterm_i2_struct_call_def by auto
        from nonvar[of "Suc n"] obtain h us where target:
          "f (Suc n) = Fun h us" by (cases "f (Suc n)", auto)
        have pos: "i # [] \<in> mu_poss \<mu> (Fun g ts)"
          using i active dst target by simp
        have subterm: "Fun g ts |_ (i # []) = Fun h us"
          using i dst target by simp
        have "(f n,f (Suc n)) \<in> mu_supt_rel \<mu>"
          unfolding src target mu_supt_rel_def mu_supt_def
          using pos subterm by blast
        with source_sn show ?thesis unfolding restrict_SN_def by auto
      next
        assume step: "(f n,f (Suc n)) \<in> csstep \<mu> R"
        with source_sn show ?thesis unfolding restrict_SN_def by auto
      qed
    qed
    have "\<not> SN (?A \<union> ?B)"
      unfolding SN_defs using restricted by blast
    with sn show False by contradiction
  qed
  show ?thesis using call_sn unfolding SN_iff_wf .
qed

locale muterm_i2 =
  fixes Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "('f \<times> nat) set"
    and cn :: "'f \<times> nat"
  assumes wf: "wf_trs (set Rs)"
begin

function i2 :: "('f,'v) term \<Rightarrow> ('f,'v) term"
where
  "i2 (Var x) = Var x"
| "i2 (Fun f ts) =
    (if \<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts}
     then Fun f ts
     else
       let us = map (\<lambda>(i,t).
         case t of
           Var x \<Rightarrow> Var x
         | Fun g ss \<Rightarrow>
             if i \<in> \<mu> (f,length ts) then i2 (Fun g ss) else Fun g ss)
           (zip [0..<length ts] ts)
       in if (f,length ts) \<in> \<Delta>
          then Fun f us
          else comb cn (Fun f us #
            map i2 (csrewrite \<mu> Rs (Fun f ts))))"
  by pat_completeness auto

termination
  apply (relation "(muterm_i2_call (set Rs) \<mu>)\<inverse>")
    apply (rule wf_muterm_i2_call[OF wf])
   apply (auto simp: muterm_i2_call_def muterm_i2_struct_call_def set_zip)
  apply (auto simp: muterm_i2_call_def intro: csrewrite_sound)
  done

definition i2_args where
  "i2_args f ts = map (\<lambda>(i,t).
    case t of
      Var x \<Rightarrow> Var x
    | Fun g ss \<Rightarrow>
        if i \<in> \<mu> (f,length ts) then i2 (Fun g ss) else Fun g ss)
      (zip [0..<length ts] ts)"

lemma i2_args_length[simp]: "length (i2_args f ts) = length ts"
  unfolding i2_args_def by simp

lemma i2_args_nth:
  assumes i: "i < length ts"
  shows "i2_args f ts ! i =
    (if i \<in> \<mu> (f,length ts) then i2 (ts ! i) else ts ! i)"
  using i unfolding i2_args_def
  by (cases "ts ! i") (simp_all add: nth_zip)

lemma i2_Fun:
  "i2 (Fun f ts) =
    (if \<not> SN_on (csstep \<mu> (set Rs)) {Fun f ts}
     then Fun f ts
     else if (f,length ts) \<in> \<Delta>
          then Fun f (i2_args f ts)
          else comb cn (Fun f (i2_args f ts) #
            map i2 (csrewrite \<mu> Rs (Fun f ts))))"
  unfolding i2_args_def by (simp add: Let_def)

definition i2_subst where
  "i2_subst t \<sigma> x =
    (if x \<in> mu_vars_term \<mu> t then i2 (\<sigma> x) else \<sigma> x)"

lemma i2_subst_active:
  assumes "x \<in> mu_vars_term \<mu> t"
  shows "i2_subst t \<sigma> x = i2 (\<sigma> x)"
  using assms unfolding i2_subst_def by simp

lemma i2_subst_inactive:
  assumes "x \<notin> mu_vars_term \<mu> t"
  shows "i2_subst t \<sigma> x = \<sigma> x"
  using assms unfolding i2_subst_def by simp

fun i2_bracket :: "('f,'v) term \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) term"
where
  "i2_bracket (Var x) \<sigma> = i2 (\<sigma> x)"
| "i2_bracket (Fun f ts) \<sigma> = Fun f
    (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i2_bracket t \<sigma> else t \<cdot> \<sigma>)
      (zip [0..<length ts] ts))"

lemma i2_bracket_Fun_length[simp]:
  "length (args (i2_bracket (Fun f ts) \<sigma>)) = length ts"
  by simp

lemma i2_bracket_Fun_nth:
  assumes i: "i < length ts"
  shows "args (i2_bracket (Fun f ts) \<sigma>) ! i =
    (if i \<in> \<mu> (f,length ts) then i2_bracket (ts ! i) \<sigma>
     else (ts ! i) \<cdot> \<sigma>)"
  using i by (simp add: nth_zip)

lemma i2_bracket_as_subst:
  assumes disj: "mu_vars_term \<mu> t \<inter> non_mu_vars_term \<mu> t = {}"
  shows "i2_bracket t \<sigma> = t \<cdot> i2_subst t \<sigma>"
  using disj
proof (induct t)
  case (Var x)
  then show ?case unfolding i2_subst_def mu_vars_term_def by simp
next
  case (Fun f ts)
  have lists: "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts) =
      map (\<lambda>t. t \<cdot> i2_subst (Fun f ts) \<sigma>) ts"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts)) =
        length (map (\<lambda>t. t \<cdot> i2_subst (Fun f ts) \<sigma>) ts)"
        by simp
      fix i
      assume i_map: "i < length (map (\<lambda>(i,t).
        if i \<in> \<mu> (f,length ts) then i2_bracket t \<sigma> else t \<cdot> \<sigma>)
        (zip [0..<length ts] ts))"
      then have i: "i < length ts" by simp
      show "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
          then i2_bracket t \<sigma> else t \<cdot> \<sigma>)
          (zip [0..<length ts] ts) ! i =
        map (\<lambda>t. t \<cdot> i2_subst (Fun f ts) \<sigma>) ts ! i"
      proof (cases "i \<in> \<mu> (f,length ts)")
        case True
        have child_disj: "mu_vars_term \<mu> (ts ! i) \<inter>
            non_mu_vars_term \<mu> (ts ! i) = {}"
        proof (rule ccontr)
          assume "mu_vars_term \<mu> (ts ! i) \<inter>
              non_mu_vars_term \<mu> (ts ! i) \<noteq> {}"
          then obtain x where xa: "x \<in> mu_vars_term \<mu> (ts ! i)"
            and xn: "x \<in> non_mu_vars_term \<mu> (ts ! i)" by blast
          have "x \<in> mu_vars_term \<mu> (Fun f ts)"
            by (rule mu_vars_term_active_argI[OF i True xa])
          moreover have "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
            by (rule non_mu_vars_term_active_argI[OF i True xn])
          ultimately show False using Fun.prems by blast
        qed
        have IH: "i2_bracket (ts ! i) \<sigma> =
            (ts ! i) \<cdot> i2_subst (ts ! i) \<sigma>"
          by (rule Fun.hyps[OF nth_mem[OF i] child_disj])
        have subst_eq: "(ts ! i) \<cdot> i2_subst (ts ! i) \<sigma> =
            (ts ! i) \<cdot> i2_subst (Fun f ts) \<sigma>"
        proof (rule term_subst_eq)
          fix x
          assume x: "x \<in> vars_term (ts ! i)"
          show "i2_subst (ts ! i) \<sigma> x = i2_subst (Fun f ts) \<sigma> x"
          proof (cases "x \<in> mu_vars_term \<mu> (ts ! i)")
            case True
            have parent: "x \<in> mu_vars_term \<mu> (Fun f ts)"
              by (rule mu_vars_term_active_argI[OF i `i \<in> \<mu> (f,length ts)` True])
            show ?thesis unfolding i2_subst_def using True parent by simp
          next
            case False
            from vars_term_active_or_inactive[OF x] False
            have child_inactive: "x \<in> non_mu_vars_term \<mu> (ts ! i)" by blast
            have parent_inactive: "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
              by (rule non_mu_vars_term_active_argI[OF i `i \<in> \<mu> (f,length ts)` child_inactive])
            have parent_not_active: "x \<notin> mu_vars_term \<mu> (Fun f ts)"
              using Fun.prems parent_inactive by blast
            show ?thesis unfolding i2_subst_def
              using False parent_not_active by simp
          qed
        qed
        show ?thesis using i True IH subst_eq by (simp add: nth_zip)
      next
        case False
        have inactive: "\<And>x. x \<in> vars_term (ts ! i) \<Longrightarrow>
            x \<notin> mu_vars_term \<mu> (Fun f ts)"
        proof -
          fix x
          assume x: "x \<in> vars_term (ts ! i)"
          have parent_inactive: "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
            apply (rule non_mu_vars_term_inactive_argI)
              apply (rule i)
             apply (rule False)
            apply (rule x)
            done
          show "x \<notin> mu_vars_term \<mu> (Fun f ts)"
            using Fun.prems parent_inactive by blast
        qed
        have subst_eq: "(ts ! i) \<cdot> \<sigma> =
            (ts ! i) \<cdot> i2_subst (Fun f ts) \<sigma>"
          by (rule term_subst_eq, simp add: i2_subst_def inactive)
        show ?thesis using i False subst_eq by (simp add: nth_zip)
      qed
    qed
  show ?case using lists by simp
qed

lemma i2_equals_bracket:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {t \<cdot> \<sigma>}"
    and roots: "\<And>p. p \<in> mu_fun_poss \<mu> t \<Longrightarrow>
      root (t |_ p) \<in> Some ` \<Delta>"
  shows "i2 (t \<cdot> \<sigma>) = i2_bracket t \<sigma>"
  using SN roots
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have root_delta: "(f,length ts) \<in> \<Delta>"
    using Fun.prems(2)[of "[]"] by auto
  have source_SN: "SN_on (csstep \<mu> (set Rs))
      {Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)}"
    using Fun.prems(1) by simp
  have args: "i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts) =
      args (i2_bracket (Fun f ts) \<sigma>)"
  proof (rule nth_equalityI)
    show "length (i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts)) =
      length (args (i2_bracket (Fun f ts) \<sigma>))" by simp
    fix i
    assume i_args: "i < length (i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
    then have i: "i < length ts" by simp
    show "i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts) ! i =
      args (i2_bracket (Fun f ts) \<sigma>) ! i"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have empty: "[] \<in> mu_poss \<mu> ((ts ! i) \<cdot> \<sigma>)"
        by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
      have pos: "i # [] \<in> mu_poss \<mu>
          (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
        using i True empty by auto
      from SN_on_mu_pos[OF wf pos source_SN]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
        using i by simp
      have sub_roots: "\<And>p. p \<in> mu_fun_poss \<mu> (ts ! i) \<Longrightarrow>
          root (ts ! i |_ p) \<in> Some ` \<Delta>"
      proof -
        fix p
        assume p: "p \<in> mu_fun_poss \<mu> (ts ! i)"
        have "i # p \<in> mu_fun_poss \<mu> (Fun f ts)"
          using i True p by auto
        from Fun.prems(2)[OF this]
        show "root (ts ! i |_ p) \<in> Some ` \<Delta>" using i p by simp
      qed
      have IH: "i2 ((ts ! i) \<cdot> \<sigma>) = i2_bracket (ts ! i) \<sigma>"
        by (rule Fun.hyps[OF nth_mem[OF i] sub_SN sub_roots])
      show ?thesis using i True IH
        by (simp add: i2_args_nth i2_bracket_Fun_nth)
    next
      case False
      then show ?thesis using i
        by (simp add: i2_args_nth i2_bracket_Fun_nth)
    qed
  qed
  have source: "Fun f ts \<cdot> \<sigma> =
      Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)" by simp
  have i2_source: "i2 (Fun f ts \<cdot> \<sigma>) =
      Fun f (i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
    unfolding source
    apply (subst i2_Fun)
    using source_SN root_delta
    apply simp
    done
  show ?case
    apply (subst i2_source)
    apply (subst args)
    apply simp
    done
qed

lemma cssteps_active_substs:
  assumes active: "\<And>x. x \<in> mu_vars_term \<mu> t \<Longrightarrow>
      (\<sigma> x, \<tau> x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    and inactive: "\<And>x. x \<in> non_mu_vars_term \<mu> t \<Longrightarrow>
      \<sigma> x = \<tau> x"
  shows "(t \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
  using active inactive
proof (induct t)
  case (Var x)
  have "x \<in> mu_vars_term \<mu> (Var x)"
    unfolding mu_vars_term_def by simp
  from Var.prems(1)[OF this] show ?case by simp
next
  case (Fun f ts)
  let ?ss = "map (\<lambda>t. t \<cdot> \<sigma>) ts"
  let ?us = "map (\<lambda>t. t \<cdot> \<tau>) ts"
  have len: "length ?ss = length ?us" by simp
  have args: "\<And>i. i < length ?ss \<Longrightarrow>
      (if i \<in> \<mu> (f,length ?ss)
       then (?ss ! i, ?us ! i) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
       else ?us ! i = ?ss ! i)"
  proof -
    fix i
    assume i_ss: "i < length ?ss"
    then have i: "i < length ts" by simp
    show "(if i \<in> \<mu> (f,length ?ss)
      then (?ss ! i, ?us ! i) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
      else ?us ! i = ?ss ! i)"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have child_active: "\<And>x. x \<in> mu_vars_term \<mu> (ts ! i) \<Longrightarrow>
          (\<sigma> x, \<tau> x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      proof -
        fix x
        assume x: "x \<in> mu_vars_term \<mu> (ts ! i)"
        have "x \<in> mu_vars_term \<mu> (Fun f ts)"
          by (rule mu_vars_term_active_argI[OF i True x])
        from Fun.prems(1)[OF this]
        show "(\<sigma> x, \<tau> x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
      qed
      have child_inactive: "\<And>x. x \<in> non_mu_vars_term \<mu> (ts ! i) \<Longrightarrow>
          \<sigma> x = \<tau> x"
      proof -
        fix x
        assume x: "x \<in> non_mu_vars_term \<mu> (ts ! i)"
        have "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
          by (rule non_mu_vars_term_active_argI[OF i True x])
        from Fun.prems(2)[OF this] show "\<sigma> x = \<tau> x" .
      qed
      from Fun.hyps[OF nth_mem[OF i] child_active child_inactive]
      show ?thesis using i True by simp
    next
      case False
      have same: "(ts ! i) \<cdot> \<sigma> = (ts ! i) \<cdot> \<tau>"
      proof (rule term_subst_eq)
        fix x
        assume x: "x \<in> vars_term (ts ! i)"
        have "x \<in> non_mu_vars_term \<mu> (Fun f ts)"
          apply (rule non_mu_vars_term_inactive_argI)
            apply (rule i)
           apply (rule False)
          apply (rule x)
          done
        from Fun.prems(2)[OF this] show "\<sigma> x = \<tau> x" .
      qed
      show ?thesis using i False same by simp
    qed
  qed
  have whole: "(Fun f ?ss, Fun f ?us)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule cssteps_FunI[OF len args])
  show ?case using whole by simp
qed

lemma i2_projects_to_bracket:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {t \<cdot> \<sigma>}"
  shows "(i2 (t \<cdot> \<sigma>), i2_bracket t \<sigma>)
    \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
  using SN
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  let ?ss = "i2_args f (map (\<lambda>t. t \<cdot> \<sigma>) ts)"
  let ?us = "args (i2_bracket (Fun f ts) \<sigma>)"
  have len: "length ?ss = length ?us" by simp
  have arg: "\<And>i. i < length ?ss \<Longrightarrow>
    (if i \<in> \<mu> (f,length ?ss)
     then (?ss ! i, ?us ! i) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
     else ?us ! i = ?ss ! i)"
  proof -
    fix i
    assume i_ss: "i < length ?ss"
    then have i: "i < length ts" by simp
    show "(if i \<in> \<mu> (f,length ?ss)
      then (?ss ! i, ?us ! i) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*
      else ?us ! i = ?ss ! i)"
    proof (cases "i \<in> \<mu> (f,length ts)")
      case True
      have empty: "[] \<in> mu_poss \<mu> ((ts ! i) \<cdot> \<sigma>)"
        by (cases "(ts ! i) \<cdot> \<sigma>") simp_all
      have pos: "i # [] \<in> mu_poss \<mu> (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts))"
        using i True empty by auto
      have source_SN: "SN_on (csstep \<mu> (set Rs))
          {Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)}"
        using Fun.prems by simp
      from SN_on_mu_pos[OF wf pos source_SN]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {(ts ! i) \<cdot> \<sigma>}"
        using i by simp
      from Fun.hyps[OF nth_mem[OF i] sub_SN]
      show ?thesis using True i by (simp add: i2_args_nth i2_bracket_Fun_nth)
    next
      case False
      then show ?thesis using i
        by (simp add: i2_args_nth i2_bracket_Fun_nth)
    qed
  qed
  have base: "(Fun f ?ss, Fun f ?us)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    by (rule cssteps_FunI[OF len arg])
  have source: "Fun f ts \<cdot> \<sigma> =
      Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)" by simp
  have whole_SN: "SN_on (csstep \<mu> (set Rs))
      {Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)}"
    using Fun.prems by simp
  have bracket: "i2_bracket (Fun f ts) \<sigma> = Fun f ?us" by simp
  show ?case
  proof (cases "(f,length ts) \<in> \<Delta>")
    case True
    have i2_source: "i2 (Fun f ts \<cdot> \<sigma>) = Fun f ?ss"
      unfolding source
      apply (subst i2_Fun)
      using True whole_SN
      apply simp
      done
    show ?thesis
      apply (subst i2_source)
      apply (subst bracket)
      apply (rule base)
      done
  next
    case False
    let ?xs = "Fun f ?ss # map i2
      (csrewrite \<mu> Rs (Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ts)))"
    have member: "Fun f ?ss \<in> set ?xs" by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project: "(comb cn ?xs, Fun f ?ss)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have first: "(comb cn ?xs, Fun f ?ss)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      by (rule trancl_into_rtrancl[OF project])
    have total: "(comb cn ?xs, Fun f ?us)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      by (rule rtrancl_trans[OF first base])
    have i2_source: "i2 (Fun f ts \<cdot> \<sigma>) = comb cn ?xs"
      unfolding source
      apply (subst i2_Fun)
      using False whole_SN
      apply simp
      done
    show ?thesis
      apply (subst i2_source)
      apply (subst bracket)
      apply (rule total)
      done
  qed
qed

lemma i2_bracket_Var[simp]: "i2_bracket t Var = t"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have lists: "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
      then i2_bracket t Var else t \<cdot> Var) (zip [0..<length ts] ts) = ts"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
      then i2_bracket t Var else t \<cdot> Var) (zip [0..<length ts] ts)) =
      length ts" by simp
    fix i
    assume i_map: "i < length (map (\<lambda>(i,t).
      if i \<in> \<mu> (f,length ts) then i2_bracket t Var else t \<cdot> Var)
      (zip [0..<length ts] ts))"
    then have i: "i < length ts" by simp
    from Fun.hyps[OF nth_mem[OF i]] show
      "map (\<lambda>(i,t). if i \<in> \<mu> (f,length ts)
        then i2_bracket t Var else t \<cdot> Var)
        (zip [0..<length ts] ts) ! i = ts ! i"
      using i by (simp add: nth_zip)
  qed
  show ?case using lists by simp
qed

lemma i2_projects_self:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {t}"
  shows "(i2 t,t) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
proof -
  have source: "t \<cdot> Var = t" by simp
  have source_SN: "SN_on (csstep \<mu> (set Rs)) {t \<cdot> Var}"
    using SN by simp
  from i2_projects_to_bracket[of t Var, OF source_SN]
  show ?thesis by simp
qed

end

locale muterm_i2_strong =
  muterm_i2 Rs \<mu> \<Delta> cn
  for Rs :: "('f::{showl,compare_order},'v) rules"
    and \<mu> :: "('f \<times> nat) \<Rightarrow> nat set"
    and \<Delta> :: "('f \<times> nat) set"
    and cn :: "'f \<times> nat" +
  fixes U T :: "('f,'v) trs"
  assumes delta: "\<Delta> = csr_u3_delta (set Rs) U"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> T"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
begin

lemma i2_root_csstep:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s,t) \<in> csrstep \<mu> (set Rs)"
  shows "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> set Rs"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    by (elim csrstepE)
  from wf lr obtain f ls where l: "l = Fun f ls"
    unfolding wf_trs_def by (cases l, auto)
  have root_l: "root l = Some (f,length ls)" unfolding l by simp
  have root_s: "root s = Some (f,length ls)" unfolding s l by simp
  show ?thesis
  proof (cases "(f,length ls) \<in> \<Delta>")
    case False
    have cs: "(s,t) \<in> csstep \<mu> (set Rs)"
      using step unfolding csstep_root_nonroot by auto
    from csrewrite_complete[OF wf cs]
    have member: "i2 t \<in> set
      (Fun f (i2_args f (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
       map i2 (csrewrite \<mu> Rs s))"
      using s l t by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project: "(comb cn
      (Fun f (i2_args f (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
       map i2 (csrewrite \<mu> Rs s)), i2 t)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have s_fun: "s = Fun f (map (\<lambda>x. x \<cdot> \<sigma>) ls)"
      unfolding s l by simp
    have s_SN: "SN_on (csstep \<mu> (set Rs))
        {Fun f (map (\<lambda>x. x \<cdot> \<sigma>) ls)}"
      using SN unfolding s_fun .
    have source_I: "i2 s = comb cn
      (Fun f (i2_args f (map (\<lambda>x. x \<cdot> \<sigma>) ls)) #
       map i2 (csrewrite \<mu> Rs s))"
      unfolding s_fun
      apply (subst i2_Fun)
      using s_SN False
      apply simp
      done
    have subset: "csstep \<mu> (ce_trs cn) \<subseteq>
        csstep \<mu> (U \<union> ce_trs cn)"
      by (rule csstep_rules_mono, simp)
    have "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>+"
      unfolding source_I by (rule trancl_mono[OF project subset])
    then show ?thesis by (rule trancl_into_rtrancl)
  next
    case True
    have True': "(f,length ls) \<in> csr_u3_delta (set Rs) U"
      using True unfolding delta .
    from True' have selected: "\<And>lr. lr \<in> set Rs \<Longrightarrow>
        root (fst lr) = Some (f,length ls) \<Longrightarrow> lr \<in> U"
      unfolding csr_u3_delta_def by auto
    have lrU: "(l,r) \<in> U"
      by (rule selected[OF lr], use root_l in simp)
    have lrT: "(l,r) \<in> T" using usable_in lrU by blast
    have lhs_disj: "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
      by (rule muterm_strongly_conservative_rule(2)[OF strong lrT])
    have rhs_disj: "mu_vars_term \<mu> r \<inter> non_mu_vars_term \<mu> r = {}"
      by (rule muterm_strongly_conservative_rule(3)[OF strong lrT])
    have active_sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
      by (rule muterm_strongly_conservative_rule(1)[OF strong lrT])
    let ?sl = "i2_subst l \<sigma>"
    let ?sr = "i2_subst r \<sigma>"
    from i2_projects_to_bracket[OF SN[unfolded s]]
    have lhs_project0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
    have lhs_bracket: "i2_bracket l \<sigma> = l \<cdot> ?sl"
      by (rule i2_bracket_as_subst[OF lhs_disj])
    have lhs_project: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sl)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      using lhs_project0 unfolding lhs_bracket .
    have sigma_active: "\<And>x. x \<in> mu_vars_term \<mu> l \<Longrightarrow>
        (?sl x,?sr x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    proof -
      fix x
      assume xl: "x \<in> mu_vars_term \<mu> l"
      show "(?sl x,?sr x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
      proof (cases "x \<in> mu_vars_term \<mu> r")
        case True
        then show ?thesis unfolding i2_subst_def using xl by simp
      next
        case False
        show ?thesis
        proof (cases "\<sigma> x")
          case (Var y)
          then show ?thesis unfolding i2_subst_def using xl False by simp
        next
          case (Fun g us)
          have q: "[] \<in> mu_fun_poss \<mu> (\<sigma> x)" unfolding Fun by simp
          have lhs_fun: "is_Fun l" unfolding l by simp
          from SN_on_active_subst_mu_subterm[
            OF wf lhs_fun SN[unfolded s] xl q]
          have sx_SN: "SN_on (csstep \<mu> (set Rs)) {\<sigma> x}" by simp
          from i2_projects_self[OF sx_SN]
          show ?thesis unfolding i2_subst_def using xl False by simp
        qed
      qed
    qed
    have sigma_inactive: "\<And>x. x \<in> non_mu_vars_term \<mu> l \<Longrightarrow>
        ?sl x = ?sr x"
    proof -
      fix x
      assume xn: "x \<in> non_mu_vars_term \<mu> l"
      have xl: "x \<notin> mu_vars_term \<mu> l" using lhs_disj xn by blast
      have xr: "x \<notin> mu_vars_term \<mu> r" using active_sub xl by blast
      show "?sl x = ?sr x" unfolding i2_subst_def using xl xr by simp
    qed
    from cssteps_active_substs[OF sigma_active sigma_inactive]
    have lhs_adjust: "(l \<cdot> ?sl,l \<cdot> ?sr)
        \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
    have root_U: "(l \<cdot> ?sr,r \<cdot> ?sr) \<in> csrstep \<mu> U"
      unfolding csrstep_iff_rstep_root rstep_r_p_s_def'
      using lrU by force
    have root_union: "(l \<cdot> ?sr,r \<cdot> ?sr)
        \<in> csstep \<mu> (U \<union> ce_trs cn)"
      using root_U csstep_rules_mono[of U "U \<union> ce_trs cn"]
      unfolding csstep_root_nonroot by auto
    have cs: "(s,t) \<in> csstep \<mu> (set Rs)"
      using step unfolding csstep_root_nonroot by auto
    from step_SN_on_target[OF SN cs]
    have rhs_SN: "SN_on (csstep \<mu> (set Rs)) {r \<cdot> \<sigma>}"
      unfolding t .
    from closed lrU have rhs_closed:
      "csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
      unfolding muterm_innermost_ur_closed_def by auto
    have rhs_roots: "\<And>p. p \<in> mu_fun_poss \<mu> r \<Longrightarrow>
        root (r |_ p) \<in> Some ` \<Delta>"
    proof -
      fix p
      assume p: "p \<in> mu_fun_poss \<mu> r"
      from mu_fun_poss_imp_fun_poss[OF p] obtain g us where
        at: "r |_ p = Fun g us" using fun_poss_fun_conv by blast
      have root: "root (r |_ p) = Some (g,length us)" unfolding at by simp
      have "(g,length us) \<in> csr_u3_delta (set Rs) U"
        by (rule csr_u3_root_rules_closed_delta[OF rhs_closed p root])
      then show "root (r |_ p) \<in> Some ` \<Delta>"
        unfolding delta root by blast
    qed
    have rhs_I0: "i2 (r \<cdot> \<sigma>) = i2_bracket r \<sigma>"
      by (rule i2_equals_bracket[OF rhs_SN rhs_roots])
    have rhs_bracket: "i2_bracket r \<sigma> = r \<cdot> ?sr"
      by (rule i2_bracket_as_subst[OF rhs_disj])
    have rhs_I: "i2 (r \<cdot> \<sigma>) = r \<cdot> ?sr"
      unfolding rhs_I0 rhs_bracket by simp
    have ce_subset: "csstep \<mu> (ce_trs cn) \<subseteq>
        csstep \<mu> (U \<union> ce_trs cn)"
      by (rule csstep_rules_mono, simp)
    have lhs_project': "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sl)
        \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF ce_subset] lhs_project])
    have lhs_adjust': "(l \<cdot> ?sl,l \<cdot> ?sr)
        \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      by (rule subsetD[OF rtrancl_mono[OF ce_subset] lhs_adjust])
    have before: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sr)
        \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      by (rule rtrancl_trans[OF lhs_project' lhs_adjust'])
    from rtrancl_into_rtrancl[OF before root_union]
    show ?thesis unfolding s t rhs_I .
  qed
qed

lemma i2_csstep:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and step: "(s,t) \<in> csstep \<mu> (set Rs)"
  shows "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
  using SN step
proof (induct s arbitrary: t)
  case (Var x)
  from csstep_Var_empty_wf[OF wf, of x t \<mu>] Var.prems(2)
  show ?case by contradiction
next
  case (Fun f ss)
  let ?A = "csstep \<mu> (U \<union> ce_trs cn)"
  show ?case
  proof (cases "(f,length ss) \<in> \<Delta>")
    case False
    from csrewrite_complete[OF wf Fun.prems(2)]
    have member: "i2 t \<in> set
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss)))"
      by simp
    from ce_trs_sound_csstep[OF member, where \<mu>=\<mu>]
    have project: "(comb cn
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss))),i2 t)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>+" .
    have source_I: "i2 (Fun f ss) = comb cn
      (Fun f (i2_args f ss) # map i2 (csrewrite \<mu> Rs (Fun f ss)))"
      apply (subst i2_Fun)
      using False Fun.prems(1)
      apply simp
      done
    have subset: "csstep \<mu> (ce_trs cn) \<subseteq> ?A"
      by (rule csstep_rules_mono, simp)
    have "(i2 (Fun f ss),i2 t) \<in> ?A\<^sup>+"
      unfolding source_I by (rule trancl_mono[OF project subset])
    then show ?thesis by (rule trancl_into_rtrancl)
  next
    case True
    from Fun.prems(2) have cases:
      "(Fun f ss,t) \<in> csrstep \<mu> (set Rs) \<or>
       (Fun f ss,t) \<in> csnrstep \<mu> (set Rs)"
      unfolding csstep_root_nonroot by auto
    from cases show ?thesis
    proof
      assume root: "(Fun f ss,t) \<in> csrstep \<mu> (set Rs)"
      show ?thesis by (rule i2_root_csstep[OF Fun.prems(1) root])
    next
      assume nonroot: "(Fun f ss,t) \<in> csnrstep \<mu> (set Rs)"
      from nonroot obtain i ts where i: "i < length ss"
        and active: "i \<in> \<mu> (f,length ss)"
        and t: "t = Fun f ts" and len: "length ts = length ss"
        and substep: "(ss ! i,ts ! i) \<in> csstep \<mu> (set Rs)"
        and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
          ts ! j = ss ! j"
        by (elim csnrstep_FunE, blast)
      have empty: "[] \<in> mu_poss \<mu> (ss ! i)"
        by (cases "ss ! i") simp_all
      have pos: "i # [] \<in> mu_poss \<mu> (Fun f ss)"
        using i active empty by auto
      from SN_on_mu_pos[OF wf pos Fun.prems(1)]
      have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}"
        using i by simp
      from Fun.hyps[OF nth_mem[OF i], of "ts ! i", OF sub_SN substep]
      have sub_I: "(i2 (ss ! i),i2 (ts ! i)) \<in> ?A\<^sup>*" .
      have ts_update: "ts = ss[i := ts ! i]"
      proof (rule nth_equalityI)
        show "length ts = length (ss[i := ts ! i])" using len by simp
        fix j
        assume j: "j < length ts"
        show "ts ! j = (ss[i := ts ! i]) ! j"
        proof (cases "j=i")
          case True
          with i show ?thesis by simp
        next
          case False
          from j len have jss: "j < length ss" by simp
          from same[OF jss False] False i show ?thesis by simp
        qed
      qed
      have i_args: "i < length (i2_args f ss)" using i by simp
      have active_args: "i \<in> \<mu> (f,length (i2_args f ss))"
        using active by simp
      have source_nth: "i2_args f ss ! i = i2 (ss ! i)"
        using i active by (simp add: i2_args_nth)
      have whole: "(Fun f (i2_args f ss),
          Fun f ((i2_args f ss)[i := i2 (ts ! i)])) \<in> ?A\<^sup>*"
        apply (rule cssteps_Fun_updateI)
          apply (rule i_args)
         apply (rule active_args)
        using sub_I source_nth
        apply simp
        done
      have args_update: "i2_args f ts =
          (i2_args f ss)[i := i2 (ts ! i)]"
      proof (rule nth_equalityI)
        show "length (i2_args f ts) =
          length ((i2_args f ss)[i := i2 (ts ! i)])" using len by simp
        fix j
        assume j: "j < length (i2_args f ts)"
        then have jts: "j < length ts" by simp
        then have jss: "j < length ss" using len by simp
        show "i2_args f ts ! j =
          (i2_args f ss)[i := i2 (ts ! i)] ! j"
        proof (cases "j=i")
          case True
          then show ?thesis using i jts active len
            by (simp add: i2_args_nth)
        next
          case False
          have same_j: "ts ! j = ss ! j" by (rule same[OF jss False])
          show ?thesis using jts jss False len same_j
            by (simp add: i2_args_nth nth_list_update)
        qed
      qed
      have target_SN: "SN_on (csstep \<mu> (set Rs)) {t}"
        by (rule step_SN_on_target[OF Fun.prems(1) Fun.prems(2)])
      have target_delta: "(f,length ts) \<in> \<Delta>" using True len by simp
      have source_I: "i2 (Fun f ss) = Fun f (i2_args f ss)"
        apply (subst i2_Fun)
        using True Fun.prems(1)
        apply simp
        done
      have target_I: "i2 t = Fun f (i2_args f ts)"
        unfolding t
        apply (subst i2_Fun)
        using target_delta target_SN t
        apply simp
        done
      show ?thesis unfolding source_I target_I args_update by (rule whole)
    qed
  qed
qed

lemma i2_cssteps:
  assumes SN: "SN_on (csstep \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csstep \<mu> (set Rs))\<^sup>*"
  shows "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
  using steps SN
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have y_SN: "SN_on (csstep \<mu> (set Rs)) {y}"
  proof (rule ccontr)
    assume "\<not> SN_on (csstep \<mu> (set Rs)) {y}"
    from steps_notSN_on_source[OF step.hyps(1) this]
      step.prems show False by contradiction
  qed
  from step.hyps(3)[OF step.prems]
  have prefix: "(i2 s,i2 y) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*" .
  from i2_csstep[OF y_SN step.hyps(2)]
  have last: "(i2 y,i2 z) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*" .
  show ?case by (rule rtrancl_trans[OF prefix last])
qed

lemma i2_pair_rhs:
  assumes dp: "(l,r) \<in> T"
    and SN: "SN_on (csstep \<mu> (set Rs)) {r \<cdot> \<sigma>}"
  shows "i2 (r \<cdot> \<sigma>) = r \<cdot> i2_subst r \<sigma>"
proof -
  have disj: "mu_vars_term \<mu> r \<inter> non_mu_vars_term \<mu> r = {}"
    by (rule muterm_strongly_conservative_rule(3)[OF strong dp])
  have bracket: "i2_bracket r \<sigma> = r \<cdot> i2_subst r \<sigma>"
    by (rule i2_bracket_as_subst[OF disj])
  show ?thesis
  proof (cases r)
    case (Var x)
    then show ?thesis unfolding i2_subst_def mu_vars_term_def by simp
  next
    case (Fun f ts)
    from closed dp have rhs_closed:
      "csr_u3_root_rules_closed (set Rs) U r (mu_fun_poss \<mu> r)"
      unfolding muterm_innermost_ur_closed_def Fun by auto
    have roots: "\<And>p. p \<in> mu_fun_poss \<mu> r \<Longrightarrow>
        root (r |_ p) \<in> Some ` \<Delta>"
    proof -
      fix p
      assume p: "p \<in> mu_fun_poss \<mu> r"
      from mu_fun_poss_imp_fun_poss[OF p] obtain g us where
        at: "r |_ p = Fun g us" using fun_poss_fun_conv by blast
      have root: "root (r |_ p) = Some (g,length us)" unfolding at by simp
      have "(g,length us) \<in> csr_u3_delta (set Rs) U"
        by (rule csr_u3_root_rules_closed_delta[OF rhs_closed p root])
      then show "root (r |_ p) \<in> Some ` \<Delta>"
        unfolding delta root by blast
    qed
    from i2_equals_bracket[OF SN roots] bracket
    show ?thesis by simp
  qed
qed

lemma i2_pair_adjust:
  assumes dp: "(l,r) \<in> T"
    and SN: "SN_on (csstep \<mu> (set Rs)) {l \<cdot> \<sigma>}"
  shows "(i2 (l \<cdot> \<sigma>),l \<cdot> i2_subst r \<sigma>)
    \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
proof -
  have lhs_disj: "mu_vars_term \<mu> l \<inter> non_mu_vars_term \<mu> l = {}"
    by (rule muterm_strongly_conservative_rule(2)[OF strong dp])
  have active_sub: "mu_vars_term \<mu> r \<subseteq> mu_vars_term \<mu> l"
    by (rule muterm_strongly_conservative_rule(1)[OF strong dp])
  let ?sl = "i2_subst l \<sigma>"
  let ?sr = "i2_subst r \<sigma>"
  from i2_projects_to_bracket[OF SN]
  have project0: "(i2 (l \<cdot> \<sigma>),i2_bracket l \<sigma>)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  have bracket: "i2_bracket l \<sigma> = l \<cdot> ?sl"
    by (rule i2_bracket_as_subst[OF lhs_disj])
  have project: "(i2 (l \<cdot> \<sigma>),l \<cdot> ?sl)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    using project0 unfolding bracket .
  have sigma_active: "\<And>x. x \<in> mu_vars_term \<mu> l \<Longrightarrow>
      (?sl x,?sr x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
  proof -
    fix x
    assume xl: "x \<in> mu_vars_term \<mu> l"
    show "(?sl x,?sr x) \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
    proof (cases "x \<in> mu_vars_term \<mu> r")
      case True
      then show ?thesis unfolding i2_subst_def using xl by simp
    next
      case False
      show ?thesis
      proof (cases "\<sigma> x")
        case (Var y)
        then show ?thesis unfolding i2_subst_def using xl False by simp
      next
        case (Fun g us)
        have lhs_fun: "is_Fun l" by (rule lhs_T[OF dp])
        have q: "[] \<in> mu_fun_poss \<mu> (\<sigma> x)" unfolding Fun by simp
        from SN_on_active_subst_mu_subterm[OF wf lhs_fun SN xl q]
        have sx_SN: "SN_on (csstep \<mu> (set Rs)) {\<sigma> x}" by simp
        from i2_projects_self[OF sx_SN]
        show ?thesis unfolding i2_subst_def using xl False by simp
      qed
    qed
  qed
  have sigma_inactive: "\<And>x. x \<in> non_mu_vars_term \<mu> l \<Longrightarrow>
      ?sl x = ?sr x"
  proof -
    fix x
    assume xn: "x \<in> non_mu_vars_term \<mu> l"
    have xl: "x \<notin> mu_vars_term \<mu> l" using lhs_disj xn by blast
    have xr: "x \<notin> mu_vars_term \<mu> r" using active_sub xl by blast
    show "?sl x = ?sr x" unfolding i2_subst_def using xl xr by simp
  qed
  from cssteps_active_substs[OF sigma_active sigma_inactive]
  have adjust: "(l \<cdot> ?sl,l \<cdot> ?sr)
      \<in> (csstep \<mu> (ce_trs cn))\<^sup>*" .
  show ?thesis by (rule rtrancl_trans[OF project adjust])
qed

lemma i2_sharp_csdp_step:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
    and step: "(Fun (shp f) ss,t) \<in> csdp_step shp \<mu> (set Rs)"
  shows "(i2 (Fun (shp f) ss),i2 t)
    \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  have step': "(sharp_term shp (Fun f ss),t)
      \<in> csdp_step shp \<mu> (set Rs)" using step by simp
  have converted: "\<exists>u. t = sharp_term shp u \<and>
      (Fun f ss,u) \<in> csnrstep \<mu> (set Rs)"
    apply (rule sharp_csdp_step_imp_csnrstep)
      apply (rule wf)
     apply (rule fresh)
    apply (rule marked_inj)
    apply (rule step')
    done
  from converted obtain u where t0: "t = sharp_term shp u"
    and nonroot: "(Fun f ss,u) \<in> csnrstep \<mu> (set Rs)" by blast
  from nonroot obtain i us where i: "i < length ss"
    and active: "i \<in> \<mu> (f,length ss)"
    and u: "u = Fun f us" and len: "length us = length ss"
    and substep: "(ss ! i,us ! i) \<in> csstep \<mu> (set Rs)"
    and same: "\<And>j. j < length ss \<Longrightarrow> j \<noteq> i \<Longrightarrow>
      us ! j = ss ! j"
    by (elim csnrstep_FunE, blast)
  have t: "t = Fun (shp f) us" using t0 u by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF i active SN]
  have sub_SN: "SN_on (csstep \<mu> (set Rs)) {ss ! i}" .
  from i2_csstep[OF sub_SN substep]
  have sub_I: "(i2 (ss ! i),i2 (us ! i))
      \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*" .
  have sharp_delta: "(shp f,length ss) \<in> \<Delta>"
  proof -
    have sharp_delta': "(shp f,length ss) \<in> csr_u3_delta (set Rs) U"
    proof (unfold csr_u3_delta_def, intro CollectI ballI impI)
      fix lr
      assume mem: "lr \<in> set Rs"
        and root: "root (fst lr) = Some (shp f,length ss)"
      from mem root have "defined (set Rs) (shp f,length ss)"
        unfolding defined_def
        by (intro exI[of _ "fst lr"] exI[of _ "snd lr"], simp)
      with fresh[of f "length ss"] show "lr \<in> U" by contradiction
    qed
    show ?thesis using sharp_delta' unfolding delta .
  qed
  have target_delta: "(shp f,length us) \<in> \<Delta>" using sharp_delta len by simp
  have source_cs_SN: "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
  proof (rule ccontr)
    assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
    have undef: "\<not> defined (set Rs) (shp f,length ss)" by (rule fresh)
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
    obtain j where j: "j < length ss"
      and active_j: "j \<in> \<mu> (shp f,length ss)"
      and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {ss ! j}" by blast
    have active_orig: "j \<in> \<mu> (f,length ss)" using active_j marked_mu by simp
    from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig SN]
      notSN_j show False by contradiction
  qed
  have target_dp_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {t}"
    by (rule step_SN_on_target[OF SN step])
  have target_cs_SN: "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) us}"
  proof (rule ccontr)
    assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) us}"
    have undef: "\<not> defined (set Rs) (shp f,length us)" by (rule fresh)
    from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
    obtain j where j: "j < length us"
      and active_j: "j \<in> \<mu> (shp f,length us)"
      and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {us ! j}" by blast
    have marked_mu_us: "\<mu> (shp f,length us) = \<mu> (f,length us)"
      using marked_mu len by simp
    have active_orig: "j \<in> \<mu> (f,length us)" using active_j marked_mu_us by simp
    have target_dp_SN': "SN_on (csdp_step shp \<mu> (set Rs))
        {Fun (shp f) us}" using target_dp_SN unfolding t .
    from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig target_dp_SN']
      notSN_j show False by contradiction
  qed
  have us_update: "us = ss[i := us ! i]"
  proof (rule nth_equalityI)
    show "length us = length (ss[i := us ! i])" using len by simp
    fix j
    assume j: "j < length us"
    show "us ! j = (ss[i := us ! i]) ! j"
    proof (cases "j=i")
      case True
      with i show ?thesis by simp
    next
      case False
      from j len have jss: "j < length ss" by simp
      from same[OF jss False] False i show ?thesis by simp
    qed
  qed
  have marked_active: "i \<in> \<mu> (shp f,length (i2_args (shp f) ss))"
    using active marked_mu by auto
  have source_nth: "i2_args (shp f) ss ! i = i2 (ss ! i)"
    using i marked_active by (simp add: i2_args_nth)
  have whole: "(Fun (shp f) (i2_args (shp f) ss),
      Fun (shp f) ((i2_args (shp f) ss)[i := i2 (us ! i)]))
      \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    apply (rule cssteps_Fun_updateI)
      using i apply simp
     apply (rule marked_active)
    using sub_I source_nth apply simp
    done
  have args_update: "i2_args (shp f) us =
      (i2_args (shp f) ss)[i := i2 (us ! i)]"
  proof (rule nth_equalityI)
    show "length (i2_args (shp f) us) =
      length ((i2_args (shp f) ss)[i := i2 (us ! i)])" using len by simp
    fix j
    assume j: "j < length (i2_args (shp f) us)"
    then have jus: "j < length us" by simp
    then have jss: "j < length ss" using len by simp
    show "i2_args (shp f) us ! j =
      (i2_args (shp f) ss)[i := i2 (us ! i)] ! j"
    proof (cases "j=i")
      case True
      then show ?thesis using i jus marked_active len
        by (simp add: i2_args_nth)
    next
      case False
      have same_j: "us ! j = ss ! j" by (rule same[OF jss False])
      show ?thesis using jus jss False len same_j
        by (simp add: i2_args_nth nth_list_update)
    qed
  qed
  have source_I: "i2 (Fun (shp f) ss) = Fun (shp f) (i2_args (shp f) ss)"
    apply (subst i2_Fun)
    using sharp_delta source_cs_SN
    apply simp
    done
  have target_I: "i2 t = Fun (shp f) (i2_args (shp f) us)"
    unfolding t
    apply (subst i2_Fun)
    using target_delta target_cs_SN
    apply simp
    done
  show ?thesis unfolding source_I target_I args_update by (rule whole)
qed

lemma i2_sharp_csdp_steps:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and source: "s = Fun (shp f) ss"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {s}"
    and steps: "(s,t) \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
  shows "(i2 s,i2 t) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
proof -
  have combined: "(i2 s,i2 t) \<in>
      (csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<and>
      SN_on (csdp_step shp \<mu> (set Rs)) {t} \<and>
      (\<exists>us. t = Fun (shp f) us \<and> length us = length ss)"
    using steps SN source
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case by auto
  next
    case (step y z)
    from step.hyps(3)[OF step.prems(1) step.prems(2)]
    have prefix: "(i2 s,i2 y) \<in>
        (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      and y_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {y}"
      and y_shape: "\<exists>us. y = Fun (shp f) us \<and> length us = length ss" by blast+
    from y_shape obtain us where y: "y = Fun (shp f) us"
      and us_len: "length us = length ss" by blast
    have one: "(i2 y,i2 z) \<in>
        (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
      unfolding y
      apply (rule i2_sharp_csdp_step[where shp=shp and f=f and ss=us and t=z])
          apply (rule fresh)
         apply (rule marked_inj)
        using marked_mu us_len apply simp
       using y_SN y apply simp
      using step.hyps(2) y apply simp
      done
    have z_SN: "SN_on (csdp_step shp \<mu> (set Rs)) {z}"
      by (rule step_SN_on_target[OF y_SN step.hyps(2)])
    have z_shape: "\<exists>vs. z = Fun (shp f) vs \<and> length vs = length ss"
    proof -
      have sharp_step: "(sharp_term shp (Fun f us),z)
          \<in> csdp_step shp \<mu> (set Rs)" using step.hyps(2) unfolding y by simp
      from sharp_csdp_step_imp_csnrstep[OF wf fresh marked_inj sharp_step]
      obtain u where z: "z = sharp_term shp u"
        and nonroot: "(Fun f us,u) \<in> csnrstep \<mu> (set Rs)" by blast
      from nonroot obtain vs where u: "u = Fun f vs"
        and len: "length vs = length us" by (elim csnrstep_FunE, blast)
      with z us_len show ?thesis by auto
    qed
    show ?case
      by (intro conjI rtrancl_trans[OF prefix one] z_SN z_shape)
  qed
  then show ?thesis by blast
qed

lemma SN_sharp_csdp_imp_SN_csstep:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_mu: "\<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and SN: "SN_on (csdp_step shp \<mu> (set Rs)) {Fun (shp f) ss}"
  shows "SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
proof (rule ccontr)
  assume notSN: "\<not> SN_on (csstep \<mu> (set Rs)) {Fun (shp f) ss}"
  have undef: "\<not> defined (set Rs) (shp f,length ss)" by (rule fresh)
  from csstep_Fun_undefined_root_notSN_imp_mu_arg_notSN[OF wf undef notSN]
  obtain j where j: "j < length ss"
    and active: "j \<in> \<mu> (shp f,length ss)"
    and notSN_j: "\<not> SN_on (csstep \<mu> (set Rs)) {ss ! j}" by blast
  have active_orig: "j \<in> \<mu> (f,length ss)" using active marked_mu by simp
  from SN_sharp_csdp_imp_SN_active_arg[OF j active_orig SN]
    notSN_j show False by contradiction
qed

theorem finite_min_csr_dpp_strong_usable_redpair:
  fixes shp :: "'f \<Rightarrow> 'f"
  assumes fresh: "\<And>g n. \<not> defined (set Rs) (shp g,n)"
    and marked_inj: "inj shp"
    and marked_mu: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (shp f) ss \<or> r = Fun (shp f) ss) \<longrightarrow>
      \<mu> (shp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pairs_in: "P \<subseteq> T"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (shp f) ls) \<and>
      (\<exists>g rs. r = Fun (shp g) rs)"
    and rewrite_NS: "csstep \<mu> (U \<union> ce_trs cn) \<subseteq> NS"
    and fin: "finite_min_csr_dpp shp \<mu> (P - S) (set Rs)"
  shows "finite_min_csr_dpp shp \<mu> P (set Rs)"
proof -
  interpret rp: compat_redpair_order S NS by (rule redpair)
  have rewrite_star_NS: "(csstep \<mu> (U \<union> ce_trs cn))\<^sup>* \<subseteq> NS"
  proof (rule subrelI)
    fix x y
    assume steps: "(x,y) \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
    show "(x,y) \<in> NS" using steps
    proof (induct rule: rtrancl_induct)
      case base
      show ?case using rp.refl_NS unfolding refl_on_def by blast
    next
      case (step y z)
      have yz: "(y,z) \<in> NS" using rewrite_NS step.hyps(2) by blast
      from transD[OF rp.trans_NS step.hyps(3) yz] show ?case .
    qed
  qed
  show ?thesis
  proof (rule finite_min_csr_dpp_redpair_simulation[
      OF redpair orient _ fin])
    fix s t \<sigma>
    assume pair: "\<And>k. (s k,t k) \<in> P"
      and target_SN: "\<And>k. SN_on (csdp_step shp \<mu> (set Rs))
        {t k \<cdot> \<sigma> k}"
      and steps: "\<And>k. (t k \<cdot> \<sigma> k,
        s (Suc k) \<cdot> \<sigma> (Suc k))
        \<in> (csdp_step shp \<mu> (set Rs))\<^sup>*"
    let ?\<tau> = "\<lambda>k. i2_subst (t k) (\<sigma> k)"
    have between: "(t k \<cdot> ?\<tau> k,
        s (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> NS" for k
    proof -
      from pair_shape pair[of k] obtain g rs where
        tk: "t k = Fun (shp g) rs" by auto
      have mu_g: "\<mu> (shp g,length rs) = \<mu> (g,length rs)"
        using marked_mu pair[of k] tk by blast
      have target_SN0: "SN_on (csdp_step shp \<mu> (set Rs))
          {Fun (shp g) (map (\<lambda>x. x \<cdot> \<sigma> k) rs)}"
        using target_SN[of k] unfolding tk by simp
      have target_cs_SN0: "SN_on (csstep \<mu> (set Rs))
          {Fun (shp g) (map (\<lambda>x. x \<cdot> \<sigma> k) rs)}"
        apply (rule SN_sharp_csdp_imp_SN_csstep[
          where shp=shp and f=g and ss="map (\<lambda>x. x \<cdot> \<sigma> k) rs"])
          apply (rule fresh)
         using mu_g apply simp
        apply (rule target_SN0)
        done
      have target_cs_SN: "SN_on (csstep \<mu> (set Rs))
          {t k \<cdot> \<sigma> k}" using target_cs_SN0 unfolding tk by simp
      have pair_T: "(s k,t k) \<in> T" using pairs_in pair[of k] by blast
      have rhs_I: "i2 (t k \<cdot> \<sigma> k) = t k \<cdot> ?\<tau> k"
        by (rule i2_pair_rhs[OF pair_T target_cs_SN])
      from pair_shape pair[of k] obtain f ls where
        sk: "s k = Fun (shp f) ls" by auto
      have transformed_steps: "(i2 (t k \<cdot> \<sigma> k),
          i2 (s (Suc k) \<cdot> \<sigma> (Suc k)))
          \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
        apply (rule i2_sharp_csdp_steps[
          where shp=shp and f=g and ss="map (\<lambda>x. x \<cdot> \<sigma> k) rs"])
             apply (rule fresh)
            apply (rule marked_inj)
           using mu_g apply simp
          unfolding tk apply simp
         using target_SN[of k] unfolding tk apply simp
        using steps[of k] unfolding tk apply simp
        done
      have next_dp_SN: "SN_on (csdp_step shp \<mu> (set Rs))
          {s (Suc k) \<cdot> \<sigma> (Suc k)}"
      proof (rule ccontr)
        assume notSN: "\<not> SN_on (csdp_step shp \<mu> (set Rs))
            {s (Suc k) \<cdot> \<sigma> (Suc k)}"
        from steps_notSN_on_source[OF steps[of k] notSN]
          target_SN[of k] show False by contradiction
      qed
      from pair_shape pair[of "Suc k"] obtain h us where
        next_s: "s (Suc k) = Fun (shp h) us" by auto
      have mu_h: "\<mu> (shp h,length us) = \<mu> (h,length us)"
        using marked_mu pair[of "Suc k"] next_s by blast
      have next_dp_SN0: "SN_on (csdp_step shp \<mu> (set Rs))
          {Fun (shp h) (map (\<lambda>x. x \<cdot> \<sigma> (Suc k)) us)}"
        using next_dp_SN unfolding next_s by simp
      have next_cs_SN0: "SN_on (csstep \<mu> (set Rs))
          {Fun (shp h) (map (\<lambda>x. x \<cdot> \<sigma> (Suc k)) us)}"
        apply (rule SN_sharp_csdp_imp_SN_csstep[
          where shp=shp and f=h and
            ss="map (\<lambda>x. x \<cdot> \<sigma> (Suc k)) us"])
          apply (rule fresh)
         using mu_h apply simp
        apply (rule next_dp_SN0)
        done
      have next_cs_SN: "SN_on (csstep \<mu> (set Rs))
          {s (Suc k) \<cdot> \<sigma> (Suc k)}"
        using next_cs_SN0 unfolding next_s by simp
      have next_pair_T: "(s (Suc k),t (Suc k)) \<in> T"
        using pairs_in pair[of "Suc k"] by blast
      have adjust: "(i2 (s (Suc k) \<cdot> \<sigma> (Suc k)),
          s (Suc k) \<cdot> ?\<tau> (Suc k))
          \<in> (csstep \<mu> (ce_trs cn))\<^sup>*"
        by (rule i2_pair_adjust[OF next_pair_T next_cs_SN])
      have ce_mono: "(csstep \<mu> (ce_trs cn))\<^sup>* \<subseteq>
          (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
        by (rule rtrancl_mono, rule csstep_rules_mono, simp)
      have total: "(i2 (t k \<cdot> \<sigma> k),
          s (Suc k) \<cdot> ?\<tau> (Suc k))
          \<in> (csstep \<mu> (U \<union> ce_trs cn))\<^sup>*"
        by (rule rtrancl_trans[OF transformed_steps ce_mono[THEN subsetD, OF adjust]])
      from rewrite_star_NS[THEN subsetD, OF total]
      show ?thesis unfolding rhs_I .
    qed
    show "\<exists>\<tau>. \<forall>k.
      (t k \<cdot> \<tau> k,s (Suc k) \<cdot> \<tau> (Suc k)) \<in> NS"
      by (rule exI[of _ ?\<tau>], use between in blast)
  qed
qed

end

theorem finite_min_csr_dpp_muterm_strong_ur_redpair:
  fixes Rs :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) rules)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
    and U T P :: "((('f,'l) lab),'v) trs"
  assumes wf: "wf_trs (set Rs)"
    and closed: "muterm_innermost_ur_closed (set Rs) U \<mu> T"
    and strong: "muterm_strongly_conservative \<mu> T"
    and usable_in: "U \<subseteq> T"
    and lhs_T: "\<And>l r. (l,r) \<in> T \<Longrightarrow> is_Fun l"
    and fresh: "\<And>f n. \<not> defined (set Rs) (Sharp f,n)"
    and marked_mu: "\<forall>(l,r)\<in>P. \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      \<mu> (Sharp f,length ss) = \<mu> (f,length ss)"
    and redpair: "compat_redpair_order S NS"
    and orient: "P \<subseteq> S \<union> NS"
    and pairs_in: "P \<subseteq> T"
    and pair_shape: "\<forall>(l,r)\<in>P.
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    and U_NS: "U \<subseteq> NS"
    and ce: "ce_compatible NS"
    and fin: "finite_min_csr_dpp Sharp \<mu>
      (P - S) (set Rs)"
  shows "finite_min_csr_dpp Sharp \<mu> P (set Rs)"
proof (cases "P = {}")
  case True
  with fin show ?thesis by simp
next
  case False
  then obtain dp where dp: "dp \<in> P" by blast
  from pair_shape dp obtain f us where lhs: "fst dp = Fun (Sharp f) us"
    by (cases dp, auto)
  obtain n where ce_bound:
    "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS"
  proof (rule ce_compatibleE[OF ce])
    fix n
    assume bound: "\<And>c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> NS"
    show thesis by (rule that[OF bound])
  qed
  let ?cn = "(Sharp f,n)"
  have ce_NS: "ce_trs ?cn \<subseteq> NS" by (rule ce_bound, simp)
  interpret rp: compat_redpair_order S NS by (rule redpair)
  have rules_NS: "U \<union> ce_trs ?cn \<subseteq> NS" using U_NS ce_NS by auto
  have rewrite_NS: "csstep \<mu> (U \<union> ce_trs ?cn) \<subseteq> NS"
  proof (rule subset_trans[OF csstep_subset_rstep])
    have "rstep (U \<union> ce_trs ?cn) \<subseteq> rstep NS"
      by (rule rstep_mono[OF rules_NS])
    also have "... \<subseteq> NS" by (rule rp.rstep_NS)
    finally show "rstep (U \<union> ce_trs ?cn) \<subseteq> NS" .
  qed
  interpret L: muterm_i2_strong Rs \<mu>
      "csr_u3_delta (set Rs) U" ?cn U T
    apply unfold_locales
         apply (rule wf)
        apply simp
       apply (rule closed)
     apply (rule strong)
     apply (rule usable_in)
    using lhs_T by blast
  show ?thesis
    by (rule L.finite_min_csr_dpp_strong_usable_redpair[
      OF fresh inj_Sharp marked_mu redpair orient pairs_in pair_shape
        rewrite_NS fin])
qed

definition muterm_mu_positions_list where
  "muterm_mu_positions_list \<mu> fn = (case map_of \<mu> fn of
      None \<Rightarrow> [0..<snd fn]
    | Some is \<Rightarrow> remdups_sort is)"

lemma set_muterm_mu_positions_list [simp]:
  "set (muterm_mu_positions_list \<mu> fn) = mu_of \<mu> fn"
  unfolding muterm_mu_positions_list_def mu_of_def
  by (auto split: option.splits)

definition muterm_marked_mu_pairs_check where
  "muterm_marked_mu_pairs_check \<mu> P = list_all (\<lambda>(l,r).
    (case root l of Some (Sharp f,n) \<Rightarrow>
       muterm_mu_positions_list \<mu> (Sharp f,n) =
         muterm_mu_positions_list \<mu> (f,n) | _ \<Rightarrow> False) \<and>
    (case root r of Some (Sharp f,n) \<Rightarrow>
       muterm_mu_positions_list \<mu> (Sharp f,n) =
         muterm_mu_positions_list \<mu> (f,n) | _ \<Rightarrow> False)) P"

lemma muterm_marked_mu_pairs_check_sound:
  assumes "muterm_marked_mu_pairs_check \<mu> P"
  shows "\<forall>(l,r)\<in>set P. \<forall>f ss.
    (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
    mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
proof (intro ballI)
  fix lr
  assume mem: "lr \<in> set P"
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  from assms mem have checked:
    "(case root l of Some (Sharp g,n) \<Rightarrow>
       muterm_mu_positions_list \<mu> (Sharp g,n) =
         muterm_mu_positions_list \<mu> (g,n) | _ \<Rightarrow> False) \<and>
     (case root r of Some (Sharp g,n) \<Rightarrow>
       muterm_mu_positions_list \<mu> (Sharp g,n) =
         muterm_mu_positions_list \<mu> (g,n) | _ \<Rightarrow> False)"
    unfolding muterm_marked_mu_pairs_check_def lr
    by (auto simp: list_all_iff split: option.splits)
  show "case lr of (l,r) \<Rightarrow> \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
    unfolding lr
  proof (simp only: prod.case, intro allI impI)
    fix f ss
    assume either: "l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss"
    from checked either have eq:
      "muterm_mu_positions_list \<mu> (Sharp f,length ss) =
       muterm_mu_positions_list \<mu> (f,length ss)" by auto
    from arg_cong[OF eq,of set] show
      "mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)" by simp
  qed
qed

definition muterm_marked_mu_entry_equal where
  "muterm_marked_mu_entry_equal \<mu> e = (case e of ((h,n),is) \<Rightarrow>
    (case h of
       Sharp f \<Rightarrow> set is = mu_of \<mu> (f,n)
     | _ \<Rightarrow> set is = mu_of \<mu> (Sharp h,n)))"

definition muterm_marked_mu_equal_check where
  "muterm_marked_mu_equal_check \<mu> =
    list_all (muterm_marked_mu_entry_equal \<mu>) \<mu>"

lemma muterm_marked_mu_equal_check_sound_unlab:
  assumes "muterm_marked_mu_equal_check \<mu>"
  shows "mu_of \<mu> (Sharp (UnLab f),n) = mu_of \<mu> (UnLab f,n)"
proof (cases "map_of \<mu> (Sharp (UnLab f),n)")
  case (Some js)
  then have mem: "((Sharp (UnLab f),n),js) \<in> set \<mu>" by (rule map_of_SomeD)
  from assms mem have eq: "set js = mu_of \<mu> (UnLab f,n)"
    unfolding muterm_marked_mu_equal_check_def
    by (auto simp: list_all_iff muterm_marked_mu_entry_equal_def)
  have marked_eq: "mu_of \<mu> (Sharp (UnLab f),n) = set js"
    unfolding mu_of_def using Some by simp
  show ?thesis using marked_eq eq by simp
next
  case marked: None
  show ?thesis
  proof (cases "map_of \<mu> (UnLab f,n)")
    case None
    with marked show ?thesis unfolding mu_of_def by simp
  next
    case (Some js)
    then have mem: "((UnLab f,n),js) \<in> set \<mu>" by (rule map_of_SomeD)
    from assms mem have eq: "set js = mu_of \<mu> (Sharp (UnLab f),n)"
      unfolding muterm_marked_mu_equal_check_def
      by (auto simp: list_all_iff muterm_marked_mu_entry_equal_def)
    have plain_eq: "mu_of \<mu> (UnLab f,n) = set js"
      unfolding mu_of_def using Some by simp
    show ?thesis using plain_eq eq by simp
  qed
qed

lemma muterm_marked_mu_equal_check_sound:
  assumes check: "muterm_marked_mu_equal_check \<mu>"
    and unmarked: "\<not> is_sharp_lab f"
  shows "mu_of \<mu> (Sharp f,n) = mu_of \<mu> (f,n)"
proof (cases "map_of \<mu> (Sharp f,n)")
  case (Some js)
  then have mem: "((Sharp f,n),js) \<in> set \<mu>" by (rule map_of_SomeD)
  from check mem have eq: "set js = mu_of \<mu> (f,n)"
    unfolding muterm_marked_mu_equal_check_def
    by (auto simp: list_all_iff muterm_marked_mu_entry_equal_def)
  have "mu_of \<mu> (Sharp f,n) = set js"
    unfolding mu_of_def using Some by simp
  then show ?thesis using eq by simp
next
  case None
  have lhs: "mu_of \<mu> (Sharp f,n) = {0..<n}"
    unfolding mu_of_def using None by simp
  show ?thesis
  proof (cases "map_of \<mu> (f,n)")
    case None_f: None
    then show ?thesis using lhs unfolding mu_of_def by simp
  next
    case (Some inds)
    then have mem: "((f,n),inds) \<in> set \<mu>" by (rule map_of_SomeD)
    from check mem unmarked have eq: "set inds = mu_of \<mu> (Sharp f,n)"
      unfolding muterm_marked_mu_equal_check_def
      by (cases f; auto simp: list_all_iff muterm_marked_mu_entry_equal_def)
    have rhs: "mu_of \<mu> (f,n) = set inds"
      unfolding mu_of_def using Some by simp
    show ?thesis using lhs eq rhs by simp
  qed
qed

fun muterm_is_marked_root where
  "muterm_is_marked_root (Fun (Sharp f) ts) = True"
| "muterm_is_marked_root t = False"

lemma muterm_is_marked_root_sound:
  assumes "muterm_is_marked_root t"
  obtains f ts where "t = Fun (Sharp f) ts"
proof (cases t)
  case (Var x)
  with assms show thesis by simp
next
  case (Fun h ts)
  show thesis
  proof (cases h)
    case (Sharp f)
    show thesis by (rule that[of f ts], simp add: Fun Sharp)
  qed (use assms Fun in auto)
qed

fun muterm_is_singly_marked_root where
  "muterm_is_singly_marked_root (Fun (Sharp (UnLab f)) ts) = True"
| "muterm_is_singly_marked_root t = False"

lemma muterm_is_singly_marked_root_sound:
  assumes "muterm_is_singly_marked_root t"
  obtains f ts where "t = Fun (Sharp (UnLab f)) ts"
proof (cases t)
  case (Var x)
  with assms show thesis by simp
next
  case (Fun h ts)
  show thesis
  proof (cases h)
    case (Sharp g)
    show thesis
    proof (cases g)
      case (UnLab f)
      show thesis by (rule that[of f ts], simp add: Fun Sharp UnLab)
    qed (use assms Fun Sharp in auto)
  qed (use assms Fun in auto)
qed

definition muterm_general_typed_shape_check where
  "muterm_general_typed_shape_check P S =
    (list_all (\<lambda>(l,r).
       muterm_is_singly_marked_root l \<and>
       (is_Var r \<or> muterm_is_singly_marked_root r)) P \<and>
     list_all (\<lambda>(a,b). muterm_is_singly_marked_root b) S)"

lemma muterm_general_typed_shape_check_sound:
  assumes "muterm_general_typed_shape_check P S"
  shows "(\<forall>(l,r)\<in>set P. (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))) \<and>
    (\<forall>(a,b)\<in>set S. \<exists>g rs. b = Fun (Sharp (UnLab g)) rs)"
proof (intro conjI)
  show "\<forall>(l,r)\<in>set P. (\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))"
  proof (intro ballI, clarify)
    fix l r
    assume lr: "(l,r) \<in> set P"
    from assms lr have l: "muterm_is_singly_marked_root l"
      and r: "is_Var r \<or> muterm_is_singly_marked_root r"
      unfolding muterm_general_typed_shape_check_def
      by (auto simp: list_all_iff)
    from muterm_is_singly_marked_root_sound[OF l] obtain f ls where
      lf: "l = Fun (Sharp (UnLab f)) ls" .
    show "(\<exists>f ls. l = Fun (Sharp (UnLab f)) ls) \<and>
        (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs))"
    proof (intro conjI)
      show "\<exists>f ls. l = Fun (Sharp (UnLab f)) ls" using lf by blast
      from r show "is_Var r \<or> (\<exists>g rs. r = Fun (Sharp (UnLab g)) rs)"
      proof
        assume "is_Var r"
        then show ?thesis by simp
      next
        assume marked_r: "muterm_is_singly_marked_root r"
        from muterm_is_singly_marked_root_sound[OF marked_r]
        obtain g rs where "r = Fun (Sharp (UnLab g)) rs" .
        then show ?thesis by blast
      qed
    qed
  qed
  show "\<forall>(a,b)\<in>set S. \<exists>g rs. b = Fun (Sharp (UnLab g)) rs"
  proof (intro ballI, clarify)
    fix a b
    assume ab: "(a,b) \<in> set S"
    from assms ab have marked_b: "muterm_is_singly_marked_root b"
      unfolding muterm_general_typed_shape_check_def
      by (auto simp: list_all_iff)
    from muterm_is_singly_marked_root_sound[OF marked_b]
    obtain g rs where b: "b = Fun (Sharp (UnLab g)) rs" .
    show "\<exists>g rs. b = Fun (Sharp (UnLab g)) rs" using b by blast
  qed
qed

definition muterm_strong_ur_redpair_proc where
  "muterm_strong_ur_redpair_proc J \<mu> rp Premove U dpp = check_return (do {
    rel_impl_redpair rp;
    let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
    check (csr_sharp_pairs_check (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''strong MU-TERM usable-rule processor requires marked pairs''));
    check (muterm_marked_mu_pairs_check \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
    check (muterm_dp_active_ur_closed_check
        (dpp_ops.rules J dpp) U \<mu> (dpp_ops.pairs J dpp))
      (showsl_lit (STR ''supplied rules are not a closed active MU-TERM set''));
    check (muterm_dp_strongly_conservative_check \<mu>
        (dpp_ops.pairs J dpp @ U))
      (showsl_lit (STR ''strong MU-TERM conservativity condition failed''));
    rel_impl.ce_compat rp;
    rel_impl_ns rp (U @ pns);
    rel_impl_s rp ps
  }) (dpp_spec.delete_pairs J dpp Premove)"

text \<open>
  Executable side conditions for the general MU-TERM usable-rules
  reduction-pair processor (Theorem 93 of the arbitrary CS-problem
  development).

  Collapsing pairs are handled by their exact unhiding bridge and therefore
  are not subject to the non-collapsing right-hand-side conservativity check.
  The usable-rule boundary is closed at active positions of non-collapsing
  pair targets, unhiding rules, and usable rules.  Active projections
  represent C-epsilon.  A strict subset of pairs may be removed and the
  residual typed problem is checked recursively.
\<close>

definition muterm_noncollapsing_pairs_list where
  "muterm_noncollapsing_pairs_list P = filter (is_Fun \<circ> snd) P"

lemma set_muterm_noncollapsing_pairs_list [simp]:
  "set (muterm_noncollapsing_pairs_list P) =
    {dp \<in> set P. is_Fun (snd dp)}"
  unfolding muterm_noncollapsing_pairs_list_def by auto

definition muterm_extended_basic_seed_list where
  "muterm_extended_basic_seed_list P S U =
    muterm_noncollapsing_pairs_list P @ S @ U"

lemma set_muterm_extended_basic_seed_list [simp]:
  "set (muterm_extended_basic_seed_list P S U) =
    {dp \<in> set P. is_Fun (snd dp)} \<union> set S \<union> set U"
  unfolding muterm_extended_basic_seed_list_def by auto

definition muterm_general_ur_redpair_proc where
  "muterm_general_ur_redpair_proc J \<mu> rp Premove U S dpp =
    check_return (case rel_impl.not_wst rp of
      None \<Rightarrow> error (showsl_lit
        (STR ''general MU-TERM reduction pair does not expose weak-subterm exceptions''))
    | Some F \<Rightarrow> do {
        rel_impl_redpair rp;
        let (ps,pns) = dpp_ops.split_pairs J dpp Premove;
        check (list_all (\<lambda>lr. lr \<in> set (dpp_ops.rules J dpp)) U \<and>
            list_all (\<lambda>lr. csr_rta08_active_root_rules_check
              (dpp_ops.rules J dpp) U \<mu> (snd lr))
              (muterm_extended_basic_seed_list (dpp_ops.pairs J dpp) S U))
          (showsl_lit (STR ''general MU-TERM usable-rule closure failed''));
        check (rhs_mu_vars_condition_list \<mu>
            (muterm_extended_basic_seed_list (dpp_ops.pairs J dpp) S U))
          (showsl_lit (STR ''general MU-TERM conservativity condition failed''));
        check (list_all (\<lambda>(l,r).
            set (mu_vars_term_list \<mu> l) \<inter>
              set (non_mu_vars_term_list \<mu> l) = {})
            (dpp_ops.pairs J dpp @ S @ U))
          (showsl_lit (STR ''general MU-TERM left-hand-side activity partition failed''));
        check (list_all (\<lambda>(l,r). case r of
            Var x \<Rightarrow> x \<in> set (mu_vars_term_list \<mu> l)
          | Fun f ts \<Rightarrow> True) (dpp_ops.pairs J dpp))
          (showsl_lit (STR ''general MU-TERM collapsing variable is not active''));
        check (muterm_general_typed_shape_check (dpp_ops.pairs J dpp) S)
          (showsl_lit (STR ''general MU-TERM typed pair or unhiding shape failed''));
        check (list_all (is_Fun \<circ> fst) S)
          (showsl_lit (STR ''general MU-TERM unhiding left-hand side is a variable''));
        check (muterm_marked_mu_equal_check \<mu>)
          (showsl_lit (STR ''marked replacement-map entries differ from their source symbols''));
        rel_impl.ce_compat rp;
        rel_impl_ns rp
          (U @ S @ csr_rta08_projection_rules_list \<mu> F @ pns)
          <+? (\<lambda>s. showsl_lit
            (STR ''problem weakly orienting general MU-TERM rules, unhiding rules, projections, or pairs\<newline>'' ) \<circ> s);
        rel_impl_s rp ps
          <+? (\<lambda>s. showsl_lit
            (STR ''problem strictly orienting general MU-TERM pairs\<newline>'' ) \<circ> s)
      }) (dpp_spec.delete_pairs J dpp Premove)"

lemma muterm_strong_ur_redpair_proc_sound:
  fixes J :: "('dpp,('f::{showl,compare_order},'l::{showl,compare_order}) lab,string) dpp_ops"
    and \<mu> :: "(('f,'l) lab) muL"
    and rp :: "(('f,'l) lab,string) rel_impl"
  assumes J: "dpp_spec J" and rp: "rel_impl rp"
    and proc: "muterm_strong_ur_redpair_proc J \<mu> rp Premove U dpp = return dpp'"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain ps pns where split: "split_pairs dpp Premove = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Premove"
    and pns: "set pns = set (pairs dpp) - set Premove" by auto
  from proc[unfolded muterm_strong_ur_redpair_proc_def Let_def split,simplified]
  have valid: "isOK (rel_impl_redpair rp)"
    and shape: "csr_sharp_pairs_check (pairs dpp)"
    and marked: "muterm_marked_mu_pairs_check \<mu> (pairs dpp)"
    and closed: "muterm_dp_active_ur_closed_check (rules dpp) U \<mu> (pairs dpp)"
    and strong: "muterm_dp_strongly_conservative_check \<mu> (pairs dpp @ U)"
    and ce: "isOK (rel_impl.ce_compat rp)"
    and weak: "isOK (rel_impl_ns rp (U @ pns))"
    and strict: "isOK (rel_impl_s rp ps)"
    and dpp': "dpp' = delete_pairs dpp Premove"
    by (auto simp: isOK_check rel_impl_list)
  from valid[unfolded rel_impl_redpair_def,simplified]
  have impl_valid: "isOK (rel_impl.valid rp)"
    and standard: "isOK (rel_impl.standard rp)"
    and sn: "isOK (rel_impl.SN rp)"
    and subst: "isOK (rel_impl.subst_s rp)" by auto
  let ?all = "ps @ U @ pns"
  from rp[unfolded rel_impl_def] impl_valid
  have all_rel: "\<forall>V. \<exists>S NS NST. rel_impl_prop rp V S NS NST" by blast
  have all_rel': "\<exists>S NS NST. rel_impl_prop rp ?all S NS NST"
    by (rule spec[OF all_rel])
  obtain S NS NST where rel_prop: "rel_impl_prop rp ?all S NS NST"
    using all_rel' by presburger
  from rel_prop strict weak subst sn standard ce
  have strict_S: "set ps \<subseteq> S"
    and U_NS: "set U \<subseteq> NS"
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
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Premove"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      pairs_sound[of dpp'] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using dpp' delete_P_Pw_sound[of dpp Premove Premove]
      rules_sound[of dpp'] by auto
  have sub: "set (pairs dpp) - S \<subseteq> set (pairs dpp) - set Premove"
    using strict_S unfolding ps by auto
  have fin_S: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - S) (set (rules dpp))"
    by (rule finite_min_csr_dpp_mono_pairs[OF sub fin[unfolded pairs' rules']])
  have shape_sem: "\<forall>(l,r)\<in>set (pairs dpp).
      (\<exists>f ls. l = Fun (Sharp f) ls) \<and>
      (\<exists>g rs. r = Fun (Sharp g) rs)"
    by (rule csr_sharp_pairs_check_sound[OF shape])
  have marked_sem: "\<forall>(l,r)\<in>set (pairs dpp). \<forall>f ss.
      (l = Fun (Sharp f) ss \<or> r = Fun (Sharp f) ss) \<longrightarrow>
      mu_of \<mu> (Sharp f,length ss) = mu_of \<mu> (f,length ss)"
    by (rule muterm_marked_mu_pairs_check_sound[OF marked])
  have closed_sem: "muterm_innermost_ur_closed (set (rules dpp))
      (set U) (mu_of \<mu>) (set (pairs dpp) \<union> set U)"
  proof -
    have base: "muterm_innermost_ur_closed (set (rules dpp))
      (set U) (mu_of \<mu>) (set (pairs dpp))"
      by (rule muterm_dp_active_ur_closed_check_sound[OF closed])
    show ?thesis using base unfolding muterm_innermost_ur_closed_def by auto
  qed
  have strong_sem: "muterm_strongly_conservative (mu_of \<mu>)
      (set (pairs dpp) \<union> set U)"
    using muterm_dp_strongly_conservative_check_sound[OF strong] by simp
  have lhs: "\<And>l r. (l,r) \<in> set (pairs dpp) \<union> set U \<Longrightarrow> is_Fun l"
  proof -
    fix l r
    assume mem: "(l,r) \<in> set (pairs dpp) \<union> set U"
    show "is_Fun l"
    proof (cases "(l,r) \<in> set (pairs dpp)")
      case True
      from shape True have check_l:
        "case root l of Some (Sharp f,n) \<Rightarrow> True | _ \<Rightarrow> False"
        unfolding csr_sharp_pairs_check_def by (auto simp: list_all_iff)
      from check_l obtain f n where "root l = Some (Sharp f,n)"
        by (cases "root l"; auto split: lab.splits)
      then obtain ls where "l = Fun (Sharp f) ls"
        by (cases l, auto)
      then show ?thesis by simp
    next
      case False
      from closed_sem have U_rules: "set U \<subseteq> set (rules dpp)"
        unfolding muterm_innermost_ur_closed_def by simp
      have in_U: "(l,r) \<in> set U" using mem False by blast
      have in_R: "(l,r) \<in> set (rules dpp)" using U_rules in_U by blast
      show ?thesis using wf[unfolded wf_trs_def] in_R
        by (metis Un_iff eq_fst_iff is_FunI)
    qed
  qed
  show ?thesis
    by (rule finite_min_csr_dpp_muterm_strong_ur_redpair[
      OF wf closed_sem strong_sem _ lhs fresh marked_sem redpair orient _
        shape_sem U_NS ce_NS fin_S]; auto)
qed

definition muterm_qcs_ur_closed where
  "muterm_qcs_ur_closed R S W \<mu> P \<longleftrightarrow>
    S \<subseteq> W \<and> W \<subseteq> R \<union> S \<and>
    (\<forall>lr\<in>W \<inter> R.
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)) \<and>
    (\<forall>lr\<in>S.
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)) \<and>
    (\<forall>dp\<in>P. is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd dp))"

text \<open>
  Once collapsing MU steps have been expanded into ordinary dependency
  pairs, the unhiding rules are part of the strict expanded step rather than
  weak rules between typed steps.  Consequently they need to be closed, but
  need not occur in the executable weak-rule set.
\<close>

definition muterm_qcs_expanded_ur_closed where
  "muterm_qcs_expanded_ur_closed R S W \<mu> P \<longleftrightarrow>
    W \<subseteq> R \<and>
    (\<forall>lr\<in>W.
      qcs_ur_closed_term R W \<mu> (snd lr)) \<and>
    (\<forall>lr\<in>S.
      qcs_ur_closed_dp_rhs R W \<mu> (snd lr)) \<and>
    (\<forall>dp\<in>P. is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs R W \<mu> (snd dp))"

lemma muterm_qcs_ur_closed_S:
  assumes "muterm_qcs_ur_closed R S W \<mu> P"
  shows "S \<subseteq> W"
  using assms unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_W:
  assumes "muterm_qcs_ur_closed R S W \<mu> P"
  shows "W \<subseteq> R \<union> S"
  using assms unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_rule:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and lr: "lr \<in> W \<inter> R"
  shows "qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
  using closed lr unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_unhiding_rule:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and lr: "lr \<in> S"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
  using closed lr unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_pair:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and dp: "dp \<in> P" and rhs: "\<not> is_Var (snd dp)"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd dp)"
  using closed dp rhs unfolding muterm_qcs_ur_closed_def by auto

lemma muterm_qcs_ur_closed_unhiding_target:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and step: "(s, sharp_term Sharp t) \<in> rrstep S"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
    (sharp_term Sharp t)"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> S"
    and target: "sharp_term Sharp t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by auto
  from muterm_qcs_ur_closed_unhiding_rule[OF closed lr]
  have rhs: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> r" by simp
  from qcs_ur_closed_dp_rhs_subst[OF rhs, of \<sigma>]
  show ?thesis unfolding target .
qed

lemma muterm_qcs_noncollapsing_target:
  assumes closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and pair: "muterm_noncollapsing_rrstep P s t"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from pair obtain l r \<sigma> where lr: "(l,r) \<in> P"
    and r_fun: "\<not> is_Var r" and target: "t = r \<cdot> \<sigma>"
    unfolding muterm_noncollapsing_rrstep_def by auto
  from closed lr r_fun
  have r_closed: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> r"
    unfolding muterm_qcs_ur_closed_def by auto
  from qcs_ur_closed_dp_rhs_subst[OF r_closed, of \<sigma>]
  show ?thesis unfolding target .
qed

lemma muterm_qcs_noncollapsing_suffix:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and pair: "muterm_noncollapsing_rrstep P s t"
    and suffix: "(t,u) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(t,u) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> u"
proof -
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
    qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
    by (rule muterm_qcs_noncollapsing_target[OF closed pair])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules target suffix]
  show ?thesis by auto
qed

lemma muterm_qcs_collapsing_unhiding_suffix:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and unhide: "(t,sharp_term Sharp v) \<in> rrstep S"
    and suffix: "(sharp_term Sharp v,u) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(sharp_term Sharp v,u) \<in>
      (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> u"
proof -
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
    qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
    (sharp_term Sharp v)"
    by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules target suffix]
  show ?thesis by auto
qed

lemma muterm_unhiding_next_closed:
  assumes wf: "wf_trs R"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and cases:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have target: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp u)"
  proof -
    from cases show ?thesis
    proof
      assume noncoll: "muterm_noncollapsing_rrstep P
        (sharp_term Sharp s) (sharp_term Sharp u)"
      show ?thesis
        by (rule muterm_qcs_noncollapsing_target[OF closed noncoll])
    next
      assume "\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
        (x,sharp_term Sharp u) \<in> rrstep S"
      then obtain x where unhide: "(x,sharp_term Sharp u) \<in> rrstep S"
        by blast
      show ?thesis
        by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
    qed
  qed
  show ?thesis using hp_u target by blast
qed

lemma muterm_unhiding_relstep_usable:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and hp: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t"
    and closed_t: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp t)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
  shows "\<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
proof -
  from hp have Tinf: "t \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    unfolding has_muterm_unhiding_property_def by auto
  from mu_Tinf_imp_SN_csnr_first_csrstep[OF wf Tinf]
  obtain s v where pref: "(t,s) \<in> (csnrstep \<mu> R)\<^sup>*"
    and root: "(s,v) \<in> csrstep \<mu> R"
    and notSN_v: "\<not> SN_on (csstep \<mu> R) {v}" by auto
  have sv: "(s,v) \<in> csstep \<mu> R"
    using root unfolding csstep_root_nonroot by auto
  have notSN_s: "\<not> SN_on (csstep \<mu> R) {s}"
    by (rule step_notSN_on_source[OF sv notSN_v])
  have sT: "s \<in> mu_Tinf \<mu> (csstep \<mu> R)"
    by (rule csnrsteps_mu_Tinf_preserve[OF wf pref Tinf notSN_s])
  have hp_s: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S s"
    by (rule muterm_unhiding_preserving_steps[OF wf preserving pref hp sT])
  from csrstep_muterm_unhiding_progress[
      OF wf root hp_s notSN_v defs cover preserving]
  obtain u where hp_u:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u"
    and cases:
      "muterm_noncollapsing_rrstep P (sharp_term Sharp s) (sharp_term Sharp u) \<or>
       (\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
         (x,sharp_term Sharp u) \<in> rrstep S)" by blast
  have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    by (rule muterm_qcs_ur_closed_rule[OF closed])
  have pref_R: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> R)\<^sup>*"
    by (rule csnrsteps_imp_sharp_csdp_steps[OF pref])
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_t pref_R]
  have pref_UR: "(sharp_term Sharp t,sharp_term Sharp s) \<in>
      (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*" by auto
  have cs_sub: "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep W"
  proof -
    have "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep (W \<inter> R)"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    moreover have "rstep (W \<inter> R) \<subseteq> rstep W"
      by (rule rstep_mono, auto)
    ultimately show ?thesis by blast
  qed
  have prefix: "(sharp_term Sharp t,sharp_term Sharp s) \<in> (rstep W)\<^sup>*"
    using pref_UR rtrancl_mono[OF cs_sub] by blast
  have target_path: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp u) \<and>
    (sharp_term Sharp t,sharp_term Sharp u) \<in>
      (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  proof -
    from cases show ?thesis
    proof
    assume noncoll: "muterm_noncollapsing_rrstep P
      (sharp_term Sharp s) (sharp_term Sharp u)"
    have pair: "(sharp_term Sharp s,sharp_term Sharp u) \<in> rrstep P"
      using noncoll unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
    show ?thesis
    proof (intro conjI)
      show "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
        by (rule muterm_qcs_noncollapsing_target[OF closed noncoll])
      show "(sharp_term Sharp t,sharp_term Sharp u) \<in>
          (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
        using prefix pair by auto
    qed
    next
    assume "\<exists>x. muterm_collapsing_rrstep P (sharp_term Sharp s) x \<and>
      (x,sharp_term Sharp u) \<in> rrstep S"
    then obtain x where pair_typed:
      "muterm_collapsing_rrstep P (sharp_term Sharp s) x"
      and unhide: "(x,sharp_term Sharp u) \<in> rrstep S" by blast
    have pair: "(sharp_term Sharp s,x) \<in> rrstep P"
      by (rule muterm_collapsing_rrstep_imp_rrstep[OF pair_typed])
    have S_W: "S \<subseteq> W" by (rule muterm_qcs_ur_closed_S[OF closed])
    have unhide_r: "(x,sharp_term Sharp u) \<in> rstep W"
    proof -
      have "(x,sharp_term Sharp u) \<in> rstep S"
        using unhide unfolding rstep_iff_rrstep_or_nrrstep by blast
      moreover have "rstep S \<subseteq> rstep W" by (rule rstep_mono[OF S_W])
      ultimately show ?thesis by blast
    qed
    show ?thesis
    proof (intro conjI)
      show "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u)"
        by (rule muterm_qcs_ur_closed_unhiding_target[OF closed unhide])
      show "(sharp_term Sharp t,sharp_term Sharp u) \<in>
          (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
        using prefix pair unhide_r by auto
    qed
    qed
  qed
  show ?thesis using hp_u target_path by blast
qed

lemma muterm_typed_relto_target_closed:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from step obtain a b where event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from closed have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    and S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
    unfolding muterm_qcs_ur_closed_def by auto
  have closed_b: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then have "muterm_noncollapsing_rrstep P a b" by simp
      then show ?thesis
        by (rule muterm_qcs_noncollapsing_target[OF closed])
    next
      assume bridge: "(a,b) \<in>
        {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain x where pair_typed: "muterm_collapsing_rrstep P a x"
        and unhide: "(x,b) \<in> rrstep S" by auto
      show ?thesis
        by (rule qcs_ur_closed_rrstep_target[OF S_rules unhide])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  show ?thesis by auto
qed

lemma muterm_typed_relto_transfer:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> s"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s,t) \<in> (rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t"
proof -
  from closed have rules: "\<And>lr. lr \<in> W \<inter> R \<Longrightarrow>
      qcs_ur_closed_term R (W \<inter> R) \<mu> (snd lr)"
    and S_W: "S \<subseteq> W"
    and S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (snd lr)"
    unfolding muterm_qcs_ur_closed_def by auto
  have cs_sub: "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep W"
  proof -
    have "csdp_step Sharp \<mu> (W \<inter> R) \<subseteq> rstep (W \<inter> R)"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    moreover have "rstep (W \<inter> R) \<subseteq> rstep W"
      by (rule rstep_mono, auto)
    ultimately show ?thesis by blast
  qed
  from step obtain a b where prefix: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_s prefix]
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*"
    by auto
  have prefix_W: "(s,a) \<in> (rstep W)\<^sup>*"
    using prefix_U rtrancl_mono[OF cs_sub] by blast
  obtain x where pair: "(a,x) \<in> rrstep P"
    and bridge: "(x,b) \<in> (rstep W)\<^sup>*"
    and closed_b: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then have nc: "muterm_noncollapsing_rrstep P a b" by simp
      have ab: "(a,b) \<in> rrstep P"
        using nc unfolding muterm_noncollapsing_rrstep_def rrstep_def' by blast
      have cb: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
        by (rule muterm_qcs_noncollapsing_target[OF closed nc])
      show ?thesis by (rule that[OF ab], use cb in auto)
    next
      assume raw: "(a,b) \<in>
        {(s,t). \<exists>x. muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain y where ay_typed: "muterm_collapsing_rrstep P a y"
        and yb: "(y,b) \<in> rrstep S" by auto
      have ay: "(a,y) \<in> rrstep P"
        by (rule muterm_collapsing_rrstep_imp_rrstep[OF ay_typed])
      have yb_W: "(y,b) \<in> (rstep W)\<^sup>*"
      proof -
        have "(y,b) \<in> rstep S"
          using yb unfolding rstep_iff_rrstep_or_nrrstep by blast
        then have "(y,b) \<in> rstep W" using rstep_mono[OF S_W] by blast
        then show ?thesis by auto
      qed
      have cb: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> b"
        by (rule qcs_ur_closed_rrstep_target[OF S_rules yb])
      show ?thesis by (rule that[OF ay yb_W cb])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> (W \<inter> R))\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> t" by auto
  have suffix_W: "(b,t) \<in> (rstep W)\<^sup>*"
    using suffix_U rtrancl_mono[OF cs_sub] by blast
  have xt: "(x,t) \<in> (rstep W)\<^sup>*"
    using bridge suffix_W by auto
  show ?thesis using prefix_W pair xt closed_t by auto
qed

theorem finite_muterm_typed_dpp_usable:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof (unfold finite_muterm_typed_dpp_def SN_rel_on_def SN_on_def, intro notI)
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  let ?B = "(rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  assume "\<exists>f. f 0 \<in> UNIV \<and> (\<forall>n. (f n,f (Suc n)) \<in> ?A)"
  then obtain f where chain: "\<And>n. (f n,f (Suc n)) \<in> ?A" by auto
  from muterm_typed_relto_target_closed[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from muterm_typed_relto_transfer[
      OF wf fresh closed Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n,?g (Suc n)) \<in> ?B" for n
    using muterm_typed_relto_transfer[
      OF wf fresh closed closed_g[of n] chain[of "Suc n"]] by auto
  from fin have sn: "SN ?B"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have g_chain: "chain ?B ?g" using g_step by simp
  have not_sn: "\<not> SN ?B"
    by (rule not_SN_onI[of ?g], simp, rule g_chain)
  from not_sn sn show False ..
qed

lemma muterm_typed_relto_transfer_expanded:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_expanded_ur_closed R S W \<mu> P"
    and closed_s: "qcs_ur_closed_dp_rhs R W \<mu> s"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "(s,t) \<in> (rstep W)\<^sup>* O
      rrstep (muterm_expanded_pairs ren P S) O (rstep W)\<^sup>* \<and>
    qcs_ur_closed_dp_rhs R W \<mu> t"
proof -
  from closed have W_R: "W \<subseteq> R"
    and rules: "\<And>lr. lr \<in> W \<Longrightarrow>
      qcs_ur_closed_term R W \<mu> (snd lr)"
    unfolding muterm_qcs_expanded_ur_closed_def by auto
  from step obtain a b where prefix:
      "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_s prefix]
  have prefix_U: "(s,a) \<in> (csdp_step Sharp \<mu> W)\<^sup>*"
    by auto
  have cs_sub: "csdp_step Sharp \<mu> W \<subseteq> rstep W"
  proof -
    have "csdp_step Sharp \<mu> W \<subseteq> rstep W"
      unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
    then show ?thesis .
  qed
  have prefix_W: "(s,a) \<in> (rstep W)\<^sup>*"
    using prefix_U rtrancl_mono[OF cs_sub] by blast
  have expanded: "(a,b) \<in> rrstep (muterm_expanded_pairs ren P S)"
    using event muterm_typed_pair_step_subset_expanded by blast
  have closed_b: "qcs_ur_closed_dp_rhs R W \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then have "muterm_noncollapsing_rrstep P a b" by simp
      then obtain l r \<sigma> where lr: "(l,r) \<in> P"
        and r_fun: "\<not> is_Var r" and target: "b = r \<cdot> \<sigma>"
        unfolding muterm_noncollapsing_rrstep_def by auto
      from closed lr r_fun have r_closed: "qcs_ur_closed_dp_rhs R W \<mu> r"
        unfolding muterm_qcs_expanded_ur_closed_def by auto
      from qcs_ur_closed_dp_rhs_subst[OF r_closed, of \<sigma>]
      show ?thesis unfolding target .
    next
      assume bridge: "(a,b) \<in> {(s,t). \<exists>x.
        muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain x where unhide: "(x,b) \<in> rrstep S" by auto
      from closed have S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
        qcs_ur_closed_dp_rhs R W \<mu> (snd lr)"
        unfolding muterm_qcs_expanded_ur_closed_def by auto
      show ?thesis by (rule qcs_ur_closed_rrstep_target[OF S_rules unhide])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  have suffix_U: "(b,t) \<in> (csdp_step Sharp \<mu> W)\<^sup>*"
    and closed_t: "qcs_ur_closed_dp_rhs R W \<mu> t" by auto
  have suffix_W: "(b,t) \<in> (rstep W)\<^sup>*"
    using suffix_U rtrancl_mono[OF cs_sub] by blast
  show ?thesis using prefix_W expanded suffix_W closed_t by auto
qed

lemma muterm_typed_relto_target_closed_expanded:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_expanded_ur_closed R S W \<mu> P"
    and step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "qcs_ur_closed_dp_rhs R W \<mu> t"
proof -
  from step obtain a b where event: "(a,b) \<in> muterm_typed_pair_step P S"
    and suffix: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from closed have rules: "\<And>lr. lr \<in> W \<Longrightarrow>
      qcs_ur_closed_term R W \<mu> (snd lr)"
    and S_rules: "\<And>lr. lr \<in> S \<Longrightarrow>
      qcs_ur_closed_dp_rhs R W \<mu> (snd lr)"
    unfolding muterm_qcs_expanded_ur_closed_def by auto
  have closed_b: "qcs_ur_closed_dp_rhs R W \<mu> b"
  proof -
    from event show ?thesis unfolding muterm_typed_pair_step_def
    proof
      assume noncoll: "(a,b) \<in> {p. case p of (x,y) \<Rightarrow>
        muterm_noncollapsing_rrstep P x y}"
      then obtain l r \<sigma> where lr: "(l,r) \<in> P"
        and r_fun: "\<not> is_Var r" and target: "b = r \<cdot> \<sigma>"
        unfolding muterm_noncollapsing_rrstep_def by auto
      from closed lr r_fun have r_closed: "qcs_ur_closed_dp_rhs R W \<mu> r"
        unfolding muterm_qcs_expanded_ur_closed_def by auto
      from qcs_ur_closed_dp_rhs_subst[OF r_closed, of \<sigma>]
      show ?thesis unfolding target .
    next
      assume bridge: "(a,b) \<in> {(s,t). \<exists>x.
        muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
      then obtain x where unhide: "(x,b) \<in> rrstep S" by auto
      show ?thesis by (rule qcs_ur_closed_rrstep_target[OF S_rules unhide])
    qed
  qed
  from qcs_ur_closed_csdp_steps[OF wf fresh rules closed_b suffix]
  show ?thesis by auto
qed

theorem finite_muterm_typed_dpp_expanded_usable:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and closed: "muterm_qcs_expanded_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,
      muterm_expanded_pairs ren P S,{},{},{},W)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof (unfold finite_muterm_typed_dpp_def SN_rel_on_def SN_on_def, intro notI)
  let ?A = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  let ?B = "(rstep W)\<^sup>* O rrstep (muterm_expanded_pairs ren P S) O
    (rstep W)\<^sup>*"
  assume "\<exists>f. f 0 \<in> UNIV \<and> (\<forall>n. (f n,f (Suc n)) \<in> ?A)"
  then obtain f where chain: "\<And>n. (f n,f (Suc n)) \<in> ?A" by auto
  from muterm_typed_relto_target_closed_expanded[OF wf fresh closed chain[of 0]]
  have closed_1: "qcs_ur_closed_dp_rhs R W \<mu> (f (Suc 0))" .
  let ?g = "\<lambda>n. f (Suc n)"
  have closed_g: "qcs_ur_closed_dp_rhs R W \<mu> (?g n)" for n
  proof (induct n)
    case 0
    show ?case using closed_1 by simp
  next
    case (Suc n)
    from muterm_typed_relto_transfer_expanded[
      OF wf fresh closed Suc.hyps chain[of "Suc n"]]
    show ?case by auto
  qed
  have g_step: "(?g n,?g (Suc n)) \<in> ?B" for n
    using muterm_typed_relto_transfer_expanded[
      OF wf fresh closed closed_g[of n] chain[of "Suc n"]] by auto
  from fin have sn: "SN ?B"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have not_sn: "\<not> SN ?B"
    by (rule not_SN_onI[of ?g], simp, simp add: chain_def g_step)
  from not_sn sn show False ..
qed

text \<open>
  An exact typed MU-TERM macro step can also be expanded before handing the
  problem to the ordinary DP framework.  Keeping all source and unhiding
  rules at this boundary is important: any subsequent usable-rule reduction
  is then justified by the ordinary DP processor itself, rather than being
  assumed by the MU transformation.
\<close>

theorem finite_muterm_typed_dpp_expanded_ordinary:
  assumes fin: "finite_dpp (False,False,
      muterm_expanded_pairs ren P S,{},{},{},R)"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
proof -
  let ?A = "(rstep R)\<^sup>* O
    rrstep (muterm_expanded_pairs ren P S) O (rstep R)\<^sup>*"
  let ?B = "(csdp_step Sharp \<mu> R)\<^sup>* O
    muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  from fin have sn: "SN ?A"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv SN_rel_on_def by simp
  have weak: "csdp_step Sharp \<mu> R \<subseteq> rstep R"
  proof -
    show ?thesis unfolding csdp_step_def csdp_step_p_def
      by (auto dest: rstep_r_p_s_imp_rstep)
  qed
  have weak_star: "(csdp_step Sharp \<mu> R)\<^sup>* \<subseteq>
      (rstep R)\<^sup>*"
    by (rule rtrancl_mono[OF weak])
  have strict: "muterm_typed_pair_step P S \<subseteq>
      rrstep (muterm_expanded_pairs ren P S)"
    by (rule muterm_typed_pair_step_subset_expanded)
  have "?B \<subseteq> ?A"
    by (meson relcomp_mono strict weak_star)
  from SN_subset[OF sn this]
  show ?thesis unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
qed

theorem finite_muterm_usable_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and preserving: "muterm_unhiding_preserving_on Sharp \<mu> R S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "SN (csstep \<mu> R)"
proof (rule ccontr)
  assume notSN: "\<not> SN (csstep \<mu> R)"
  from not_SN_imp_Tinf[OF notSN] obtain t0 where
    t0T: "t0 \<in> Tinf (csstep \<mu> R)" by blast
  have hp0: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t0"
    by (rule Tinf_has_muterm_unhiding_property[OF t0T])
  from muterm_unhiding_next_closed[
      OF wf hp0 defs cover preserving closed]
  obtain t1 where hp1:
      "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t1"
    and closed1: "qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu>
      (sharp_term Sharp t1)" by blast
  let ?A = "(rstep W)\<^sup>* O rrstep P O (rstep W)\<^sup>*"
  have step_ex: "\<And>t. has_muterm_unhiding_property Sharp \<mu>
      (csstep \<mu> R) S t \<Longrightarrow>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t) \<Longrightarrow>
      \<exists>u. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
        (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A"
    by (rule muterm_unhiding_relstep_usable[
      OF wf fresh _ _ defs cover preserving closed])
  have all_ex: "\<forall>t. \<exists>u.
      (has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<and>
       qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t)) \<longrightarrow>
      (has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S u \<and>
       qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp u) \<and>
       (sharp_term Sharp t,sharp_term Sharp u) \<in> ?A)"
    using step_ex by blast
  from choice[OF all_ex] obtain nxt where nxt:
      "\<And>t. has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S t \<Longrightarrow>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp t) \<Longrightarrow>
        has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (nxt t) \<and>
        qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp (nxt t)) \<and>
        (sharp_term Sharp t,sharp_term Sharp (nxt t)) \<in> ?A"
    by blast
  define ts where "ts = rec_nat t1 (\<lambda>n t. nxt t)"
  have ts_inv: "has_muterm_unhiding_property Sharp \<mu> (csstep \<mu> R) S (ts n) \<and>
      qcs_ur_closed_dp_rhs R (W \<inter> R) \<mu> (sharp_term Sharp (ts n))"
    for n
  proof (induct n)
    case 0
    show ?case unfolding ts_def using hp1 closed1 by simp
  next
    case (Suc n)
    from nxt[OF Suc.hyps[THEN conjunct1] Suc.hyps[THEN conjunct2]]
    show ?case unfolding ts_def by simp
  qed
  have ts_step: "(sharp_term Sharp (ts n),sharp_term Sharp (ts (Suc n))) \<in> ?A"
    for n
    using nxt[OF ts_inv[of n, THEN conjunct1] ts_inv[of n, THEN conjunct2]]
    unfolding ts_def by simp
  define f where "f n = sharp_term Sharp (ts n)" for n
  have chain: "\<And>n. (f n,f (Suc n)) \<in> ?A"
    unfolding f_def using ts_step by simp
  have f_chain: "chain ?A f" using chain by simp
  have not_sn: "\<not> SN ?A"
    by (rule not_SN_onI[of f], simp, rule f_chain)
  from fin have rel_sn: "SN_rel (rrstep P) (rstep W)"
    unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  then have sn: "SN ?A" unfolding SN_rel_on_def .
  from not_sn sn show False ..
qed

corollary finite_muterm_exact_usable_CSDP_imp_SN_csstep:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and defs: "{f. defined R f} \<subseteq> D"
    and cover: "muterm_unhiding_coverage Sharp \<mu> D R P S"
    and closed: "muterm_qcs_ur_closed R S W \<mu> P"
    and fin: "finite_dpp (False,False,P,{},{},{},W)"
  shows "SN (csstep \<mu> R)"
  by (rule finite_muterm_usable_CSDP_imp_SN_csstep[
      OF wf fresh defs cover
        muterm_unhiding_preserving_on_from_coverage[OF wf defs cover]
        closed fin])

definition muterm_qcs_ur_closed_check where
  "muterm_qcs_ur_closed_check R S W \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set W) S \<and>
     list_all (\<lambda>lr. lr \<in> set R \<or> lr \<in> set S) W \<and>
     (let U = filter (\<lambda>lr. lr \<in> set R) W
      in list_all (\<lambda>lr. qcs_ur_closed_term_check R U \<mu> (snd lr)) U \<and>
         list_all (\<lambda>lr. qcs_ur_closed_dp_rhs_check R U \<mu> (snd lr)) S \<and>
         list_all (\<lambda>dp. is_Var (snd dp) \<or>
           qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)) P))"

definition muterm_qcs_expanded_ur_closed_check where
  "muterm_qcs_expanded_ur_closed_check R S W \<mu> P =
    (list_all (\<lambda>lr. lr \<in> set R) W \<and>
     list_all (\<lambda>lr. qcs_ur_closed_term_check R W \<mu> (snd lr)) W \<and>
     list_all (\<lambda>lr. qcs_ur_closed_dp_rhs_check R W \<mu> (snd lr)) S \<and>
     list_all (\<lambda>dp. is_Var (snd dp) \<or>
       qcs_ur_closed_dp_rhs_check R W \<mu> (snd dp)) P)"

lemma muterm_qcs_expanded_ur_closed_check_sound:
  assumes check: "muterm_qcs_expanded_ur_closed_check R S W \<mu> P"
  shows "muterm_qcs_expanded_ur_closed (set R) (set S) (set W)
    (mu_of \<mu>) (set P)"
proof -
  from check have W_R: "set W \<subseteq> set R"
    and W: "\<And>lr. lr \<in> set W \<Longrightarrow>
      qcs_ur_closed_term_check R W \<mu> (snd lr)"
    and S: "\<And>lr. lr \<in> set S \<Longrightarrow>
      qcs_ur_closed_dp_rhs_check R W \<mu> (snd lr)"
    and P: "\<And>dp. dp \<in> set P \<Longrightarrow> is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs_check R W \<mu> (snd dp)"
    unfolding muterm_qcs_expanded_ur_closed_check_def list_all_iff by auto
  show ?thesis unfolding muterm_qcs_expanded_ur_closed_def
  proof (intro conjI ballI)
    show "set W \<subseteq> set R" by (rule W_R)
  next
    fix lr
    assume lr: "lr \<in> set W"
    show "qcs_ur_closed_term (set R) (set W) (mu_of \<mu>) (snd lr)"
      by (rule qcs_ur_closed_term_check_sound[OF W[OF lr]])
  next
    fix lr
    assume lr: "lr \<in> set S"
    show "qcs_ur_closed_dp_rhs (set R) (set W) (mu_of \<mu>) (snd lr)"
      by (rule qcs_ur_closed_dp_rhs_check_sound[OF S[OF lr]])
  next
    fix dp
    assume dp: "dp \<in> set P"
    from P[OF dp] show "is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs (set R) (set W) (mu_of \<mu>) (snd dp)"
      by (auto intro: qcs_ur_closed_dp_rhs_check_sound)
  qed
qed

lemma muterm_qcs_ur_closed_check_sound:
  assumes check: "muterm_qcs_ur_closed_check R S W \<mu> P"
  shows "muterm_qcs_ur_closed (set R) (set S) (set W) (mu_of \<mu>) (set P)"
proof -
  let ?U = "filter (\<lambda>lr. lr \<in> set R) W"
  have U_set: "set ?U = set W \<inter> set R" by auto
  from check have S_W: "set S \<subseteq> set W"
    and W_RS: "set W \<subseteq> set R \<union> set S"
    and U: "\<And>lr. lr \<in> set ?U \<Longrightarrow>
      qcs_ur_closed_term_check R ?U \<mu> (snd lr)"
    and S: "\<And>lr. lr \<in> set S \<Longrightarrow>
      qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd lr)"
    and P: "\<And>dp. dp \<in> set P \<Longrightarrow> is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd dp)"
    unfolding muterm_qcs_ur_closed_check_def Let_def
    by (auto simp: list_all_iff)
  show ?thesis unfolding muterm_qcs_ur_closed_def
  proof (intro conjI ballI)
    show "set S \<subseteq> set W" by (rule S_W)
    show "set W \<subseteq> set R \<union> set S" by (rule W_RS)
  next
    fix lr
    assume lr: "lr \<in> set W \<inter> set R"
    from qcs_ur_closed_term_check_sound[OF U[of lr]] lr U_set
    show "qcs_ur_closed_term (set R) (set W \<inter> set R)
      (mu_of \<mu>) (snd lr)" by simp
  next
    fix lr
    assume lr: "lr \<in> set S"
    from qcs_ur_closed_dp_rhs_check_sound[OF S[OF lr]] U_set
    show "qcs_ur_closed_dp_rhs (set R) (set W \<inter> set R)
      (mu_of \<mu>) (snd lr)" by simp
  next
    fix dp
    assume dp: "dp \<in> set P"
    from P[OF dp] show "is_Var (snd dp) \<or>
      qcs_ur_closed_dp_rhs (set R) (set W \<inter> set R)
        (mu_of \<mu>) (snd dp)"
    proof
      assume "is_Var (snd dp)"
      then show ?thesis by simp
    next
      assume checked: "qcs_ur_closed_dp_rhs_check R ?U \<mu> (snd dp)"
      from qcs_ur_closed_dp_rhs_check_sound[OF checked] U_set
      show ?thesis by simp
    qed
  qed
qed

fun check_muterm_expanded_csr_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f,label_type,string) csr_dp_termination_proof \<Rightarrow> showsl check"
and check_muterm_expanded_csr_components ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow> 'dpp \<Rightarrow>
   (('f,label_type,string) csr_dp_termination_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Dep_Graph_Proc edpts) =
    debug i (STR ''expanded MU-TERM CSR dependency graph'') (do {
      _ \<leftarrow> check_csr_dep_graph_proc J \<mu> dpp edpts;
      check_muterm_expanded_csr_components I J \<mu> i dpp edpts
    })"
| "check_muterm_expanded_csr_proof I J \<mu> i dpp
      (CSR_DP_Ordinary_Proof (Redpair_UR_Proc redp Pr U subprf)) =
    (case muterm_strong_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U dpp of
       Inl _ \<Rightarrow> check_csr_dp_termination_proof_min I J \<mu> False i dpp
         (CSR_DP_Ordinary_Proof (Redpair_UR_Proc redp Pr U subprf))
     | Inr dpp' \<Rightarrow>
         debug i (STR ''expanded strong MU-TERM usable-rule reduction pair'')
           (check_csr_dp_termination_proof_min I J \<mu> False
             (add_index i 1) dpp' (CSR_DP_Ordinary_Proof subprf)))"
| "check_muterm_expanded_csr_proof I J \<mu> i dpp prf =
    check_csr_dp_termination_proof_min I J \<mu> False i dpp prf"
| "check_muterm_expanded_csr_components I J \<mu> i dpp [] = succeed"
| "check_muterm_expanded_csr_components I J \<mu> i dpp
      ((None,C)#rest) =
    check_muterm_expanded_csr_components I J \<mu> (add_index i 1) dpp rest"
| "check_muterm_expanded_csr_components I J \<mu> i dpp
      ((Some prf,C)#rest) = do {
    check_muterm_expanded_csr_proof I J \<mu> (add_index i 1)
      (dpp_ops.intersect_pairs J dpp C) prf;
    check_muterm_expanded_csr_components I J \<mu> (add_index i 1) dpp rest
  }"

lemma check_muterm_expanded_csr_components_member:
  assumes ok: "isOK (check_muterm_expanded_csr_components
      I J \<mu> i dpp edps)"
    and mem: "(Some prf,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_expanded_csr_proof I J \<mu> j
    (dpp_ops.intersect_pairs J dpp C) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems head None show ?thesis
      by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = head")
      case True
      with Cons.prems head Some show ?thesis by auto
    next
      case False
      from Cons.prems head Some False show ?thesis
        by (auto intro: Cons.hyps)
    qed
  qed
qed

lemma check_muterm_expanded_csr_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_muterm_expanded_csr_proof I J \<mu> i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
  using ok plain wf fresh
proof (induct "prf" arbitrary: dpp i)
  case (CSR_DP_Ordinary_Proof dpprf)
  show ?case
  proof (cases "\<exists>redp Pr U subprf.
      dpprf = Redpair_UR_Proc redp Pr U subprf")
    case True
    then obtain redp Pr U subprf where shape:
      "dpprf = Redpair_UR_Proc redp Pr U subprf" by blast
    show ?thesis
    proof (cases "muterm_strong_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U dpp")
      case (Inl error)
      from CSR_DP_Ordinary_Proof.prems(1) shape Inl have standard:
        "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
          (CSR_DP_Ordinary_Proof dpprf))" by simp
      show ?thesis by (rule check_csr_dp_termination_proof_min_sound[
        OF I J CSR_DP_Ordinary_Proof.prems(2-4) standard])
    next
      case (Inr dpp')
      have proc: "muterm_strong_ur_redpair_proc J \<mu>
          (get_rel_impl redp) Pr U dpp = return dpp'"
        using Inr by simp
      from CSR_DP_Ordinary_Proof.prems(1) shape Inr have rec:
        "isOK (check_csr_dp_termination_proof_min I J \<mu> False
          (add_index i 1) dpp' (CSR_DP_Ordinary_Proof subprf))" by simp
      have dpp_eq: "dpp' = dpp_spec.delete_pairs J dpp Pr"
        using proc unfolding muterm_strong_ur_redpair_proc_def by auto
      have plain': "plain_csr_dpp J dpp'"
        unfolding dpp_eq by (rule plain_csr_dpp_delete_pairs[
          OF J CSR_DP_Ordinary_Proof.prems(2)])
      interpret dpp_spec J by fact
      have rules': "set (rules dpp') = set (rules dpp)"
        using dpp_eq delete_P_Pw_sound[of dpp Pr Pr]
          rules_sound[of dpp'] by auto
      have wf': "wf_trs (set (rules dpp'))"
        using CSR_DP_Ordinary_Proof.prems(3) unfolding rules' .
      have fresh': "\<And>f n. \<not> defined (set (rules dpp')) (Sharp f,n)"
        using CSR_DP_Ordinary_Proof.prems(4) unfolding rules' .
      have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
          (set (pairs dpp')) (set (rules dpp'))"
        by (rule check_csr_dp_termination_proof_min_sound[
          OF I J plain' wf' fresh' rec])
      show ?thesis by (rule muterm_strong_ur_redpair_proc_sound[
        OF J get_rel_impl proc CSR_DP_Ordinary_Proof.prems(3-4) fin])
    qed
  next
    case False
    from CSR_DP_Ordinary_Proof.prems(1) False have standard:
      "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
        (CSR_DP_Ordinary_Proof dpprf))" by (cases dpprf, auto)
    show ?thesis by (rule check_csr_dp_termination_proof_min_sound[
      OF I J CSR_DP_Ordinary_Proof.prems(2-4) standard])
  qed
next
  case (CSR_DP_Dep_Graph_Proc edps)
  from CSR_DP_Dep_Graph_Proc.prems(1) have graph:
      "isOK (check_csr_dep_graph_proc J \<mu> dpp edps)"
    and components: "isOK (check_muterm_expanded_csr_components
      I J \<mu> i dpp edps)" by auto
  show ?case
  proof (rule check_csr_dep_graph_proc_min_sound[
      OF J CSR_DP_Dep_Graph_Proc.prems(2) graph])
    fix p C
    assume mem: "(Some p,C) \<in> set edps"
    let ?d = "dpp_ops.intersect_pairs J dpp C"
    from check_muterm_expanded_csr_components_member[OF components mem]
    obtain j where rec:
      "isOK (check_muterm_expanded_csr_proof I J \<mu> j ?d p)" by blast
    have plain': "plain_csr_dpp J ?d"
      by (rule plain_csr_dpp_intersect_pairs[
        OF J CSR_DP_Dep_Graph_Proc.prems(2)])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J ?d =
      (NFS dpp,M dpp,set (P dpp) \<inter> set C,
        set (Pw dpp) \<inter> set C,set (Q dpp),set (R dpp),set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J ?d =
      (NFS ?d,M ?d,set (P ?d),set (Pw ?d),set (Q ?d),
        set (R ?d),set (Rw ?d))" by (rule dpp_sound)
    have pairs': "set (pairs ?d) = set (pairs dpp) \<inter> set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of ?d] by auto
    have rules': "set (rules ?d) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of ?d] by auto
    have fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs ?d)) (set (rules ?d))"
      apply (rule CSR_DP_Dep_Graph_Proc.hyps)
          apply (rule mem)
         apply simp
        apply simp
       apply (rule rec)
      apply (rule plain')
      using CSR_DP_Dep_Graph_Proc.prems(3-4) unfolding rules' by auto
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) \<inter> set C) (set (rules dpp))"
      using fin unfolding pairs' rules' .
  qed
next
  case CSR_DP_P_is_Empty
  from CSR_DP_P_is_Empty.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      CSR_DP_P_is_Empty)"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_P_is_Empty.prems(2-4) standard])
next
  case (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child)
  from CSR_DP_Subterm_Criterion_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Subterm_Criterion_Proc x1 x2 x3 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Subterm_Criterion_Proc.prems(2-4) standard])
next
  case (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child)
  from CSR_DP_Gen_Subterm_Criterion_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Gen_Subterm_Criterion_Proc x1 x2 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Gen_Subterm_Criterion_Proc.prems(2-4) standard])
next
  case (CSR_DP_Usable_Rules_Proc x1 child)
  from CSR_DP_Usable_Rules_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Usable_Rules_Proc x1 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Usable_Rules_Proc.prems(2-4) standard])
next
  case (CSR_DP_Instantiation_Proc x1 x2 child)
  from CSR_DP_Instantiation_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Instantiation_Proc x1 x2 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Instantiation_Proc.prems(2-4) standard])
next
  case (CSR_DP_Forward_Instantiation_Proc x1 x2 child)
  from CSR_DP_Forward_Instantiation_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Forward_Instantiation_Proc x1 x2 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Forward_Instantiation_Proc.prems(2-4) standard])
next
  case (CSR_DP_Redpair_UR_Proc x1 x2 x3 child)
  from CSR_DP_Redpair_UR_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Redpair_UR_Proc x1 x2 x3 child))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Redpair_UR_Proc.prems(2-4) standard])
next
  case (CSR_DP_Size_Change_Subterm_Proc x)
  from CSR_DP_Size_Change_Subterm_Proc.prems(1) have standard:
    "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp
      (CSR_DP_Size_Change_Subterm_Proc x))"
    by (simp only: check_muterm_expanded_csr_proof.simps)
  show ?case by (rule check_csr_dp_termination_proof_min_sound[
    OF I J CSR_DP_Size_Change_Subterm_Proc.prems(2-4) standard])
qed

datatype (dead 'f, dead 'l, dead 'v) muterm_typed_dp_proof =
    Muterm_Typed_P_Is_Empty
  | Muterm_Typed_Local_Usable
      "('f,'l,'v) trsLL" "('f,'l,'v) dp_termination_proof"
  | Muterm_Typed_General_Usable
      "('f,'l) lab redtriple_impl" "('f,'l,'v) trsLL"
      "('f,'l,'v) trsLL" "('f,'l,'v) muterm_typed_dp_proof"
  | Muterm_Typed_Pair_Augmentation
      "(('f,'l) lab,'v) rule" "('f,'l,'v) trsLL"
      "('f,'l,'v) muterm_typed_dp_proof"
  | Muterm_Typed_CSR_Proof "('f,'l,'v) csr_dp_termination_proof"
  | Muterm_Typed_Expanded_CSR_Proof "('f,'l,'v) csr_dp_termination_proof"
  | Muterm_Typed_Expanded_Extended_Basic_CSR_Proof
      "('f,'l,'v) csr_dp_termination_proof"
  | Muterm_Typed_Expanded_Local_Usable
      "('f,'l,'v) trsLL" "('f,'l,'v) dp_termination_proof"
  | Muterm_Typed_Expanded_Strong_Usable
      "('f,'l,'v) trsLL" "('f,'l) lab redtriple_impl"
      "('f,'l,'v) trsLL" "('f,'l,'v) csr_dp_termination_proof"
  | Muterm_Typed_Expanded_Ordinary
      "('f,'l,'v) dp_termination_proof"
  | Muterm_Typed_Dep_Graph
      "(('f,'l,'v) muterm_typed_dp_proof option \<times> ('f,'l,'v) trsLL) list"

definition check_muterm_typed_dep_graph where
  "check_muterm_typed_dep_graph \<mu> R S P dps = do {
    check_wf_trs (R @ S);
    check_subseteq P (concat (map snd dps))
      <+? (\<lambda>dp. showsl_lit (STR ''typed MU-TERM dependency pair '') \<circ>
        showsl_rule dp \<circ> showsl_lit (STR '' is missing in decomposition\<newline>''));
    check_graph_decomp
      (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst))
      graph_approx_csr_rt Multi_Map.insert
      (csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) (R @ S))
      (map (\<lambda>(real,Cs). (real \<noteq> None,
        map (\<lambda>(s,t). ((s,t),())) Cs)) dps)
  }"

fun check_muterm_typed_dp_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   ('f,label_type,string) muterm_typed_dp_proof \<Rightarrow> showsl check"
and check_muterm_typed_graph_components ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   (('f,label_type) lab) muL \<Rightarrow> showsl \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type) lab,string) rules \<Rightarrow>
   (('f,label_type,string) muterm_typed_dp_proof option \<times>
    ('f,label_type,string) trsLL) list \<Rightarrow> showsl check"
where
  "check_muterm_typed_dp_proof I J \<mu> i R S P Muterm_Typed_P_Is_Empty =
    check (P = []) (i \<circ> showsl_lit (STR '': MU-TERM dependency pairs are not empty''))"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Local_Usable U prf) =
    debug i (STR ''MU-TERM ordinary reduction-pair continuation'') (do {
      check (list_all (\<lambda>lr. lr \<in> set U) S)
        (i \<circ> showsl_lit (STR '': MU-TERM usable rules omit an unhiding rule''));
      check (list_all (\<lambda>lr. lr \<in> set R \<or> lr \<in> set S) U)
        (i \<circ> showsl_lit (STR '': extraneous MU-TERM usable rule''));
      let UR = filter (\<lambda>lr. lr \<in> set R) U;
      check (list_all (\<lambda>lr.
          qcs_ur_closed_term_check R UR \<mu> (snd lr)) UR)
        (i \<circ> showsl_lit (STR '': ordinary MU-TERM rule closure failed''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_dp_rhs_check R UR \<mu> (snd lr)) S)
        (i \<circ> showsl_lit (STR '': MU-TERM unhiding closure failed''));
      check (list_all (\<lambda>dp. is_Var (snd dp) \<or>
          qcs_ur_closed_dp_rhs_check R UR \<mu> (snd dp)) P)
        (i \<circ> showsl_lit (STR '': MU-TERM pair closure failed''));
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False P [] [] [] U) prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_General_Usable redp Pr U prf) =
    debug i (STR ''general typed MU-TERM usable-rule reduction pair'') (do {
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      dpp' \<leftarrow> muterm_general_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U S dpp;
      check_muterm_typed_dp_proof I J \<mu> (add_index i 1) R S
        (dpp_ops.pairs J dpp') prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Pair_Augmentation st sts prf) =
    debug i (STR ''typed MU-TERM pair augmentation'') (do {
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      dpp' \<leftarrow> csr_instantiation_proc J \<mu> st sts dpp;
      check_subseteq P (dpp_ops.pairs J dpp')
        <+? (\<lambda>dp. showsl_lit
          (STR ''typed MU-TERM augmentation removed original pair\<newline>'') \<circ>
          showsl_rule dp);
      check_muterm_typed_dp_proof I J \<mu> (add_index i 1) R S
        (dpp_ops.pairs J dpp') prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_CSR_Proof prf) =
    debug i (STR ''MU-TERM noncollapsing CSR component'') (do {
      check (list_all (is_Fun \<circ> snd) P)
        (i \<circ> showsl_lit (STR '': collapsing pair requires the typed MU-TERM processor''));
      let dpp = dpp_ops.mk J False False P [] [] [] R;
      check_csr_dp_termination_proof_min I J \<mu> False (add_index i 1) dpp prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Expanded_CSR_Proof prf) =
    debug i (STR ''expanded typed MU-TERM CSR component'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      let dpp = dpp_ops.mk J False False E [] [] [] R;
      check_muterm_expanded_csr_proof I J \<mu> (add_index i 1) dpp prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Expanded_Extended_Basic_CSR_Proof prf) =
    error (i \<circ> showsl_lit
      (STR '': extended-basic proof requires the production checker''))"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Expanded_Local_Usable U prf) =
    debug i (STR ''expanded MU-TERM ordinary reduction-pair continuation'') (do {
      check (list_all (\<lambda>lr. lr \<in> set R) U)
        (i \<circ> showsl_lit (STR '': extraneous MU-TERM usable rule''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_term_check R U \<mu> (snd lr)) U)
        (i \<circ> showsl_lit (STR '': ordinary MU-TERM rule closure failed''));
      check (list_all (\<lambda>lr.
          qcs_ur_closed_dp_rhs_check R U \<mu> (snd lr)) S)
        (i \<circ> showsl_lit (STR '': MU-TERM unhiding closure failed''));
      check (list_all (\<lambda>dp. is_Var (snd dp) \<or>
          qcs_ur_closed_dp_rhs_check R U \<mu> (snd dp)) P)
        (i \<circ> showsl_lit (STR '': MU-TERM pair closure failed''));
      let E = muterm_expanded_pairs_list string_renameN P S;
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False E [] [] [] U) prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Expanded_Strong_Usable U redp Pr prf) =
    debug i (STR ''expanded strong MU-TERM usable-rule reduction pair'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      let dpp = dpp_ops.mk J False False E [] [] [] R;
      dpp' \<leftarrow> muterm_strong_ur_redpair_proc J \<mu>
        (get_rel_impl redp) Pr U dpp;
      check_csr_dp_termination_proof_min I J \<mu> False
        (add_index i 1) dpp' prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Expanded_Ordinary prf) =
    debug i (STR ''expanded MU-TERM ordinary DP continuation'') (do {
      let E = muterm_expanded_pairs_list string_renameN P S;
      check_dp_termination_proof I J False (add_index i 1)
        (dpp_ops.mk J False False E [] [] [] R) prf
    })"
| "check_muterm_typed_dp_proof I J \<mu> i R S P
      (Muterm_Typed_Dep_Graph edps) =
    debug i (STR ''typed MU-TERM dependency graph'') (do {
      _ \<leftarrow> check_muterm_typed_dep_graph \<mu> R S P edps;
      check_muterm_typed_graph_components I J \<mu> i R S P edps
    })"
| "check_muterm_typed_graph_components I J \<mu> i R S P [] = succeed"
| "check_muterm_typed_graph_components I J \<mu> i R S P
      ((None,C)#rest) =
    check_muterm_typed_graph_components I J \<mu> (add_index i 1) R S P rest"
| "check_muterm_typed_graph_components I J \<mu> i R S P
      ((Some prf,C)#rest) = do {
    check_muterm_typed_dp_proof I J \<mu> (add_index i 1) R S
      (filter (\<lambda>dp. dp \<in> set C) P) prf;
    check_muterm_typed_graph_components I J \<mu> (add_index i 1) R S P rest
  }"

lemma muterm_typed_pair_step_noncollapsing:
  assumes nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
  shows "muterm_typed_pair_step P S = rrstep P"
proof (rule equalityI)
  show "muterm_typed_pair_step P S \<subseteq> rrstep P"
  proof
  fix st
  assume mem: "st \<in> muterm_typed_pair_step P S"
  then show "st \<in> rrstep P"
    unfolding muterm_typed_pair_step_def
  proof
    assume "st \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
    then obtain s t where st: "st = (s,t)"
      and step: "muterm_noncollapsing_rrstep P s t" by auto
    from step show ?thesis unfolding st muterm_noncollapsing_rrstep_def
      rrstep_def' by auto
  next
    assume "st \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    then obtain s t x where st: "st = (s,t)"
      and collapse: "muterm_collapsing_rrstep P s x" by auto
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      unfolding muterm_collapsing_rrstep_def by auto
    from nc[rule_format,OF pair] show ?thesis by simp
  qed
  qed
next
  show "rrstep P \<subseteq> muterm_typed_pair_step P S"
  proof
  fix st
  assume mem: "st \<in> rrstep P"
  obtain s t where st: "st = (s,t)" by (cases st)
  from mem obtain l r \<sigma> where pair: "(l,r) \<in> P"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding st rrstep_def' by auto
  have "muterm_noncollapsing_rrstep P s t"
    unfolding muterm_noncollapsing_rrstep_def
    using pair nc[rule_format,OF pair] s t by auto
  then show "st \<in> muterm_typed_pair_step P S"
    unfolding st muterm_typed_pair_step_def by auto
  qed
qed

lemma muterm_typed_pair_step_mono:
  assumes "P \<subseteq> Q"
  shows "muterm_typed_pair_step P S \<subseteq> muterm_typed_pair_step Q S"
proof
  fix st
  assume mem: "st \<in> muterm_typed_pair_step P S"
  obtain a b where st: "st = (a,b)" by (cases st)
  have memab: "(a,b) \<in> muterm_typed_pair_step P S" using mem st by simp
  from memab consider
      (noncoll) "muterm_noncollapsing_rrstep P a b"
    | (collapse) x where "muterm_collapsing_rrstep P a x"
        "(x,b) \<in> rrstep S"
    unfolding muterm_typed_pair_step_def by blast
  then show "st \<in> muterm_typed_pair_step Q S"
  proof cases
    case noncoll
    from noncoll obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by auto
    have step: "muterm_noncollapsing_rrstep Q a b"
      unfolding muterm_noncollapsing_rrstep_def
      using assms pair rv a b by blast
    show ?thesis unfolding st muterm_typed_pair_step_def using step by blast
  next
    case (collapse x)
    from collapse(1) obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by auto
    have step: "muterm_collapsing_rrstep Q a x"
      unfolding muterm_collapsing_rrstep_def using assms pair a x by blast
    show ?thesis unfolding st muterm_typed_pair_step_def
      using step collapse(2) by blast
  qed
qed

lemma muterm_min_typed_pair_step_mono:
  assumes "P \<subseteq> Q"
  shows "muterm_min_typed_pair_step shp \<mu> R P S \<subseteq>
    muterm_min_typed_pair_step shp \<mu> R Q S"
  unfolding muterm_min_typed_pair_step_def
  using muterm_typed_pair_step_mono[OF assms] by blast

lemma finite_muterm_min_typed_dpp_mono_pairs:
  assumes sub: "P \<subseteq> Q"
    and fin: "finite_muterm_min_typed_dpp shp \<mu> R Q S"
  shows "finite_muterm_min_typed_dpp shp \<mu> R P S"
  unfolding finite_muterm_min_typed_dpp_def
  by (rule SN_rel_mono[
      OF muterm_min_typed_pair_step_mono[OF sub] subset_refl
        fin[unfolded finite_muterm_min_typed_dpp_def]])

lemma finite_csr_dpp_imp_finite_muterm_typed_noncollapsing:
  assumes nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
    and fin: "finite_csr_dpp Sharp \<mu> P R"
  shows "finite_muterm_typed_dpp Sharp \<mu> R P S"
  using fin muterm_typed_pair_step_noncollapsing[OF nc]
  unfolding finite_csr_dpp_def finite_muterm_typed_dpp_def by simp

lemma finite_min_csr_dpp_imp_finite_muterm_min_typed_noncollapsing:
  assumes nc: "\<forall>dp\<in>P. is_Fun (snd dp)"
    and fin: "finite_min_csr_dpp Sharp \<mu> P R"
  shows "finite_muterm_min_typed_dpp Sharp \<mu> R P S"
  using fin muterm_typed_pair_step_noncollapsing[OF nc]
  unfolding finite_min_csr_dpp_def finite_muterm_min_typed_dpp_def
    muterm_min_typed_pair_step_def csr_min_pair_step_def
  by simp

lemma check_muterm_typed_graph_components_member:
  assumes ok: "isOK (check_muterm_typed_graph_components
      I J \<mu> i R S P edps)"
    and mem: "(Some prf,C) \<in> set edps"
  shows "\<exists>j. isOK (check_muterm_typed_dp_proof I J \<mu> j R S
    (filter (\<lambda>dp. dp \<in> set C) P) prf)"
  using ok mem
proof (induct edps arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  obtain po D where head: "head = (po,D)" by (cases head)
  show ?case
  proof (cases po)
    case None
    from Cons.prems(1) head None have tail:
      "isOK (check_muterm_typed_graph_components
        I J \<mu> (add_index i 1) R S P rest)" by simp
    from Cons.prems(2) head None have mem': "(Some prf,C) \<in> set rest"
      by auto
    show ?thesis by (rule Cons.hyps[OF tail mem'])
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = head")
      case True
      from Cons.prems(1) head Some True show ?thesis by auto
    next
      case False
      from Cons.prems(1) head Some have tail:
        "isOK (check_muterm_typed_graph_components
          I J \<mu> (add_index i 1) R S P rest)" by simp
      from Cons.prems(2) False have mem': "(Some prf,C) \<in> set rest"
        by auto
      show ?thesis by (rule Cons.hyps[OF tail mem'])
    qed
  qed
qed

lemma rrstep_subset_csdp_step_union:
  "rrstep S \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
proof
  fix st
  assume "st \<in> rrstep S"
  then obtain l r \<sigma> where lr: "(l,r) \<in> S"
    and st: "st = (l \<cdot> \<sigma>,r \<cdot> \<sigma>)"
    unfolding rrstep_def' by auto
  have lr_union: "(l,r) \<in> R \<union> S" using lr by blast
  have root: "(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> rstep_r_p_s (R \<union> S) (l,r) [] \<sigma>"
    unfolding rstep_r_p_s_def Let_def using lr_union
    by (simp add: ctxt_supt_id)
  show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
    unfolding st csdp_step_def csdp_step_p_def
    apply (rule Quasi_Order.mem_rel_ofI)
    apply (rule exI[of _ "[]"])
    apply (rule Quasi_Order.mem_rel_ofI)
    apply (intro conjI)
     apply (rule exI[of _ "(l,r)"])
     apply (rule exI[of _ \<sigma>])
     apply (rule root)
    by (simp add: csdp_step_cond_def)
qed

lemma muterm_typed_relto_witness:
  assumes step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step P S O (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_typed_pair_step {(l,r)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from step obtain a b where pre: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_typed_pair_step P S"
    and post: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  have Rsub: "csdp_step Sharp \<mu> R \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
  proof
    fix st
    assume mem: "st \<in> csdp_step Sharp \<mu> R"
    then obtain a b p lr \<sigma> where st: "st = (a,b)"
      and cond: "csdp_step_cond Sharp \<mu> p a"
      and raw: "(a,b) \<in> rstep_r_p_s R lr p \<sigma>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lrR: "lr \<in> R"
      unfolding rstep_r_p_s_def Let_def by auto
    have lrRS: "lr \<in> R \<union> S" using lrR by blast
    have raw': "(a,b) \<in> rstep_r_p_s (R \<union> S) lr p \<sigma>"
      using raw lrRS unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using pre rtrancl_mono[OF Rsub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using post rtrancl_mono[OF Rsub] by blast
  have event_cases:
      "(a,b) \<in> {(s,t). muterm_noncollapsing_rrstep P s t} \<or>
       (a,b) \<in> {(s,t). \<exists>x.
         muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    using event unfolding muterm_typed_pair_step_def by blast
  from event_cases show ?thesis
  proof
    assume raw: "(a,b) \<in> {(s,t). muterm_noncollapsing_rrstep P s t}"
    then have nc: "muterm_noncollapsing_rrstep P a b" by simp
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "muterm_noncollapsing_rrstep {(l,r)} a b"
      unfolding muterm_noncollapsing_rrstep_def using pair rv a b by auto
    have typed: "(a,b) \<in> muterm_typed_pair_step {(l,r)} S"
      unfolding muterm_typed_pair_step_def using one by auto
    have body: "(l,r) \<in> P \<and>
        (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
          muterm_typed_pair_step {(l,r)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
      using pair pre' post' pre typed post unfolding a b by blast
    show ?thesis using body by blast
  next
    assume raw: "(a,b) \<in> {(s,t). \<exists>x.
      muterm_collapsing_rrstep P s x \<and> (x,t) \<in> rrstep S}"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep S" by auto
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have typed: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} S"
      unfolding muterm_typed_pair_step_def using one bridge by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (R \<union> S)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
      using bridge' post' by auto
    have vy: "Var y \<cdot> \<sigma> = \<sigma> y"
      by (cases "Var y", simp_all)
    have body: "(l,Var y) \<in> P \<and>
        (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (\<sigma> y,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
        (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
          muterm_typed_pair_step {(l,Var y)} S O (csdp_step Sharp \<mu> R)\<^sup>*"
      using pair pre' post'' pre typed post
      unfolding a x by blast
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x="Var y" in exI)
      apply (rule_tac x=\<sigma> in exI)
      using body vy by simp
  qed
qed

lemma muterm_min_typed_relto_witness:
  assumes step: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R P S O
      (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "\<exists>l r \<sigma>. (l,r) \<in> P \<and>
    (s,l \<cdot> \<sigma>) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (r \<cdot> \<sigma>,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>* \<and>
    (s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
      muterm_min_typed_pair_step Sharp \<mu> R {(l,r)} S O
      (csdp_step Sharp \<mu> R)\<^sup>*"
proof -
  from step obtain a b where pre: "(s,a) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
    and event: "(a,b) \<in> muterm_min_typed_pair_step Sharp \<mu> R P S"
    and post: "(b,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>*" by auto
  from event have typed: "(a,b) \<in> muterm_typed_pair_step P S"
    and normal: "SN_on (csdp_step Sharp \<mu> R) {b}"
    unfolding muterm_min_typed_pair_step_def by auto
  have Rsub: "csdp_step Sharp \<mu> R \<subseteq> csdp_step Sharp \<mu> (R \<union> S)"
  proof
    fix st
    assume mem: "st \<in> csdp_step Sharp \<mu> R"
    then obtain x y p lr \<tau> where st: "st = (x,y)"
      and cond: "csdp_step_cond Sharp \<mu> p x"
      and raw: "(x,y) \<in> rstep_r_p_s R lr p \<tau>"
      unfolding csdp_step_def csdp_step_p_def by auto
    from raw have lrR: "lr \<in> R"
      unfolding rstep_r_p_s_def Let_def by auto
    have raw': "(x,y) \<in> rstep_r_p_s (R \<union> S) lr p \<tau>"
      using raw lrR unfolding rstep_r_p_s_def Let_def by auto
    show "st \<in> csdp_step Sharp \<mu> (R \<union> S)"
      unfolding st csdp_step_def csdp_step_p_def using cond raw' by blast
  qed
  have pre': "(s,a) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using pre rtrancl_mono[OF Rsub] by blast
  have post': "(b,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
    using post rtrancl_mono[OF Rsub] by blast
  from typed have cases:
      "muterm_noncollapsing_rrstep P a b \<or>
       (\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S)"
    unfolding muterm_typed_pair_step_def by blast
  from cases show ?thesis
  proof
    assume nc: "muterm_noncollapsing_rrstep P a b"
    then obtain l r \<sigma> where pair: "(l,r) \<in> P" and rv: "\<not> is_Var r"
      and a: "a = l \<cdot> \<sigma>" and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,r)} S"
      unfolding muterm_typed_pair_step_def muterm_noncollapsing_rrstep_def
      using rv a b by auto
    have min: "(a,b) \<in> muterm_min_typed_pair_step Sharp \<mu> R {(l,r)} S"
      unfolding muterm_min_typed_pair_step_def using one normal by auto
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x=r in exI)
      apply (rule_tac x=\<sigma> in exI)
      using pair pre' post' pre min post unfolding a b by blast
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S"
    then obtain x where collapse: "muterm_collapsing_rrstep P a x"
      and bridge: "(x,b) \<in> rrstep S" by blast
    from collapse obtain l y \<sigma> where pair: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    have one_coll: "muterm_collapsing_rrstep {(l,Var y)} a x"
      unfolding muterm_collapsing_rrstep_def using a x by auto
    have one: "(a,b) \<in> muterm_typed_pair_step {(l,Var y)} S"
      unfolding muterm_typed_pair_step_def using one_coll bridge by auto
    have min: "(a,b) \<in>
        muterm_min_typed_pair_step Sharp \<mu> R {(l,Var y)} S"
      unfolding muterm_min_typed_pair_step_def using one normal by auto
    have bridge': "(x,b) \<in> csdp_step Sharp \<mu> (R \<union> S)"
      using rrstep_subset_csdp_step_union bridge by blast
    have post'': "(x,t) \<in> (csdp_step Sharp \<mu> (R \<union> S))\<^sup>*"
      using bridge' post' by auto
    have vy: "Var y \<cdot> \<sigma> = \<sigma> y" by simp
    have whole: "(s,t) \<in> (csdp_step Sharp \<mu> R)\<^sup>* O
        muterm_min_typed_pair_step Sharp \<mu> R {(l,Var y)} S O
        (csdp_step Sharp \<mu> R)\<^sup>*"
      using pre min post unfolding a by blast
    show ?thesis
      apply (rule_tac x=l in exI)
      apply (rule_tac x="Var y" in exI)
      apply (rule_tac x=\<sigma> in exI)
      apply (intro conjI)
         apply (rule pair)
        apply (rule pre'[unfolded a])
       apply (simp only: vy, rule post''[unfolded x])
      by (rule whole)
  qed
qed

lemma csr_dep_graph_edge_check_steps_all:
  fixes R :: "(((('f::{showl,compare_order},label_type) lab),'v::compare_order) rules)"
  assumes wf: "wf_trs (set R)"
    and steps: "(t \<cdot> \<sigma>,u \<cdot> \<tau>) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
  shows "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) R
    ((((s,t),()),((u,v),())))"
proof (simp only: csr_dep_graph_edge_check.simps, intro conjI notI)
  assume no: "csr_inactive_arg_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_frozen_root_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_frozen_root_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_tcap_no_edge R t u"
  from csr_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_reverse_tcap_no_edge R t u"
  from csr_reverse_tcap_no_edge_sound[OF no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_root_tcap_no_edge (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_root_tcap_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_shared_inactive_arg_no_edge
    (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_shared_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
next
  assume no: "csr_shared_source_inactive_arg_no_edge
    (csr_dp_root_mu (mu_of \<mu>)) R t u"
  from csr_shared_source_inactive_arg_no_edge_sound[OF wf no, of \<sigma> \<tau>] steps
  show False by blast
qed

lemma check_muterm_typed_dep_graph_select_component:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and pair: "\<And>i. (s i,t i) \<in> set P"
    and steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set (R @ S)))\<^sup>*"
  shows "\<exists>prf Cs n. (Some prf,Cs) \<in> set edps \<and>
    (\<forall>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs)"
proof -
  let ?echeck = "csr_dep_graph_edge_check (csr_dp_root_mu (mu_of \<mu>)) (R @ S)"
  let ?conv = "\<lambda>(real,Cs). (real \<noteq> None,map (\<lambda>(s,t). ((s,t),())) Cs)"
  let ?p = "\<lambda>i. ((s i,t i),())"
  from check have wf: "wf_trs (set (R @ S))"
    and subset: "set P \<subseteq> set (concat (map snd edps))"
    and scc: "isOK (check_graph_decomp (showsl \<circ> fst)
      (Multi_Map.empty (root o fst o fst)) graph_approx_csr_rt
      Multi_Map.insert ?echeck (map ?conv edps))"
    unfolding check_muterm_typed_dep_graph_def by (auto simp: Let_def)
  have path: "\<And>i. ?echeck (?p i,?p (Suc i))"
  proof -
    fix i
    show "?echeck (?p i,?p (Suc i))"
      unfolding Let_def
      by (rule csr_dep_graph_edge_check_steps_all[
        where R="R @ S" and s="s i" and t="t i"
          and u="s (Suc i)" and v="t (Suc i)"
          and \<sigma>="\<sigma> i" and \<tau>="\<sigma> (Suc i)",
        OF wf steps[of i]])
  qed
  have lift_node: "\<And>l r. (l,r) \<in> set (concat (map snd edps)) \<Longrightarrow>
    ((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
  proof -
    fix l r
    assume lr: "(l,r) \<in> set (concat (map snd edps))"
    then obtain x where x: "x \<in> set edps" and lrx: "(l,r) \<in> set (snd x)"
      by auto
    obtain real Cs where xeq: "x = (real,Cs)" by (cases x,auto)
    from x xeq have mem: "(real,Cs) \<in> set edps" by simp
    from lrx xeq have lrCs: "(l,r) \<in> set Cs" by simp
    have node: "((l,r),()) \<in> set (map (\<lambda>(s,t). ((s,t),())) Cs)"
      using lrCs by force
    have conv_mem: "?conv (real,Cs) \<in> set (map ?conv edps)"
      using mem by (auto split: prod.splits)
    have comp_mem: "snd (?conv (real,Cs)) \<in> set (map snd (map ?conv edps))"
      using conv_mem unfolding set_map by blast
    have node': "((l,r),()) \<in> set (snd (?conv (real,Cs)))" using node by simp
    show "((l,r),()) \<in> set (concat (map snd (map ?conv edps)))"
      using comp_mem node' unfolding set_concat by blast
  qed
  have nodes: "path_nodes ?p \<subseteq> set (concat (map snd (map ?conv edps)))"
    using pair subset lift_node unfolding path_nodes_def by blast
  have key_insert: "\<And>x m. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
    Multi_Map.key_fun (Multi_Map.insert x m) = root \<circ> fst \<circ> fst" by simp
  have approx: "\<And>m a b. Multi_Map.key_fun m = root \<circ> fst \<circ> fst \<Longrightarrow>
    ?echeck (a,b) \<Longrightarrow> b \<in> set (Multi_Map.values m) \<Longrightarrow>
    b \<in> set (graph_approx_csr_rt m a)"
    unfolding graph_approx_csr_rt.simps by simp
  have component: "\<exists>q C. (?p =\<dots> q) \<and>
    C \<in> set (map snd (filter fst (map ?conv edps))) \<and>
    path_nodes q \<subseteq> set C"
    by (rule check_graph_decomp_sound[of "\<lambda>m. set (Multi_Map.values m)",
      OF values_empty values_insert, of "\<lambda>m. Multi_Map.key_fun m = (root o fst o fst)",
      OF key_fun_empty key_insert approx scc path nodes])
  from component obtain q C where suffix: "?p =\<dots> q"
    and ending: "path_nodes q \<subseteq> set C"
    and component_mem: "C \<in> set (map snd (filter fst (map ?conv edps)))"
    by blast
  from component_mem obtain p Cs where mem: "(Some p,Cs) \<in> set edps"
    and C: "C = map (\<lambda>(s,t). ((s,t),())) Cs" by force
  from suffix obtain n where pq: "\<And>m. ?p (m+n) = q m"
    unfolding Graph.suffix_def by blast
  have CP: "\<And>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs"
  proof -
    fix m
    have "?p (m+n) \<in> path_nodes q"
      using pq[of m] unfolding path_nodes_def by blast
    with ending C pair[of "m+n"]
    show "(s (m+n),t (m+n)) \<in> set P \<inter> set Cs" by force
  qed
  show ?thesis
  proof (intro exI conjI)
    show "(Some p,Cs) \<in> set edps" by (rule mem)
    show "\<forall>m. (s (m+n),t (m+n)) \<in> set P \<inter> set Cs"
    proof
      fix m
      show "(s (m+n),t (m+n)) \<in> set P \<inter> set Cs" by (rule CP)
    qed
  qed
qed

lemma check_muterm_typed_dep_graph_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_typed_dpp Sharp (mu_of \<mu>) (set R)
        (set P \<inter> set C) (set S)"
  shows "finite_muterm_typed_dpp Sharp (mu_of \<mu>) (set R) (set P) (set S)"
proof -
  let ?P = "set P"
  let ?RL = "R @ S"
  let ?RS = "set ?RL"
  show ?thesis
    unfolding finite_muterm_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    let ?A = "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step ?P (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?A)"
    then obtain ch where chain: "\<And>i. (ch i,ch (Suc i)) \<in> ?A" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?P \<and>
      (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(l,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof
      fix i
      from muterm_typed_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?P \<and>
        (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step {(l,r)} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?P"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_typed_pair_step {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    from check_muterm_typed_dep_graph_select_component[
      where \<mu>=\<mu> and R=R and S=S and P=P and edps=edps
        and s=s and t=t and \<sigma>=\<sigma>, OF check pair steps]
    obtain p Cs n where mem: "(Some p,Cs) \<in> set edps"
      and CP_all: "\<forall>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    from CP_all have CP: "\<And>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    let ?tail = "\<lambda>m. ch (m+n)"
    have tail_step: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof -
      fix m
      have singleton: "{(s (m+n),t (m+n))} \<subseteq> ?P \<inter> set Cs"
        using CP[of m] by auto
      have mono: "muterm_typed_pair_step {(s (m+n),t (m+n))} (set S)
        \<subseteq> muterm_typed_pair_step (?P \<inter> set Cs) (set S)"
        by (rule muterm_typed_pair_step_mono[OF singleton])
      have suc_add: "Suc m+n = Suc (m+n)" by simp
      have inc: "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step {(s (m+n),t (m+n))} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* \<subseteq>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      from typed[of "m+n"] inc show "(?tail m,?tail (Suc m)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        unfolding suc_add
        by blast
    qed
    have tail_sn: "SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_typed_dpp_def SN_rel_on_def .
    have tail_is_chain: "chain
      ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
       muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
       (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_typed_pair_step (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed


lemma check_muterm_min_typed_dep_graph_sound:
  fixes \<mu> :: "(('f::{showl,compare_order},label_type) lab) muL"
  assumes check: "isOK (check_muterm_typed_dep_graph \<mu> R S P edps)"
    and fin: "\<And>prf C. (Some prf,C) \<in> set edps \<Longrightarrow>
      finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R)
        (set P \<inter> set C) (set S)"
  shows "finite_muterm_min_typed_dpp Sharp (mu_of \<mu>) (set R) (set P) (set S)"
proof -
  let ?P = "set P"
  let ?RL = "R @ S"
  let ?RS = "set ?RL"
  show ?thesis
    unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def SN_on_def
  proof (rule notI)
    let ?A = "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) ?P (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    assume infinite: "\<exists>f. f 0 \<in> UNIV \<and>
      (\<forall>i. (f i,f (Suc i)) \<in> ?A)"
    then obtain ch where chain: "\<And>i. (ch i,ch (Suc i)) \<in> ?A" by auto
    have ex_step: "\<forall>i. \<exists>l r \<sigma>.
      (l,r) \<in> ?P \<and>
      (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(l,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof
      fix i
      from muterm_min_typed_relto_witness[OF chain[of i]]
      show "\<exists>l r \<sigma>. (l,r) \<in> ?P \<and>
        (ch i,l \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
        (ch i,ch (Suc i)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(l,r)} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (simp add: set_append)
    qed
    from choice[OF ex_step] obtain s where choose_s: "\<forall>i. \<exists>r \<sigma>.
      (s i,r) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (r \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(s i,r)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_s] obtain t where choose_t: "\<forall>i. \<exists>\<sigma>.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma>) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma>,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R) {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from choice[OF choose_t] obtain \<sigma> where chosen: "\<forall>i.
      (s i,t i) \<in> ?P \<and>
      (ch i,s i \<cdot> \<sigma> i) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (t i \<cdot> \<sigma> i,ch (Suc i)) \<in> (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>* \<and>
      (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast
    from chosen have pair: "\<And>i. (s i,t i) \<in> ?P"
      and pre: "\<And>i. (ch i,s i \<cdot> \<sigma> i) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and post: "\<And>i. (t i \<cdot> \<sigma> i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      and typed: "\<And>i. (ch i,ch (Suc i)) \<in>
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
        muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s i,t i)} (set S) O
        (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
      by blast+
    have steps: "\<And>i. (t i \<cdot> \<sigma> i,s (Suc i) \<cdot> \<sigma> (Suc i)) \<in>
      (csdp_step Sharp (mu_of \<mu>) ?RS)\<^sup>*"
      using post pre by (meson rtrancl_trans)
    from check_muterm_typed_dep_graph_select_component[
      where \<mu>=\<mu> and R=R and S=S and P=P and edps=edps
        and s=s and t=t and \<sigma>=\<sigma>, OF check pair steps]
    obtain p Cs n where mem: "(Some p,Cs) \<in> set edps"
      and CP_all: "\<forall>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    from CP_all have CP: "\<And>m. (s (m+n),t (m+n)) \<in> ?P \<inter> set Cs"
      by auto
    let ?tail = "\<lambda>m. ch (m+n)"
    have tail_step: "\<And>m. (?tail m,?tail (Suc m)) \<in>
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
    proof -
      fix m
      have singleton: "{(s (m+n),t (m+n))} \<subseteq> ?P \<inter> set Cs"
        using CP[of m] by auto
      have mono: "muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          {(s (m+n),t (m+n))} (set S)
        \<subseteq> muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
          (?P \<inter> set Cs) (set S)"
        by (rule muterm_min_typed_pair_step_mono[OF singleton])
      have suc_add: "Suc m+n = Suc (m+n)" by simp
      have inc: "(csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            {(s (m+n),t (m+n))} (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* \<subseteq>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        by (meson relcomp_mono mono subset_refl)
      from typed[of "m+n"] inc show "(?tail m,?tail (Suc m)) \<in>
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
          muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
            (?P \<inter> set Cs) (set S) O
          (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*"
        unfolding suc_add
        by blast
    qed
    have tail_sn: "SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      using fin[OF mem]
      unfolding finite_muterm_min_typed_dpp_def SN_rel_on_def .
    have tail_is_chain: "chain
      ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
       muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
         (?P \<inter> set Cs) (set S) O
       (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*) ?tail"
      using tail_step by simp
    have not_tail_sn: "\<not> SN ((csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>* O
      muterm_min_typed_pair_step Sharp (mu_of \<mu>) (set R)
        (?P \<inter> set Cs) (set S) O
      (csdp_step Sharp (mu_of \<mu>) (set R))\<^sup>*)"
      by (rule not_SN_onI[of ?tail], simp, rule tail_is_chain)
    from not_tail_sn tail_sn show False ..
  qed
qed


end
