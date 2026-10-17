section \<open>Giesl--Arts AAECC Switch to Innermost Termination\<close>

text \<open>
  This checker theory formalizes the signature separation used by Theorem 16 of
  Giesl and Arts.  Keeping the partition predicate independent of the
  executable checker makes the eventual soundness theorem state exactly the
  mathematical side conditions that a certificate has to establish.
\<close>

theory AAECC_Innermost_Switch
  imports
    Right_Forward_Closures.Gramlich_Innermost_Switch
    TRS.Signature_Extension
begin

definition aaecc_list_singleton_ext :: "'a rel \<Rightarrow> 'a list rel" where
  "aaecc_list_singleton_ext R =
    {(xs @ a # ys, xs @ b # ys) | xs a ys b. (a,b) \<in> R}"

lemma aaecc_SN_list_singleton_ext:
  assumes "SN R"
  shows "SN (aaecc_list_singleton_ext R)"
proof -
  have eq: "aaecc_list_singleton_ext R = listrel1 R"
    unfolding aaecc_list_singleton_ext_def listrel1_def by blast
  from assms show ?thesis unfolding eq SN_iff_wf
    by (metis listrel1_converse wf_listrel1_iff)
qed

definition aaecc_signature_separated ::
  "'f sig \<Rightarrow> ('f,'v) trs \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "aaecc_signature_separated F R1 R2 \<longleftrightarrow>
    funas_trs R1 \<inter> F = {} \<and>
    (\<forall>(l,r)\<in>R2.
      is_Fun r \<and>
      root l \<in> Some ` F \<and>
      root r \<in> Some ` F \<and>
      funas_args_term l \<inter> F = {} \<and>
      funas_args_term r \<inter> F = {})"

definition aaecc_signature_impl ::
  "'f list \<Rightarrow> ('f,'v) rule list \<Rightarrow> ('f,'v) rule list \<Rightarrow> ('f \<times> nat) list"
where
  "aaecc_signature_impl fs R1 R2 =
    filter (\<lambda>(f,n). f \<in> set fs) (funas_trs_list (R1 @ R2))"

definition aaecc_signature_separated_impl ::
  "'f list \<Rightarrow> ('f,'v) rule list \<Rightarrow> ('f,'v) rule list \<Rightarrow> bool"
where
  "aaecc_signature_separated_impl fs R1 R2 =
    (let F = set (aaecc_signature_impl fs R1 R2) in
      list_all (\<lambda>fa. fa \<notin> F) (funas_trs_list R1) \<and>
      list_all (\<lambda>(l,r).
        is_Fun r \<and>
        root l \<in> Some ` F \<and>
        root r \<in> Some ` F \<and>
        list_all (\<lambda>fa. fa \<notin> F) (funas_args_term_list l) \<and>
        list_all (\<lambda>fa. fa \<notin> F) (funas_args_term_list r)) R2)"

lemma aaecc_signature_separated_impl_sound:
  assumes "aaecc_signature_separated_impl fs R1 R2"
  shows "aaecc_signature_separated
    (set (aaecc_signature_impl fs R1 R2)) (set R1) (set R2)"
  using assms unfolding aaecc_signature_separated_impl_def
    aaecc_signature_separated_def Let_def list_all_iff
  by auto

lemma aaecc_signature_separated_R1:
  assumes "aaecc_signature_separated F R1 R2" and "(l,r) \<in> R1"
  shows "funas_term l \<inter> F = {}" "funas_term r \<inter> F = {}"
proof -
  from assms(1) have disjoint: "funas_trs R1 \<inter> F = {}"
    unfolding aaecc_signature_separated_def by simp
  from assms(2) have member:
      "funas_rule (l,r) \<subseteq> funas_trs R1"
    unfolding funas_trs_def by auto
  from member disjoint have "funas_rule (l,r) \<inter> F = {}" by auto
  then show "funas_term l \<inter> F = {}" "funas_term r \<inter> F = {}"
    unfolding funas_rule_def by auto
qed

lemma aaecc_signature_separated_R2:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and lr: "(l,r) \<in> R2"
  shows "is_Fun r"
    "root l \<in> Some ` F"
    "root r \<in> Some ` F"
    "funas_args_term l \<inter> F = {}"
    "funas_args_term r \<inter> F = {}"
  using sep lr unfolding aaecc_signature_separated_def by auto

lemma aaecc_R2_non_collapsing:
  assumes "aaecc_signature_separated F R1 R2"
  shows "non_collapsing R2"
  using aaecc_signature_separated_R2(1)[OF assms]
  unfolding non_collapsing_def by auto

lemma aaecc_signature_free_has_no_R2_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and free: "funas_term s \<inter> F = {}"
  shows "(s,t) \<notin> rstep R2"
proof
  assume step: "(s,t) \<in> rstep R2"
  from step obtain C l r sigma where lr: "(l,r) \<in> R2"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>" by auto
  from aaecc_signature_separated_R2(2)[OF sep lr]
  obtain fn where fn: "fn \<in> F" "root l = Some fn" by auto
  have fn_l: "fn \<in> funas_term l"
    using fn(2) unfolding funas_term_conv by auto
  have fn_instance: "fn \<in> funas_term (l \<cdot> sigma)"
    using fn_l unfolding funas_term_subst by auto
  have "fn \<in> funas_term s"
    using fn_instance unfolding s funas_term_ctxt_apply by auto
  with fn(1) free show False by auto
qed

lemma aaecc_signature_free_R1_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and free: "funas_term s \<inter> F = {}"
    and step: "(s,t) \<in> rstep R1"
  shows "funas_term t \<inter> F = {}"
proof -
  from step obtain C l r sigma where lr: "(l,r) \<in> R1"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>" by auto
  from wf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from aaecc_signature_separated_R1[OF sep lr]
  show ?thesis using free vars unfolding s t funas_term_ctxt_apply
    funas_term_subst by blast
qed

lemma aaecc_R1_step_no_new_signature:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and step: "(s,t) \<in> rstep R1"
  shows "funas_term t \<inter> F \<subseteq> funas_term s \<inter> F"
proof -
  from step obtain C l r sigma where lr: "(l,r) \<in> R1"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>" by auto
  from wf lr have vars: "vars_term r \<subseteq> vars_term l"
    unfolding wf_trs_def by auto
  from aaecc_signature_separated_R1[OF sep lr]
  show ?thesis using vars unfolding s t funas_term_ctxt_apply
    funas_term_subst by blast
qed

lemma aaecc_signature_free_R1_steps:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and free: "funas_term s \<inter> F = {}"
    and steps: "(s,t) \<in> (rstep R1)\<^sup>*"
  shows "funas_term t \<inter> F = {}"
  apply (rule rtrancl_induct[OF steps])
   apply (rule free)
  by (meson aaecc_signature_free_R1_step sep wf)

lemma aaecc_signature_free_NF_union:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and free: "funas_term s \<inter> F = {}"
  shows "s \<in> NF_trs (R1 \<union> R2) \<longleftrightarrow> s \<in> NF_trs R1"
  unfolding rstep_union NF_iff_no_step
  using aaecc_signature_free_has_no_R2_step[OF sep free] by blast

lemma aaecc_signature_free_inn_R1_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and free: "funas_term s \<inter> F = {}"
    and step: "(s,t) \<in> inn_rstep R1"
  shows "(s,t) \<in> inn_rstep (R1 \<union> R2)"
    "funas_term t \<inter> F = {}"
proof -
  from step obtain l r sigma C where lr: "(l,r) \<in> R1"
    and args_nf: "set (args (l \<cdot> sigma)) \<subseteq> NF_trs R1"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>"
    by (cases rule: inn_rstep.cases) auto
  have args_nf_union:
      "set (args (l \<cdot> sigma)) \<subseteq> NF_trs (R1 \<union> R2)"
  proof
    fix u
    assume u: "u \<in> set (args (l \<cdot> sigma))"
    have sub_instance: "funas_term u \<subseteq> funas_term (l \<cdot> sigma)"
      using u funas_term_args by auto
    have sub_source: "funas_term (l \<cdot> sigma) \<subseteq> funas_term s"
      unfolding s funas_term_ctxt_apply by auto
    have u_free: "funas_term u \<inter> F = {}"
      using free sub_instance sub_source by auto
    from args_nf u aaecc_signature_free_NF_union[OF sep u_free]
    show "u \<in> NF_trs (R1 \<union> R2)" by blast
  qed
  show "(s,t) \<in> inn_rstep (R1 \<union> R2)"
    unfolding s t by (rule inn_rstep[OF UnI1[OF lr] args_nf_union])
  from step[THEN set_mp[OF inn_rstep_rstep]]
  show "funas_term t \<inter> F = {}"
    by (rule aaecc_signature_free_R1_step[OF sep wf free])
qed

lemma aaecc_signature_free_SN_R1:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term s \<inter> F = {}"
  shows "SN_on (inn_rstep R1) {s}"
proof (rule ccontr)
  assume "\<not> SN_on (inn_rstep R1) {s}"
  then obtain f where f0: "f 0 = s"
    and steps: "\<And>i. (f i, f (Suc i)) \<in> inn_rstep R1"
    unfolding SN_defs by blast
  have free_f: "funas_term (f i) \<inter> F = {}" for i
  proof (induct i)
    case 0
    show ?case using free unfolding f0 .
  next
    case (Suc i)
    from aaecc_signature_free_inn_R1_step(2)[
        OF sep wf Suc steps[of i]]
    show ?case .
  qed
  have union_steps:
      "(f i, f (Suc i)) \<in> inn_rstep (R1 \<union> R2)" for i
    by (rule aaecc_signature_free_inn_R1_step(1)[
        OF sep wf free_f steps])
  from inner_SN show False unfolding SN_defs using union_steps by blast
qed

context
  fixes ren :: "'v :: infinite renaming2"
begin

interpretation aaecc_clean: cleaning_same_var "- F"
    "\<lambda>_. Var undefined" "Var undefined"
  by (unfold_locales, auto)

fun aaecc_inn_clean_term ::
  "'f sig \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term" where
  "aaecc_inn_clean_term F (Var x) = Var x"
| "aaecc_inn_clean_term F (Fun f ts) =
    (if (f,length ts) \<in> - F
     then Fun f (map (aaecc_inn_clean_term F) ts)
     else Var undefined)"

fun aaecc_clean_below ::
  "'f sig \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term" where
  "aaecc_clean_below F (Var x) = Var x"
| "aaecc_clean_below F (Fun f ts) =
    Fun f (map (aaecc_inn_clean_term F) ts)"

lemma aaecc_inn_clean_term_eq:
  "aaecc_inn_clean_term F t = aaecc_clean.clean_term F t"
  by (induct t) auto

lemma aaecc_clean_below_update_eq:
  assumes i: "i < length ss"
    and eq: "aaecc_inn_clean_term F (ss ! i) = aaecc_inn_clean_term F u"
  shows "aaecc_clean_below F (Fun f ss) =
    aaecc_clean_below F (Fun f (ss[i := u]))"
proof -
  have mapped_nth: "aaecc_inn_clean_term F (ss ! i) =
      map (aaecc_inn_clean_term F) ss ! i" using i by simp
  show ?thesis
    apply (simp add: map_update)
    apply (subst eq[symmetric])
    apply (rule sym)
    apply (simp only: mapped_nth list_update_id)
    done
qed

definition aaecc_inn_clean_subst where
  "aaecc_inn_clean_subst F sigma = aaecc_inn_clean_term F \<circ> sigma"

lemma aaecc_clean_term_funas:
  "funas_term (aaecc_inn_clean_term F t) \<subseteq> - F"
  by (induct t) (auto split: if_splits)

lemma aaecc_clean_below_args:
  "funas_args_term (aaecc_clean_below F t) \<subseteq> - F"
proof (cases t)
  case (Var x)
  show ?thesis unfolding Var funas_args_term_def by simp
next
  case (Fun f ts)
  show ?thesis unfolding Fun funas_args_term_def
    using aaecc_clean_term_funas by auto
qed

lemma aaecc_alien_below_is_alien_or_below_alien_root:
  assumes z: "z \<in> set (aliens_below F t)"
  shows "z \<in> set (aliens F t) \<or>
    (t \<in> set (aliens F t) \<and> z \<lhd> t)"
proof (cases t)
  case (Var x)
  with z show ?thesis by simp
next
  case (Fun f ts)
  show ?thesis
  proof (cases "(f,length ts) \<in> F")
    case True
    with z show ?thesis unfolding Fun by simp
  next
    case False
    from z obtain u where u: "u \<in> set ts"
      and zu: "z \<in> set (aliens F u)" unfolding Fun by auto
    from aliens_imp_supteq[OF zu] have "u \<unrhd> z" .
    with u have "z \<lhd> Fun f ts" by auto
    with False show ?thesis unfolding Fun by simp
  qed
qed

lemma aaecc_concat_map_nth_split:
  assumes i: "i < length xs" and mid: "f (xs ! i) = pre @ a # ys"
  shows "concat (map f xs) =
    (concat (map f (take i xs)) @ pre) @ a #
      (ys @ concat (map f (drop (Suc i) xs)))"
proof -
  have split: "xs = take i xs @ xs ! i # drop (Suc i) xs"
    by (rule id_take_nth_drop[OF i])
  show ?thesis
    apply (subst (1) split)
    apply (simp only: map_append list.map concat_append concat.simps mid
        append_assoc append_Cons)
    done
qed

lemma aaecc_inn_clean_subst_apply:
  assumes "funas_term t \<subseteq> - F"
  shows "aaecc_inn_clean_term F (t \<cdot> sigma) =
    t \<cdot> aaecc_inn_clean_subst F sigma"
  using assms
proof (induct t)
  case (Var x)
  show ?case by (simp add: aaecc_inn_clean_subst_def o_def)
next
  case (Fun f ts)
  have head: "(f,length ts) \<in> - F" using Fun.prems by auto
  have child: "funas_term t \<subseteq> - F" if "t \<in> set ts" for t
    using Fun.prems that by auto
  have IH: "aaecc_inn_clean_term F (t \<cdot> sigma) =
      t \<cdot> aaecc_inn_clean_subst F sigma" if "t \<in> set ts" for t
    by (rule Fun.hyps[OF that child[OF that]])
  show ?case using head IH
    by (simp add: aaecc_inn_clean_subst_def o_def)
qed

lemma aaecc_clean_subst_apply_term_below:
  assumes static: "funas_args_term t \<subseteq> - F"
    and isfun: "is_Fun t"
  shows "aaecc_clean_below F (t \<cdot> sigma) =
    t \<cdot> aaecc_inn_clean_subst F sigma"
proof -
  from isfun obtain f ts where t: "t = Fun f ts" by (cases t) auto
  have each: "aaecc_inn_clean_term F (u \<cdot> sigma) =
      u \<cdot> aaecc_inn_clean_subst F sigma" if "u \<in> set ts" for u
  proof (rule aaecc_inn_clean_subst_apply)
    from static that show "funas_term u \<subseteq> - F"
      unfolding t funas_args_term_def by auto
  qed
  show ?thesis unfolding t
    by (simp add: aaecc_inn_clean_subst_def o_def each)
qed

lemma aaecc_clean_subst_apply_term_below_unrooted:
  assumes static: "funas_term t \<subseteq> - F"
    and unrooted: "root (t \<cdot> sigma) \<notin> Some ` F"
  shows "aaecc_clean_below F (t \<cdot> sigma) =
    t \<cdot> aaecc_inn_clean_subst F sigma"
proof (cases t)
  case (Var x)
  show ?thesis using unrooted
    by (cases "sigma x")
       (auto simp: Var aaecc_inn_clean_subst_def o_def)
next
  case (Fun f ts)
  from static have args: "funas_args_term (Fun f ts) \<subseteq> - F"
    unfolding Fun funas_args_term_def by auto
  from aaecc_clean_subst_apply_term_below[OF args, of sigma]
  show ?thesis by (simp add: Fun)
qed

lemma aaecc_R2_step_changes_one_alien:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and step: "(s,t) \<in> rstep R2"
  shows "aaecc_clean.clean_term F s = aaecc_clean.clean_term F t \<and>
    (\<exists>xs a b ys.
      aliens (- F) s = xs @ a # ys \<and>
      aliens (- F) t = xs @ b # ys \<and>
      (a,b) \<in> rstep R2)"
proof -
  let ?c = "aaecc_clean.clean_term F"
  let ?a = "aliens (- F)"
  from step obtain C l r sigma where lr: "(l,r) \<in> R2"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>" by auto
  show ?thesis unfolding s t
  proof (induct C)
    case Hole
    from aaecc_signature_separated_R2(2)[OF sep lr]
    obtain f ls where l: "l = Fun f ls" and f: "(f,length ls) \<in> F"
      by (cases l) auto
    from aaecc_signature_separated_R2(3)[OF sep lr]
    obtain g rs where r: "r = Fun g rs" and g: "(g,length rs) \<in> F"
      by (cases r) auto
    have clean: "?c (l \<cdot> sigma) = Var undefined"
      "?c (r \<cdot> sigma) = Var undefined"
      unfolding l r using f g by auto
    have aliens: "?a (l \<cdot> sigma) = [l \<cdot> sigma]"
      "?a (r \<cdot> sigma) = [r \<cdot> sigma]"
      unfolding l r using f g by auto
    from lr have root_step: "(l \<cdot> sigma,r \<cdot> sigma) \<in> rstep R2"
      by (rule rstep.rstep[of l r R2 _ Hole sigma]) auto
    show ?case unfolding intp_actxt.simps
    proof (intro conjI)
      from clean show "?c (l \<cdot> sigma) = ?c (r \<cdot> sigma)" by simp
      show "\<exists>xs a b ys. ?a (l \<cdot> sigma) = xs @ a # ys \<and>
          ?a (r \<cdot> sigma) = xs @ b # ys \<and> (a,b) \<in> rstep R2"
        by (rule exI[of _ "[]"], rule exI[of _ "l \<cdot> sigma"],
            rule exI[of _ "r \<cdot> sigma"], rule exI[of _ "[]"],
            use aliens root_step in auto)
    qed
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?t = "\<lambda>u. Fun f (bef @ C\<langle>u \<cdot> sigma\<rangle> # aft)"
    show ?case
    proof (cases "(f,?n) \<in> - F")
      case False
      then have clean: "?c (?t l) = Var undefined"
        "?c (?t r) = Var undefined" by auto
      from False have aliens: "?a (?t l) = [] @ ?t l # []"
        "?a (?t r) = [] @ ?t r # []" by auto
      from nrrstepI[OF lr refl refl, of "More f bef C aft" sigma]
      have nr_step: "(?t l,?t r) \<in> nrrstep R2" by auto
      from nr_step have alien_step: "(?t l,?t r) \<in> rstep R2"
        using nrrstep_imp_rstep by blast
      show ?thesis unfolding intp_actxt.simps clean aliens
        by (intro conjI, simp,
            rule exI[of _ "[]"], rule exI[of _ "?t l"],
            rule exI[of _ "?t r"], rule exI[of _ "[]"],
            use alien_step in auto)
    next
      case True
      then have clean:
        "?c (?t l) = Fun f (map ?c bef @ ?c (C\<langle>l \<cdot> sigma\<rangle>) # map ?c aft)"
        "?c (?t r) = Fun f (map ?c bef @ ?c (C\<langle>r \<cdot> sigma\<rangle>) # map ?c aft)"
        by auto
      from True have aliens:
        "?a (?t l) = concat (map ?a bef) @ ?a (C\<langle>l \<cdot> sigma\<rangle>) @ concat (map ?a aft)"
        "?a (?t r) = concat (map ?a bef) @ ?a (C\<langle>r \<cdot> sigma\<rangle>) @ concat (map ?a aft)"
        by auto
      from More obtain xs a b ys where ih:
        "?c (C\<langle>l \<cdot> sigma\<rangle>) = ?c (C\<langle>r \<cdot> sigma\<rangle>)"
        "?a (C\<langle>l \<cdot> sigma\<rangle>) = xs @ a # ys"
        "?a (C\<langle>r \<cdot> sigma\<rangle>) = xs @ b # ys"
        "(a,b) \<in> rstep R2" by blast
      show ?thesis unfolding intp_actxt.simps clean aliens ih
      proof (intro conjI)
        show "Fun f (map ?c bef @ ?c (C\<langle>r \<cdot> sigma\<rangle>) # map ?c aft) =
            Fun f (map ?c bef @ ?c (C\<langle>r \<cdot> sigma\<rangle>) # map ?c aft)"
          by simp
        show "\<exists>xsa aa ba ysa.
          concat (map ?a bef) @ (xs @ a # ys) @ concat (map ?a aft) =
            xsa @ aa # ysa \<and>
          concat (map ?a bef) @ (xs @ b # ys) @ concat (map ?a aft) =
            xsa @ ba # ysa \<and> (aa,ba) \<in> rstep R2"
          by (rule exI[of _ "concat (map ?a bef) @ xs"],
              rule exI[of _ a], rule exI[of _ b],
              rule exI[of _ "ys @ concat (map ?a aft)"],
              use ih(4) in auto)
      qed
    qed
  qed
qed

definition aaecc_R1_nf ::
  "('f,'v) trs \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term"
where
  "aaecc_R1_nf R1 s = (SOME t. (s,t) \<in> (rstep R1)\<^sup>!)"

definition aaecc_R1_ok ::
  "'v :: infinite renaming2 \<Rightarrow> ('f,'v) trs \<Rightarrow> bool"
where
  "aaecc_R1_ok (rho :: 'v renaming2) R1 \<longleftrightarrow>
    WCR (rstep R1) \<and>
    (\<forall>l r. (False,l,r) \<notin> critical_pairs rho R1 R1)"

definition aaecc_R1_nf_subst ::
  "('f,'v) trs \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) subst"
where
  "aaecc_R1_nf_subst R1 sigma x = aaecc_R1_nf R1 (sigma x)"

lemma aaecc_signature_free_R1_termination:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term s \<inter> F = {}"
  shows "SN_on (rstep R1) {s}"
proof -
  have WCR: "WCR (rstep R1)"
    using no_cp unfolding aaecc_R1_ok_def by blast
  have WCR_on:
      "WCR_on (rstep R1) {t. SN_on (rstep R1) {t}}"
    using WCR unfolding WCR_on_def by blast
  have overlay: "\<And>l r. (False,l,r) \<notin> critical_pairs ren R1 R1"
    using no_cp unfolding aaecc_R1_ok_def by blast
  from SN_innermost_switch_locally_confluent_overlay_local[
      OF WCR_on overlay wf]
  have switch: "SN_on (inn_rstep R1) = SN_on (rstep R1)" .
  from aaecc_signature_free_SN_R1[OF sep wf inner_SN free]
  show ?thesis unfolding switch .
qed

lemma aaecc_R1_termination:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
  shows "SN (rstep R1)"
proof -
  let ?B = "- F"
  have FR: "funas_trs R1 \<subseteq> ?B"
    using sep unfolding aaecc_signature_separated_def by auto
  have restricted: "SN (sig_step ?B (rstep R1))"
  proof (rule ccontr)
    assume "\<not> SN (sig_step ?B (rstep R1))"
    then obtain f where steps:
        "\<And>i. (f i,f (Suc i)) \<in> sig_step ?B (rstep R1)"
      unfolding SN_defs by blast
    from steps[of 0] have free: "funas_term (f 0) \<inter> F = {}"
      unfolding sig_step_def by auto
    from aaecc_signature_free_R1_termination[
        OF sep wf no_cp inner_SN free]
    show False unfolding SN_on_def using steps by auto
  qed
  from SN_sig_rstep_imp_SN_rstep[OF FR restricted]
  show ?thesis .
qed

lemma aaecc_R1_nf_reaches:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term s \<inter> F = {}"
  shows "(s, aaecc_R1_nf R1 s) \<in> (rstep R1)\<^sup>!"
proof -
  from aaecc_signature_free_R1_termination[OF assms]
  have "\<exists>t. (s,t) \<in> (rstep R1)\<^sup>!"
    by (rule SN_on_imp_normalizability)
  from someI_ex[OF this]
  show ?thesis unfolding aaecc_R1_nf_def .
qed

lemma aaecc_R1_nf_unique:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term s \<inter> F = {}"
    and normal: "(s,t) \<in> (rstep R1)\<^sup>!"
  shows "aaecc_R1_nf R1 s = t"
proof -
  have WCR: "WCR (rstep R1)"
    using no_cp unfolding aaecc_R1_ok_def by blast
  from aaecc_signature_free_R1_termination[OF sep wf no_cp inner_SN free]
  have SN: "SN_on (rstep R1) {s}" .
  have WCR_SN: "WCR_on (rstep R1) {x. SN_on (rstep R1) {x}}"
    using WCR unfolding WCR_on_def by auto
  have CR: "CR_on (rstep R1) {s}"
    by (rule Newman_local[OF SN WCR_SN])
  from CR_on_same_NF[OF CR _
      aaecc_R1_nf_reaches[OF sep wf no_cp inner_SN free] normal]
  show ?thesis by simp
qed

lemma aaecc_R2_lhs_normal:
  assumes wf: "wf_trs R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and lr2: "(l,r) \<in> R2"
    and normal: "\<And>x. x \<in> vars_term l \<Longrightarrow> sigma x \<in> NF_trs R1"
  shows "l \<cdot> sigma \<in> NF_trs R1"
proof (rule ccontr)
  assume not_nf: "l \<cdot> sigma \<notin> NF_trs R1"
  from not_nf obtain u where step: "(l \<cdot> sigma,u) \<in> rstep R1"
    unfolding NF_iff_no_step by blast
  from step obtain C l1 r1 tau where lr1: "(l1,r1) \<in> R1"
    and source: "l \<cdot> sigma = C\<langle>l1 \<cdot> tau\<rangle>" by auto
  have sup: "l \<cdot> sigma \<unrhd> l1 \<cdot> tau"
    unfolding source by auto
  from supteq_subst_cases'[OF sup]
  show False
  proof
    assume "\<exists>x. x \<in> vars_term l \<and> sigma x \<unrhd> l1 \<cdot> tau"
    then obtain x where x: "x \<in> vars_term l"
      and sub: "sigma x \<unrhd> l1 \<cdot> tau" by auto
    have sigma_nf: "sigma x \<in> NF_trs R1" by (rule normal[OF x])
    have redex: "(l1 \<cdot> tau,r1 \<cdot> tau) \<in> rstep R1"
      using lr1 by auto
    have "l1 \<cdot> tau \<notin> NF_trs R1" using redex by auto
    moreover have "l1 \<cdot> tau \<in> NF_trs R1"
      by (rule NF_subterm[OF sigma_nf sub])
    ultimately show False by simp
  next
    assume "\<exists>w \<unlhd> l. is_Fun w \<and> l1 \<cdot> tau = w \<cdot> sigma"
    then obtain w where sub: "w \<unlhd> l" and isfun: "is_Fun w"
      and inst: "w \<cdot> sigma = l1 \<cdot> tau" by auto
    from sub obtain D where l: "l = D\<langle>w\<rangle>" by auto
    from critical_pairs_exI[OF lr2 lr1 l isfun inst refl, of ren]
      no_cross_cp show False by auto
  qed
qed

lemma aaecc_subst_image_signature_free:
  assumes free: "funas_term (t \<cdot> sigma) \<inter> F = {}"
    and x: "x \<in> vars_term t"
  shows "funas_term (sigma x) \<inter> F = {}"
  using free x unfolding funas_term_subst by blast

lemma aaecc_subst_image_signature_free_below_root:
  assumes fun_t: "is_Fun t"
    and free: "funas_args_term (t \<cdot> sigma) \<inter> F = {}"
    and x: "x \<in> vars_term t"
  shows "funas_term (sigma x) \<inter> F = {}"
proof -
  from fun_t obtain f ts where t: "t = Fun f ts" by auto
  from x obtain u where u: "u \<in> set ts" "x \<in> vars_term u"
    unfolding t by auto
  have "funas_term (u \<cdot> sigma) \<inter> F = {}"
    using free u unfolding t funas_args_term_def by auto
  from aaecc_subst_image_signature_free[OF this u(2)] show ?thesis .
qed

lemma aaecc_R1_nf_subst_reaches:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term (t \<cdot> sigma) \<inter> F = {}"
    and x: "x \<in> vars_term t"
  shows "(sigma x, aaecc_R1_nf_subst R1 sigma x) \<in> (rstep R1)\<^sup>!"
  unfolding aaecc_R1_nf_subst_def
  by (rule aaecc_R1_nf_reaches[OF sep wf no_cp inner_SN
        aaecc_subst_image_signature_free[OF free x]])

lemma aaecc_R1_nf_subst_signature_free:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term (t \<cdot> sigma) \<inter> F = {}"
    and x: "x \<in> vars_term t"
  shows "funas_term (aaecc_R1_nf_subst R1 sigma x) \<inter> F = {}"
proof -
  have x_free: "funas_term (sigma x) \<inter> F = {}"
    by (rule aaecc_subst_image_signature_free[OF free x])
  from aaecc_R1_nf_subst_reaches[OF sep wf no_cp inner_SN free x]
  have steps: "(sigma x, aaecc_R1_nf_subst R1 sigma x)
      \<in> (rstep R1)\<^sup>*" by auto
  from aaecc_signature_free_R1_steps[OF sep wf x_free steps]
  show ?thesis .
qed

lemma aaecc_R1_nf_subst_signature_free_below_root:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and fun_t: "is_Fun t"
    and args_free: "funas_args_term (t \<cdot> sigma) \<inter> F = {}"
    and x: "x \<in> vars_term t"
  shows "funas_term (aaecc_R1_nf_subst R1 sigma x) \<inter> F = {}"
proof -
  have x_free: "funas_term (sigma x) \<inter> F = {}"
    by (rule aaecc_subst_image_signature_free_below_root[
        OF fun_t args_free x])
  from aaecc_R1_nf_reaches[OF sep wf no_cp inner_SN x_free]
  have steps: "(sigma x, aaecc_R1_nf_subst R1 sigma x)
      \<in> (rstep R1)\<^sup>*" unfolding aaecc_R1_nf_subst_def by auto
  from aaecc_signature_free_R1_steps[OF sep wf x_free steps]
  show ?thesis .
qed

lemma aaecc_term_nf_subst_reaches:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and free: "funas_term (t \<cdot> sigma) \<inter> F = {}"
  shows "(t \<cdot> sigma, t \<cdot> aaecc_R1_nf_subst R1 sigma)
      \<in> (rstep R1)\<^sup>*"
proof (rule term_subst_rsteps)
  fix x
  assume x: "x \<in> vars_term t"
  from aaecc_R1_nf_subst_reaches[OF sep wf no_cp inner_SN free x]
  show "(sigma x, aaecc_R1_nf_subst R1 sigma x) \<in> (rstep R1)\<^sup>*"
    by auto
qed

lemma aaecc_term_nf_subst_reaches_below_root:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and fun_t: "is_Fun t"
    and args_free: "funas_args_term (t \<cdot> sigma) \<inter> F = {}"
  shows "(t \<cdot> sigma, t \<cdot> aaecc_R1_nf_subst R1 sigma)
      \<in> (rstep R1)\<^sup>*"
proof (rule term_subst_rsteps)
  fix x
  assume x: "x \<in> vars_term t"
  have x_free: "funas_term (sigma x) \<inter> F = {}"
    by (rule aaecc_subst_image_signature_free_below_root[
        OF fun_t args_free x])
  from aaecc_R1_nf_reaches[OF sep wf no_cp inner_SN x_free]
  show "(sigma x, aaecc_R1_nf_subst R1 sigma x) \<in> (rstep R1)\<^sup>*"
    unfolding aaecc_R1_nf_subst_def by auto
qed

lemma aaecc_nf_subst_args_free:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and fun_t: "is_Fun t"
    and static_free: "funas_args_term t \<inter> F = {}"
    and args_free: "funas_args_term (t \<cdot> sigma) \<inter> F = {}"
  shows "funas_args_term (t \<cdot> aaecc_R1_nf_subst R1 sigma) \<inter> F = {}"
proof -
  from fun_t obtain f ts where t: "t = Fun f ts" by auto
  have image_free:
      "funas_term (aaecc_R1_nf_subst R1 sigma x) \<inter> F = {}"
    if x: "x \<in> vars_term t" for x
    by (rule aaecc_R1_nf_subst_signature_free_below_root[
        OF sep wf no_cp inner_SN fun_t args_free x])
  have term_free:
      "funas_term (u \<cdot> aaecc_R1_nf_subst R1 sigma) \<inter> F = {}"
    if u: "u \<in> set ts" for u
  proof -
    have static_u: "funas_term u \<inter> F = {}"
      using static_free u unfolding t funas_args_term_def by auto
    have image_u:
        "funas_term (aaecc_R1_nf_subst R1 sigma x) \<inter> F = {}"
      if x: "x \<in> vars_term u" for x
    proof (rule image_free)
      from u x show "x \<in> vars_term t" unfolding t by auto
    qed
    show ?thesis unfolding funas_term_subst
      using static_u image_u by auto
  qed
  show ?thesis unfolding t funas_args_term_def
    using term_free by auto
qed

lemma aaecc_R2_lhs_nf:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and lr2: "(l,r) \<in> R2"
    and args_free: "funas_args_term (l \<cdot> sigma) \<inter> F = {}"
  shows "l \<cdot> aaecc_R1_nf_subst R1 sigma \<in> NF_trs R1"
proof (rule aaecc_R2_lhs_normal[OF wf no_cross_cp lr2])
  fix x
  assume x: "x \<in> vars_term l"
  from aaecc_signature_separated_R2(2)[OF sep lr2]
  have fun_l: "is_Fun l" by (cases l) auto
  have x_free: "funas_term (sigma x) \<inter> F = {}"
    by (rule aaecc_subst_image_signature_free_below_root[
        OF fun_l args_free x])
  from aaecc_R1_nf_reaches[OF sep wf no_cp inner_SN x_free]
  show "aaecc_R1_nf_subst R1 sigma x \<in> NF_trs R1"
    unfolding aaecc_R1_nf_subst_def normalizability_def by auto
qed

lemma aaecc_R2_nf_subst_args_free:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and lr2: "(l,r) \<in> R2"
    and args_free: "funas_args_term (l \<cdot> sigma) \<inter> F = {}"
  shows "funas_args_term (l \<cdot> aaecc_R1_nf_subst R1 sigma) \<inter> F = {}"
proof -
  from aaecc_signature_separated_R2(2)[OF sep lr2]
  obtain f ts where l: "l = Fun f ts" by (cases l) auto
  have static_free: "funas_args_term l \<inter> F = {}"
    by (rule aaecc_signature_separated_R2(4)[OF sep lr2])
  show ?thesis by (rule aaecc_nf_subst_args_free[
        OF sep wf no_cp inner_SN _ static_free args_free], use l in auto)
qed

lemma aaecc_R2_nf_subst_innermost_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and lr2: "(l,r) \<in> R2"
    and args_free: "funas_args_term (l \<cdot> sigma) \<inter> F = {}"
  shows "(l \<cdot> aaecc_R1_nf_subst R1 sigma,
      r \<cdot> aaecc_R1_nf_subst R1 sigma)
      \<in> inn_rstep (R1 \<union> R2)"
proof -
  have lhs_nf: "l \<cdot> aaecc_R1_nf_subst R1 sigma \<in> NF_trs R1"
    by (rule aaecc_R2_lhs_nf[OF sep wf no_cp no_cross_cp inner_SN
        lr2 args_free])
  have normalized_args_free:
      "funas_args_term (l \<cdot> aaecc_R1_nf_subst R1 sigma) \<inter> F = {}"
    by (rule aaecc_R2_nf_subst_args_free[
        OF sep wf no_cp inner_SN lr2 args_free])
  have args_nf: "set (args (l \<cdot> aaecc_R1_nf_subst R1 sigma))
      \<subseteq> NF_trs (R1 \<union> R2)"
  proof
    fix u
    assume u: "u \<in> set (args (l \<cdot> aaecc_R1_nf_subst R1 sigma))"
    from aaecc_signature_separated_R2(2)[OF sep lr2]
    have fun_l: "is_Fun l" by (cases l) auto
    have sub: "l \<cdot> aaecc_R1_nf_subst R1 sigma \<rhd> u"
      by (metis u fun_l is_Fun_Fun_conv subst_apply_eq_Var supt.arg
          term.distinct(1) term.exhaust_sel)
    have u_nf_R1: "u \<in> NF_trs R1"
      by (rule NF_subterm[OF lhs_nf]) (use sub in auto)
    have u_free: "funas_term u \<inter> F = {}"
      using normalized_args_free u unfolding funas_args_term_def by auto
    from aaecc_signature_free_NF_union[OF sep u_free] u_nf_R1
    show "u \<in> NF_trs (R1 \<union> R2)" by simp
  qed
  have "(Hole\<langle>l \<cdot> aaecc_R1_nf_subst R1 sigma\<rangle>,
      Hole\<langle>r \<cdot> aaecc_R1_nf_subst R1 sigma\<rangle>)
      \<in> inn_rstep (R1 \<union> R2)"
    by (rule inn_rstep[OF UnI2[OF lr2] args_nf])
  then show ?thesis by simp
qed

lemma aaecc_signature_rooted_R1_termination:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and root: "root t \<in> Some ` F"
    and args_free: "funas_args_term t \<inter> F = {}"
  shows "SN_on (rstep R1) {t}"
proof -
  from root obtain f ts where t: "t = Fun f ts" and f: "(f,length ts) \<in> F"
    by (cases t) auto
  have arg_SN: "SN_on (rstep R1) {u}" if u: "u \<in> set ts" for u
  proof (rule aaecc_signature_free_R1_termination[OF sep wf no_cp inner_SN])
    show "funas_term u \<inter> F = {}"
      using args_free u unfolding t funas_args_term_def by auto
  qed
  have nvar: "\<forall>(l,r)\<in>R1. is_Fun l"
    using wf unfolding wf_trs_def by auto
  have ndef: "\<not> defined R1 (f,length ts)"
  proof
    assume "defined R1 (f,length ts)"
    then obtain l r where lr: "(l,r) \<in> R1" and rt: "root l = Some (f,length ts)"
      unfolding defined_def by auto
    from rt have "(f,length ts) \<in> funas_term l"
      unfolding funas_term_conv by auto
    with aaecc_signature_separated_R1(1)[OF sep lr] f show False by auto
  qed
  show ?thesis unfolding t
    by (rule SN_args_imp_SN_rstep[OF arg_SN nvar ndef])
qed

lemma aaecc_signature_rooted_R1_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and root: "root s \<in> Some ` F"
    and args_free: "funas_args_term s \<inter> F = {}"
    and step: "(s,t) \<in> rstep R1"
  shows "root t = root s"
    "funas_args_term t \<inter> F = {}"
proof -
  from root obtain f ss where s: "s = Fun f ss" and f: "(f,length ss) \<in> F"
    by (cases s) auto
  from step obtain C l r sigma where lr: "(l,r) \<in> R1"
    and src: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and tgt: "t = C\<langle>r \<cdot> sigma\<rangle>" by auto
  have C: "C \<noteq> Hole"
  proof
    assume "C = Hole"
    with src s have eq: "Fun f ss = l \<cdot> sigma" by auto
    from wf lr have fun_l: "is_Fun l" unfolding wf_trs_def by auto
    from eq fun_l have "(f,length ss) \<in> funas_term l"
      by (cases l) auto
    with f aaecc_signature_separated_R1(1)[OF sep lr] show False by auto
  qed
  show root_eq: "root t = root s"
    unfolding src tgt by (cases C) (use C in auto)
  from aaecc_R1_step_no_new_signature[OF sep wf step]
  have subset: "funas_term t \<inter> F \<subseteq> {(f,length ss)}"
    using args_free unfolding s funas_args_term_def by auto
  from root_eq s obtain ts where t: "t = Fun f ts"
    by (cases t) auto
  have nr: "(s,t) \<in> nrrstep R1"
    unfolding src tgt by (rule nrrstepI[OF lr _ _ C]) auto
  from nr[unfolded s t nrrstep_iff_arg_rstep]
  obtain i u where i: "i < length ss" and ts: "ts = ss[i:=u]"
    and arg_step: "(ss ! i,u) \<in> rstep R1" by auto
  have old_free: "funas_term (ss ! j) \<inter> F = {}"
    if j: "j < length ss" for j
  proof -
    have sub: "funas_term (ss ! j) \<subseteq>
        \<Union>(funas_term ` set ss)"
      using nth_mem[OF j] by auto
    from args_free sub show ?thesis
      unfolding s funas_args_term_def by auto
  qed
  have new_free: "funas_term u \<inter> F = {}"
    by (rule aaecc_signature_free_R1_step[
        OF sep wf old_free[OF i] arg_step])
  have old_mem_free: "funas_term x \<inter> F = {}"
    if x: "x \<in> set ss" for x
  proof -
    from x obtain j where j: "j < length ss" and xeq: "x = ss ! j"
      unfolding in_set_conv_nth by auto
    show ?thesis unfolding xeq by (rule old_free[OF j])
  qed
  have updated: "set (ss[i:=u]) \<subseteq> insert u (set ss)"
    by (rule set_update_subset_insert)
  show "funas_args_term t \<inter> F = {}"
    unfolding t ts funas_args_term_def
    using updated old_mem_free new_free by auto
qed

lemma aaecc_signature_rooted_inn_R1_step:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and root: "root s \<in> Some ` F"
    and args_free: "funas_args_term s \<inter> F = {}"
    and step: "(s,t) \<in> inn_rstep R1"
  shows "(s,t) \<in> inn_rstep (R1 \<union> R2)"
    "root t = root s"
    "funas_args_term t \<inter> F = {}"
proof -
  from step obtain l r sigma C where lr: "(l,r) \<in> R1"
    and args_nf: "set (args (l \<cdot> sigma)) \<subseteq> NF_trs R1"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>"
    by (cases rule: inn_rstep.cases) auto
  have args_nf_union:
      "set (args (l \<cdot> sigma)) \<subseteq> NF_trs (R1 \<union> R2)"
  proof
    fix u
    assume u: "u \<in> set (args (l \<cdot> sigma))"
    from u obtain f ts where inst: "l \<cdot> sigma = Fun f ts"
      by (cases "l \<cdot> sigma") auto
    from u have uts: "u \<in> set ts" unfolding inst by simp
    have inner: "l \<cdot> sigma \<rhd> u"
      unfolding inst by (rule supt.arg[OF uts])
    have outer: "s \<unrhd> l \<cdot> sigma"
      unfolding s by (rule ctxt_supteq) simp
    have sub: "s \<rhd> u"
      by (rule supteq_supt_trans[OF outer inner])
    have u_free: "funas_term u \<inter> F = {}"
    proof -
      from root obtain f ss where sf: "s = Fun f ss" by (cases s) auto
      from supt_imp_subt_at_nepos[OF sub]
      obtain i p where pos: "i # p \<in> poss s" and at: "s |_ (i # p) = u"
        by blast
      from args_poss[OF pos] obtain g ts where shape: "s = Fun g ts"
        and p: "p \<in> poss (ts ! i)" and i: "i < length ts" .
      from sf shape have ts: "ts = ss" by auto
      have below: "ts ! i \<unrhd> ts ! i |_ p"
        by (rule subt_at_imp_supteq[OF p])
      have at': "ts ! i |_ p = u" using at shape by simp
      from below at' have below': "ts ! i \<unrhd> u" by simp
      from i below' have ii: "i < length ss" and below_ss: "ss ! i \<unrhd> u"
        unfolding ts by auto
      have arg_free: "funas_term (ss ! i) \<inter> F = {}"
      proof -
        have mem: "funas_term (ss ! i) \<subseteq>
            \<Union>(funas_term ` set ss)" using nth_mem[OF ii] by auto
        from args_free mem show ?thesis
          unfolding sf funas_args_term_def by auto
      qed
      from supteq_imp_funas_term_subset[OF below_ss] arg_free
      show ?thesis by auto
    qed
    from args_nf u aaecc_signature_free_NF_union[OF sep u_free]
    show "u \<in> NF_trs (R1 \<union> R2)" by blast
  qed
  show "(s,t) \<in> inn_rstep (R1 \<union> R2)"
    unfolding s t by (rule inn_rstep[OF UnI1[OF lr] args_nf_union])
  from step[THEN set_mp[OF inn_rstep_rstep]]
  show "root t = root s"
    "funas_args_term t \<inter> F = {}"
    by (rule aaecc_signature_rooted_R1_step[OF sep wf root args_free])+
qed

lemma aaecc_signature_rooted_inn_R1_steps:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and root: "root s \<in> Some ` F"
    and args_free: "funas_args_term s \<inter> F = {}"
    and steps: "(s,t) \<in> (inn_rstep R1)\<^sup>*"
  shows "(s,t) \<in> (inn_rstep (R1 \<union> R2))\<^sup>*"
    "root t = root s"
    "funas_args_term t \<inter> F = {}"
proof -
  have all: "(s,t) \<in> (inn_rstep (R1 \<union> R2))\<^sup>* \<and>
      root t = root s \<and> funas_args_term t \<inter> F = {}"
    using steps root args_free
  proof (induct rule: rtrancl_induct)
    case base
    show ?case using base.prems by simp
  next
    case (step y z)
    have IH: "(s,y) \<in> (inn_rstep (R1 \<union> R2))\<^sup>* \<and>
        root y = root s \<and> funas_args_term y \<inter> F = {}"
      by (rule step.hyps(3)[OF step.prems])
    from IH step.prems have y_root: "root y \<in> Some ` F"
      and y_free: "funas_args_term y \<inter> F = {}" by auto
    from aaecc_signature_rooted_inn_R1_step[
        OF sep wf y_root y_free step.hyps(2)] IH
    show ?case by auto
  qed
  then show "(s,t) \<in> (inn_rstep (R1 \<union> R2))\<^sup>*"
    "root t = root s"
    "funas_args_term t \<inter> F = {}" by auto
qed

lemma aaecc_R1_nf_inn_reaches_rooted:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and root: "root s \<in> Some ` F"
    and args_free: "funas_args_term s \<inter> F = {}"
  shows "(s, aaecc_R1_nf R1 s) \<in> (inn_rstep (R1 \<union> R2))\<^sup>*"
proof -
  from aaecc_signature_rooted_R1_termination[
      OF sep wf no_cp inner_SN root args_free]
  have SN: "SN_on (inn_rstep R1) {s}"
    by (rule SN_on_subset1[OF _ inn_rstep_rstep])
  from SN_on_imp_normalizability[OF SN]
  obtain t where normal: "(s,t) \<in> (inn_rstep R1)\<^sup>!" by blast
  from normal have reach: "(s,t) \<in> (inn_rstep R1)\<^sup>*"
    and nf: "t \<in> NF (inn_rstep R1)"
    unfolding normalizability_def by auto
  have reach_r: "(s,t) \<in> (rstep R1)\<^sup>*"
    using reach rtrancl_mono[OF inn_rstep_rstep, of R1] by auto
  have nf_r: "t \<in> NF (rstep R1)"
    using nf by (simp add: NF_inn_rstep_rstep)
  have normal_r: "(s,t) \<in> (rstep R1)\<^sup>!"
    unfolding normalizability_def using reach_r nf_r by auto
  have WCR: "WCR (rstep R1)"
    using no_cp unfolding aaecc_R1_ok_def by blast
  have SN_r: "SN_on (rstep R1) {s}"
    by (rule aaecc_signature_rooted_R1_termination[
        OF sep wf no_cp inner_SN root args_free])
  have WCR_SN: "WCR_on (rstep R1) {x. SN_on (rstep R1) {x}}"
    using WCR unfolding WCR_on_def by auto
  have CR: "CR_on (rstep R1) {s}"
    by (rule Newman_local[OF SN_r WCR_SN])
  from SN_on_imp_normalizability[OF SN_r]
  have exists_nf: "\<exists>u. (s,u) \<in> (rstep R1)\<^sup>!" .
  from someI_ex[OF exists_nf]
  have chosen_nf: "(s,aaecc_R1_nf R1 s) \<in> (rstep R1)\<^sup>!"
    unfolding aaecc_R1_nf_def .
  from CR_on_same_NF[OF CR _
      chosen_nf normal_r]
  have nf: "aaecc_R1_nf R1 s = t" by simp
  from aaecc_signature_rooted_inn_R1_steps[
      OF sep wf root args_free reach]
  show ?thesis unfolding nf by auto
qed

lemma aaecc_R1_nf_reaches_rooted:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and root: "root t \<in> Some ` F"
    and args_free: "funas_args_term t \<inter> F = {}"
  shows "(t, aaecc_R1_nf R1 t) \<in> (rstep R1)\<^sup>!"
proof -
  from aaecc_signature_rooted_R1_termination[OF assms]
  have "\<exists>u. (t,u) \<in> (rstep R1)\<^sup>!"
    by (rule SN_on_imp_normalizability)
  from someI_ex[OF this]
  show ?thesis unfolding aaecc_R1_nf_def .
qed

lemma aaecc_R1_nf_unique_rooted:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R1"
    and no_cp: "aaecc_R1_ok ren R1"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and root: "root s \<in> Some ` F"
    and args_free: "funas_args_term s \<inter> F = {}"
    and normal: "(s,t) \<in> (rstep R1)\<^sup>!"
  shows "aaecc_R1_nf R1 s = t"
proof -
  have WCR: "WCR (rstep R1)"
    using no_cp unfolding aaecc_R1_ok_def by blast
  from aaecc_signature_rooted_R1_termination[
      OF sep wf no_cp inner_SN root args_free]
  have SN: "SN_on (rstep R1) {s}" .
  have WCR_SN: "WCR_on (rstep R1) {x. SN_on (rstep R1) {x}}"
    using WCR unfolding WCR_on_def by auto
  have CR: "CR_on (rstep R1) {s}"
    by (rule Newman_local[OF SN WCR_SN])
  from CR_on_same_NF[OF CR _
      aaecc_R1_nf_reaches_rooted[
        OF sep wf no_cp inner_SN root args_free] normal]
  show ?thesis by simp
qed

lemma aaecc_R2_rhs_instance_args_free:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs R2"
    and lr2: "(l,r) \<in> R2"
    and lhs_free: "funas_args_term (l \<cdot> sigma) \<inter> F = {}"
  shows "funas_args_term (r \<cdot> sigma) \<inter> F = {}"
proof -
  from aaecc_signature_separated_R2(1)[OF sep lr2]
  obtain f rs where r: "r = Fun f rs" by (cases r) auto
  from aaecc_signature_separated_R2(2)[OF sep lr2]
  have fun_l: "is_Fun l" by (cases l) auto
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf lr2 unfolding wf_trs_def by auto
  have image_free: "funas_term (sigma x) \<inter> F = {}"
    if x: "x \<in> vars_term r" for x
    by (rule aaecc_subst_image_signature_free_below_root[
        OF fun_l lhs_free], use vars x in auto)
  have term_free: "funas_term (u \<cdot> sigma) \<inter> F = {}"
    if u: "u \<in> set rs" for u
  proof -
    have static_u: "funas_term u \<inter> F = {}"
      using aaecc_signature_separated_R2(5)[OF sep lr2] u
      unfolding r funas_args_term_def by auto
    have image_u: "funas_term (sigma x) \<inter> F = {}"
      if x: "x \<in> vars_term u" for x
    proof (rule image_free)
      from u x show "x \<in> vars_term r" unfolding r by auto
    qed
    show ?thesis unfolding funas_term_subst
      using static_u image_u by auto
  qed
  from aaecc_signature_separated_R2(5)[OF sep lr2]
  show ?thesis unfolding r funas_args_term_def
    using term_free by auto
qed

lemma aaecc_R2_normalized_connection:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf1: "wf_trs R1"
    and wf2: "wf_trs R2"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and lr2: "(l,r) \<in> R2"
    and lr2': "(l',r') \<in> R2"
    and lhs_free: "funas_args_term (l \<cdot> sigma) \<inter> F = {}"
    and connection: "(r \<cdot> sigma, l' \<cdot> tau) \<in> (rstep R1)\<^sup>*"
    and lhs_free': "funas_args_term (l' \<cdot> tau) \<inter> F = {}"
  shows "aaecc_R1_nf R1 (r \<cdot> aaecc_R1_nf_subst R1 sigma) =
    l' \<cdot> aaecc_R1_nf_subst R1 tau"
proof -
  have rhs_free: "funas_args_term (r \<cdot> sigma) \<inter> F = {}"
    by (rule aaecc_R2_rhs_instance_args_free[OF sep wf2 lr2 lhs_free])
  have rhs_nfsubst_free:
      "funas_args_term (r \<cdot> aaecc_R1_nf_subst R1 sigma) \<inter> F = {}"
  proof -
    from aaecc_signature_separated_R2(1)[OF sep lr2]
    have fun_r: "is_Fun r" .
    from aaecc_signature_separated_R2(5)[OF sep lr2]
    have static_free: "funas_args_term r \<inter> F = {}" .
    show ?thesis by (rule aaecc_nf_subst_args_free[
        OF sep wf1 no_cp inner_SN fun_r static_free rhs_free])
  qed
  have rhs_root: "root (r \<cdot> aaecc_R1_nf_subst R1 sigma) \<in> Some ` F"
    using aaecc_signature_separated_R2(3)[OF sep lr2]
    by (cases r) auto
  have rhs_sigma_to_nfsubst:
      "(r \<cdot> sigma, r \<cdot> aaecc_R1_nf_subst R1 sigma)
        \<in> (rstep R1)\<^sup>*"
    by (rule aaecc_term_nf_subst_reaches_below_root[
        OF sep wf1 no_cp inner_SN
          aaecc_signature_separated_R2(1)[OF sep lr2] rhs_free])
  have rhs_to_nf:
      "(r \<cdot> aaecc_R1_nf_subst R1 sigma,
        aaecc_R1_nf R1 (r \<cdot> aaecc_R1_nf_subst R1 sigma))
        \<in> (rstep R1)\<^sup>!"
    by (rule aaecc_R1_nf_reaches_rooted[
        OF sep wf1 no_cp inner_SN rhs_root rhs_nfsubst_free])
  have lhs_tau_to_nfsubst:
      "(l' \<cdot> tau, l' \<cdot> aaecc_R1_nf_subst R1 tau)
        \<in> (rstep R1)\<^sup>*"
    by (rule aaecc_term_nf_subst_reaches_below_root[
        OF sep wf1 no_cp inner_SN _ lhs_free'],
        use aaecc_signature_separated_R2(2)[OF sep lr2'] in auto)
  have lhs_nf: "l' \<cdot> aaecc_R1_nf_subst R1 tau \<in> NF_trs R1"
    by (rule aaecc_R2_lhs_nf[
        OF sep wf1 no_cp no_cross_cp inner_SN lr2' lhs_free'])
  have original_to_lhs_nf:
      "(r \<cdot> sigma, l' \<cdot> aaecc_R1_nf_subst R1 tau)
        \<in> (rstep R1)\<^sup>!"
    using connection lhs_tau_to_nfsubst lhs_nf by auto
  have original_to_rhs_nf:
      "(r \<cdot> sigma,
        aaecc_R1_nf R1 (r \<cdot> aaecc_R1_nf_subst R1 sigma))
        \<in> (rstep R1)\<^sup>!"
    using rhs_sigma_to_nfsubst rhs_to_nf by auto
  have WCR: "WCR (rstep R1)"
    using no_cp unfolding aaecc_R1_ok_def by blast
  from aaecc_signature_rooted_R1_termination[
      OF sep wf1 no_cp inner_SN _ rhs_free]
  have SN: "SN_on (rstep R1) {r \<cdot> sigma}"
    using aaecc_signature_separated_R2(3)[OF sep lr2]
    by (cases r) auto
  have WCR_SN: "WCR_on (rstep R1) {x. SN_on (rstep R1) {x}}"
    using WCR unfolding WCR_on_def by auto
  have CR: "CR_on (rstep R1) {r \<cdot> sigma}"
    by (rule Newman_local[OF SN WCR_SN])
  from CR_on_same_NF[OF CR _ original_to_rhs_nf original_to_lhs_nf]
  show ?thesis by simp
qed

theorem aaecc_no_infinite_R2_root_chain:
  fixes l r :: "nat \<Rightarrow> ('f,'v) term"
    and sigma :: "nat \<Rightarrow> ('f,'v) subst"
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf1: "wf_trs R1"
    and wf2: "wf_trs R2"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
    and rules: "\<And>n. (l n,r n) \<in> R2"
    and lhs_free: "\<And>n. funas_args_term (l n \<cdot> sigma n) \<inter> F = {}"
    and connection: "\<And>n. (r n \<cdot> sigma n,
      l (Suc n) \<cdot> sigma (Suc n)) \<in> (rstep R1)\<^sup>*"
  shows False
proof -
  let ?A = "inn_rstep (R1 \<union> R2)"
  let ?W = "\<lambda>n. l n \<cdot> aaecc_R1_nf_subst R1 (sigma n)"
  let ?V = "\<lambda>n. r n \<cdot> aaecc_R1_nf_subst R1 (sigma n)"
  have root_step: "(?W n, ?V n) \<in> ?A" for n
    by (rule aaecc_R2_nf_subst_innermost_step[
        OF sep wf1 no_cp no_cross_cp inner_SN rules lhs_free])
  have rhs_free: "funas_args_term (r n \<cdot> sigma n) \<inter> F = {}" for n
    by (rule aaecc_R2_rhs_instance_args_free[
        OF sep wf2 rules lhs_free])
  have V_free: "funas_args_term (?V n) \<inter> F = {}" for n
  proof -
    from aaecc_signature_separated_R2(1)[OF sep rules[of n]]
    have fun_r: "is_Fun (r n)" .
    from aaecc_signature_separated_R2(5)[OF sep rules[of n]]
    have static_free: "funas_args_term (r n) \<inter> F = {}" .
    show ?thesis by (rule aaecc_nf_subst_args_free[
        OF sep wf1 no_cp inner_SN fun_r static_free rhs_free])
  qed
  have V_root: "root (?V n) \<in> Some ` F" for n
    using aaecc_signature_separated_R2(3)[OF sep rules[of n]]
    by (cases "r n") auto
  have normalized_connection:
      "aaecc_R1_nf R1 (?V n) = ?W (Suc n)" for n
    by (rule aaecc_R2_normalized_connection[
        OF sep wf1 wf2 no_cp no_cross_cp inner_SN
          rules[of n] rules[of "Suc n"] lhs_free[of n]
          connection[of n] lhs_free[of "Suc n"]])
  have tail_steps: "(?V n, ?W (Suc n)) \<in> ?A\<^sup>*" for n
    using aaecc_R1_nf_inn_reaches_rooted[
        OF sep wf1 no_cp inner_SN V_root V_free, of n]
    unfolding normalized_connection[of n] .
  have positive: "(?W n, ?W (Suc n)) \<in> ?A\<^sup>+" for n
    using root_step[of n] tail_steps[of n] by auto
  from inner_SN have SN_positive: "SN (?A\<^sup>+)"
    by (rule SN_imp_SN_trancl)
  have chain_positive: "chain (?A\<^sup>+) ?W"
    unfolding chain_def using positive by simp
  have not_local: "\<not> SN_on (?A\<^sup>+) {?W 0}"
    by (rule chain_imp_not_SN_on[OF chain_positive])
  have local_SN: "SN_on (?A\<^sup>+) {?W 0}"
    by (rule SN_on_subset2[OF _ SN_positive]) auto
  from not_local local_SN show False by contradiction
qed

lemma aaecc_root_in_signature_preserved:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and step: "(s,t) \<in> rstep (R1 \<union> R2)"
    and rooted: "root s \<in> Some ` F"
  shows "root t \<in> Some ` F"
proof -
  from step obtain C l r sigma where lr: "(l,r) \<in> R1 \<union> R2"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>"
    by (cases rule: rstep.cases) auto
  show ?thesis
  proof (cases C)
    case Hole
    show ?thesis
    proof (cases "(l,r) \<in> R1")
      case True
      have lrU: "(l,r) \<in> R1 \<union> R2" using True by auto
      from wf lrU obtain fl ls where lfun: "l = Fun fl ls"
        unfolding wf_trs_def by blast
      from aaecc_signature_separated_R1(1)[OF sep True]
      have "root (l \<cdot> sigma) \<notin> Some ` F"
        unfolding lfun by auto
      with rooted have contra: False unfolding s Hole by simp
      from contra show ?thesis by blast
    next
      case False
      with lr have lr2: "(l,r) \<in> R2" by auto
      from aaecc_signature_separated_R2(3)[OF sep lr2]
      show ?thesis unfolding t Hole by (cases r) auto
    qed
  next
    case (More f bef D aft)
    with rooted show ?thesis unfolding s t by simp
  qed
qed

lemma aaecc_step_clean_below:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and step: "(s,t) \<in> rstep (R1 \<union> R2)"
  shows "(aaecc_clean_below F s,
      aaecc_clean_below F t) \<in> rstep R1 \<union> rrstep R2 \<or>
    (aaecc_clean_below F s =
      aaecc_clean_below F t \<and>
      (\<exists>xs a b ys.
        aliens_below (- F) s = xs @ a # ys \<and>
        aliens_below (- F) t = xs @ b # ys \<and>
        (a,b) \<in> rstep (R1 \<union> R2))) \<or>
    (root s \<notin> Some ` F \<and> root t \<in> Some ` F)"
proof (cases "(s,t) \<in> rrstep (R1 \<union> R2)")
  case True
  then obtain l r sigma where lr: "(l,r) \<in> R1 \<union> R2"
    and s: "s = l \<cdot> sigma" and t: "t = r \<cdot> sigma"
    by (rule rrstepE)
  show ?thesis
  proof (cases "(l,r) \<in> R1")
    case lr1: True
    have static: "funas_term l \<subseteq> - F"
      "funas_term r \<subseteq> - F"
      using aaecc_signature_separated_R1[OF sep lr1]
      by auto
    have lrU: "(l,r) \<in> R1 \<union> R2" using lr1 by auto
    from wf lrU obtain fl ls where lfun: "l = Fun fl ls"
      unfolding wf_trs_def by blast
    have isfun_l: "is_Fun l" unfolding lfun by simp
    from isfun_l obtain fl ls where l: "l = Fun fl ls" by (cases l) auto
    have source_unrooted: "root (l \<cdot> sigma) \<notin> Some ` F"
      using static(1) unfolding l by auto
    show ?thesis
    proof (cases "root (r \<cdot> sigma) \<in> Some ` F")
      case True
      with source_unrooted show ?thesis unfolding s t by auto
    next
      case False
      have cleaned:
          "aaecc_clean_below F (l \<cdot> sigma) =
            l \<cdot> aaecc_inn_clean_subst F sigma"
          "aaecc_clean_below F (r \<cdot> sigma) =
            r \<cdot> aaecc_inn_clean_subst F sigma"
        by (rule aaecc_clean_subst_apply_term_below_unrooted[
              OF static(1) source_unrooted],
            rule aaecc_clean_subst_apply_term_below_unrooted[
              OF static(2) False])
      have "(l \<cdot> aaecc_inn_clean_subst F sigma,
          r \<cdot> aaecc_inn_clean_subst F sigma) \<in> rstep R1"
        by (rule rstep.rstep[of l r R1 _ Hole], use lr1 in auto)
      then show ?thesis unfolding s t cleaned by auto
    qed
  next
    case False
    with lr have lr2: "(l,r) \<in> R2" by auto
    have static: "funas_args_term l \<subseteq> - F"
      "funas_args_term r \<subseteq> - F"
      using sep lr2 unfolding aaecc_signature_separated_def by auto
    have cleaned:
        "aaecc_clean_below F (l \<cdot> sigma) =
          l \<cdot> aaecc_inn_clean_subst F sigma"
        "aaecc_clean_below F (r \<cdot> sigma) =
          r \<cdot> aaecc_inn_clean_subst F sigma"
    proof -
      from aaecc_signature_separated_R2(2)[OF sep lr2]
      have lf: "is_Fun l" by (cases l) auto
      from aaecc_signature_separated_R2(1)[OF sep lr2]
      have rf: "is_Fun r" .
      show "aaecc_clean_below F (l \<cdot> sigma) =
          l \<cdot> aaecc_inn_clean_subst F sigma"
        by (rule aaecc_clean_subst_apply_term_below[OF static(1) lf])
      show "aaecc_clean_below F (r \<cdot> sigma) =
          r \<cdot> aaecc_inn_clean_subst F sigma"
        by (rule aaecc_clean_subst_apply_term_below[OF static(2) rf])
    qed
    have "(l \<cdot> aaecc_inn_clean_subst F sigma,
        r \<cdot> aaecc_inn_clean_subst F sigma) \<in> rrstep R2"
      by (rule rrstepI[OF lr2 refl refl])
    then show ?thesis unfolding s t cleaned by auto
  qed
next
  case False
  with step have nr: "(s,t) \<in> nrrstep (R1 \<union> R2)"
    unfolding rstep_iff_rrstep_or_nrrstep by auto
  from nr[unfolded nrrstep_iff_arg_rstep]
  obtain f ss i u where s: "s = Fun f ss" and i: "i < length ss"
    and t: "t = Fun f (ss[i := u])"
    and arg: "(ss ! i,u) \<in> rstep (R1 \<union> R2)" by auto
  show ?thesis
  proof (cases "(ss ! i,u) \<in> rstep R1")
    case arg1: True
    have FR1: "funas_trs R1 \<subseteq> - F"
      using sep unfolding aaecc_signature_separated_def by auto
    from aaecc_clean.rstep_sig_alien_nrrstep[OF arg1 FR1]
    show ?thesis
    proof
      assume cstep: "(aaecc_clean.clean_term F (ss ! i),
          aaecc_clean.clean_term F u) \<in> sig_step (- F) (rstep R1)"
      have clean_step:
          "(aaecc_clean_below F s,
            aaecc_clean_below F t) \<in> rstep R1"
      proof -
        have child: "(aaecc_inn_clean_term F (ss ! i),
            aaecc_inn_clean_term F u) \<in> rstep R1"
          using cstep unfolding sig_step_def aaecc_inn_clean_term_eq by auto
        have nr: "(Fun f (map (aaecc_inn_clean_term F) ss),
            Fun f ((map (aaecc_inn_clean_term F) ss)
              [i := aaecc_inn_clean_term F u])) \<in> nrrstep R1"
          unfolding nrrstep_iff_arg_rstep
          apply (rule exI[of _ f])
          apply (rule exI[of _ "map (aaecc_inn_clean_term F) ss"])
          apply (rule exI[of _ i])
          apply (rule exI[of _ "aaecc_inn_clean_term F u"])
          using i child by (simp add: nth_map)
        from nrrstep_imp_rstep[OF nr]
        show ?thesis unfolding s t by (simp add: map_update)
      qed
      then show ?thesis by auto
    next
      assume alien: "aaecc_clean.clean_term F (ss ! i) =
          aaecc_clean.clean_term F u \<and>
        (\<exists>xs a b ys. aliens (- F) (ss ! i) = xs @ a # ys \<and>
          aliens (- F) u = xs @ b # ys \<and> (a,b) \<in> nrrstep R1)"
      then obtain xs a b ys where clean:
          "aaecc_clean.clean_term F (ss ! i) = aaecc_clean.clean_term F u"
        and aa: "aliens (- F) (ss ! i) = xs @ a # ys"
        and bb: "aliens (- F) u = xs @ b # ys"
        and ab: "(a,b) \<in> nrrstep R1" by auto
      have clean_below: "aaecc_clean_below F s =
          aaecc_clean_below F t"
      proof -
        have child_eq: "aaecc_inn_clean_term F (ss ! i) =
            aaecc_inn_clean_term F u"
          using clean unfolding aaecc_inn_clean_term_eq .
        have mapped_nth: "aaecc_inn_clean_term F (ss ! i) =
            map (aaecc_inn_clean_term F) ss ! i"
          using i by simp
        show ?thesis unfolding s t
          apply (simp add: map_update)
          apply (subst child_eq[symmetric])
          apply (rule sym)
          apply (simp only: mapped_nth list_update_id)
          done
      qed
      have left: "aliens_below (- F) s =
          (concat (map (aliens (- F)) (take i ss)) @ xs) @ a #
          (ys @ concat (map (aliens (- F)) (drop (Suc i) ss)))"
        unfolding s aliens_below.simps
        by (rule aaecc_concat_map_nth_split[
            where xs=ss and i=i and f="aliens (- F)"
              and pre=xs and a=a and ys=ys, OF i aa])
      have right: "aliens_below (- F) t =
          (concat (map (aliens (- F)) (take i ss)) @ xs) @ b #
          (ys @ concat (map (aliens (- F)) (drop (Suc i) ss)))"
        using upd_conv_take_nth_drop[OF i, of u] bb
        unfolding t aliens_below.simps by (simp add: append_assoc)
      from nrrstep_imp_rstep[OF ab]
      have ab1: "(a,b) \<in> rstep R1" .
      from rstep_mono[of R1 "R1 \<union> R2"] ab1
      have "(a,b) \<in> rstep (R1 \<union> R2)" by auto
      with clean_below left right show ?thesis by blast
    qed
  next
    case False
    with arg have arg2: "(ss ! i,u) \<in> rstep R2" by auto
    from aaecc_R2_step_changes_one_alien[OF sep arg2]
    obtain xs a b ys where clean:
        "aaecc_clean.clean_term F (ss ! i) = aaecc_clean.clean_term F u"
      and aa: "aliens (- F) (ss ! i) = xs @ a # ys"
      and bb: "aliens (- F) u = xs @ b # ys"
      and ab: "(a,b) \<in> rstep R2" by blast
    have clean_below: "aaecc_clean_below F s =
        aaecc_clean_below F t"
    proof -
      from clean have eq: "aaecc_inn_clean_term F (ss ! i) =
          aaecc_inn_clean_term F u"
        unfolding aaecc_inn_clean_term_eq .
      show ?thesis unfolding s t
        by (rule aaecc_clean_below_update_eq[OF i eq])
    qed
    have left: "aliens_below (- F) s =
        (concat (map (aliens (- F)) (take i ss)) @ xs) @ a #
        (ys @ concat (map (aliens (- F)) (drop (Suc i) ss)))"
      unfolding s aliens_below.simps
      by (rule aaecc_concat_map_nth_split[
          where xs=ss and i=i and f="aliens (- F)"
            and pre=xs and a=a and ys=ys, OF i aa])
    have right: "aliens_below (- F) t =
        (concat (map (aliens (- F)) (take i ss)) @ xs) @ b #
        (ys @ concat (map (aliens (- F)) (drop (Suc i) ss)))"
      using upd_conv_take_nth_drop[OF i, of u] bb
      unfolding t aliens_below.simps by (simp add: append_assoc)
    from ab have "(a,b) \<in> rstep (R1 \<union> R2)" by auto
    with clean_below left right show ?thesis by blast
  qed
qed

lemma aaecc_step_preserves_alien_invariant:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and closed: "\<And>a b. a \<in> X \<Longrightarrow>
      (a,b) \<in> rstep (R1 \<union> R2) \<Longrightarrow> b \<in> X"
    and source: "set (aliens (- F) s) \<subseteq> X"
    and step: "(s,t) \<in> rstep (R1 \<union> R2)"
  shows "set (aliens (- F) t) \<subseteq> X"
proof -
  from step obtain C l r sigma where lr: "(l,r) \<in> R1 \<union> R2"
    and s: "s = C\<langle>l \<cdot> sigma\<rangle>"
    and t: "t = C\<langle>r \<cdot> sigma\<rangle>"
    by (cases rule: rstep.cases) auto
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf lr unfolding wf_trs_def by auto
  show ?thesis using source unfolding s t
  proof (induct C)
    case Hole
    show ?case
    proof (cases "(l,r) \<in> R1")
      case True
      have static: "funas_term l \<subseteq> - F" "funas_term r \<subseteq> - F"
        using aaecc_signature_separated_R1[OF sep True] by auto
      from Hole vars show ?thesis
        unfolding intp_actxt.simps aliens_subst[OF static(1)]
          aliens_subst[OF static(2)] by auto
    next
      case False
      with lr have lr2: "(l,r) \<in> R2" by auto
      from aaecc_signature_separated_R2(2)[OF sep lr2]
      obtain f ls where l: "l = Fun f ls" and f: "(f,length ls) \<in> F"
        by (cases l) auto
      from aaecc_signature_separated_R2(3)[OF sep lr2]
      obtain g rs where r: "r = Fun g rs" and g: "(g,length rs) \<in> F"
        by (cases r) auto
      have al: "aliens (- F) (l \<cdot> sigma) = [l \<cdot> sigma]"
        "aliens (- F) (r \<cdot> sigma) = [r \<cdot> sigma]"
        unfolding l r using f g by auto
      have st: "(l \<cdot> sigma,r \<cdot> sigma) \<in> rstep (R1 \<union> R2)"
        by (rule rstep.rstep[of l r "R1 \<union> R2" _ Hole sigma])
          (use lr in auto)
      from Hole al closed[OF _ st] show ?thesis by auto
    qed
  next
    case (More f bef C aft)
    let ?n = "Suc (length bef + length aft)"
    let ?S = "(More f bef C aft)\<langle>l \<cdot> sigma\<rangle>"
    let ?T = "(More f bef C aft)\<langle>r \<cdot> sigma\<rangle>"
    show ?case
    proof (cases "(f,?n) \<in> - F")
      case False
      have al: "aliens (- F) ?S = [?S]" "aliens (- F) ?T = [?T]"
        using False by auto
      have st: "(?S,?T) \<in> rstep (R1 \<union> R2)"
        by (rule rstep.rstep[of l r "R1 \<union> R2" _
            "More f bef C aft" sigma]) (use lr in auto)
      from More(2) al closed[OF _ st] show ?thesis by auto
    next
      case True
      from More(2) True have inner:
          "set (aliens (- F) C\<langle>l \<cdot> sigma\<rangle>) \<subseteq> X"
        by auto
      from More(1)[OF inner] True More(2) show ?thesis by auto
    qed
  qed
qed

lemma aaecc_step_preserves_below_alien_invariant:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and closed: "\<And>a b. a \<in> X \<Longrightarrow>
      (a,b) \<in> rstep (R1 \<union> R2) \<Longrightarrow> b \<in> X"
    and subterm_closed: "\<And>a b. a \<in> X \<Longrightarrow> b \<lhd> a \<Longrightarrow> b \<in> X"
    and source: "set (aliens_below (- F) s) \<subseteq> X"
    and step: "(s,t) \<in> rstep (R1 \<union> R2)"
  shows "set (aliens_below (- F) t) \<subseteq> X"
proof (cases "(s,t) \<in> rrstep (R1 \<union> R2)")
  case True
  then obtain l r sigma where lr: "(l,r) \<in> R1 \<union> R2"
    and s: "s = l \<cdot> sigma" and t: "t = r \<cdot> sigma"
    by (rule rrstepE)
  have static: "funas_args_term l \<subseteq> - F"
    "funas_args_term r \<subseteq> - F"
  proof -
    show "funas_args_term l \<subseteq> - F"
    proof (cases "(l,r) \<in> R1")
      case True
      from aaecc_signature_separated_R1(1)[OF sep True]
      show ?thesis unfolding funas_term_conv by auto
    next
      case False
      with lr have "(l,r) \<in> R2" by auto
      from aaecc_signature_separated_R2(4)[OF sep this]
      show ?thesis by auto
    qed
    show "funas_args_term r \<subseteq> - F"
    proof (cases "(l,r) \<in> R1")
      case True
      from aaecc_signature_separated_R1(2)[OF sep True]
      show ?thesis unfolding funas_term_conv by auto
    next
      case False
      with lr have "(l,r) \<in> R2" by auto
      from aaecc_signature_separated_R2(5)[OF sep this]
      show ?thesis by auto
    qed
  qed
  have vars: "vars_term r \<subseteq> vars_term l"
    using wf lr unfolding wf_trs_def by auto
  from wf lr obtain fl ls where lfun: "l = Fun fl ls"
    unfolding wf_trs_def by blast
  have isfun_l: "is_Fun l" unfolding lfun by simp
  show ?thesis
  proof (cases r)
    case (Fun fr rs)
    have isfun_r: "is_Fun r" unfolding Fun by simp
    show ?thesis using source vars unfolding s t
      aliens_below_subst[OF static(1) isfun_l]
      aliens_below_subst[OF static(2) isfun_r]
      by auto
  next
    case (Var x)
    from vars have xin: "x \<in> vars_term l" unfolding Var by auto
    from xin have xin_list: "x \<in> set (vars_term_list l)" by simp
    have alien_sigma: "set (aliens (- F) (sigma x)) \<subseteq> X"
      using source xin_list unfolding s
        aliens_below_subst[OF static(1) isfun_l] by auto
    have target: "set (aliens_below (- F) (sigma x)) \<subseteq> X"
    proof
      fix z
      assume zb: "z \<in> set (aliens_below (- F) (sigma x))"
      from aaecc_alien_below_is_alien_or_below_alien_root[OF zb]
        alien_sigma subterm_closed
      have zin: "z \<in> X" by blast
      from zin show "z \<in> X" .
    qed
    show ?thesis unfolding t Var using target by simp
  qed
next
  case False
  with step have nr: "(s,t) \<in> nrrstep (R1 \<union> R2)"
    unfolding rstep_iff_rrstep_or_nrrstep by auto
  from nr[unfolded nrrstep_iff_arg_rstep]
  obtain f ss i u where s: "s = Fun f ss" and i: "i < length ss"
    and t: "t = Fun f (ss[i := u])"
    and arg: "(ss ! i,u) \<in> rstep (R1 \<union> R2)" by auto
  have arg_source: "set (aliens (- F) (ss ! i)) \<subseteq> X"
  proof
    fix x
    assume x: "x \<in> set (aliens (- F) (ss ! i))"
    from i have nth: "ss ! i \<in> set ss" by simp
    from source have src:
        "(\<Union>a\<in>set ss. set (aliens (- F) a)) \<subseteq> X"
      unfolding s by (simp add: set_concat)
    from src nth x show "x \<in> X" by auto
  qed
  from aaecc_step_preserves_alien_invariant[
      OF sep wf closed arg_source arg]
  have arg_target: "set (aliens (- F) u) \<subseteq> X" .
  have all_source: "\<And>v. v \<in> set ss \<Longrightarrow>
      set (aliens (- F) v) \<subseteq> X"
    using source unfolding s by (auto simp: set_concat)
  have all_target: "\<And>v. v \<in> set (ss[i := u]) \<Longrightarrow>
      set (aliens (- F) v) \<subseteq> X"
  proof -
    fix v
    assume vin: "v \<in> set (ss[i := u])"
    from set_update_subset_insert[THEN subsetD, OF vin]
    have "v = u \<or> v \<in> set ss" by auto
    with all_source arg_target show "set (aliens (- F) v) \<subseteq> X"
      by auto
  qed
  show ?thesis unfolding s t using all_target
    by (auto simp: set_concat)
qed

lemma aaecc_SN_rel_root_steps:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf1: "wf_trs R1" and wf2: "wf_trs R2"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
  shows "SN_rel (sig_step_below (- F) (rrstep R2))
    (sig_step_below (- F) (rstep R1))"
proof (unfold SN_rel_defs, rule ccontr)
  let ?S = "sig_step_below (- F) (rrstep R2)"
  let ?W = "sig_step_below (- F) (rstep R1)"
  assume "\<not> SN (relto ?S ?W)"
  then obtain g where chain:
      "\<And>n. (g n,g (Suc n)) \<in> relto ?S ?W"
    unfolding SN_defs by blast
  have one_block: "\<exists>u v.
      (g n,u) \<in> ?W\<^sup>* \<and> (u,v) \<in> ?S \<and>
      (v,g (Suc n)) \<in> ?W\<^sup>*" for n
    using chain[of n] by auto
  then have "\<forall>n. \<exists>u v.
      (g n,u) \<in> ?W\<^sup>* \<and> (u,v) \<in> ?S \<and>
      (v,g (Suc n)) \<in> ?W\<^sup>*" by blast
  from choice[OF this] obtain u where "\<forall>n. \<exists>v.
      (g n,u n) \<in> ?W\<^sup>* \<and> (u n,v) \<in> ?S \<and>
      (v,g (Suc n)) \<in> ?W\<^sup>*" by metis
  from choice[OF this] obtain v where blocks:
      "\<And>n. (g n,u n) \<in> ?W\<^sup>*"
      "\<And>n. (u n,v n) \<in> ?S"
      "\<And>n. (v n,g (Suc n)) \<in> ?W\<^sup>*" by blast
  have one_rule: "\<exists>l r sigma.
      (l,r) \<in> R2 \<and> u n = l \<cdot> sigma \<and> v n = r \<cdot> sigma"
    for n
  proof -
    from blocks(2)[of n] have "(u n,v n) \<in> rrstep R2"
      unfolding sig_step_below_def by auto
    then obtain l r sigma where "(l,r) \<in> R2"
      "u n = l \<cdot> sigma" "v n = r \<cdot> sigma" by (rule rrstepE)
    then show ?thesis by blast
  qed
  then have "\<forall>n. \<exists>l r sigma.
      (l,r) \<in> R2 \<and> u n = l \<cdot> sigma \<and> v n = r \<cdot> sigma"
    by blast
  from choice[OF this] obtain l where "\<forall>n. \<exists>r sigma.
      (l n,r) \<in> R2 \<and> u n = l n \<cdot> sigma \<and> v n = r \<cdot> sigma"
    by metis
  from choice[OF this] obtain r where "\<forall>n. \<exists>sigma.
      (l n,r n) \<in> R2 \<and> u n = l n \<cdot> sigma \<and>
      v n = r n \<cdot> sigma" by metis
  from choice[OF this] obtain sigma where rules: "\<And>n. (l n,r n) \<in> R2"
    and u: "\<And>n. u n = l n \<cdot> sigma n"
    and v: "\<And>n. v n = r n \<cdot> sigma n" by blast
  have lhs_free: "funas_args_term (l n \<cdot> sigma n) \<inter> F = {}" for n
    using blocks(2)[of n, unfolded sig_step_below_def u]
    by auto
  have W_subset: "?W \<subseteq> rstep R1"
    unfolding sig_step_below_def by auto
  have connection: "(r n \<cdot> sigma n,
      l (Suc n) \<cdot> sigma (Suc n)) \<in> (rstep R1)\<^sup>*" for n
    using rtrancl_mono[OF W_subset, THEN subsetD, OF blocks(3)[of n]]
      rtrancl_mono[OF W_subset, THEN subsetD, OF blocks(1)[of "Suc n"]]
    unfolding v u by auto
  show False
    by (rule aaecc_no_infinite_R2_root_chain[
        where l=l and r=r and sigma=sigma,
        OF sep wf1 wf2 no_cp no_cross_cp inner_SN rules lhs_free connection])
qed

lemma aaecc_SN_rel_and_SN_imp_SN_union:
  assumes relative: "SN_rel R S" and weak: "SN S"
  shows "SN (R \<union> S)"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and> chain (R \<union> S) f"
  then obtain f where chain: "chain (R \<union> S) f" by auto
  from relative[unfolded SN_rel_on_conv SN_rel_on_alt_def, rule_format,
      of f] chain
  have finite_R: "\<not> (INFM i. (f i,f (Suc i)) \<in> R)" by auto
  then obtain m where tail_R: "\<And>i. i > m \<Longrightarrow>
      (f i,f (Suc i)) \<notin> R"
    unfolding INFM_nat by blast
  let ?g = "\<lambda>i. f (Suc m + i)"
  have chainS: "chain S ?g" unfolding chain_def
  proof
    fix i
    from chain[unfolded chain_def, rule_format, of "Suc m + i"]
      tail_R[of "Suc m + i"]
    show "(?g i,?g (Suc i)) \<in> S" by auto
  qed
  have not_local: "\<not> SN_on S {?g 0}"
    by (rule chain_imp_not_SN_on[OF chainS])
  have local_SN: "SN_on S {?g 0}"
    by (rule SN_on_subset2[OF _ weak]) auto
  from not_local local_SN show False by contradiction
qed

lemma aaecc_clean_structural_SN:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf1: "wf_trs R1" and wf2: "wf_trs R2"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
  shows "SN (sig_step_below (- F) (rrstep R2) \<union>
    sig_step_below (- F) (rstep R1))"
proof -
  let ?S = "sig_step_below (- F) (rrstep R2)"
  let ?W = "sig_step_below (- F) (rstep R1)"
  have rel: "SN_rel ?S ?W"
    by (rule aaecc_SN_rel_root_steps[OF assms])
  have R1_SN: "SN (rstep R1)"
    by (rule aaecc_R1_termination[OF sep wf1 no_cp inner_SN])
  have W_SN: "SN ?W"
    by (rule SN_subset[OF R1_SN], unfold sig_step_below_def, auto)
  show ?thesis by (rule aaecc_SN_rel_and_SN_imp_SN_union[OF rel W_SN])
qed

theorem aaecc_innermost_termination:
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and no_cp: "aaecc_R1_ok ren R1"
    and no_cross_cp: "critical_pairs ren R2 R1 = {}"
    and inner_SN: "SN (inn_rstep (R1 \<union> R2))"
  shows "SN (rstep (R1 \<union> R2))"
proof (rule ccontr)
  let ?U = "rstep (R1 \<union> R2)"
  let ?X = "{a. SN_on ?U {a}}"
  let ?A = "{(a,b). a \<in> ?X \<and> (a,b) \<in> ?U}"
  let ?S = "sig_step_below (- F) (rrstep R2)"
  let ?W = "sig_step_below (- F) (rstep R1)"
  let ?P = "?S \<union> ?W"
  assume not_SN: "\<not> SN ?U"
  from not_SN_imp_Tinf[OF not_SN]
  obtain t0 where Tinf: "t0 \<in> Tinf ?U" by auto
  from Tinf[unfolded Tinf_def]
  have nSN: "\<not> SN_on ?U {t0}"
    and minimal: "\<And>u. u \<lhd> t0 \<Longrightarrow> SN_on ?U {u}" by auto
  from nSN obtain f where f0: "f 0 = t0"
    and steps: "\<And>i. (f i,f (Suc i)) \<in> ?U"
    unfolding SN_defs by blast
  have X_closed: "b \<in> ?X" if a: "a \<in> ?X" and ab: "(a,b) \<in> ?U"
    for a b
    using step_preserves_SN_on[OF ab] a by auto
  have X_subterm_closed: "b \<in> ?X" if a: "a \<in> ?X" and ba: "b \<lhd> a"
    for a b
  proof -
    from ba have ab: "a \<unrhd> b" by auto
    from a have aSN: "SN_on ?U {a}" by simp
    from ctxt_closed_SN_on_subt[OF ctxt_closed_rstep aSN ab]
    show ?thesis by simp
  qed
  have alien0: "set (aliens_below (- F) (f 0)) \<subseteq> ?X"
  proof
    fix a
    assume a: "a \<in> set (aliens_below (- F) (f 0))"
    have proper: "a \<lhd> f 0"
    proof -
      from a obtain g ts u where ft: "f 0 = Fun g ts"
        and u: "u \<in> set ts" and au: "u \<unrhd> a"
        by (cases "f 0") (auto dest: aliens_imp_supteq)
      from u au show ?thesis unfolding ft by auto
    qed
    from minimal[of a, unfolded f0[symmetric], OF proper]
    show "a \<in> ?X" by simp
  qed
  have aliens: "set (aliens_below (- F) (f i)) \<subseteq> ?X" for i
  proof (induct i)
    case 0
    show ?case by (rule alien0)
  next
    case (Suc i)
    show ?case by (rule aaecc_step_preserves_below_alien_invariant[
        OF sep wf X_closed X_subterm_closed Suc steps[of i]])
  qed
  let ?c = "\<lambda>i. aaecc_clean_below F (f i)"
  let ?as = "\<lambda>i. aliens_below (- F) (f i)"
  let ?E = "\<lambda>i. root (f i) \<notin> Some ` F \<and>
    root (f (Suc i)) \<in> Some ` F"
  have clean_args: "funas_args_term (?c i) \<subseteq> - F" for i
    by (rule aaecc_clean_below_args)
  have projection: "(?c i,?c (Suc i)) \<in> ?P \<or>
      (?c i = ?c (Suc i) \<and>
        (?as i,?as (Suc i)) \<in> aaecc_list_singleton_ext ?A) \<or> ?E i" for i
  proof -
  from aaecc_step_clean_below[OF sep wf steps[of i]]
    show ?thesis
    proof
      assume structural: "(?c i,?c (Suc i)) \<in> rstep R1 \<union> rrstep R2"
      from structural clean_args[of i] clean_args[of "Suc i"]
      show ?thesis unfolding sig_step_below_def by auto
    next
      assume rest: "(?c i = ?c (Suc i) \<and>
        (\<exists>xs a b ys. ?as i = xs @ a # ys \<and>
          ?as (Suc i) = xs @ b # ys \<and> (a,b) \<in> ?U)) \<or> ?E i"
      then show ?thesis
      proof
        assume bottom: "?c i = ?c (Suc i) \<and>
          (\<exists>xs a b ys. ?as i = xs @ a # ys \<and>
            ?as (Suc i) = xs @ b # ys \<and> (a,b) \<in> ?U)"
        then obtain xs a b ys where aa: "?as i = xs @ a # ys"
          and bb: "?as (Suc i) = xs @ b # ys" and ab: "(a,b) \<in> ?U"
          by auto
        from bottom have eq: "?c i = ?c (Suc i)" by auto
        from aliens[of i] aa have aX: "a \<in> ?X" by auto
        show ?thesis unfolding aaecc_list_singleton_ext_def
          using eq aa bb ab aX by blast
      next
        assume exceptional: "?E i"
        then show ?thesis by auto
      qed
    qed
  qed
  have rooted_step: "root (f (Suc i)) \<in> Some ` F"
    if "root (f i) \<in> Some ` F" for i
    by (rule aaecc_root_in_signature_preserved[OF sep wf steps[of i] that])
  have no_exception_tail: "\<exists>m. \<forall>i>m. \<not> ?E i"
  proof (cases "\<exists>k. root (f k) \<in> Some ` F")
    case False
    show ?thesis
    proof (intro exI[of _ 0] allI impI notI)
      fix i
      assume "i > 0" and "?E i"
      with False show False by auto
    qed
  next
    case True
    then obtain k where rooted: "root (f k) \<in> Some ` F" by auto
    have rooted_tail: "root (f (k+n)) \<in> Some ` F" for n
    proof (induct n)
      case 0
      show ?case using rooted by simp
    next
      case (Suc n)
      from rooted_step[OF Suc]
      show ?case by (simp add: add_Suc_right)
    qed
    show ?thesis
    proof (intro exI[of _ k] allI impI notI)
      fix i
      assume ik: "i > k" and exceptional: "?E i"
      have "root (f i) \<in> Some ` F"
        using rooted_tail[of "i-k"] ik by simp
      with exceptional show False by auto
    qed
  qed
  from no_exception_tail obtain e where etail: "\<And>i. i > e \<Longrightarrow>
      \<not> ?E i" by auto
  have A_SN: "SN ?A"
    unfolding SN_on_def chain_def by blast
  have list_SN: "SN (aaecc_list_singleton_ext ?A)"
    by (rule aaecc_SN_list_singleton_ext[OF A_SN])
  have inf_structural: "INFM i. (?c i,?c (Suc i)) \<in> ?P"
  proof (rule ccontr)
    assume "\<not> (INFM i. (?c i,?c (Suc i)) \<in> ?P)"
    then obtain m where tail: "\<And>i. i > m \<Longrightarrow>
        (?c i,?c (Suc i)) \<notin> ?P"
      unfolding INFM_nat by blast
    let ?b = "max m e"
    let ?g = "\<lambda>i. ?as (Suc ?b + i)"
    have chain_g: "chain (aaecc_list_singleton_ext ?A) ?g"
      unfolding chain_def
    proof
      fix i
      have im: "Suc ?b + i > m" and ie: "Suc ?b + i > e" by simp_all
      have noP: "(?c (Suc ?b + i),?c (Suc (Suc ?b + i))) \<notin> ?P"
        by (rule tail[OF im])
      have noE: "\<not> ?E (Suc ?b + i)" by (rule etail[OF ie])
      from projection[of "Suc ?b + i"] noP noE
      show "(?g i,?g (Suc i)) \<in> aaecc_list_singleton_ext ?A"
        by auto
    qed
    have witness: "\<exists>h. h 0 \<in> UNIV \<and>
        chain (aaecc_list_singleton_ext ?A) h"
    proof (rule exI[of _ ?g], intro conjI)
      show "?g 0 \<in> UNIV" by simp
      show "chain (aaecc_list_singleton_ext ?A) ?g" by (rule chain_g)
    qed
    from list_SN witness show False unfolding SN_on_def by blast
  qed
  from wf have wf1: "wf_trs R1" and wf2: "wf_trs R2"
    unfolding wf_trs_def by auto
  have structural_SN: "SN ?P"
    by (rule aaecc_clean_structural_SN[
        OF sep wf1 wf2 no_cp no_cross_cp inner_SN])
  have relative_Id: "SN_rel ?P Id"
    using structural_SN unfolding SN_rel_defs by simp
  let ?d = "\<lambda>i. ?c (Suc e + i)"
  have clean_chain: "chain (?P \<union> Id) ?d"
    unfolding chain_def
  proof
    fix i
    have ie: "Suc e + i > e" by simp
    have noE: "\<not> ?E (Suc e + i)" by (rule etail[OF ie])
    from projection[of "Suc e + i"] noE
    show "(?d i,?d (Suc i)) \<in> ?P \<union> Id" by auto
  qed
  have inf_d: "INFM i. (?d i,?d (Suc i)) \<in> ?P"
  proof (unfold INFM_nat, intro allI)
    fix m
    from inf_structural[unfolded INFM_nat, rule_format,
        of "Suc e + m"]
    obtain n where n: "n > Suc e + m"
      and stepn: "(?c n,?c (Suc n)) \<in> ?P" by auto
    let ?j = "n - Suc e"
    have jm: "?j > m" using n by arith
    have nj: "Suc e + ?j = n" using n by arith
    show "\<exists>j>m. (?d j,?d (Suc j)) \<in> ?P"
    proof (intro exI[of _ ?j] conjI)
      show "?j > m" by (rule jm)
      show "(?d ?j,?d (Suc ?j)) \<in> ?P"
        using stepn nj by (simp add: add_Suc_right)
    qed
  qed
  have chain_init: "chain (?P \<union> Id) ?d \<and> ?d 0 \<in> UNIV"
    using clean_chain by simp
  from relative_Id[unfolded SN_rel_on_conv SN_rel_on_alt_def,
      rule_format, of ?d, OF chain_init]
  have not_inf_d: "\<not> (INFM i. (?d i,?d (Suc i)) \<in> ?P)" .
  from not_inf_d inf_d show False by contradiction
qed

end

end
