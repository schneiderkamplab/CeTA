theory LP_Constructor_Source
  imports LP_Constructor_Rewriting LP_PiDP_Source
begin

text \<open>Data erasure fixes the finitely many constructors of the source
  clauses. All other data symbols may be mapped to a fresh constructor. This
  preserves every source step while keeping generated control symbols out of
  runtime data. Predicate and continuation symbols are not erased.\<close>

lemma lp_data_map_subst:
  "map_lp_iterm data id (lp_isubst t \<sigma>) =
    lp_isubst (map_lp_iterm data id t) (\<lambda>x. map_lp_iterm data id (\<sigma> x))"
proof (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
  case Eq_lp_iterm
  show ?case by (cases t)
    (auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl_strong)
qed

lemma lp_data_map_eval:
  assumes fixed: "\<And>f. f\<in>funs_term t \<Longrightarrow> data f=f"
  shows "map_lp_iterm data id (lp_ieval t \<rho>) =
    lp_ieval t (\<lambda>x. map_lp_iterm data id (\<rho> x))"
  using fixed by (induct t) (auto intro!: map_cong)

definition lp_data_atom where
  "lp_data_atom data a = (fst a,map (map_lp_iterm data id) (snd a))"

definition lp_data_fixed_atom where
  "lp_data_fixed_atom data a = (\<forall>t\<in>set (snd a). \<forall>f\<in>funs_term t. data f=f)"

definition lp_data_fixed_program where
  "lp_data_fixed_program data P = (\<forall>c\<in>set P.
    lp_data_fixed_atom data (fst c) \<and> list_all (lp_data_fixed_atom data) (snd c))"

lemma lp_data_atom_eval:
  "lp_data_fixed_atom data a \<Longrightarrow>
    lp_data_atom data (lp_atom_eval a \<rho>) =
    lp_atom_eval a (\<lambda>x. map_lp_iterm data id (\<rho> x))"
  unfolding lp_data_atom_def lp_atom_eval_def lp_data_fixed_atom_def
  by (auto simp: map_map o_def intro!: map_cong lp_data_map_eval)

lemma lp_data_atom_subst:
  "lp_data_atom data (lp_iatom_subst a \<sigma>) =
    lp_iatom_subst (lp_data_atom data a) (\<lambda>x. map_lp_iterm data id (\<sigma> x))"
  by (simp add: lp_data_atom_def lp_iatom_subst_def map_map o_def lp_data_map_subst)

fun lp_data_config where
  "lp_data_config data (LPICall a) = LPICall (lp_data_atom data a)"
| "lp_data_config data (LPIDone a) = LPIDone (lp_data_atom data a)"
| "lp_data_config data (LPIWait c i \<rho> k) =
    LPIWait c i (\<lambda>x. map_lp_iterm data id (\<rho> x)) (lp_data_config data k)"

lemma lp_data_config_subst:
  "lp_data_config data (lp_iconfig_subst s \<sigma>) =
    lp_iconfig_subst (lp_data_config data s) (\<lambda>x. map_lp_iterm data id (\<sigma> x))"
  by (induct s) (simp_all add: lp_data_atom_subst lp_data_map_subst
    lp_data_map_subst[unfolded id_def] id_def)

lemma lp_data_fixed_head:
  "lp_data_fixed_program data P \<Longrightarrow> c<length P \<Longrightarrow>
    lp_data_fixed_atom data (fst (P!c))"
  unfolding lp_data_fixed_program_def by (simp add: nth_mem)

lemma lp_data_fixed_body:
  "lp_data_fixed_program data P \<Longrightarrow> c<length P \<Longrightarrow>
    i<length (snd (P!c)) \<Longrightarrow> lp_data_fixed_atom data (snd (P!c)!i)"
  unfolding lp_data_fixed_program_def list_all_iff by (meson nth_mem)

lemma lp_data_local:
  assumes fixed: "lp_data_fixed_program data P" and st: "(s,t)\<in>lp_ilocal P"
  shows "(lp_data_config data s,lp_data_config data t)\<in>lp_ilocal P"
  using st
  by (induct rule: lp_ilocal.induct)
    (auto simp: lp_data_atom_eval[OF lp_data_fixed_head[OF fixed]]
      lp_data_atom_eval[OF lp_data_fixed_body[OF fixed]]
      intro: lp_ilocal.intros)

lemma lp_data_machine:
  assumes fixed: "lp_data_fixed_program data P" and st: "(s,t)\<in>lp_imachine P"
  shows "(lp_data_config data s,lp_data_config data t)\<in>lp_imachine P"
proof -
  obtain \<sigma> where local: "(lp_iconfig_subst s \<sigma>,t)\<in>lp_ilocal P"
    using st unfolding lp_imachine_def by blast
  have mapped: "(lp_iconfig_subst (lp_data_config data s)
      (\<lambda>x. map_lp_iterm data id (\<sigma> x)),lp_data_config data t)\<in>lp_ilocal P"
    using lp_data_local[OF fixed local] by (simp add: lp_data_config_subst)
  show ?thesis using mapped unfolding lp_imachine_def by blast
qed

lemma lp_data_iframe:
  assumes fixed: "lp_data_fixed_program data P" and step: "(s,t)\<in>lp_iframe P"
  shows "(lp_data_config data s,lp_data_config data t)\<in>lp_iframe P"
proof -
  obtain c i \<rho> k k' \<sigma> where s: "s=LPIWait c i \<rho> k"
    and t: "t=LPIWait c i (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) k'"
    and local: "(lp_iconfig_subst k \<sigma>,k')\<in>lp_ilocal P"
    using step unfolding lp_iframe_def by blast
  have mapped: "(lp_iconfig_subst (lp_data_config data k)
      (\<lambda>x. map_lp_iterm data id (\<sigma> x)),lp_data_config data k')\<in>lp_ilocal P"
    using lp_data_local[OF fixed local] by (simp add: lp_data_config_subst)
  show ?thesis using mapped
    by (auto simp: s t lp_iframe_def lp_data_map_subst)
qed

lemma lp_data_iframes:
  assumes fixed: "lp_data_fixed_program data P" and path: "(s,t)\<in>(lp_iframe P)\<^sup>*"
  shows "(lp_data_config data s,lp_data_config data t)\<in>(lp_iframe P)\<^sup>*"
  using path by (induct rule: rtrancl_induct)
    (auto intro: rtrancl_into_rtrancl lp_data_iframe[OF fixed])

context lp_translation
begin

lemma data_ilocal_constructor:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U"
    and st: "(s,t)\<in>lp_ilocal P"
  shows "(iencode (lp_data_config data s),iencode (lp_data_config data t))\<in>lp_cactive C (set translated) U"
  using st
proof (induct rule: lp_ilocal.induct)
  case (fact c \<rho>)
  have r: "(lp_tag inp (fst (P!c)),lp_tag out (fst (P!c)))\<in>set translated"
    using entry_member[OF fact(1)] fact(2) by (simp add: entry_rule_def)
  have h: "lp_data_fixed_atom data (fst (P!c))" by (rule lp_data_fixed_head[OF fixed fact(1)])
  have st: "(lp_ieval (lp_tag inp (fst (P!c))) (\<lambda>x. map_lp_iterm data id (\<rho> x)),
      lp_ieval (lp_tag out (fst (P!c))) (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>lp_cactive C (set translated) U"
    by (rule lp_cactive_root[OF r shapes[OF r] lp_constructor_value_map[OF range]])
  show ?case using st by (simp only: lp_data_config.simps lp_data_atom_eval[OF h] iencode.simps lp_itag_eval)
next
  case (enter c \<rho>)
  have r: "(lp_tag inp (fst (P!c)),wrap c 0 (lp_tag inp (snd (P!c)!0)))\<in>set translated"
    using entry_member[OF enter(1)] enter(2) by (simp add: entry_rule_def)
  have h: "lp_data_fixed_atom data (fst (P!c))" by (rule lp_data_fixed_head[OF fixed enter(1)])
  have b: "lp_data_fixed_atom data (snd (P!c)!0)"
    by (rule lp_data_fixed_body[OF fixed enter(1)]) (use enter(2) in simp)
  have st: "(lp_ieval (lp_tag inp (fst (P!c))) (\<lambda>x. map_lp_iterm data id (\<rho> x)),
      lp_ieval (wrap c 0 (lp_tag inp (snd (P!c)!0))) (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>lp_cactive C (set translated) U"
    by (rule lp_cactive_root[OF r shapes[OF r] lp_constructor_value_map[OF range]])
  show ?case using st
    by (simp only: lp_data_config.simps lp_data_atom_eval[OF h] lp_data_atom_eval[OF b];
      simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (advance c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i)))\<in>set translated"
    using return_member[OF advance(1), of i] advance(2) by (simp add: return_rule_def)
  have b: "lp_data_fixed_atom data (snd (P!c)!i)"
    by (rule lp_data_fixed_body[OF fixed advance(1)]) (use advance(2) in simp)
  have b': "lp_data_fixed_atom data (snd (P!c)!Suc i)"
    by (rule lp_data_fixed_body[OF fixed advance(1,2)])
  have st: "(lp_ieval (wrap c i (lp_tag out (snd (P!c)!i))) (\<lambda>x. map_lp_iterm data id (\<rho> x)),
      lp_ieval (wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))) (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>lp_cactive C (set translated) U"
    by (rule lp_cactive_root[OF r shapes[OF r] lp_constructor_value_map[OF range]])
  show ?case using st
    by (simp only: lp_data_config.simps lp_data_atom_eval[OF b] lp_data_atom_eval[OF b'];
      simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (leave c i \<rho>)
  have r: "(wrap c i (lp_tag out (snd (P!c)!i)),lp_tag out (fst (P!c)))\<in>set translated"
    using return_member[OF leave(1,2)] leave(3) by (simp add: return_rule_def)
  have b: "lp_data_fixed_atom data (snd (P!c)!i)"
    by (rule lp_data_fixed_body[OF fixed leave(1,2)])
  have h: "lp_data_fixed_atom data (fst (P!c))" by (rule lp_data_fixed_head[OF fixed leave(1)])
  have st: "(lp_ieval (wrap c i (lp_tag out (snd (P!c)!i))) (\<lambda>x. map_lp_iterm data id (\<rho> x)),
      lp_ieval (lp_tag out (fst (P!c))) (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>lp_cactive C (set translated) U"
    by (rule lp_cactive_root[OF r shapes[OF r] lp_constructor_value_map[OF range]])
  show ?case using st
    by (simp only: lp_data_config.simps lp_data_atom_eval[OF b] lp_data_atom_eval[OF h];
      simp add: wrap_def env_def o_def lp_itag_eval)
next
  case (frame s t c i \<rho>)
  show ?case by (simp only: lp_data_config.simps iencode.simps,
    rule lp_cactive.frame[OF frames frame(2)])
qed

lemma data_iframe_constructor:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and marked: "\<And>c i. sharp (u c i)\<in>U"
    and st: "(s,t)\<in>lp_iframe P"
  shows "(mencode sharp (lp_data_config data s),mencode sharp (lp_data_config data t))\<in>(lp_clink C (set translated) U)\<^sup>*"
proof -
  obtain c i \<rho> k k' \<sigma> where s: "s=LPIWait c i \<rho> k"
    and t: "t=LPIWait c i (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) k'"
    and local: "(lp_iconfig_subst k \<sigma>,k')\<in>lp_ilocal P"
    using st unfolding lp_iframe_def by blast
  have active: "(iencode (lp_data_config data (lp_iconfig_subst k \<sigma>)),iencode (lp_data_config data k'))\<in>lp_cactive C (set translated) U"
    by (rule data_ilocal_constructor[OF fixed range shapes frames local])
  have lifted: "(lp_isubst (mencode sharp (lp_data_config data s)) (\<lambda>x. map_lp_iterm data id (\<sigma> x)),
      mencode sharp (lp_data_config data t))\<in>lp_cactive C (set translated) U"
    using lp_cactive.frame[OF marked active, of c i
      "map (\<lambda>x. map_lp_iterm data id (lp_isubst (\<rho> x) \<sigma>)) (lp_saved_vars (P!c) i)"]
    by (simp add: s t lp_data_config_subst iencode_subst lp_data_map_subst o_def)
  have first: "(mencode sharp (lp_data_config data s),
      lp_isubst (mencode sharp (lp_data_config data s)) (\<lambda>x. map_lp_iterm data id (\<sigma> x)))\<in>lp_clink C (set translated) U"
    unfolding lp_clink_def by blast
  have second: "(lp_isubst (mencode sharp (lp_data_config data s)) (\<lambda>x. map_lp_iterm data id (\<sigma> x)),
      mencode sharp (lp_data_config data t))\<in>lp_clink C (set translated) U"
    using lifted unfolding lp_clink_def by blast
  show ?thesis by (rule rtrancl_into_rtrancl[OF r_into_rtrancl[OF first] second])
qed

lemma data_iframes_constructor:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and marked: "\<And>c i. sharp (u c i)\<in>U"
    and path: "(s,t)\<in>(lp_iframe P)\<^sup>*"
  shows "(mencode sharp (lp_data_config data s),mencode sharp (lp_data_config data t))\<in>(lp_clink C (set translated) U)\<^sup>*"
  using path by (induct rule: rtrancl_induct)
    (auto intro: rtrancl_trans data_iframe_constructor[where sharp=sharp, OF fixed range shapes frames marked])

lemma data_top_bad_pair:
  assumes fixed: "lp_data_fixed_program data P"
    and top: "(s,t) \<in> lp_itop P" and bad: "\<not> SN_on (lp_imachine P) {t}"
  obtains l r \<rho> k where "(l,r) \<in> set (pi_pairs sharp)"
    "mencode sharp (lp_data_config data s) = lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    "mencode sharp (lp_data_config data k) = lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    "lp_iminimal P k"
  using top bad
proof (cases rule: lp_itop.cases)
  case (fact c \<rho>)
  then show ?thesis using bad lp_done_SN by blast
next
  case (enter c \<rho>)
  let ?l = "lp_tag inp (fst (P!c))"
  let ?r = "wrap c 0 (lp_tag inp (snd (P!c)!0))"
  let ?b = "lp_tag inp (snd (P!c)!0)"
  have p1: "(lp_mark sharp ?l,lp_mark sharp ?r) \<in> set (pi_pairs sharp)"
    by (rule entry_pair_member[OF enter(3)]) (simp add: entry_pairs_def enter(4))
  have p2: "(lp_mark sharp ?l,lp_mark sharp ?b) \<in> set (pi_pairs sharp)"
    by (rule entry_pair_member[OF enter(3)]) (simp add: entry_pairs_def enter(4))
  have h: "lp_data_fixed_atom data (fst (P!c))"
    by (rule lp_data_fixed_head[OF fixed enter(3)])
  have b: "lp_data_fixed_atom data (snd (P!c)!0)"
    by (rule lp_data_fixed_body[OF fixed enter(3)]) (use enter(4) in simp)
  have choice: "lp_iminimal P t \<or> lp_iminimal P (LPICall (lp_atom_eval (snd (P!c)!0) \<rho>))"
    using lp_choose_bad_wait[OF bad[unfolded enter(2)]] enter(2) by simp
  from choice show ?thesis
    using that[OF p1, of \<rho> t] that[OF p2, of \<rho> "LPICall (lp_atom_eval (snd (P!c)!0) \<rho>)"]
    by (simp only: enter(1,2) lp_data_config.simps lp_data_atom_eval[OF h]
        lp_data_atom_eval[OF b];
      auto simp: lp_tag_def lp_itag_def lp_atom_eval_def wrap_def env_def o_def)
next
  case (advance c i \<rho>)
  let ?l = "wrap c i (lp_tag out (snd (P!c)!i))"
  let ?r = "wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))"
  let ?b = "lp_tag inp (snd (P!c)!Suc i)"
  have ib: "i<length (snd (P!c))" using advance(4) by simp
  have p1: "(lp_mark sharp ?l,lp_mark sharp ?r) \<in> set (pi_pairs sharp)"
    by (rule return_pair_member[OF advance(3) ib]) (simp add: return_pairs_def advance(4))
  have p2: "(lp_mark sharp ?l,lp_mark sharp ?b) \<in> set (pi_pairs sharp)"
    by (rule return_pair_member[OF advance(3) ib]) (simp add: return_pairs_def advance(4))
  have b: "lp_data_fixed_atom data (snd (P!c)!i)"
    by (rule lp_data_fixed_body[OF fixed advance(3) ib])
  have b': "lp_data_fixed_atom data (snd (P!c)!Suc i)"
    by (rule lp_data_fixed_body[OF fixed advance(3,4)])
  have choice: "lp_iminimal P t \<or> lp_iminimal P (LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>))"
    using lp_choose_bad_wait[OF bad[unfolded advance(2)]] advance(2) by simp
  from choice show ?thesis
    using that[OF p1, of \<rho> t] that[OF p2, of \<rho> "LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>)"]
    by (simp only: advance(1,2) lp_data_config.simps lp_data_atom_eval[OF b]
        lp_data_atom_eval[OF b'];
      auto simp: lp_tag_def lp_itag_def lp_atom_eval_def wrap_def env_def o_def)
next
  case (leave c i \<rho>)
  then show ?thesis using bad lp_done_SN by blast
qed

lemma data_minimal_next_pair:
  fixes a :: "('f,'v) term"
  assumes fixed: "lp_data_fixed_program data P"
    and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. u c i\<in>U" and marked: "\<And>c i. sharp (u c i)\<in>U"
    and minimal: "lp_iminimal P s"
    and pr: "lp_iproject \<pi> (mencode sharp (lp_data_config data s)) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains l r \<rho> k where "(l,r)\<in>set (pi_pairs sharp)"
    "(mencode sharp (lp_data_config data s),lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>(lp_clink C (set translated) U)\<^sup>*"
    "mencode sharp (lp_data_config data k)=lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    "lp_iminimal P k"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x))) b"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))) b"
proof -
  obtain x y where path: "(s,x)\<in>(lp_iframe P)\<^sup>*" and root: "(x,y)\<in>lp_iroot P"
    and bad: "\<not> SN_on (lp_imachine P) {y}"
    by (rule lp_iminimal_first_root[OF minimal]) blast
  obtain \<sigma> where top: "(lp_iconfig_subst x \<sigma>,y)\<in>lp_itop P"
    using root unfolding lp_iroot_def by blast
  obtain l r \<rho> k where pair: "(l,r)\<in>set (pi_pairs sharp)"
    and left: "mencode sharp (lp_data_config data (lp_iconfig_subst x \<sigma>))=lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    and right: "mencode sharp (lp_data_config data k)=lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    and min: "lp_iminimal P k"
    by (rule data_top_bad_pair[OF fixed top bad]) blast
  have inst0: "(mencode sharp (lp_data_config data x),
      lp_isubst (mencode sharp (lp_data_config data x)) (\<lambda>x. map_lp_iterm data id (\<sigma> x)))\<in>lp_clink C (set translated) U"
    unfolding lp_clink_def by blast
  have inst: "(mencode sharp (lp_data_config data x),lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>lp_clink C (set translated) U"
    using inst0 left by (simp add: lp_data_config_subst mencode_subst)
  have links: "(mencode sharp (lp_data_config data s),lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>(lp_clink C (set translated) U)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF data_iframes_constructor[where sharp=sharp,
      OF fixed range shapes frames marked path] inst])
  have ordinary: "(mencode sharp (lp_data_config data s),lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x)))\<in>(lp_pi_link (set translated))\<^sup>*"
    using links rtrancl_mono[OF lp_clink_ordinary] by blast
  obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval l (\<lambda>x. map_lp_iterm data id (\<rho> x))) b"
    by (rule lp_pi_links_projection[OF ordinary pr rv]) blast
  obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> (lp_ieval r (\<lambda>x. map_lp_iterm data id (\<rho> x))) c"
    by (rule lp_infinite_rule_projection[OF pb dv[OF pair] pair]) blast
  show ?thesis by (rule that[OF pair links right min]) (use pb pc in blast)+
qed

end
end
