(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Hybrid_Recursive_Subterm
  imports CSR_Frozen_Recursive_Subterm
begin

text \<open>
  A hybrid recursive projection may first select an active argument of a
  marked root and then select an inactive argument below an undefined
  constructor.  Rewriting may change the other active constructor arguments,
  but it cannot change the selected inactive argument.  This is the missing
  case between active CSR SCT and the directly frozen recursive criterion.
\<close>

definition csr_hybrid_one_layer_index ::
  "((('f,'l) lab) mu) \<Rightarrow> ((('f,'l) lab), 'v) rule set \<Rightarrow>
   ((('f,'l) lab) afs) \<Rightarrow> (('f,'l) lab) \<Rightarrow>
   ((('f,'l) lab) proj) \<Rightarrow> ((('f,'l) lab), 'v) term \<Rightarrow> bool"
where
  "csr_hybrid_one_layer_index \<mu> R \<pi> U p t \<longleftrightarrow>
    (case t of
      Fun (Sharp f) ts \<Rightarrow>
        let i = p (Sharp f, length ts)
        in i < length ts \<and> i \<in> \<mu> (f,length ts) \<and>
          (case ts ! i of
            Fun g us \<Rightarrow> \<not> defined R (g,length us) \<and>
              (case afs \<pi> (g,length us) of
                Collapse j \<Rightarrow> j < length us \<and>
                  j \<notin> \<mu> (g,length us)
              | _ \<Rightarrow> False)
          | Var _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

definition csr_hybrid_one_layer_index_list ::
  "((('f,'l) lab) mu) \<Rightarrow> ((('f,'l) lab), 'v) rules \<Rightarrow>
   ((('f,'l) lab) afs) \<Rightarrow> (('f,'l) lab) \<Rightarrow>
   ((('f,'l) lab) proj) \<Rightarrow> ((('f,'l) lab), 'v) term \<Rightarrow> bool"
where
  "csr_hybrid_one_layer_index_list \<mu> R \<pi> U p t \<longleftrightarrow>
    (case t of
      Fun (Sharp f) ts \<Rightarrow>
        let i = p (Sharp f, length ts)
        in i < length ts \<and> i \<in> \<mu> (f,length ts) \<and>
          (case ts ! i of
            Fun g us \<Rightarrow> (g,length us) \<notin> set (defined_list R) \<and>
              (case afs \<pi> (g,length us) of
                Collapse j \<Rightarrow> j < length us \<and>
                  j \<notin> \<mu> (g,length us)
              | _ \<Rightarrow> False)
          | Var _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

lemma csr_hybrid_one_layer_index_list_set [simp]:
  "csr_hybrid_one_layer_index_list \<mu> R \<pi> U p t =
    csr_hybrid_one_layer_index \<mu> (set R) \<pi> U p t"
  unfolding csr_hybrid_one_layer_index_list_def
    csr_hybrid_one_layer_index_def
  by (cases t; auto simp: Let_def set_defined_list
    split: lab.splits term.splits af_entry.splits)

lemma csr_hybrid_one_layer_index_shape:
  assumes valid: "csr_hybrid_one_layer_index \<mu> R \<pi> U p t"
  shows "csr_u3_mixed_term_shape U t"
  using valid
  unfolding csr_hybrid_one_layer_index_def
    csr_u3_mixed_term_shape_def
  by (cases t; auto split: lab.splits term.splits af_entry.splits)

definition csr_mixed_recursive_index ::
  "((('f,'l) lab) mu) \<Rightarrow> ((('f,'l) lab), 'v) rule set \<Rightarrow>
   ((('f,'l) lab) afs) \<Rightarrow> (('f,'l) lab) \<Rightarrow>
   ((('f,'l) lab) proj) \<Rightarrow> ((('f,'l) lab), 'v) term \<Rightarrow> bool"
where
  "csr_mixed_recursive_index \<mu> R \<pi> U p t \<longleftrightarrow>
    csr_frozen_projection_index \<mu> U p t \<or>
    csr_hybrid_one_layer_index \<mu> R \<pi> U p t"

lemma csr_mixed_recursive_index_shape:
  assumes "csr_mixed_recursive_index \<mu> R \<pi> U p t"
  shows "csr_u3_mixed_term_shape U t"
  using assms csr_frozen_projection_index_shape
    csr_hybrid_one_layer_index_shape
  unfolding csr_mixed_recursive_index_def by blast

lemma csr_frozen_hybrid_same_root_disjoint:
  assumes frozen: "csr_frozen_projection_index \<mu> U p t"
    and hybrid: "csr_hybrid_one_layer_index \<mu> R \<pi> U p s"
    and roots: "root s = root t"
  shows False
  using frozen hybrid roots
  unfolding csr_frozen_projection_index_def
    csr_hybrid_one_layer_index_def
  by (cases t; cases s; auto simp: Let_def
    split: lab.splits term.splits af_entry.splits)

lemma csr_hybrid_one_layer_indexE:
  assumes valid: "csr_hybrid_one_layer_index \<mu> R \<pi> U p t"
  obtains f ts i g us j where
    "t = Fun (Sharp f) ts"
    "i = p (Sharp f,length ts)"
    "i < length ts"
    "i \<in> \<mu> (f,length ts)"
    "ts ! i = Fun g us"
    "\<not> defined R (g,length us)"
    "afs \<pi> (g,length us) = Collapse j"
    "j < length us"
    "j \<notin> \<mu> (g,length us)"
proof (cases t)
  case (Var x)
  with valid show thesis
    unfolding csr_hybrid_one_layer_index_def by simp
next
  case (Fun a ts)
  note t_eq = Fun
  show thesis
  proof (cases a)
    case (Sharp f)
    let ?i = "p (Sharp f,length ts)"
    show thesis
    proof (cases "ts ! ?i")
      case (Var x)
      with valid Fun Sharp show thesis
        unfolding csr_hybrid_one_layer_index_def
        by (simp split: af_entry.splits)
    next
      case (Fun g us)
      note arg_eq = Fun
      show thesis
      proof (cases "afs \<pi> (g,length us)")
        case (Collapse j)
        have t_sharp: "t = Fun (Sharp f) ts" using t_eq Sharp by simp
        from valid t_eq Sharp arg_eq Collapse
        have i_bound: "?i < length ts"
          and i_active: "?i \<in> \<mu> (f,length ts)"
          and undef: "\<not> defined R (g,length us)"
          and j_bound: "j < length us"
          and j_inactive: "j \<notin> \<mu> (g,length us)"
          unfolding csr_hybrid_one_layer_index_def by (simp_all add: Let_def)
        show thesis by (rule that[OF t_sharp refl i_bound i_active
          arg_eq undef Collapse j_bound j_inactive])
      next
        case (AFList xs)
        with valid t_eq Sharp arg_eq show thesis
          unfolding csr_hybrid_one_layer_index_def by simp
      qed
    qed
  next
    case (Lab f l)
    with valid t_eq show thesis
      unfolding csr_hybrid_one_layer_index_def by simp
  next
    case (FunLab f ls)
    with valid t_eq show thesis
      unfolding csr_hybrid_one_layer_index_def by simp
  next
    case (UnLab f)
    with valid t_eq show thesis
      unfolding csr_hybrid_one_layer_index_def by simp
  qed
qed

lemma csstep_Fun_inactive_arg_preserved_plain:
  fixes g :: "(('f::{showl,compare_order},
    'l::{showl,compare_order}) lab)"
  assumes wf: "wf_trs R"
    and undef: "\<not> defined R (g,length ts)"
    and j: "j < length ts" "j \<notin> \<mu> (g,length ts)"
    and step: "(Fun g ts,v) \<in> csstep \<mu> R"
  shows "\<exists>us. v = Fun g us \<and> length us = length ts \<and>
    us ! j = ts ! j"
proof -
  from step obtain p lr \<sigma> where st:
      "(Fun g ts,v) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csstep_cond \<mu> p (Fun g ts)"
    unfolding csstep_def csstep_p_def by auto
  show ?thesis
  proof (cases p)
    case Nil
    from st Nil have lr: "lr \<in> R" and lhs: "fst lr \<cdot> \<sigma> = Fun g ts"
      unfolding rstep_r_p_s_def by (auto simp: Let_def)
    from wf lr have "is_Fun (fst lr)"
      unfolding wf_trs_def by (cases lr, force)
    then obtain h ss where l: "fst lr = Fun h ss" by (cases "fst lr"; auto)
    from lhs l have "h = g" "length ss = length ts" by auto
    with lr l have "defined R (g,length ts)"
      unfolding defined_def by (intro exI[of _ "fst lr"] exI[of _ "snd lr"],
        cases lr, auto)
    with undef show ?thesis by contradiction
  next
    case (Cons i q)
    from st Cons have iq: "i < length ts" "q \<in> poss (ts ! i)"
      unfolding rstep_r_p_s_def by (auto simp: Let_def)
    from cond Cons iq have active: "i \<in> \<mu> (g,length ts)"
      unfolding csstep_cond_def
      by (drule_tac x = "[]" in spec, drule_tac x = i in spec,
          drule_tac x = q in spec, auto)
    with j(2) have ij: "i \<noteq> j" by auto
    from st Cons have v:
      "v = Fun g (ts[i := replace_at (ts ! i) q (snd lr \<cdot> \<sigma>)])"
      unfolding rstep_r_p_s_def'
      using iq by (simp add: upd_conv_take_nth_drop)
    let ?us = "ts[i := replace_at (ts ! i) q (snd lr \<cdot> \<sigma>)]"
    have len: "length ?us = length ts" by simp
    have nth: "?us ! j = ts ! j"
      using j(1) iq(1) ij by simp
    show ?thesis
      using v len nth by blast
  qed
qed

lemma cssteps_preserve_one_inactive_layer:
  fixes g :: "(('f::{showl,compare_order},
    'l::{showl,compare_order}) lab)"
  assumes wf: "wf_trs R"
    and undef: "\<not> defined R (g,length ts)"
    and j: "j < length ts" "j \<notin> \<mu> (g,length ts)"
    and steps: "(Fun g ts,v) \<in> (csstep \<mu> R)\<^sup>*"
  shows "\<exists>us. v = Fun g us \<and> length us = length ts \<and>
    us ! j = ts ! j"
  using steps undef
proof (induct rule: rtrancl_induct)
  case base
  show ?case using j by auto
next
  case (step y z)
  from step.hyps(3)[OF step.prems] obtain ys where
    y: "y = Fun g ys" and len: "length ys = length ts"
    and same: "ys ! j = ts ! j" by blast
  have undef_y: "\<not> defined R (g,length ys)" using step.prems len by simp
  have j_y: "j < length ys" using j len by simp
  from csstep_Fun_inactive_arg_preserved_plain[
      OF wf undef_y j_y _ step.hyps(2)[unfolded y]]
  obtain zs where z: "z = Fun g zs" and zlen: "length zs = length ys"
    and zsame: "zs ! j = ys ! j"
    using j(2) len by auto
  show ?case
    unfolding z using zlen len zsame same by auto
qed

lemma csr_hybrid_one_layer_transition:
  fixes U :: "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab)"
    and \<pi> :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid_t: "csr_hybrid_one_layer_index \<mu> R \<pi> U p t"
    and valid_s: "csr_hybrid_one_layer_index \<mu> R \<pi> U p s"
    and target_SN: "SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>}"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "csr_frozen_recursive_view \<pi> p t \<cdot> af_subst \<pi> \<sigma> =
    csr_frozen_recursive_view \<pi> p s \<cdot> af_subst \<pi> \<tau>"
proof -
  from valid_t obtain f ts i g us j where
    t: "t = Fun (Sharp f) ts" and i: "i = p (Sharp f,length ts)"
    and i_bound: "i < length ts" and i_active: "i \<in> \<mu> (f,length ts)"
    and arg_t: "ts ! i = Fun g us"
    and undef_g: "\<not> defined R (g,length us)"
    and collapse_g: "afs \<pi> (g,length us) = Collapse j"
    and j_bound: "j < length us" and j_inactive: "j \<notin> \<mu> (g,length us)"
    by (rule csr_hybrid_one_layer_indexE)
  from valid_s obtain h ss k q vs m where
    s: "s = Fun (Sharp h) ss" and k: "k = p (Sharp h,length ss)"
    and k_bound: "k < length ss" and k_active: "k \<in> \<mu> (h,length ss)"
    and arg_s: "ss ! k = Fun q vs"
    and collapse_q: "afs \<pi> (q,length vs) = Collapse m"
    and m_bound: "m < length vs"
    by (rule csr_hybrid_one_layer_indexE)
  have shape_t: "csr_u3_mixed_term_shape U t"
    by (rule csr_hybrid_one_layer_index_shape[OF valid_t])
  have shape_s: "csr_u3_mixed_term_shape U s"
    by (rule csr_hybrid_one_layer_index_shape[OF valid_s])
  have roots: "root s = root t"
    by (rule csr_mixed_sct_root_transition[
      OF wf fresh_sharp fresh_U unsharp shape_t shape_s steps])
  from roots t s have hf: "h = f" and lens: "length ss = length ts" by auto
  have ki: "k = i" using k i hf lens by simp
  have index_t: "csr_sct_index t (Suc i)" using t i_bound by simp
  have index_s: "csr_sct_index s (Suc i)" using s k_bound ki by simp
  have outer_steps:
    "(ts ! i \<cdot> \<sigma>, ss ! i \<cdot> \<tau>) \<in> (csstep \<mu> R)\<^sup>*"
  proof -
    have "(get_arg t (Suc i) \<cdot> \<sigma>, get_arg s (Suc i) \<cdot> \<tau>) \<in>
        restrict_SN ((csstep \<mu> R)\<^sup>*) (csstep \<mu> R) \<union> Id"
      by (rule csr_sct_get_arg_transition[
        OF wf fresh_sharp index_t index_s target_SN steps])
    then show ?thesis
      unfolding restrict_SN_def using t s i_bound k_bound ki by auto
  qed
  have outer_steps':
    "(Fun g (map (\<lambda>u. u \<cdot> \<sigma>) us), ss ! i \<cdot> \<tau>) \<in>
      (csstep \<mu> R)\<^sup>*"
    using outer_steps arg_t by simp
  from cssteps_preserve_one_inactive_layer[
      OF wf _ _ _ outer_steps']
  obtain zs where finish: "ss ! i \<cdot> \<tau> = Fun g zs"
    and zs_len: "length zs = length us"
    and selected: "zs ! j = us ! j \<cdot> \<sigma>"
    using undef_g j_bound j_inactive by auto
  from finish arg_s ki have qg: "q = g"
    and maps: "map (\<lambda>u. u \<cdot> \<tau>) vs = zs" by auto
  have vs_len: "length vs = length us"
    using arg_cong[OF maps, of length] zs_len by simp
  from collapse_q collapse_g qg vs_len have mj: "m = j" by simp
  have selected_s: "vs ! j \<cdot> \<tau> = us ! j \<cdot> \<sigma>"
  proof -
    have "vs ! j \<cdot> \<tau> = map (\<lambda>u. u \<cdot> \<tau>) vs ! j"
      using j_bound vs_len by simp
    also have "... = zs ! j" using maps by simp
    also have "... = us ! j \<cdot> \<sigma>" by (rule selected)
    finally show ?thesis .
  qed
  have selected_af:
    "af_term \<pi> (vs ! j) \<cdot> af_subst \<pi> \<tau> =
      af_term \<pi> (us ! j) \<cdot> af_subst \<pi> \<sigma>"
    using arg_cong[OF selected_s, of "af_term \<pi>"]
    by (simp only: af_subst)
  have proj_t: "proj_term p t = Fun g us"
    using t i i_bound arg_t by (simp add: Let_def)
  have proj_s: "proj_term p s = Fun q vs"
    using s k k_bound arg_s by (simp add: Let_def)
  show ?thesis
    unfolding csr_frozen_recursive_view_def proj_t proj_s
    using collapse_g collapse_q qg j_bound m_bound selected_af mj
    by (simp only: af_term.simps apply_af_entry.simps nth_map)
qed

lemma csr_mixed_recursive_transition:
  fixes U :: "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab)"
    and \<pi> :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid_t: "csr_mixed_recursive_index \<mu> R \<pi> U p t"
    and valid_s: "csr_mixed_recursive_index \<mu> R \<pi> U p s"
    and target_SN: "SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>}"
    and steps: "(t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>*"
  shows "csr_frozen_recursive_view \<pi> p t \<cdot> af_subst \<pi> \<sigma> =
    csr_frozen_recursive_view \<pi> p s \<cdot> af_subst \<pi> \<tau>"
proof -
  have shape_t: "csr_u3_mixed_term_shape U t"
    by (rule csr_mixed_recursive_index_shape[OF valid_t])
  have shape_s: "csr_u3_mixed_term_shape U s"
    by (rule csr_mixed_recursive_index_shape[OF valid_s])
  have roots: "root s = root t"
    by (rule csr_mixed_sct_root_transition[
      OF wf fresh_sharp fresh_U unsharp shape_t shape_s steps])
  from valid_t consider
      (frozen) "csr_frozen_projection_index \<mu> U p t"
    | (hybrid) "csr_hybrid_one_layer_index \<mu> R \<pi> U p t"
    unfolding csr_mixed_recursive_index_def by blast
  then show ?thesis
  proof cases
    case frozen
    have frozen_s: "csr_frozen_projection_index \<mu> U p s"
    proof (rule ccontr)
      assume not_frozen_s: "\<not> csr_frozen_projection_index \<mu> U p s"
      from valid_s have hybrid_s:
          "csr_hybrid_one_layer_index \<mu> R \<pi> U p s"
        unfolding csr_mixed_recursive_index_def using not_frozen_s by blast
      show False by (rule csr_frozen_hybrid_same_root_disjoint[
        OF frozen hybrid_s roots])
    qed
    show ?thesis by (rule csr_frozen_projection_transition[
      OF wf fresh_sharp fresh_U unsharp frozen frozen_s steps])
  next
    case hybrid
    have hybrid_s: "csr_hybrid_one_layer_index \<mu> R \<pi> U p s"
    proof (rule ccontr)
      assume not_hybrid_s:
        "\<not> csr_hybrid_one_layer_index \<mu> R \<pi> U p s"
      from valid_s have frozen_s:
          "csr_frozen_projection_index \<mu> U p s"
        unfolding csr_mixed_recursive_index_def using not_hybrid_s by blast
      show False by (rule csr_frozen_hybrid_same_root_disjoint[
        OF frozen_s hybrid roots[symmetric]])
    qed
    show ?thesis by (rule csr_hybrid_one_layer_transition[
      OF wf fresh_sharp fresh_U unsharp hybrid hybrid_s target_SN steps])
  qed
qed

theorem finite_min_csr_dpp_recursive_subterm:
  fixes U :: "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab)"
    and p :: "((('f,'l) lab) proj)"
    and af :: "((('f,'l) lab)) afs"
    and V :: "((('f,'l) lab), 'v) term \<Rightarrow> bool"
  assumes valid: "\<forall>(u,v)\<in>P. V u \<and> V v"
    and transition: "\<And>t s \<sigma> \<tau>.
      V t \<Longrightarrow> V s \<Longrightarrow>
      SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>} \<Longrightarrow>
      (t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>* \<Longrightarrow>
      csr_frozen_recursive_view af p t \<cdot> af_subst af \<sigma> =
      csr_frozen_recursive_view af p s \<cdot> af_subst af \<tau>"
    and deleted: "D \<subseteq> P"
    and strict: "\<forall>(u,v)\<in>D.
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and weak: "\<forall>(u,v)\<in>P-D.
      csr_frozen_recursive_view af p u = csr_frozen_recursive_view af p v \<or>
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P-D) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof (rule ccontr)
  let ?RS = "csdp_step Sharp \<mu> R"
  let ?S = "{\<rhd>}"
  let ?W = "Id"
  assume not_fin: "\<not> finite_min_csr_dpp Sharp \<mu> P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<And>k. (s k,t k) \<in> P"
    and target_SN: "\<And>k. SN_on ?RS {t k \<cdot> \<sigma> k}"
    and steps: "\<And>k. (t k \<cdot> \<sigma> k,
      s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?RS\<^sup>*"
    by blast
  let ?view = "csr_frozen_recursive_view af p"
  let ?v = "\<lambda>k. ?view (s k) \<cdot> af_subst af (\<sigma> k)"
  have between: "?view (t k) \<cdot> af_subst af (\<sigma> k) =
      ?view (s (Suc k)) \<cdot> af_subst af (\<sigma> (Suc k))" for k
  proof -
    from valid pair[of k] have valid_t: "V (t k)" by auto
    from valid pair[of "Suc k"] have valid_s: "V (s (Suc k))" by auto
    show ?thesis by (rule transition[OF valid_t valid_s target_SN steps])
  qed
  have strict_step: "(u,v) \<in> D \<Longrightarrow>
      (?view u \<cdot> af_subst af \<rho>, ?view v \<cdot> af_subst af \<rho>) \<in> ?S"
    for u v \<rho>
    using strict supt_subst by blast
  have projected: "(?v k, ?v (Suc k)) \<in> ?S \<union> ?W" for k
  proof (cases "(s k,t k) \<in> D")
    case True
    have first: "(?v k, ?view (t k) \<cdot> af_subst af (\<sigma> k)) \<in> ?S"
      by (rule strict_step[OF True])
    with between[of k] show ?thesis by auto
  next
    case False
    with pair[of k] have residual: "(s k,t k) \<in> P-D" by auto
    from weak[rule_format, OF residual]
    consider (eq) "?view (s k) = ?view (t k)"
      | (sub) "?view (s k) \<rhd> ?view (t k)" by blast
    then show ?thesis
    proof cases
      case eq
      have "?v k = ?view (t k) \<cdot> af_subst af (\<sigma> k)"
        using eq by simp
      with between[of k] show ?thesis by auto
    next
      case sub
      have first: "(?v k, ?view (t k) \<cdot> af_subst af (\<sigma> k)) \<in> ?S"
        using supt_subst[OF sub, of "af_subst af (\<sigma> k)"] by simp
      with between[of k] show ?thesis by auto
    qed
  qed
  have proj_chain: "chain (?W \<union> ?S) ?v"
    using projected by (simp add: Un_commute)
  have compat: "?W O ?S \<subseteq> ?S" by auto
  have sn_on_S: "SN_on ?S {?v 0}"
    by (rule SN_on_subset2[OF _ SN_supt], simp)
  have "\<exists>j. \<forall>k\<ge>j. (?v k, ?v (Suc k)) \<in> ?W - ?S"
    by (rule non_strict_ending[OF proj_chain compat sn_on_S])
  then obtain j where tail: "\<And>k. k \<ge> j \<Longrightarrow>
    (?v k, ?v (Suc k)) \<in> ?W - ?S" by auto
  have pair_tail: "(s (k+j),t (k+j)) \<in> P-D" for k
  proof (rule DiffI)
    show "(s (k+j),t (k+j)) \<in> P" by (rule pair)
    show "(s (k+j),t (k+j)) \<notin> D"
    proof
      assume inD: "(s (k+j),t (k+j)) \<in> D"
      have first: "(?v (k+j), ?view (t (k+j)) \<cdot>
          af_subst af (\<sigma> (k+j))) \<in> ?S"
        by (rule strict_step[OF inD])
      with between[of "k+j"] have inS:
        "(?v (k+j), ?v (Suc (k+j))) \<in> ?S" by auto
      from tail[of "k+j"] inS show False by auto
    qed
  qed
  let ?ss = "shift s j"
  let ?tt = "shift t j"
  let ?\<tau> = "shift \<sigma> j"
  let ?RP = "csr_min_pair_step Sharp \<mu> (P-D) R"
  let ?rel = "?RS\<^sup>* O ?RP O ?RS\<^sup>*"
  let ?vals = "\<lambda>k. ?ss k \<cdot> ?\<tau> k"
  have rel_step: "(?vals k, ?vals (Suc k)) \<in> ?rel" for k
  proof -
    have pair_k: "(?ss k,?tt k) \<in> P-D" using pair_tail[of k] by simp
    have rr_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> rrstep (P-D)"
      unfolding rrstep_def' by (rule Quasi_Order.mem_rel_ofI, use pair_k in auto)
    have sn_k: "SN_on ?RS {?tt k \<cdot> ?\<tau> k}"
      using target_SN[of "k+j"] by simp
    have min_k: "(?ss k \<cdot> ?\<tau> k, ?tt k \<cdot> ?\<tau> k) \<in> ?RP"
      unfolding csr_min_pair_step_def using rr_k sn_k by auto
    have steps_k: "(?tt k \<cdot> ?\<tau> k, ?ss (Suc k) \<cdot> ?\<tau> (Suc k)) \<in> ?RS\<^sup>*"
      using steps[of "k+j"] by simp
    show ?thesis using min_k steps_k by auto
  qed
  have vals_chain: "chain ?rel ?vals" using rel_step by simp
  have "\<not> SN_on ?rel UNIV"
    by (rule not_SN_onI[OF _ vals_chain], simp)
  moreover from fin have "SN_on ?rel UNIV"
    unfolding finite_min_csr_dpp_def SN_rel_on_def .
  ultimately show False by contradiction
qed

theorem finite_min_csr_dpp_hybrid_recursive_subterm:
  fixes U :: "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab)"
    and p :: "((('f,'l) lab) proj)"
    and af :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid: "\<forall>(u,v)\<in>P.
      csr_hybrid_one_layer_index \<mu> R af U p u \<and>
      csr_hybrid_one_layer_index \<mu> R af U p v"
    and deleted: "D \<subseteq> P"
    and strict: "\<forall>(u,v)\<in>D.
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and weak: "\<forall>(u,v)\<in>P-D.
      csr_frozen_recursive_view af p u = csr_frozen_recursive_view af p v \<or>
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P-D) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  have transition: "\<And>t s \<sigma> \<tau>.
      csr_hybrid_one_layer_index \<mu> R af U p t \<Longrightarrow>
      csr_hybrid_one_layer_index \<mu> R af U p s \<Longrightarrow>
      SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>} \<Longrightarrow>
      (t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>* \<Longrightarrow>
      csr_frozen_recursive_view af p t \<cdot> af_subst af \<sigma> =
      csr_frozen_recursive_view af p s \<cdot> af_subst af \<tau>"
    by (rule csr_hybrid_one_layer_transition[
      OF wf fresh_sharp fresh_U unsharp])
  show ?thesis by (rule finite_min_csr_dpp_recursive_subterm[
    OF valid transition deleted strict weak fin])
qed

theorem finite_min_csr_dpp_mixed_recursive_subterm:
  fixes U :: "(('f::{showl,compare_order}, 'l::{showl,compare_order}) lab)"
    and p :: "((('f,'l) lab) proj)"
    and af :: "((('f,'l) lab)) afs"
  assumes wf: "wf_trs R"
    and fresh_sharp: "\<And>f n. \<not> defined R (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined R (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and valid: "\<forall>(u,v)\<in>P.
      csr_mixed_recursive_index \<mu> R af U p u \<and>
      csr_mixed_recursive_index \<mu> R af U p v"
    and deleted: "D \<subseteq> P"
    and strict: "\<forall>(u,v)\<in>D.
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and weak: "\<forall>(u,v)\<in>P-D.
      csr_frozen_recursive_view af p u = csr_frozen_recursive_view af p v \<or>
      csr_frozen_recursive_view af p u \<rhd>
      csr_frozen_recursive_view af p v"
    and fin: "finite_min_csr_dpp Sharp \<mu> (P-D) R"
  shows "finite_min_csr_dpp Sharp \<mu> P R"
proof -
  have transition: "\<And>t s \<sigma> \<tau>.
      csr_mixed_recursive_index \<mu> R af U p t \<Longrightarrow>
      csr_mixed_recursive_index \<mu> R af U p s \<Longrightarrow>
      SN_on (csdp_step Sharp \<mu> R) {t \<cdot> \<sigma>} \<Longrightarrow>
      (t \<cdot> \<sigma>, s \<cdot> \<tau>) \<in> (csdp_step Sharp \<mu> R)\<^sup>* \<Longrightarrow>
      csr_frozen_recursive_view af p t \<cdot> af_subst af \<sigma> =
      csr_frozen_recursive_view af p s \<cdot> af_subst af \<tau>"
    by (rule csr_mixed_recursive_transition[
      OF wf fresh_sharp fresh_U unsharp])
  show ?thesis by (rule finite_min_csr_dpp_recursive_subterm[
    OF valid transition deleted strict weak fin])
qed

definition csr_hybrid_projection_pair_valid where
  "csr_hybrid_projection_pair_valid \<mu> R \<pi> U p lr \<longleftrightarrow>
    (case lr of (l,r) \<Rightarrow>
      (csr_frozen_projection_index (mu_of \<mu>) U p l \<or>
       csr_hybrid_one_layer_index_list (mu_of \<mu>) R \<pi> U p l) \<and>
      (csr_frozen_projection_index (mu_of \<mu>) U p r \<or>
       csr_hybrid_one_layer_index_list (mu_of \<mu>) R \<pi> U p r))"

definition csr_hybrid_recursive_subterm_proc ::
  "('dpp, (('f::{showl,compare_order}, 'l::{showl,compare_order}) lab),
      string) dpp_ops \<Rightarrow>
   (('f,'l) lab) \<Rightarrow> (('f,'l) lab) muL \<Rightarrow>
   (('f,'l) lab) projL \<Rightarrow>
   ((((('f,'l) lab),string) rule \<times>
      ((('f,'l) lab),string) rseq) list) \<Rightarrow>
   ((('f,'l) lab),string) rules \<Rightarrow> 'dpp \<Rightarrow> 'dpp result"
where
  "csr_hybrid_recursive_subterm_proc J U \<mu> pL rseq Pr dpp =
    (case afs_of (csr_projection_collapsing_afs pL) of
      None \<Rightarrow> error (showsl_lit (STR ''invalid hybrid recursive projection''))
    | Some \<pi> \<Rightarrow> check_return (let
        p = create_proj pL;
        P = dpp_ops.pairs J dpp;
        R = dpp_ops.rules J dpp;
        (ps,pns) = dpp_ops.split_pairs J dpp Pr
        in check (rseq = [] \<and>
          list_all (csr_hybrid_projection_pair_valid \<mu> R \<pi> U p) P \<and>
          list_all (csr_frozen_projection_pair_strict \<pi> p) ps \<and>
          list_all (csr_frozen_projection_pair_weak \<pi> p) pns)
          (showsl_lit (STR ''invalid hybrid recursive CSR subterm criterion'')))
        (dpp_spec.delete_pairs J dpp Pr))"

lemma csr_hybrid_recursive_subterm_proc_sound:
  fixes J :: "('dpp, (('f::{showl,compare_order},
      'l::{showl,compare_order}) lab),string) dpp_ops"
  assumes J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh_sharp: "\<And>f n.
      \<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and fresh_U: "\<And>n. \<not> defined (set (dpp_ops.rules J dpp)) (U,n)"
    and unsharp: "\<not> is_sharp_lab U"
    and proc: "csr_hybrid_recursive_subterm_proc J U \<mu> pL rseq Pr dpp = return dpp'"
    and fin: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (dpp_ops.pairs J dpp')) (set (dpp_ops.rules J dpp'))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  interpret dpp_spec J by fact
  obtain \<pi> where af: "afs_of (csr_projection_collapsing_afs pL) = Some \<pi>"
    using proc unfolding csr_hybrid_recursive_subterm_proc_def
    by (cases "afs_of (csr_projection_collapsing_afs pL)"; auto)
  obtain ps pns where split: "split_pairs dpp Pr = (ps,pns)" by force
  from split_pairs_sound[OF split]
  have ps: "set ps = set (pairs dpp) \<inter> set Pr"
    and pns: "set pns = set (pairs dpp) - set Pr" by auto
  let ?p = "create_proj pL"
  note ok = proc[unfolded csr_hybrid_recursive_subterm_proc_def af split Let_def,
    simplified]
  from ok have valid: "\<forall>(u,v)\<in>set (pairs dpp).
      csr_mixed_recursive_index (mu_of \<mu>) (set (rules dpp)) \<pi> U ?p u \<and>
      csr_mixed_recursive_index (mu_of \<mu>) (set (rules dpp)) \<pi> U ?p v"
    by (auto simp: list_all_iff csr_hybrid_projection_pair_valid_def
      csr_mixed_recursive_index_def)
  from ok have strict: "\<forall>(u,v)\<in>set ps.
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v"
    by (auto simp: list_all_iff csr_frozen_projection_pair_strict_def)
  from ok have weak: "\<forall>(u,v)\<in>set pns.
      csr_frozen_recursive_view \<pi> ?p u = csr_frozen_recursive_view \<pi> ?p v \<or>
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v"
    by (auto simp: list_all_iff csr_frozen_projection_pair_weak_def)
  from ok have dpp': "dpp' = delete_pairs dpp Pr" by auto
  have sem: "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS dpp,M dpp,set (P dpp) - set Pr,
       set (Pw dpp) - set Pr,set (Q dpp),set (R dpp),set (Rw dpp))"
    by (rule delete_P_Pw_sound)
  have sem': "dpp_ops.dpp J (delete_pairs dpp Pr) =
      (NFS (delete_pairs dpp Pr),M (delete_pairs dpp Pr),
       set (P (delete_pairs dpp Pr)),set (Pw (delete_pairs dpp Pr)),
       set (Q (delete_pairs dpp Pr)),set (R (delete_pairs dpp Pr)),
       set (Rw (delete_pairs dpp Pr)))" by (rule dpp_sound)
  from plain have plain_fields:
      "set (pairs dpp) = set (P dpp)" "set (Pw dpp) = {}"
    unfolding plain_csr_dpp_def using pairs_sound[of dpp] by auto
  have pairs': "set (pairs dpp') = set (pairs dpp) - set Pr"
    using sem sem' dpp' plain_fields pairs_sound[of "delete_pairs dpp Pr"] by auto
  have rules': "set (rules dpp') = set (rules dpp)"
    using sem sem' dpp' rules_sound[of dpp]
      rules_sound[of "delete_pairs dpp Pr"] by auto
  have remaining: "set (pairs dpp) - set ps = set (pairs dpp) - set Pr"
    using ps by auto
  have fin_res: "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))"
    using fin pairs' rules' remaining by simp
  show ?thesis
  proof (rule finite_min_csr_dpp_mixed_recursive_subterm[
      where D="set ps" and p="?p" and af=\<pi> and U=U])
    show "wf_trs (set (rules dpp))" by (rule wf)
    show "\<And>f n. \<not> defined (set (rules dpp)) (Sharp f,n)"
      by (rule fresh_sharp)
    show "\<And>n. \<not> defined (set (rules dpp)) (U,n)" by (rule fresh_U)
    show "\<not> is_sharp_lab U" by (rule unsharp)
    show "\<forall>(u,v)\<in>set (pairs dpp).
      csr_mixed_recursive_index (mu_of \<mu>) (set (rules dpp)) \<pi> U ?p u \<and>
      csr_mixed_recursive_index (mu_of \<mu>) (set (rules dpp)) \<pi> U ?p v"
      by (rule valid)
    show "set ps \<subseteq> set (pairs dpp)" using ps by auto
    show "\<forall>(u,v)\<in>set ps.
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v" by (rule strict)
    show "\<forall>(u,v)\<in>set (pairs dpp) - set ps.
      csr_frozen_recursive_view \<pi> ?p u = csr_frozen_recursive_view \<pi> ?p v \<or>
      csr_frozen_recursive_view \<pi> ?p u \<rhd>
      csr_frozen_recursive_view \<pi> ?p v" using pns weak ps by auto
    show "finite_min_csr_dpp Sharp (mu_of \<mu>)
      (set (pairs dpp) - set ps) (set (rules dpp))" by (rule fin_res)
  qed
qed

end
