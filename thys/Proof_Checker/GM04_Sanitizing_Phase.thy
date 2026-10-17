theory GM04_Sanitizing_Phase
  imports Proof_Checker.GM04_Complete_Transformation
begin

definition gm04_sanitizing_phase_rel ::
    "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> bool) rel" where
  "gm04_sanitizing_phase_rel R source =
    {p. \<exists>s t. p = ((s,False),(t,True)) \<and>
      (source s \<longrightarrow> (s,t) \<in> R)} \<union>
    {p. \<exists>s. p = ((s,True),(s,False)) \<and> source s}"

lemma gm04_sanitizing_phase_rel_cases:
  assumes step: "(x,y) \<in> gm04_sanitizing_phase_rel R source"
  obtains s t where "x = (s,False)" "y = (t,True)"
      "source s \<Longrightarrow> (s,t) \<in> R"
    | s where "x = (s,True)" "y = (s,False)" "source s"
  using step unfolding gm04_sanitizing_phase_rel_def by auto

lemma gm04_sanitizing_phase_alternates:
  assumes step: "(x,y) \<in> gm04_sanitizing_phase_rel R source"
  shows "snd y = (\<not> snd x)"
proof -
  from gm04_sanitizing_phase_rel_cases[OF step]
  show ?thesis by cases simp_all
qed

lemma gm04_sanitizing_phase_false_source:
  assumes first: "(x,y) \<in> gm04_sanitizing_phase_rel R source"
    and second: "(y,z) \<in> gm04_sanitizing_phase_rel R source"
    and false: "snd z = False"
  shows "source (fst z)"
proof -
  from gm04_sanitizing_phase_rel_cases[OF second]
  show ?thesis using false by cases auto
qed

lemma gm04_sanitizing_phase_two_steps:
  assumes first: "(x,y) \<in> gm04_sanitizing_phase_rel R source"
    and second: "(y,z) \<in> gm04_sanitizing_phase_rel R source"
    and false: "snd x = False"
    and source: "source (fst x)"
  shows "(fst x,fst z) \<in> R"
proof -
  from gm04_sanitizing_phase_rel_cases[OF first]
  obtain s t where x: "x = (s,False)" and y: "y = (t,True)"
    and st: "source s \<Longrightarrow> (s,t) \<in> R"
    using false by cases auto
  from gm04_sanitizing_phase_rel_cases[OF second]
  obtain u where y': "y = (u,True)" and z: "z = (u,False)"
    using y by cases auto
  from source st x y y' z show ?thesis by simp
qed

lemma gm04_SN_sanitizing_phase_rel:
  assumes SN: "SN R"
  shows "SN (gm04_sanitizing_phase_rel R source)"
proof (unfold SN_on_def, intro notI)
  assume "\<exists>f. f 0 \<in> UNIV \<and>
      chain (gm04_sanitizing_phase_rel R source) f"
  then obtain f where chain:
      "chain (gm04_sanitizing_phase_rel R source) f" by auto
  have step: "(f i,f (Suc i)) \<in> gm04_sanitizing_phase_rel R source"
    for i using chain unfolding chain_def by blast
  let ?k = "if snd (f 0) = False then Suc (Suc 0) else Suc 0"
  have k_false: "snd (f ?k) = False"
  proof (cases "snd (f 0) = False")
    case True
    from gm04_sanitizing_phase_alternates[OF step[of 0]]
      gm04_sanitizing_phase_alternates[OF step[of 1]] True
    show ?thesis by auto
  next
    case False
    from gm04_sanitizing_phase_alternates[OF step[of 0]] False
    show ?thesis by simp
  qed
  have k_source: "source (fst (f ?k))"
  proof (cases "snd (f 0) = False")
    case True
    have zfalse: "snd (f (Suc (Suc 0))) = False"
      using k_false True by simp
    have src: "source (fst (f (Suc (Suc 0))))"
      by (rule gm04_sanitizing_phase_false_source[
          OF step[of 0] step[of "Suc 0"] zfalse])
    show ?thesis using src True by simp
  next
    case False
    from gm04_sanitizing_phase_rel_cases[OF step[of 0]]
    have src: "source (fst (f (Suc 0)))" using False by cases auto
    show ?thesis using src False by simp
  qed
  let ?g = "\<lambda>n. fst (f (?k + 2*n))"
  have false_tail: "snd (f (?k + 2*n)) = False" for n
  proof (induct n)
    case 0
    show ?case using k_false by simp
  next
    case (Suc n)
    from gm04_sanitizing_phase_alternates[OF step[of "?k + 2*n"]]
      gm04_sanitizing_phase_alternates[OF step[of "Suc (?k + 2*n)"]]
      Suc
    show ?case by (simp add: algebra_simps)
  qed
  have source_tail: "source (fst (f (?k + 2*n)))" for n
  proof (induct n)
    case 0
    show ?case using k_source by simp
  next
    case (Suc n)
    have target_index: "Suc (Suc (?k + 2*n)) = ?k + 2 * Suc n"
      by simp
    have zfalse: "snd (f (Suc (Suc (?k + 2*n)))) = False"
      using false_tail[of "Suc n"] target_index by simp
    have raw: "source (fst (f (Suc (Suc (?k + 2*n)))))"
      by (rule gm04_sanitizing_phase_false_source[
          OF step[of "?k + 2*n"] step[of "Suc (?k + 2*n)"] zfalse])
    show ?case using raw target_index by simp
  qed
  have projected: "(?g n,?g (Suc n)) \<in> R" for n
  proof -
    have target_index: "Suc (Suc (?k + 2*n)) = ?k + 2 * Suc n"
      by simp
    have raw: "(fst (f (?k + 2*n)),
        fst (f (Suc (Suc (?k + 2*n))))) \<in> R"
      by (rule gm04_sanitizing_phase_two_steps[
          OF step[of "?k + 2*n"] step[of "Suc (?k + 2*n)"]
            false_tail source_tail])
    show ?thesis using raw target_index by simp
  qed
  have "chain R ?g" using projected unfolding chain_def by blast
  then have not_SN: "\<not> SN R" by (rule not_SN_onI[OF UNIV_I])
  show False by (rule notE[OF not_SN SN])
qed

theorem gm04_finite_dpp_from_pair_connectors_sanitizing:
  fixes decode ::
    "(('f,string) term \<times> ('f,string) term) \<Rightarrow> ('a \<times> bool)"
  assumes source_SN: "SN R"
    and simulation: "\<And>l r l' r'.
      (l,r) \<in> subst.closure P \<Longrightarrow>
      (l',r') \<in> subst.closure P \<Longrightarrow>
      (r,l') \<in> (rstep S)\<^sup>* \<Longrightarrow>
      (decode (l,r), decode (l',r'))
        \<in> gm04_sanitizing_phase_rel R source"
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
  have phases: "chain (gm04_sanitizing_phase_rel R source)
      (\<lambda>i. decode (?pair i))"
    unfolding chain_def
  proof
    fix i
    show "(decode (?pair i),decode (?pair (Suc i)))
        \<in> gm04_sanitizing_phase_rel R source"
      by (rule simulation[OF pair[of i] pair[of "Suc i"] connector[of i]])
  qed
  from phases have "\<not> SN (gm04_sanitizing_phase_rel R source)"
    by (rule not_SN_onI[OF UNIV_I])
  with gm04_SN_sanitizing_phase_rel[OF source_SN] show False
    by contradiction
qed

lemma gm04_constant_subst_ground:
  assumes "ground c"
  shows "ground (t \<cdot> (\<lambda>_. c))"
  using assms by (induct t) auto

lemma gm04_qrsteps_count_first_root:
  assumes steps: "(s,t) \<in> (qrstep nfs Q S) ^^ n"
    and roots: "root s \<noteq> root t"
  shows "\<exists>k m u v.
      n = k + Suc m \<and>
      (s,u) \<in> (nrqrstep nfs Q S) ^^ k \<and>
      (u,v) \<in> rqrstep nfs Q S \<and>
      (v,t) \<in> (qrstep nfs Q S) ^^ m"
  using steps roots
proof (induct n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from relpow_Suc_D2[OF Suc.prems(1)]
  obtain z where first: "(s,z) \<in> qrstep nfs Q S"
    and rest: "(z,t) \<in> (qrstep nfs Q S) ^^ n" by blast
  from first consider
      (root) "(s,z) \<in> rqrstep nfs Q S"
    | (below) "(s,z) \<in> nrqrstep nfs Q S"
    unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
  then show ?case
  proof cases
    case root
    show ?thesis
    proof (intro exI conjI)
      show "Suc n = 0 + Suc n" by simp
      show "(s,s) \<in> (nrqrstep nfs Q S) ^^ 0" by simp
      show "(s,z) \<in> rqrstep nfs Q S" by (rule root)
      show "(z,t) \<in> (qrstep nfs Q S) ^^ n" by (rule rest)
    qed
  next
    case below
    have same_root: "root s = root z"
      by (rule nrqrstep_preserves_root[OF below])
    have different: "root z \<noteq> root t"
      using Suc.prems(2) same_root by simp
    from Suc.hyps[OF rest different]
    obtain k m u v where count: "n = k + Suc m"
      and prefix: "(z,u) \<in> (nrqrstep nfs Q S) ^^ k"
      and root_step: "(u,v) \<in> rqrstep nfs Q S"
      and suffix: "(v,t) \<in> (qrstep nfs Q S) ^^ m" by blast
    have prefix': "(s,u) \<in> (nrqrstep nfs Q S) ^^ Suc k"
      using below prefix by (rule relpow_Suc_I2)
    show ?thesis
    proof (intro exI conjI)
      show "Suc n = Suc k + Suc m" using count by simp
      show "(s,u) \<in> (nrqrstep nfs Q S) ^^ Suc k" by (rule prefix')
      show "(u,v) \<in> rqrstep nfs Q S" by (rule root_step)
      show "(v,t) \<in> (qrstep nfs Q S) ^^ m" by (rule suffix)
    qed
  qed
qed

theorem gm04_finite_dpp_from_ground_pair_connectors_sanitizing:
  fixes decode ::
    "(('f,string) term \<times> ('f,string) term) \<Rightarrow> ('a \<times> bool)"
    and c :: "('f,string) term"
  assumes source_SN: "SN R"
    and ground_c: "ground c"
    and simulation: "\<And>l r l' r'.
      (l,r) \<in> subst.closure P \<Longrightarrow>
      (l',r') \<in> subst.closure P \<Longrightarrow>
      (r,l') \<in> (rstep S)\<^sup>* \<Longrightarrow>
      ground l \<Longrightarrow> ground r \<Longrightarrow>
      ground l' \<Longrightarrow> ground r' \<Longrightarrow>
      (decode (l,r), decode (l',r'))
        \<in> gm04_sanitizing_phase_rel R source"
  shows "finite_dpp (False,False,P,{},{},{},S)"
proof (rule ccontr)
  assume "\<not> finite_dpp (False,False,P,{},{},{},S)"
  then obtain s t \<sigma> where chain:
      "min_ichain (False,False,P,{},{},{},S) s t \<sigma>"
    unfolding finite_dpp_def by blast
  let ?g = "\<lambda>(_::string). c"
  let ?\<tau> = "\<lambda>i. \<sigma> i \<circ>\<^sub>s ?g"
  let ?pair = "\<lambda>i. (s i \<cdot> ?\<tau> i, t i \<cdot> ?\<tau> i)"
  have ichain: "ichain (False,False,P,{},{},{},S) s t \<sigma>"
    using chain by simp
  have pair: "\<And>i. ?pair i \<in> subst.closure P"
  proof -
    fix i
    from ichain have raw: "(s i,t i) \<in> P"
      by (simp add: ichain.simps)
    show "?pair i \<in> subst.closure P"
      by (rule subst.closureI2[OF raw, where
            a="\<sigma> i \<circ>\<^sub>s (\<lambda>(_::string). c)"], simp_all)
  qed
  have connector: "\<And>i. (t i \<cdot> ?\<tau> i,
      s (Suc i) \<cdot> ?\<tau> (Suc i))
      \<in> (rstep S)\<^sup>*"
  proof -
    fix i
    have raw: "(t i \<cdot> \<sigma> i,
        s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep S)\<^sup>*"
      using ichain by (simp add: ichain.simps)
    from subst.closedD[OF
        subst.closed_rtrancl[OF subst_closed_rstep] raw, of ?g]
    show "(t i \<cdot> ?\<tau> i,
        s (Suc i) \<cdot> ?\<tau> (Suc i)) \<in> (rstep S)\<^sup>*"
      by (simp add: subst_subst_compose)
  qed
  have ground_pair: "\<And>i. ground (fst (?pair i)) \<and>
      ground (snd (?pair i))"
  proof -
    fix i
    have gs: "ground ((s i \<cdot> \<sigma> i) \<cdot> ?g)"
      by (rule gm04_constant_subst_ground[OF ground_c])
    have gt: "ground ((t i \<cdot> \<sigma> i) \<cdot> ?g)"
      by (rule gm04_constant_subst_ground[OF ground_c])
    from gs gt show "ground (fst (?pair i)) \<and> ground (snd (?pair i))"
      by (simp add: subst_subst_compose)
  qed
  have phases: "chain (gm04_sanitizing_phase_rel R source)
      (\<lambda>i. decode (?pair i))"
    unfolding chain_def
  proof
    fix i
    from ground_pair[of i] ground_pair[of "Suc i"]
    show "(decode (?pair i),decode (?pair (Suc i)))
        \<in> gm04_sanitizing_phase_rel R source"
      by (intro simulation[OF pair[of i] pair[of "Suc i"]
            connector[of i]]) simp_all
  qed
  from phases have "\<not> SN (gm04_sanitizing_phase_rel R source)"
    by (rule not_SN_onI[OF UNIV_I])
  with gm04_SN_sanitizing_phase_rel[OF source_SN] show False
    by contradiction
qed

theorem gm04_finite_exact_top_pairs_sanitizing:
  fixes S :: "('f,string) trs"
  assumes source_SN: "SN R"
    and wf: "wf_trs S"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and ok_mark: "ok \<noteq> mark"
    and active_ok_impossible: "\<And>x y.
      (Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and proper_mark_impossible: "\<And>x y.
      (Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and active_mark: "\<And>x y. source x \<Longrightarrow>
      (Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow>
      (x,y) \<in> R"
    and proper_ok: "\<And>x y.
      (Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow>
      x = y \<and> source y"
  shows "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
proof (rule gm04_finite_dpp_from_pair_connectors_sanitizing[
    OF source_SN, where decode="gm04_decode_top_pair mark"])
  fix l r l' r'
  assume first: "(l,r) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and second: "(l',r') \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and connector: "(r,l') \<in> (rstep S)\<^sup>*"
  from gm04_top_pair_instance_cases[OF first]
  show "(gm04_decode_top_pair mark (l,r),gm04_decode_top_pair mark (l',r'))
      \<in> gm04_sanitizing_phase_rel R source"
  proof cases
    case (1 x)
    note first_ok = 1
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      note second_ok = 1
      from connector first_ok second_ok
      have inner: "(Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis by (rule FalseE[OF active_ok_impossible[OF inner]])
    next
      case (2 y)
      note second_mark = 2
      from connector first_ok second_mark
      have inner: "(Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis
        unfolding gm04_decode_top_pair_def gm04_sanitizing_phase_rel_def
        using first_ok second_mark active_mark[OF _ inner]
        by (auto simp: ok_mark)
    qed
  next
    case (2 x)
    note first_mark = 2
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      note second_ok = 1
      from connector first_mark second_ok
      have inner: "(Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from proper_ok[OF inner] first_mark second_ok show ?thesis
        unfolding gm04_decode_top_pair_def gm04_sanitizing_phase_rel_def
        by (auto simp: ok_mark)
    next
      case (2 y)
      note second_mark = 2
      from connector first_mark second_mark
      have inner: "(Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis by (rule FalseE[OF proper_mark_impossible[OF inner]])
    qed
  qed
qed

theorem gm04_finite_exact_top_pairs_ground_sanitizing:
  fixes S :: "('f,string) trs" and c :: "('f,string) term"
  assumes source_SN: "SN R"
    and ground_c: "ground c"
    and wf: "wf_trs S"
    and fresh_top: "\<not> defined S (top_sharp,1)"
    and ok_mark: "ok \<noteq> mark"
    and active_ok_impossible: "\<And>x y.
      ground x \<Longrightarrow> ground y \<Longrightarrow>
      (Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and proper_mark_impossible: "\<And>x y.
      ground x \<Longrightarrow> ground y \<Longrightarrow>
      (Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow> False"
    and active_mark: "\<And>x y. ground x \<Longrightarrow> ground y \<Longrightarrow>
      source x \<Longrightarrow>
      (Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow>
      (x,y) \<in> R"
    and proper_ok: "\<And>x y. ground x \<Longrightarrow> ground y \<Longrightarrow>
      (Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>* \<Longrightarrow>
      x = y \<and> source y"
  shows "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
proof (rule gm04_finite_dpp_from_ground_pair_connectors_sanitizing[
    OF source_SN ground_c, where decode="gm04_decode_top_pair mark"])
  fix l r l' r'
  assume first: "(l,r) \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and second: "(l',r') \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
    and connector: "(r,l') \<in> (rstep S)\<^sup>*"
    and ground_l: "ground l" and ground_r: "ground r"
    and ground_l': "ground l'" and ground_r': "ground r'"
  from gm04_top_pair_instance_cases[OF first]
  show "(gm04_decode_top_pair mark (l,r),gm04_decode_top_pair mark (l',r'))
      \<in> gm04_sanitizing_phase_rel R source"
  proof cases
    case (1 x)
    note first_ok = 1
    have ground_x: "ground x" using ground_l first_ok by simp
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      note second_ok = 1
      have ground_y: "ground y" using ground_l' second_ok by simp
      from connector first_ok second_ok
      have inner: "(Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis by (rule FalseE[OF active_ok_impossible[
          OF ground_x ground_y inner]])
    next
      case (2 y)
      note second_mark = 2
      have ground_y: "ground y" using ground_l' second_mark by simp
      from connector first_ok second_mark
      have inner: "(Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis
        unfolding gm04_decode_top_pair_def gm04_sanitizing_phase_rel_def
        using first_ok second_mark active_mark[OF ground_x ground_y _ inner]
        by (auto simp: ok_mark)
    qed
  next
    case (2 x)
    note first_mark = 2
    have ground_x: "ground x" using ground_l first_mark by simp
    from gm04_top_pair_instance_cases[OF second]
    show ?thesis
    proof cases
      case (1 y)
      note second_ok = 1
      have ground_y: "ground y" using ground_l' second_ok by simp
      from connector first_mark second_ok
      have inner: "(Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      from proper_ok[OF ground_x ground_y inner] first_mark second_ok
      show ?thesis
        unfolding gm04_decode_top_pair_def gm04_sanitizing_phase_rel_def
        by (auto simp: ok_mark)
    next
      case (2 y)
      note second_mark = 2
      have ground_y: "ground y" using ground_l' second_mark by simp
      from connector first_mark second_mark
      have inner: "(Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
        using gm04_top_wrapper_rsteps_iff[OF wf fresh_top] by simp
      show ?thesis by (rule FalseE[OF proper_mark_impossible[
          OF ground_x ground_y inner]])
    qed
  qed
qed

lemma gm04_non_top_steps_to_source_are_identity:
  fixes S :: "('f,string) trs"
  assumes S: "S = set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and steps: "(s,t) \<in> (rstep S)\<^sup>*"
    and source: "funas_term t \<subseteq> set F"
  shows "s = t"
  using steps source
proof (induct rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  from step.hyps(2) step.prems
  have False by (rule gm04_non_top_step_cannot_produce_source[OF fresh S])
  then show ?case by (rule FalseE)
qed

lemma gm04_ground_fun_arg:
  assumes "ground (Fun f xs)" "q \<in> set xs"
  shows "ground q"
  using assms by simp

lemma gm04_ground_wrapped_fun_arg:
  assumes "ground (Fun f (map (\<lambda>x. Fun g [x]) xs))"
    and "q \<in> set xs"
  shows "ground q"
  using assms by auto

lemma gm04_ground_fun_update_wrapper:
  assumes "ground (Fun f xs)" and "i < length xs"
  shows "ground (Fun f (xs[i := Fun g [xs ! i]]))"
  using assms
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases i) auto
qed

lemma gm04_source_term_FunI:
  assumes ground: "ground (Fun f xs)"
    and root: "(f,length xs) \<in> set F"
    and args: "\<And>x. x \<in> set xs \<Longrightarrow> gm04_source_term F x"
  shows "gm04_source_term F (Fun f xs)"
  using ground root args unfolding gm04_source_term_def by auto

lemma gm04_root_source_step_to_ok_cases_full:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source_root: "(f,length zs) \<in> set F"
    and root_step: "(Fun f zs,u) \<in> rqrstep True {} S"
    and suffix: "(u,Fun ok [y]) \<in> (qrstep True {} S)\<^sup>*"
  obtains \<sigma> where
      "zs = map (\<lambda>x. Fun ok [x \<cdot> \<sigma>])
        (gm04_vars (length zs))"
      "u = Fun ok [Fun f
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
proof (rule gm04_root_source_step_to_ok_cases[
    OF S fresh source_root root_step suffix])
  fix \<sigma>
  assume zs: "zs = map (\<lambda>x. Fun ok [x \<cdot> \<sigma>])
      (gm04_vars (length zs))"
    and u: "u = Fun ok [Fun f
      (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
  show thesis by (rule that[OF zs u])
qed

lemma gm04_proper_ok_ground_converse_count:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and wf: "wf_trs S"
    and ground_x: "ground x"
    and ground_y: "ground y"
    and steps: "(Fun proper [x],Fun ok [y]) \<in> (rstep S) ^^ n"
  shows "x = y \<and> gm04_source_term F y"
  using ground_x ground_y steps
proof (induct n arbitrary: x y rule: less_induct)
  case (less n)
  from fresh have different: "root (Fun proper [x]) \<noteq> root (Fun ok [y])"
    unfolding gm04_roles_fresh_def by simp
  have qsteps: "(Fun proper [x],Fun ok [y])
      \<in> (qrstep True {} S) ^^ n"
    using less.prems(3) by simp
  from gm04_qrsteps_count_first_root[
      OF qsteps different]
  obtain k m u v where count: "n = k + Suc m"
    and prefix: "(Fun proper [x],u) \<in> (nrqrstep True {} S) ^^ k"
    and root_step: "(u,v) \<in> rqrstep True {} S"
    and suffix: "(v,Fun ok [y]) \<in> (qrstep True {} S) ^^ m"
    by blast
  from nrqrsteps_preserve_root_fun[OF relpow_imp_rtrancl[OF prefix]]
  obtain us where u: "u = Fun proper us" by blast
  have len_us: "length us = 1"
    using nrqrsteps_num_args[OF relpow_imp_rtrancl[OF prefix]] unfolding u by simp
  then obtain z where us: "us = [z]" by (cases us) auto
  have arg_prefix_count: "\<exists>j\<le>k. (x,z) \<in> (rstep S) ^^ j"
    using nrqrsteps_imp_arg_qrsteps_count[OF prefix, of 0]
    unfolding u us by simp
  from gm04_root_proper_step_cases[OF S fresh root_step[unfolded u us]]
  obtain f ar \<sigma> where fn: "(f,ar) \<in> set F"
    and z: "z = Fun f (map (\<lambda>w. w \<cdot> \<sigma>) (gm04_vars ar))"
    and v: "v = snd (gm04_proper_rule proper ok (f,ar)) \<cdot> \<sigma>" .
  have ground_z: "ground z"
  proof -
    from arg_prefix_count obtain j where path: "(x,z) \<in> (rstep S) ^^ j" by blast
    show ?thesis
      by (rule rsteps_ground[OF _ less.prems(1) relpow_imp_rtrancl[OF path]],
          use wf in \<open>simp add: wf_trs_def\<close>)
  qed
  show ?case
  proof (cases "ar = 0")
    case True
    then have v_ok: "v = Fun ok [z]"
      using v z by (simp add: gm04_proper_rule_def Let_def)
    have zy: "(z,y) \<in> (rstep S)\<^sup>*"
      using relpow_imp_rtrancl[OF suffix] v_ok
        gm04_non_top_role_wrapper_rsteps_iff[OF S wf fresh, of ok z y]
      by simp
    have source_z: "gm04_source_term F z"
      using ground_z fn z True unfolding gm04_source_term_def by simp
    have nf_z: "z \<in> NF (rstep S)"
      using gm04_source_term_no_non_top_step[OF S fresh source_z]
      unfolding NF_def by blast
    have eq: "z = y"
      using zy nf_z by (rule NF_not_suc)
    from arg_prefix_count obtain j where xz: "(x,z) \<in> (rstep S) ^^ j" by blast
    have xeq: "x = z"
      by (rule gm04_non_top_steps_to_source_are_identity[
        OF S fresh relpow_imp_rtrancl[OF xz]],
        use source_z in \<open>simp add: gm04_source_term_def\<close>)
    show ?thesis using eq xeq source_z by simp
  next
    case False
    let ?xs = "map (\<lambda>w. w \<cdot> \<sigma>) (gm04_vars ar)"
    have v_expand: "v = Fun f (map (\<lambda>w. Fun proper [w]) ?xs)"
      by (rule gm04_proper_rule_rhs_nonzero_instance[OF False v refl refl])
    from fresh fn have f_ok: "f \<noteq> ok"
      unfolding gm04_roles_fresh_def by auto
    have roots2: "root v \<noteq> root (Fun ok [y])"
      unfolding v_expand using f_ok by simp
    from gm04_qrsteps_count_first_root[
        OF suffix roots2]
    obtain k2 m2 u2 v2 where count2: "m = k2 + Suc m2"
      and prefix2: "(v,u2) \<in> (nrqrstep True {} S) ^^ k2"
      and root2: "(u2,v2) \<in> rqrstep True {} S"
      and suffix2: "(v2,Fun ok [y]) \<in> (qrstep True {} S) ^^ m2"
      by blast
    from nrqrsteps_preserve_root_fun[
        OF relpow_imp_rtrancl[OF prefix2[unfolded v_expand]]]
    obtain zs where u2: "u2 = Fun f zs" by blast
    have len_zs: "length zs = length ?xs"
      using nrqrsteps_num_args[
        OF relpow_imp_rtrancl[OF prefix2[unfolded v_expand]]]
      unfolding u2 by simp
    have fn_zs: "(f,length zs) \<in> set F" using fn len_zs by simp
    from gm04_root_source_step_to_ok_cases_full[
        OF S fresh fn_zs root2[unfolded u2]
          relpow_imp_rtrancl[OF suffix2]]
    obtain \<tau> where zs: "zs = map (\<lambda>w. Fun ok [w \<cdot> \<tau>])
        (gm04_vars (length zs))"
      and v2: "v2 = Fun ok [Fun f
        (map (\<lambda>w. w \<cdot> \<tau>) (gm04_vars (length zs)))]"
      by blast
    let ?ys = "map (\<lambda>w. w \<cdot> \<tau>) (gm04_vars (length zs))"
    have len_ys: "length ?ys = length ?xs" using len_zs by simp
    have root_step_rr: "(Fun proper [z],v) \<in> rrstep S"
      using root_step[unfolded u us] by simp
    have root_step_r: "(Fun proper [z],v) \<in> rstep S"
      by (rule rrstep_imp_rstep[OF root_step_rr])
    have vc: "\<And>l r. (l,r) \<in> S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
      using wf unfolding wf_trs_def by blast
    have ground_wrapped: "ground (Fun proper [z])" using ground_z by simp
    have ground_v: "ground v"
      by (rule rstep_ground[OF vc ground_wrapped root_step_r])
    have prefix2_nr: "(v,u2) \<in> (nrrstep S)\<^sup>*"
      using relpow_imp_rtrancl[OF prefix2] by simp
    have prefix2_r: "(v,u2) \<in> (rstep S)\<^sup>*"
      by (rule nrrsteps_imp_rsteps[OF prefix2_nr])
    have ground_u2: "ground u2"
      by (rule rsteps_ground[OF vc ground_v prefix2_r])
    have ground_fun_xs: "ground (Fun f ?xs)" using ground_z z by metis
    have ground_xs: "\<And>q. q \<in> set ?xs \<Longrightarrow> ground q"
      by (rule gm04_ground_fun_arg[OF ground_fun_xs])
    have u2_shape: "u2 = Fun f (map (\<lambda>w. Fun ok [w]) ?ys)"
      using u2 zs by (simp add: o_def)
    have ground_fun_ys:
        "ground (Fun f (map (\<lambda>w. Fun ok [w]) ?ys))"
      using ground_u2 unfolding u2_shape .
    have ground_ys: "\<And>q. q \<in> set ?ys \<Longrightarrow> ground q"
      by (rule gm04_ground_wrapped_fun_arg[OF ground_fun_ys])
    have arg_results: "\<And>i. i < length ?xs \<Longrightarrow>
        ?xs ! i = ?ys ! i \<and> gm04_source_term F (?ys ! i)"
    proof -
      fix i
      assume i: "i < length ?xs"
      from nrqrsteps_imp_arg_qrsteps_count[OF prefix2[unfolded v_expand], of i]
      obtain j where jk: "j \<le> k2" and path:
        "(Fun proper [?xs ! i],zs ! i) \<in> (rstep S) ^^ j"
        using i len_zs unfolding u2 by auto
      have ji: "j < n" using jk count count2 by arith
      have ground_xi: "ground (?xs ! i)"
        by (rule ground_xs[OF nth_mem[OF i]])
      have ground_yi: "ground (?ys ! i)"
        by (rule ground_ys[OF nth_mem], use i len_ys in simp)
      have zi: "zs ! i = Fun ok [?ys ! i]"
        using zs i len_zs len_ys by (simp add: nth_map)
      have path': "(Fun proper [?xs ! i],Fun ok [?ys ! i])
          \<in> (rstep S) ^^ j"
        using path unfolding zi .
      show "?xs ! i = ?ys ! i \<and> gm04_source_term F (?ys ! i)"
        by (rule less.hyps[OF ji ground_xi ground_yi path'])
    qed
    have eq_args: "\<And>i. i < length ?xs \<Longrightarrow> ?xs ! i = ?ys ! i"
      using arg_results by blast
    have xs_ys: "?xs = ?ys"
    proof (rule nth_equalityI)
      show "length ?xs = length ?ys" using len_ys by simp
      fix i
      assume "i < length ?xs"
      then show "?xs ! i = ?ys ! i" by (rule eq_args)
    qed
    have final_path: "(Fun f ?ys,y) \<in> (rstep S)\<^sup>*"
      using relpow_imp_rtrancl[OF suffix2] v2
        gm04_non_top_role_wrapper_rsteps_iff[OF S wf fresh, of ok]
      by simp
    have ground_final: "ground (Fun f ?ys)"
    proof (simp only: ground.simps)
      show "\<forall>q\<in>set ?ys. ground q"
        by (intro ballI, rule ground_ys)
    qed
    have root_final: "(f,length ?ys) \<in> set F"
      using fn len_zs len_ys by simp
    have source_final: "gm04_source_term F (Fun f ?ys)"
    proof (rule gm04_source_term_FunI[OF ground_final root_final])
      fix q
      assume q: "q \<in> set ?ys"
      then obtain i where i: "i < length ?ys" and q: "q = ?ys ! i"
        by (metis in_set_conv_nth)
      have ix: "i < length ?xs" using i len_ys by simp
      from arg_results[OF ix] q
      show "gm04_source_term F q" by blast
    qed
    have final_eq: "Fun f ?ys = y"
    proof -
      have "Fun f ?ys \<in> NF (rstep S)"
        using gm04_source_term_no_non_top_step[OF S fresh source_final]
        unfolding NF_def by blast
      from final_path this show ?thesis by (rule NF_not_suc)
    qed
    have source_z: "gm04_source_term F z"
      using source_final xs_ys unfolding z by simp
    from arg_prefix_count obtain j where xz: "(x,z) \<in> (rstep S) ^^ j" by blast
    have xeq: "x = z"
      by (rule gm04_non_top_steps_to_source_are_identity[
        OF S fresh relpow_imp_rtrancl[OF xz]],
        use source_z in \<open>simp add: gm04_source_term_def\<close>)
    show ?thesis using xeq xs_ys final_eq source_final unfolding z by simp
  qed
qed

lemma gm04_proper_ok_ground_converse:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and wf: "wf_trs S"
    and ground_x: "ground x"
    and ground_y: "ground y"
    and steps: "(Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
  shows "x = y \<and> gm04_source_term F y"
proof -
  from rtrancl_imp_relpow[OF steps]
  obtain n where "(Fun proper [x],Fun ok [y]) \<in> (rstep S) ^^ n" by blast
  then show ?thesis
    by (rule gm04_proper_ok_ground_converse_count[
      OF S fresh wf ground_x ground_y])
qed

lemma gm04_root_source_step_to_mark_cases_full:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source_root: "(f,length zs) \<in> set F"
    and finite_mu: "finite (\<mu> (f,length zs))"
    and root_step: "(Fun f zs,u) \<in> rqrstep True {} S"
    and suffix: "(u,Fun mark [y]) \<in> (qrstep True {} S)\<^sup>*"
  obtains i \<sigma> where
      "i \<in> \<mu> (f,length zs)" "i < length zs"
      "zs = (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))
        [i := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
          (gm04_vars (length zs))) ! i]]"
      "u = Fun mark [Fun f
        (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
proof (rule gm04_root_source_step_to_mark_cases_early[
    OF S fresh source_root finite_mu TrueI root_step suffix])
  fix i \<sigma>
  assume i1: "i \<in> \<mu> (f,length zs)" and i2: "i < length zs"
    and zs: "zs = (map (\<lambda>x. x \<cdot> \<sigma>)
      (gm04_vars (length zs)))
      [i := Fun mark [(map (\<lambda>x. x \<cdot> \<sigma>)
        (gm04_vars (length zs))) ! i]]"
    and u: "u = Fun mark [Fun f
      (map (\<lambda>x. x \<cdot> \<sigma>) (gm04_vars (length zs)))]"
  show thesis by (rule that[OF i1 i2 zs u])
qed

lemma gm04_source_steps_identity:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "gm04_source_term F s"
    and steps: "(s,t) \<in> (rstep S)\<^sup>*"
  shows "s = t"
proof -
  have "s \<in> NF (rstep S)"
    using gm04_source_term_no_non_top_step[OF S fresh source]
    unfolding NF_def by blast
  from steps this show ?thesis by (rule NF_not_suc)
qed

lemma gm04_active_source_step_is_root:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and source: "gm04_source_term F x"
    and step: "(Fun active [x],t) \<in> qrstep True {} S"
  shows "(Fun active [x],t) \<in> rqrstep True {} S"
proof -
  from step consider
      (root) "(Fun active [x],t) \<in> rqrstep True {} S"
    | (nonroot) "(Fun active [x],t) \<in> nrqrstep True {} S"
    unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
  then show ?thesis
  proof cases
    case root
    then show ?thesis .
  next
    case nonroot
    from nrqrstep_imp_arg_qrstep[OF nonroot]
    obtain i where i: "i < length (args (Fun active [x]))"
      and arg: "(args (Fun active [x]) ! i,args t ! i)
        \<in> qrstep True {} S" by blast
    from i have "i = 0" by simp
    with arg have "(x,args t ! 0) \<in> rstep S" by simp
    then show ?thesis
      using gm04_source_term_no_non_top_step[OF S fresh source] by blast
  qed
qed

lemma gm04_active_mark_ground_converse:
  fixes S :: "('f,string) trs"
  assumes S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and source_x: "gm04_source_term F x"
    and ground_y: "ground y"
    and steps: "(Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
  shows "(x,y) \<in> (csstep \<mu> (set R))\<^sup>+ \<and>
    gm04_source_term F y"
  using source_x ground_y steps
proof (induct x arbitrary: y)
  case (Var v)
  then show ?case unfolding gm04_source_term_def by simp
next
  case (Fun f xs)
  from fresh have neq: "active \<noteq> mark"
    unfolding gm04_roles_fresh_def by auto
  from Fun.prems(3) obtain u where first:
      "(Fun active [Fun f xs],u) \<in> rstep S"
    and suffix: "(u,Fun mark [y]) \<in> (rstep S)\<^sup>*"
  proof (cases rule: converse_rtranclE)
    case base
    with neq show ?thesis by simp
  next
    case (step u)
    show thesis by (rule that[OF step])
  qed
  have first_q: "(Fun active [Fun f xs],u) \<in> qrstep True {} S"
    using first by simp
  have root: "(Fun active [Fun f xs],u) \<in> rqrstep True {} S"
    by (rule gm04_active_source_step_is_root[OF S fresh Fun.prems(1) first_q])
  from gm04_root_active_step_cases[OF S fresh finite_mu root]
  show ?case
  proof cases
    fix l r \<sigma>
    assume lr: "(l,r) \<in> set R"
      and x: "Fun f xs = l \<cdot> \<sigma>"
      and u: "u = Fun mark [r \<cdot> \<sigma>]"
      and nfs: "NF_subst True (Fun active [l],Fun mark [r]) \<sigma> {}"
    have original_step: "(Fun f xs,r \<cdot> \<sigma>)
        \<in> csstep \<mu> (set R)"
      using lr x unfolding csstep_def csstep_p_def csstep_cond_def
        rstep_r_p_s_def' by force
    have original_rstep: "(Fun f xs,r \<cdot> \<sigma>)
        \<in> rstep (set R)"
      by (rule csstep_subset_rstep[THEN subsetD, OF original_step])
    have source_z: "gm04_source_term F (r \<cdot> \<sigma>)"
    proof (unfold gm04_source_term_def, intro conjI)
      show "ground (r \<cdot> \<sigma>)"
        by (rule rstep_ground[OF _ _ original_rstep],
          use wf_source Fun.prems(1) in
            \<open>auto simp: wf_trs_def gm04_source_term_def\<close>)
      show "funas_term (r \<cdot> \<sigma>) \<subseteq> set F"
        by (rule rstep_preserves_funas_terms[
          OF signature _ original_rstep wf_source],
          use Fun.prems(1) in \<open>simp add: gm04_source_term_def\<close>)
    qed
    have inner: "(r \<cdot> \<sigma>,y) \<in> (rstep S)\<^sup>*"
      using suffix u gm04_non_top_role_wrapper_rsteps_iff[
        OF S wf fresh, of mark "r \<cdot> \<sigma>" y] by simp
    have eq: "r \<cdot> \<sigma> = y"
      by (rule gm04_source_steps_identity[OF S fresh source_z inner])
    show ?thesis using original_step source_z eq by simp
  next
    fix g ar i \<sigma>
    assume fn: "(g,ar) \<in> set F" and active_i: "i \<in> \<mu> (g,ar)"
      and i: "i < ar"
      and x: "Fun f xs = Fun g
        (map (\<lambda>w. w \<cdot> \<sigma>) (gm04_vars ar))"
      and u: "u = Fun g
        ((map (\<lambda>w. w \<cdot> \<sigma>) (gm04_vars ar))
          [i := Fun active [(map (\<lambda>w. w \<cdot> \<sigma>)
            (gm04_vars ar)) ! i]])"
    from x have gf: "g = f" and ar: "ar = length xs"
      and args: "map (\<lambda>w. w \<cdot> \<sigma>) (gm04_vars ar) = xs"
      by auto
    have source_root: "(f,length xs) \<in> set F" using fn gf ar by simp
    have below: "i < length xs" using i ar by simp
    have active_i': "i \<in> \<mu> (f,length xs)" using active_i gf ar by simp
    have u_shape: "u = Fun f (xs[i := Fun active [xs ! i]])"
      using u gf args below by simp
    have suffix': "(Fun f (xs[i := Fun active [xs ! i]]),Fun mark [y])
        \<in> (rstep S)\<^sup>*"
      using suffix unfolding u_shape .
    have suffix_q: "(Fun f (xs[i := Fun active [xs ! i]]),Fun mark [y])
        \<in> (qrstep True {} S)\<^sup>*"
      using suffix' by simp
    from qrsteps_rqrstep_cases_nrqrstep[
        OF suffix_q]
    consider
        (same_root) zs where "length zs = length xs"
          "Fun mark [y] = Fun f zs"
      | (root_case) "(Fun f (xs[i := Fun active [xs ! i]]),Fun mark [y])
          \<in> (nrqrstep True {} S)\<^sup>* O rqrstep True {} S O
            (qrstep True {} S)\<^sup>*"
      by auto
    then show ?thesis
    proof cases
      case same_root
      from fresh source_root same_root show ?thesis
        unfolding gm04_roles_fresh_def by auto
    next
      case root_case
      then obtain v w where pre:
          "(Fun f (xs[i := Fun active [xs ! i]]),v)
            \<in> (nrqrstep True {} S)\<^sup>*"
        and root_step: "(v,w) \<in> rqrstep True {} S"
        and post: "(w,Fun mark [y]) \<in> (qrstep True {} S)\<^sup>*"
        by auto
      from nrqrsteps_preserve_root_fun[OF pre]
      obtain zs where v: "v = Fun f zs" by blast
      have len_zs: "length zs = length xs"
        using nrqrsteps_num_args[OF pre] unfolding v by simp
      have arg_steps: "\<And>k. k < length xs \<Longrightarrow>
          ((xs[i := Fun active [xs ! i]]) ! k,zs ! k)
            \<in> (rstep S)\<^sup>*"
      proof -
        fix k
        assume k: "k < length xs"
        from nrqrsteps_imp_arg_qrsteps[OF pre, of k] k len_zs
        show "((xs[i := Fun active [xs ! i]]) ! k,zs ! k)
            \<in> (rstep S)\<^sup>*"
          unfolding v by simp
      qed
      have source_root_zs: "(f,length zs) \<in> set F"
        using source_root len_zs by simp
      have finite_zs: "finite (\<mu> (f,length zs))" by (rule finite_mu)
      from gm04_root_source_step_to_mark_cases_full[
          OF S fresh source_root_zs finite_zs root_step[unfolded v] post]
      obtain j \<tau> where j: "j \<in> \<mu> (f,length zs)" "j < length zs"
        and zs: "zs = (map (\<lambda>w. w \<cdot> \<tau>)
          (gm04_vars (length zs)))
          [j := Fun mark [(map (\<lambda>w. w \<cdot> \<tau>)
            (gm04_vars (length zs))) ! j]]"
        and w: "w = Fun mark [Fun f
          (map (\<lambda>w. w \<cdot> \<tau>) (gm04_vars (length zs)))]"
        by blast
      let ?us = "map (\<lambda>w. w \<cdot> \<tau>) (gm04_vars (length zs))"
      have len_us: "length ?us = length xs" using len_zs by simp
      have ji: "j = i"
      proof (rule ccontr)
        assume neq: "j \<noteq> i"
        have jx: "j < length xs" using j(2) len_zs by simp
        have path_j: "(xs ! j,Fun mark [?us ! j]) \<in> (rstep S)\<^sup>*"
          using arg_steps[OF jx] zs j(2) len_zs neq below by simp
        have source_j: "gm04_source_term F (xs ! j)"
          using Fun.prems(1) nth_mem[OF jx]
          unfolding gm04_source_term_def by auto
        have "xs ! j = Fun mark [?us ! j]"
          by (rule gm04_source_steps_identity[OF S fresh source_j path_j])
        moreover from fresh source_j have
          "root (xs ! j) \<noteq> Some (mark,length [?us ! j])"
          unfolding gm04_source_term_def gm04_roles_fresh_def
          by (cases "xs ! j") auto
        ultimately show False by simp
      qed
      have child_path: "(Fun active [xs ! i],Fun mark [?us ! i])
          \<in> (rstep S)\<^sup>*"
        using arg_steps[OF below] zs ji below len_zs by simp
      have source_child: "gm04_source_term F (xs ! i)"
        using Fun.prems(1) nth_mem[OF below]
        unfolding gm04_source_term_def by auto
      have ground_ui: "ground (?us ! i)"
      proof -
        have ground_start: "ground (Fun f (xs[i := Fun active [xs ! i]]))"
          by (rule gm04_ground_fun_update_wrapper[OF _ below],
            use Fun.prems(1) in \<open>simp add: gm04_source_term_def\<close>)
        have vc: "\<And>l r. (l,r) \<in> S \<Longrightarrow>
            vars_term r \<subseteq> vars_term l"
          using wf unfolding wf_trs_def by blast
        have pre_nr: "(Fun f (xs[i := Fun active [xs ! i]]),v)
            \<in> (nrrstep S)\<^sup>*"
          using pre by simp
        have pre_r: "(Fun f (xs[i := Fun active [xs ! i]]),v)
            \<in> (rstep S)\<^sup>*"
          by (rule nrrsteps_imp_rsteps[OF pre_nr])
        have ground_v: "ground v"
          by (rule rsteps_ground[OF vc ground_start pre_r])
        have "ground (zs ! i)"
          using ground_v below len_zs unfolding v by auto
        then show ?thesis using zs ji j(2) len_zs below by simp
      qed
      from Fun.hyps[OF nth_mem[OF below] source_child ground_ui child_path]
      have child_result: "(xs ! i,?us ! i)
          \<in> (csstep \<mu> (set R))\<^sup>+"
        and source_ui: "gm04_source_term F (?us ! i)" by auto
      have other_eq: "\<And>k. k < length xs \<Longrightarrow> k \<noteq> i \<Longrightarrow>
          xs ! k = ?us ! k"
      proof -
        fix k
        assume k: "k < length xs" and neq: "k \<noteq> i"
        have path_k: "(xs ! k,?us ! k) \<in> (rstep S)\<^sup>*"
          using arg_steps[OF k] zs ji k neq below len_zs by simp
        have source_k: "gm04_source_term F (xs ! k)"
          using Fun.prems(1) nth_mem[OF k]
          unfolding gm04_source_term_def by auto
        show "xs ! k = ?us ! k"
          by (rule gm04_source_steps_identity[OF S fresh source_k path_k])
      qed
      have updated: "xs[i := ?us ! i] = ?us"
      proof (rule nth_equalityI)
        show "length (xs[i := ?us ! i]) = length ?us" using len_us by simp
        fix k
        assume k: "k < length (xs[i := ?us ! i])"
        show "(xs[i := ?us ! i]) ! k = ?us ! k"
        proof (cases "k = i")
          case True
          with k below show ?thesis by simp
        next
          case False
          from other_eq[of k] k False show ?thesis by simp
        qed
      qed
      have lifted: "(Fun f xs,Fun f ?us)
          \<in> (csstep \<mu> (set R))\<^sup>+"
      proof -
        have raw: "(Fun f xs,Fun f (xs[i := ?us ! i]))
            \<in> (csstep \<mu> (set R))\<^sup>+"
          by (rule gm04_csstep_trancl_descend[
            OF below active_i' child_result])
        show ?thesis using raw unfolding updated .
      qed
      have post_inner: "(Fun f ?us,y) \<in> (rstep S)\<^sup>*"
        using post w gm04_non_top_role_wrapper_rsteps_iff[
          OF S wf fresh, of mark "Fun f ?us" y] by simp
      have ground_us: "ground (Fun f ?us)"
      proof (simp only: ground.simps)
        show "\<forall>q\<in>set ?us. ground q"
        proof (intro ballI)
          fix q
          assume "q \<in> set ?us"
          then obtain k where k: "k < length ?us" and q: "q = ?us ! k"
            by (metis in_set_conv_nth)
          show "ground q"
          proof (cases "k = i")
            case True
            with source_ui q show ?thesis unfolding gm04_source_term_def by simp
          next
            case False
            have kx: "k < length xs" using k len_us by simp
            from other_eq[OF kx False] Fun.prems(1) nth_mem[OF kx] q
            show ?thesis unfolding gm04_source_term_def by simp
          qed
        qed
      qed
      have root_us: "(f,length ?us) \<in> set F"
        using source_root len_us by simp
      have args_source: "\<And>q. q \<in> set ?us \<Longrightarrow>
          gm04_source_term F q"
      proof -
        fix q
        assume "q \<in> set ?us"
        then obtain k where k: "k < length ?us" and q: "q = ?us ! k"
          by (metis in_set_conv_nth)
        show "gm04_source_term F q"
        proof (cases "k = i")
          case True
          with source_ui q show ?thesis by simp
        next
          case False
          have kx: "k < length xs" using k len_us by simp
          have source_k: "gm04_source_term F (xs ! k)"
            using Fun.prems(1) nth_mem[OF kx]
            unfolding gm04_source_term_def by auto
          from other_eq[OF kx False] source_k q show ?thesis by simp
        qed
      qed
      have source_us: "gm04_source_term F (Fun f ?us)"
        by (rule gm04_source_term_FunI[OF ground_us root_us args_source])
      have final_eq: "Fun f ?us = y"
        by (rule gm04_source_steps_identity[OF S fresh source_us post_inner])
      show ?thesis using lifted source_us final_eq by simp
    qed
  qed
qed

theorem gm04_finite_schema_top_pairs_full_ground:
  fixes S :: "('f,string) trs" and c :: "('f,string) term"
  assumes source_SN: "SN (csstep \<mu> (set R))"
    and ground_c: "ground c"
    and S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and fresh_top: "\<not> defined S (top_sharp,1)"
  shows "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
proof (rule gm04_finite_exact_top_pairs_ground_sanitizing[
    OF SN_imp_SN_trancl[OF source_SN] ground_c wf fresh_top,
    where source="gm04_source_term F"])
  show "ok \<noteq> mark"
    using fresh unfolding gm04_roles_fresh_def by auto
next
  fix x y
  assume "ground x" "ground y"
    "(Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
  with gm04_non_top_cross_phases_impossible(1)[OF S fresh]
  show False by blast
next
  fix x y
  assume "ground x" "ground y"
    "(Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
  with gm04_non_top_cross_phases_impossible(2)[OF S fresh]
  show False by blast
next
  fix x y
  assume gx: "ground x" and gy: "ground y"
    and sx: "gm04_source_term F x"
    and steps: "(Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
  from gm04_active_mark_ground_converse[
      OF S fresh signature wf_source wf finite_mu sx gy steps]
  show "(x,y) \<in> (csstep \<mu> (set R))\<^sup>+" by blast
next
  fix x y
  assume gx: "ground x" and gy: "ground y"
    and steps: "(Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
  show "x = y \<and> gm04_source_term F y"
    by (rule gm04_proper_ok_ground_converse[OF S fresh wf gx gy steps])
qed

theorem gm04_finite_schema_top_pairs_full_ground_sig:
  fixes S :: "('f,string) trs" and c :: "('f,string) term"
  assumes source_SN: "SN (sig_step (set F) (csstep \<mu> (set R)))"
    and ground_c: "ground c"
    and S: "S = set
      (gm04_non_top_rules \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and wf_source: "wf_trs (set R)"
    and wf: "wf_trs S"
    and finite_mu: "\<And>f n. finite (\<mu> (f,n))"
    and fresh_top: "\<not> defined S (top_sharp,1)"
  shows "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
proof (rule gm04_finite_exact_top_pairs_ground_sanitizing[
    OF gm04_SN_sig_csstep_trancl[OF source_SN signature wf_source]
      ground_c wf fresh_top,
    where source="gm04_source_term F"])
  show "ok \<noteq> mark"
    using fresh unfolding gm04_roles_fresh_def by auto
next
  fix x y
  assume "ground x" "ground y"
    "(Fun active [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
  with gm04_non_top_cross_phases_impossible(1)[OF S fresh]
  show False by blast
next
  fix x y
  assume "ground x" "ground y"
    "(Fun proper [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
  with gm04_non_top_cross_phases_impossible(2)[OF S fresh]
  show False by blast
next
  fix x y
  assume gx: "ground x" and gy: "ground y"
    and sx: "gm04_source_term F x"
    and steps: "(Fun active [x],Fun mark [y]) \<in> (rstep S)\<^sup>*"
  from gm04_active_mark_ground_converse[
      OF S fresh signature wf_source wf finite_mu sx gy steps]
  have xy: "(x,y) \<in> (csstep \<mu> (set R))\<^sup>+" by blast
  from sx have xsig: "funas_term x \<subseteq> set F"
    unfolding gm04_source_term_def by auto
  from gm04_active_mark_ground_converse[
      OF S fresh signature wf_source wf finite_mu sx gy steps]
  have sy: "gm04_source_term F y" by blast
  from sy have ysig: "funas_term y \<subseteq> set F"
    unfolding gm04_source_term_def by auto
  show "(x,y) \<in> sig_step (set F) ((csstep \<mu> (set R))\<^sup>+)"
    using xy xsig ysig unfolding sig_step_def by auto
next
  fix x y
  assume gx: "ground x" and gy: "ground y"
    and steps: "(Fun proper [x],Fun ok [y]) \<in> (rstep S)\<^sup>*"
  show "x = y \<and> gm04_source_term F y"
    by (rule gm04_proper_ok_ground_converse[OF S fresh wf gx gy steps])
qed

ML_command \<open>writeln "GM04_SANITIZING_PHASE_OK"\<close>

end
