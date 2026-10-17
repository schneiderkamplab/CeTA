theory CSR_Muterm_Innermost_Usable_Exec
  imports CSR_Muterm_Innermost_Usable
begin

lemma muterm_innermost_ur_closed_pairs_subset:
  assumes "muterm_innermost_ur_closed R U \<mu> Q" and "P \<subseteq> Q"
  shows "muterm_innermost_ur_closed R U \<mu> P"
proof -
  from assms(1) have subset: "U \<subseteq> R"
    and pairs: "\<forall>dp\<in>Q. \<not> is_Var (snd dp) \<longrightarrow>
      csr_u3_root_rules_closed R U (snd dp) (mu_fun_poss \<mu> (snd dp))"
    and rules: "\<forall>lr\<in>U. csr_u3_root_rules_closed R U (snd lr)
      (mu_fun_poss \<mu> (snd lr))"
    unfolding muterm_innermost_ur_closed_def by simp_all
  have restricted: "\<forall>dp\<in>P. \<not> is_Var (snd dp) \<longrightarrow>
      csr_u3_root_rules_closed R U (snd dp) (mu_fun_poss \<mu> (snd dp))"
  proof (intro ballI impI)
    fix dp
    assume dp: "dp \<in> P" and nonvar: "\<not> is_Var (snd dp)"
    have dp_Q: "dp \<in> Q" by (rule subsetD[OF assms(2) dp])
    show "csr_u3_root_rules_closed R U (snd dp) (mu_fun_poss \<mu> (snd dp))"
      by (rule pairs[rule_format, OF dp_Q nonvar])
  qed
  show ?thesis unfolding muterm_innermost_ur_closed_def
    by (intro conjI subset restricted rules)
qed

lemma rhs_mu_vars_condition_subset:
  assumes "rhs_mu_vars_condition \<mu> Q" and "P \<subseteq> Q"
  shows "rhs_mu_vars_condition \<mu> P"
proof -
  from assms(1) have condition: "\<forall>l r. (l,r) \<in> Q \<longrightarrow>
    (\<forall>x. x \<in> mu_vars_term \<mu> r \<longrightarrow> x \<in> mu_vars_term \<mu> l)"
    unfolding rhs_mu_vars_condition_def by blast
  show ?thesis unfolding rhs_mu_vars_condition_def
  proof (intro allI impI)
    fix l r x
    assume lr: "(l,r) \<in> P" and x: "x \<in> mu_vars_term \<mu> r"
    have lr_Q: "(l,r) \<in> Q" by (rule subsetD[OF assms(2) lr])
    show "x \<in> mu_vars_term \<mu> l" by (rule condition[rule_format, OF lr_Q x])
  qed
qed

lemma muterm_innermost_collapsing_target_safe:
  fixes R U P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes closed: "muterm_innermost_ur_closed R U \<mu> (P \<union> S)"
    and conservative: "rhs_mu_vars_condition \<mu> (P \<union> S)"
    and ly: "(l,Var y) \<in> P"
    and l: "l = Fun (Sharp f) ls"
    and marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and source: "innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>)"
    and cd: "(c,d) \<in> S"
    and d: "d = Fun (Sharp g) ds"
    and bridge: "c \<cdot> \<theta> = \<sigma> y"
  shows "muterm_innermost_ur_safe R U \<mu> (d \<cdot> \<theta>)"
proof -
  have conservative_P: "rhs_mu_vars_condition \<mu> P"
    by (rule rhs_mu_vars_condition_subset[OF conservative], blast)
  have y_rhs: "y \<in> mu_vars_term \<mu> (Var y)"
    unfolding mu_vars_term_def by simp
  have y_l: "y \<in> mu_vars_term \<mu> l"
    using conservative_P ly y_rhs unfolding rhs_mu_vars_condition_def by blast
  have sigma_y_NF: "\<sigma> y \<in> NF (csstep \<mu> R)"
    by (rule innermost_pair_source_active_subst_NF[
      OF source l marked_l y_l])
  have d_fun: "is_Fun d" using d by simp
  from closed have closed_pairs: "\<forall>dp\<in>P \<union> S.
      \<not> is_Var (snd dp) \<longrightarrow>
      csr_u3_root_rules_closed R U (snd dp) (mu_fun_poss \<mu> (snd dp))"
    unfolding muterm_innermost_ur_closed_def by blast
  have skeleton: "muterm_innermost_ur_skeleton R U \<mu> d"
  proof (rule muterm_root_closed_imp_skeleton)
    have cd_union: "(c,d) \<in> P \<union> S" using cd by simp
    from closed_pairs[rule_format, OF cd_union] d_fun show
      "csr_u3_root_rules_closed R U d (mu_fun_poss \<mu> d)"
      by simp
  qed
  have normal: "\<theta> z \<in> NF (csstep \<mu> R)"
    if z: "z \<in> mu_vars_term \<mu> d" for z
  proof -
    have z_c: "z \<in> mu_vars_term \<mu> c"
      using conservative cd z unfolding rhs_mu_vars_condition_def by blast
    then obtain p where p: "p \<in> mu_poss \<mu> c"
      and at: "c |_ p = Var z"
      unfolding mu_vars_term_def by blast
    have p_sub: "p \<in> mu_poss \<mu> (c \<cdot> \<theta>)"
      by (rule mu_poss_subst_lift[OF p])
    have p_pos: "p \<in> poss c" using p mu_poss_imp_poss by blast
    have at_sub: "(c \<cdot> \<theta>) |_ p = \<theta> z"
      using subt_at_subst[OF p_pos, of \<theta>] at by simp
    have c_NF: "c \<cdot> \<theta> \<in> NF (csstep \<mu> R)"
      using sigma_y_NF bridge by simp
    show ?thesis
      using NF_csstep_mu_pos[OF c_NF p_sub] unfolding at_sub .
  qed
  show ?thesis
    by (rule muterm_innermost_ur_safe_subst[OF skeleton normal])
qed

lemma muterm_innermost_noncollapsing_target_safe:
  fixes R U P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes closed: "muterm_innermost_ur_closed R U \<mu> (P \<union> S)"
    and conservative: "rhs_mu_vars_condition \<mu> (P \<union> S)"
    and lr: "(l,r) \<in> P"
    and l: "l = Fun (Sharp f) ls"
    and r: "r = Fun (Sharp g) rs"
    and marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
    and source: "innermost_pair_source Sharp \<mu> R (l \<cdot> \<sigma>)"
  shows "muterm_innermost_ur_safe R U \<mu> (r \<cdot> \<sigma>)"
proof -
  have closed_P: "muterm_innermost_ur_closed R U \<mu> P"
    by (rule muterm_innermost_ur_closed_pairs_subset[OF closed], blast)
  have conservative_P: "rhs_mu_vars_condition \<mu> P"
    by (rule rhs_mu_vars_condition_subset[OF conservative], blast)
  show ?thesis
    by (rule muterm_innermost_pair_target_safe[
      OF closed_P conservative_P lr l r marked_l source])
qed

lemma muterm_innermost_typed_target_safeI:
  fixes R U P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) trs)"
    and \<mu> :: "((('f,'l) lab) \<times> nat) \<Rightarrow> nat set"
  assumes closed: "muterm_innermost_ur_closed R U \<mu> (P \<union> S)"
    and conservative: "rhs_mu_vars_condition \<mu> (P \<union> S)"
    and p_shape: "\<forall>(l,r)\<in>P. \<exists>f ls.
      l = Fun (Sharp f) ls \<and>
      \<mu> (Sharp f,length ls) = \<mu> (f,length ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        \<mu> (Sharp g,length rs) = \<mu> (g,length rs)))"
    and s_shape: "\<forall>(l,r)\<in>S. is_Fun l \<and> (\<exists>g rs.
      r = Fun (Sharp g) rs \<and>
      \<mu> (Sharp g,length rs) = \<mu> (g,length rs))"
  shows "muterm_innermost_typed_target_safe R U \<mu> P S"
proof (unfold muterm_innermost_typed_target_safe_def, intro allI impI)
  fix a b
  assume event: "(a,b) \<in> muterm_innermost_typed_pair_step Sharp \<mu> R P S"
  then have typed: "(a,b) \<in> muterm_typed_pair_step P S"
    and source: "innermost_pair_source Sharp \<mu> R a"
    unfolding muterm_innermost_typed_pair_step_def by auto
  from typed have cases:
      "muterm_noncollapsing_rrstep P a b \<or>
       (\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S)"
    unfolding muterm_typed_pair_step_def by simp
  from cases show "\<exists>f bs. b = Fun (Sharp f) bs \<and>
      \<mu> (Sharp f,length bs) = \<mu> (f,length bs) \<and>
      muterm_innermost_ur_safe R U \<mu> b"
  proof
    assume nc: "muterm_noncollapsing_rrstep P a b"
    then obtain l r \<sigma> where lr: "(l,r) \<in> P"
      and r_fun: "\<not> is_Var r" and a: "a = l \<cdot> \<sigma>"
      and b: "b = r \<cdot> \<sigma>"
      unfolding muterm_noncollapsing_rrstep_def by blast
    from p_shape[rule_format, OF lr] obtain f ls where l: "l = Fun (Sharp f) ls"
      and marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)"
      and rhs: "is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        \<mu> (Sharp g,length rs) = \<mu> (g,length rs))" by blast
    from rhs r_fun obtain g rs where r: "r = Fun (Sharp g) rs"
      and marked_r: "\<mu> (Sharp g,length rs) = \<mu> (g,length rs)"
      by blast
    have safe: "muterm_innermost_ur_safe R U \<mu> (r \<cdot> \<sigma>)"
      by (rule muterm_innermost_noncollapsing_target_safe[
        OF closed conservative lr l r marked_l source[unfolded a]])
    show ?thesis using b r marked_r safe by simp
  next
    assume coll: "\<exists>x. muterm_collapsing_rrstep P a x \<and> (x,b) \<in> rrstep S"
    then obtain x where px: "muterm_collapsing_rrstep P a x"
      and xb: "(x,b) \<in> rrstep S" by blast
    from px obtain l y \<sigma> where ly: "(l,Var y) \<in> P"
      and a: "a = l \<cdot> \<sigma>" and x: "x = \<sigma> y"
      unfolding muterm_collapsing_rrstep_def by blast
    from xb obtain c d \<theta> where cd: "(c,d) \<in> S"
      and x': "x = c \<cdot> \<theta>" and b: "b = d \<cdot> \<theta>"
      unfolding rrstep_def' by blast
    from p_shape[rule_format, OF ly] obtain f ls where l: "l = Fun (Sharp f) ls"
      and marked_l: "\<mu> (Sharp f,length ls) = \<mu> (f,length ls)" by blast
    from s_shape[rule_format, OF cd] obtain g ds where d: "d = Fun (Sharp g) ds"
      and marked_d: "\<mu> (Sharp g,length ds) = \<mu> (g,length ds)" by blast
    have bridge: "c \<cdot> \<theta> = \<sigma> y" using x x' by simp
    have safe: "muterm_innermost_ur_safe R U \<mu> (d \<cdot> \<theta>)"
      by (rule muterm_innermost_collapsing_target_safe[
        OF closed conservative ly l marked_l source[unfolded a]
          cd d bridge])
    show ?thesis using b d marked_d safe by simp
  qed
qed

fun muterm_marked_target_check where
  "muterm_marked_target_check \<mu> (Fun (Sharp f) ts) =
    (muterm_mu_positions_list \<mu> (Sharp f,length ts) =
      muterm_mu_positions_list \<mu> (f,length ts))"
| "muterm_marked_target_check \<mu> t = False"

lemma muterm_marked_target_check_sound:
  assumes "muterm_marked_target_check \<mu> t"
  obtains f ts where "t = Fun (Sharp f) ts"
    "mu_of \<mu> (Sharp f,length ts) = mu_of \<mu> (f,length ts)"
proof (cases t)
  case (Var x)
  with assms show ?thesis by simp
next
  case (Fun h ts)
  show ?thesis
  proof (cases h)
    case (Sharp f)
    from assms[unfolded Fun Sharp]
    have eq: "muterm_mu_positions_list \<mu> (Sharp f,length ts) =
      muterm_mu_positions_list \<mu> (f,length ts)" by simp
    have set_eq: "mu_of \<mu> (Sharp f,length ts) =
      mu_of \<mu> (f,length ts)"
      using arg_cong[OF eq, of set] by simp
    show ?thesis by (rule that[OF Fun[unfolded Sharp] set_eq])
  qed (use assms Fun in auto)
qed

definition muterm_innermost_typed_shape_check where
  "muterm_innermost_typed_shape_check \<mu> P S =
    (list_all (\<lambda>(l,r). muterm_marked_target_check \<mu> l \<and>
      (is_Var r \<or> muterm_marked_target_check \<mu> r)) P \<and>
     list_all (\<lambda>(l,r). is_Fun l \<and>
      muterm_marked_target_check \<mu> r) S)"

lemma muterm_innermost_typed_shape_check_sound:
  assumes check: "muterm_innermost_typed_shape_check \<mu> P S"
  shows "(\<forall>(l,r)\<in>set P. \<exists>f ls.
      l = Fun (Sharp f) ls \<and>
      mu_of \<mu> (Sharp f,length ls) = mu_of \<mu> (f,length ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs)))) \<and>
    (\<forall>(l,r)\<in>set S. is_Fun l \<and> (\<exists>g rs.
      r = Fun (Sharp g) rs \<and>
      mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs)))"
proof (intro conjI ballI)
  fix q
  assume q: "q \<in> set P"
  obtain l r where qr: "q = (l,r)" by (cases q)
  from check q have l_check: "muterm_marked_target_check \<mu> l"
    and r_check: "is_Var r \<or> muterm_marked_target_check \<mu> r"
    unfolding muterm_innermost_typed_shape_check_def qr
    by (auto simp: list_all_iff)
  from muterm_marked_target_check_sound[OF l_check]
  obtain f ls where l: "l = Fun (Sharp f) ls"
    and marked_l: "mu_of \<mu> (Sharp f,length ls) =
      mu_of \<mu> (f,length ls)" by blast
  show "case q of (l,r) \<Rightarrow> \<exists>f ls.
      l = Fun (Sharp f) ls \<and>
      mu_of \<mu> (Sharp f,length ls) = mu_of \<mu> (f,length ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs)))"
    unfolding qr
  proof (simp only: prod.case, intro exI conjI)
    show "l = Fun (Sharp f) ls" by (rule l)
    show "mu_of \<mu> (Sharp f,length ls) = mu_of \<mu> (f,length ls)"
      by (rule marked_l)
    from r_check show "is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs))"
    proof
      assume "is_Var r"
      then show ?thesis by simp
    next
      assume marked: "muterm_marked_target_check \<mu> r"
      from muterm_marked_target_check_sound[OF marked]
      obtain g rs where r: "r = Fun (Sharp g) rs"
        and marked_r: "mu_of \<mu> (Sharp g,length rs) =
          mu_of \<mu> (g,length rs)" by blast
      show ?thesis using r marked_r by blast
    qed
  qed
next
  fix q
  assume q: "q \<in> set S"
  obtain l r where qr: "q = (l,r)" by (cases q)
  from check q have l_fun: "is_Fun l"
    and r_check: "muterm_marked_target_check \<mu> r"
    unfolding muterm_innermost_typed_shape_check_def qr
    by (auto simp: list_all_iff)
  from muterm_marked_target_check_sound[OF r_check]
  obtain g rs where r: "r = Fun (Sharp g) rs"
    and marked_r: "mu_of \<mu> (Sharp g,length rs) =
      mu_of \<mu> (g,length rs)" by blast
  show "case q of (l,r) \<Rightarrow> is_Fun l \<and> (\<exists>g rs.
      r = Fun (Sharp g) rs \<and>
      mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs))"
    unfolding qr using l_fun r marked_r by simp
qed

definition muterm_expanded_innermost_usable_check where
  "muterm_expanded_innermost_usable_check R U \<mu> P S =
    (muterm_innermost_ur_closed_check R U \<mu> (P @ S) \<and>
     rhs_mu_vars_condition_list \<mu> (P @ S @ U) \<and>
     muterm_innermost_typed_shape_check \<mu> P S)"

lemma muterm_expanded_innermost_usable_check_sound:
  fixes R U P S :: "(((('f::{showl,compare_order},'l::{showl,compare_order}) lab),'v) rules)"
    and \<mu> :: "((('f,'l) lab) muL)"
  assumes check: "muterm_expanded_innermost_usable_check R U \<mu> P S"
  shows "muterm_innermost_ur_closed (set R) (set U) (mu_of \<mu>)
      (set P \<union> set S) \<and>
    rhs_mu_vars_condition (mu_of \<mu>) (set U) \<and>
    muterm_innermost_typed_target_safe (set R) (set U) (mu_of \<mu>)
      (set P) (set S)"
proof -
  from check have closed_check:
      "muterm_innermost_ur_closed_check R U \<mu> (P @ S)"
    and conservative_check: "rhs_mu_vars_condition_list \<mu> (P @ S @ U)"
    and shape_check: "muterm_innermost_typed_shape_check \<mu> P S"
    unfolding muterm_expanded_innermost_usable_check_def by auto
  have closed: "muterm_innermost_ur_closed (set R) (set U) (mu_of \<mu>)
      (set P \<union> set S)"
    using muterm_innermost_ur_closed_check_sound[OF closed_check] by simp
  have conservative_all: "rhs_mu_vars_condition (mu_of \<mu>)
      (set P \<union> (set S \<union> set U))"
    using rhs_mu_vars_condition_list_sound[OF conservative_check] by simp
  have conservative_PS: "rhs_mu_vars_condition (mu_of \<mu>)
      (set P \<union> set S)"
    by (rule rhs_mu_vars_condition_subset[OF conservative_all], blast)
  have conservative_U: "rhs_mu_vars_condition (mu_of \<mu>) (set U)"
    by (rule rhs_mu_vars_condition_subset[OF conservative_all], blast)
  from muterm_innermost_typed_shape_check_sound[OF shape_check]
  have p_shape: "\<forall>(l,r)\<in>set P. \<exists>f ls.
      l = Fun (Sharp f) ls \<and>
      mu_of \<mu> (Sharp f,length ls) = mu_of \<mu> (f,length ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs)))"
    and s_shape: "\<forall>(l,r)\<in>set S. is_Fun l \<and> (\<exists>g rs.
      r = Fun (Sharp g) rs \<and>
      mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs))" by auto
  have target: "muterm_innermost_typed_target_safe
      (set R) (set U) (mu_of \<mu>) (set P) (set S)"
  proof (rule muterm_innermost_typed_target_safeI[
      where R="set R" and U="set U" and \<mu>="mu_of \<mu>"
        and P="set P" and S="set S"])
    show "muterm_innermost_ur_closed (set R) (set U) (mu_of \<mu>)
      (set P \<union> set S)" by (rule closed)
    show "rhs_mu_vars_condition (mu_of \<mu>) (set P \<union> set S)"
      by (rule conservative_PS)
    show "\<forall>(l,r)\<in>set P. \<exists>f ls.
      l = Fun (Sharp f) ls \<and>
      mu_of \<mu> (Sharp f,length ls) = mu_of \<mu> (f,length ls) \<and>
      (is_Var r \<or> (\<exists>g rs. r = Fun (Sharp g) rs \<and>
        mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs)))"
      by (rule p_shape)
    show "\<forall>(l,r)\<in>set S. is_Fun l \<and> (\<exists>g rs.
      r = Fun (Sharp g) rs \<and>
      mu_of \<mu> (Sharp g,length rs) = mu_of \<mu> (g,length rs))"
      by (rule s_shape)
  qed
  show ?thesis using closed conservative_U target by auto
qed

end
