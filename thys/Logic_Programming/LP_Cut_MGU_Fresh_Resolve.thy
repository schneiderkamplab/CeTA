theory LP_Cut_MGU_Fresh_Resolve
 imports LP_Cut_MGU_Normalize
begin

text \<open>Fresh clause variables use a namespace disjoint from the complete
active continuation. Checked global factorization preserves every live variable;
no prefix-only most-generality premise is substituted here.\<close>

theorem lpc_checked_mgu_resolve_fresh_namespace:
  fixes a h :: "('f,string) term"
    and rename_clause_var :: "string \<Rightarrow> string"
  assumes checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (rename_clause_var x)))] V images"
    and injective: "inj rename_clause_var"
    and fresh_a: "vars_term a \<inter> range rename_clause_var = {}"
    and fresh_gs: "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<inter> range rename_clause_var = {}"
  shows "lpc_mgu_resolve (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (rename_clause_var x)) LPIVar)"
proof -
  let ?s = "\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar"
  let ?r = "\<lambda>x. ?s (rename_clause_var x)"
  let ?eqs = "[(a,h\<cdot>(\<lambda>x. Var (rename_clause_var x)))]"
  have unifies: "lp_isubst (lp_ieval a LPIVar) ?s = lp_ieval h ?r"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_equations_def lp_ieval_subst lp_ieval_finite_subst)
  have factor: "\<And>\<tau> \<nu> :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu> \<Longrightarrow>
    \<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
  proof -
    fix \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume comparison: "lp_isubst (lp_ieval a LPIVar) \<tau> = lp_ieval h \<nu>"
    let ?d = "\<lambda>x. if x\<in>range rename_clause_var then \<nu> (inv_into UNIV rename_clause_var x) else \<tau> x"
    have renamed: "\<And>x. ?d (rename_clause_var x) = \<nu> x"
      by (simp add: inv_f_f[OF injective])
    have old: "\<And>t. (vars_term t \<inter> range rename_clause_var = {}) \<Longrightarrow> lp_ieval t ?d = lp_ieval t \<tau>"
      by (rule lp_ieval_cong) auto
    have solution: "lp_equations ?eqs ?d"
      using comparison old[OF fresh_a]
      by (simp add: lp_equations_def lp_ieval_finite_subst lp_ieval_subst renamed inv_f_f[OF injective])
    have composed: "(\<lambda>x. lp_isubst (?s x) ?d) = ?d"
      by (rule ext) (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked solution])
    have composed_eval: "(\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) ?d) = ?d"
      using composed by (simp add: lp_ieval_subst)
    have active: "\<And>t. (vars_term t \<inter> range rename_clause_var = {}) \<Longrightarrow>
      lp_isubst (lp_isubst (lp_ieval t LPIVar) ?s) ?d = lp_isubst (lp_ieval t LPIVar) \<tau>"
      by (simp add: lp_ieval_subst composed_eval old)
    show "\<exists>\<delta>.
      lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) \<delta> = lp_isubst (lp_ieval a LPIVar) \<tau> \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) \<delta>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
      map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) \<delta>)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    proof (rule exI[of _ ?d], intro conjI)
      show "lp_isubst (lp_isubst (lp_ieval a LPIVar) ?s) ?d = lp_isubst (lp_ieval a LPIVar) \<tau>"
        by (rule active[OF fresh_a])
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) ?d))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) =
        map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>))
        (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs)"
        unfolding map_map o_def lp_cut_map_comp
        by (rule map_cong[OF refl], rule lp_cut_goal_map_cong, rule active)
          (use fresh_gs in \<open>auto simp:\<close>)
      show "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?r) ?d)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
      proof -
        have "(\<lambda>x. lp_isubst (?r x) ?d) = \<nu>"
          using fun_cong[OF composed, of "rename_clause_var _"] by (auto simp: renamed inv_f_f[OF injective])
        then show ?thesis by (simp add: lp_ieval_subst)
      qed
    qed
  qed
  show ?thesis unfolding lpc_mgu_resolve_def using unifies factor by blast
qed

lemma lpc_fresh_namespace_for_finite_interface:
  fixes A :: "string set"
  assumes finite: "finite A"
  shows "\<exists>rename_clause_var :: string \<Rightarrow> string.
    inj rename_clause_var \<and> A \<inter> range rename_clause_var = {}"
proof -
  let ?k = "Suc (Lattices_Big.linorder_class.Max (insert 0 (length ` A)))"
  have old: "length x < ?k" if "x\<in>A" for x
  proof -
    have fin: "finite (insert (0::nat) (length ` A))" using finite by simp
    have member: "length x \<in> insert 0 (length ` A)" using that by auto
    have bound: "length x \<le> Lattices_Big.linorder_class.Max (insert 0 (length ` A))"
      by (rule Max_ge[OF fin member])
    show ?thesis using bound by arith
  qed
  have new: "?k \<le> length x" if "x\<in>range (lp_prefix ?k)" for x
    using that by (auto simp: lp_prefix_def)
  have injective: "inj (lp_prefix ?k)"
    by (auto simp: inj_on_def lp_prefix_def)
  have separate: "A \<inter> range (lp_prefix ?k) = {}"
  proof (rule equals0I)
    fix x assume member: "x\<in>A \<inter> range (lp_prefix ?k)"
    have lower: "length x < ?k" by (rule old) (use member in auto)
    have upper: "?k \<le> length x" by (rule new) (use member in auto)
    show False using lower upper by arith
  qed
  show ?thesis by (rule exI[of _ "lp_prefix ?k"]) (simp add: injective separate)
qed

ML \<open>
val checked = [@{thm lpc_checked_mgu_resolve_fresh_namespace},
 @{thm lpc_fresh_namespace_for_finite_interface}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted rename_clause_var namespace dependency" else ();
\<close>
end
