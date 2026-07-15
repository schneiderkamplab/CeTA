theory Matrix_Core_Order_Impl
  imports 
    Matrix_Core_Order
    Jordan_Normal_Form.Matrix_Impl
    Certification_Monads.Check_Monad
    Certification_Monads.Error_Monad
    Show.Shows_Literal
    Term_Order_Impl
    First_Order_Rewriting.Trs_Impl
begin

type_synonym ('f,'a) fun_coeffs = "(('f \<times> nat) \<times> ('a mat list \<times> 'a mat)) list"
  \<comment> \<open>the list of function symbols occurring in a TRS and their corresponding interpretation coefficients\<close>

datatype core_matrix_mode = E_I | M_I

definition "show_core_matrix_inter_main mode d idx intr =
     showsl_lit (STR ''core matrix interpretation (mode = '')
   o showsl_lit mode
   o showsl_lit (STR '') with dimension '') o showsl d o showsl_lit (STR '' and strict indices I = '')
   o showsl (map Suc idx) o showsl_lit (STR '' where\<newline>'')
   o showsl_sep (\<lambda> ((f,n),(cs,c)). 
          showsl_lit (STR ''['')
        o showsl (Fun f (map (\<lambda> i. Var (''x'' @ show i)) [1..<Suc n])) 
        o showsl_lit (STR ''] = '')
        o showsl (LPoly c (zip (map (\<lambda> i. ''x'' @ show i) [1..<Suc n]) cs))
     ) (showsl_lit (STR ''\<newline>'')) intr
   o showsl_lit (STR ''\<newline>and\<newline>[f(x1,..,xn)] = x1 + ... + xn + 1 for all other symbols f\<newline>\<newline>'')"  


locale core_mat_inter_impl = core_mat_inter n \<delta> for n :: nat and 
  \<delta> :: "'a :: {showl, ordered_ab_group_add,ordered_semiring_1,Rings.ordered_semiring_0,SN_delta_order}" 
begin

definition check_valid_dims where "check_valid_dims = 
  (\<lambda> ((f,k),(cs,c)). do { 
       check (Ball (set cs) (\<lambda> c. c \<in> carrier_mat n n \<and> c \<ge>\<^sub>m 0\<^sub>m n n)) (showsl (STR ''coefficients must be in N''));
       check (c \<in> carrier_mat n n) (showsl (STR ''wrong matrix dimension of constant part''));
       check (length cs = k) (
         showsl (STR ''number of coefficient of symbol '') o showsl f o showsl (STR '' differs from arity of symbol''))
      })" 

definition in_MI where [simp]: "in_MI I a = (a \<in> M\<^sub>I (set I))" 
definition in_LI where [simp]: "in_LI I a = (a \<in> L\<^sub>I (set I))" 
definition in_N where [simp]: "in_N a = (a \<in> N)" 

lemma in_N_code: "in_N a = (a \<in> carrier_mat n n \<and> a \<ge>\<^sub>m 0\<^sub>m n n)" 
  unfolding N_def in_N_def by auto

lemma in_MI_code: "in_MI I a = (in_N a \<and> (\<forall>i\<in>set I. \<exists>j\<in>set I. 1 \<le> a $$ (i, j)))" 
  unfolding in_MI_def in_N_def M\<^sub>I_def by auto

lemma in_LI_code: "in_LI I a = (in_N a \<and> (\<forall>i\<in>set I. \<exists>j\<in>set I. \<delta> \<le> a $$ (i, j)))" 
  unfolding in_LI_def in_N_def L\<^sub>I_def by auto

definition core_EI_rel_impl :: "nat list \<Rightarrow> ('f :: showl,'a)fun_coeffs \<Rightarrow> ('f, 'v :: showl) rel_impl" where
  "core_EI_rel_impl I fk_cs = (let 
   def = (\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n;
   Alpha = Alpha_list_to_Alpha def fk_cs;
   checkNS = (\<lambda> lr. check (check_lpoly_EI_N (set I) (alpha_lhs_minus_rhs Alpha lr)) 
       (showsl (STR ''could not weakly orient rule '') o showsl_rule lr o
        showsl_nl o showsl (STR ''where lhs - rhs evaluates to '') o showsl (alpha_lhs_minus_rhs Alpha lr))) in
   \<lparr>rel_impl.valid = do {check (\<delta> > 0) (showsl (STR ''delta must be positive''));
       check (Ball (set I) (\<lambda> i. i < n)) (showsl (STR ''indices in I must be below matrix dimension''));
       check (I \<noteq> []) (showsl (STR ''indices I must be non-empty''));
       check_allm check_valid_dims fk_cs;
       check_allm (\<lambda> (fk,_). check (check_lpoly_EI_EI (set I) (inter_lpoly Alpha fk)) 
        (showsl (STR ''cannot ensure that interpretation of symbol '') o showsl (fst fk) o showsl (STR '' is function from E-I^* to E-I''))) fk_cs       
     },
     standard = succeed,
     desc = show_core_matrix_inter_main (STR ''E_I'') n I fk_cs,
     s = (\<lambda> lr. check (check_lpoly_EI_PI (set I) I (alpha_lhs_minus_rhs Alpha lr)) 
       (showsl (STR ''could not strictly orient rule '') o showsl_rule lr o
        showsl_nl o showsl (STR ''where lhs - rhs evaluates to '') o showsl (alpha_lhs_minus_rhs Alpha lr))),
     ns = checkNS, 
     nst = checkNS,
     af = core_mat_af Alpha, 
     top_af = core_mat_af Alpha,
     SN = succeed,
     subst_s = succeed,
     ce_compat = succeed,
     co_rewr = succeed,
     top_mono = succeed,
     top_refl = succeed,
     mono_af = (\<lambda> f. {}), \<comment> \<open>IGNORE: not yet implemented\<close>
     mono = (\<lambda> _. check_allm (\<lambda> (_,csc). check (Ball (set (fst csc)) (\<lambda> a. a \<ge>\<^sub>m oneE\<^sub>I (set I))) (showsl (STR '' require monotone coefficient in E-I''))) fk_cs),
     not_wst = None, \<comment> \<open>IGNORE: not yet implemented\<close>
     not_sst = None, \<comment> \<open>IGNORE: not yet implemented\<close>
     cpx = no_complexity_check \<rparr>)"

lemma core_EI_rel_impl: "rel_impl (core_EI_rel_impl I fk_cs)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?I = "set I"
  let ?def = "(\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n" 
  have def: "?def \<in> carrier_mat n n" by auto
  define Alpha where "Alpha = Alpha_list_to_Alpha ?def fk_cs" 
  note valid = 1[unfolded core_EI_rel_impl_def Let_def, simplified, folded Alpha_def]
  have pre: "0 < \<delta>" "0 \<le> \<delta>" "?I \<subseteq> {..<n}" "?I \<noteq> {}" using valid by auto
  have pre1: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
  proof (intro allI impI, rule Alpha_list_to_Alpha_dim[OF def Alpha_def], goal_cases)
    case (1 f' k' cs' c' f k cs c)
    from valid 1 have "isOK (check_valid_dims ((f, k), cs, c))" by auto
    from this[unfolded check_valid_dims_def split]
    show ?case by (auto simp: N_def)
  qed
  note E\<^sub>IN = E\<^sub>IN[OF pre(4,3)]
  note P\<^sub>IP = P\<^sub>IP[OF pre(4,3)]
  note N_P\<^sub>I_closed = N_P\<^sub>I_closed[OF pre(4,3)]
  note EI_PI_mult = EI_PI_mult[OF pre(4,3,1)]
  have defP: "?def \<in> P\<^sub>I (set I)"
  proof -
    from pre obtain i where "i < n" "i \<in> set I" by (cases I, auto)
    thus ?thesis unfolding P\<^sub>I_def N_def using pre(1)
      by (auto intro!: bexI[of _ i])
  qed
  note p1 = pre1 pre(3,2)
  note p1' = pre(4,3) pre1 pre(2)
  let ?S = "wf_algebra.S_A (S (P\<^sub>I (set I)) (E\<^sub>I (set I))) (E\<^sub>I (set I)) (alpha Alpha)" 
  let ?NS = "wf_algebra.NS_A (NS (E\<^sub>I (set I))) (E\<^sub>I (set I)) (alpha Alpha)"
  have pre2: "\<forall>as f. set as \<subseteq> E\<^sub>I (set I) \<longrightarrow> alpha Alpha f as \<in> E\<^sub>I (set I)" 
    by (rule Alpha_list_to_Alpha_EI[OF p1' Alpha_def refl], insert valid, auto)
  note p2 = pre1 pre(1) E\<^sub>IN P\<^sub>IP N_P\<^sub>I_closed EI_PI_mult pre2
  have redtrip: "redtriple_order ?S ?NS ?NS" 
    by (rule coreAlgebra_redtriple_order[OF p2])
  have ce: "ce_compatible ?S" "ce_compatible ?NS" 
    using ce_compat[OF p2 Alpha_def defP] by auto
  note ctxt_closed_S = ctxt_closed_S[OF p2]

  interpret redtriple_order ?S ?NS ?NS by fact

  note wf_alpha_lhs_minus_rhs = wf_alpha_lhs_minus_rhs[OF pre1]

  {
    fix rule :: "('b,'c)rule" 
    assume "check_lpoly_EI_N ?I (alpha_lhs_minus_rhs Alpha rule)" 
    from check_lpoly_EI_N[OF pre(4,3) wf_alpha_lhs_minus_rhs this]
    have "\<forall>\<gamma>. range \<gamma> \<subseteq> E\<^sub>I ?I \<longrightarrow>
      eval_lpoly mat_sq_ring \<gamma> (alpha_lhs_minus_rhs Alpha rule)
      \<in> N" .
    hence "rule \<in> ?NS" 
      by (subst coreAlgebra_NS_A_def[OF p2], auto)
  } note NS_crit = this
  show ?case unfolding core_EI_rel_impl_def Let_def rel_impl.simps Alpha_def[symmetric]
  proof (rule exI[of _ ?S], intro exI[of _ ?NS], intro conjI impI allI
      refl_NST ctxt_NS subst_NS subst_S not_subterm_rel_info.simps ce
          compat_S_NS compat_NS_S trans_S trans_NS S_imp_NS SN top_mono_same, goal_cases)
    show "irrefl ?S" using SN by (metis SN_on_irrefl irrefl_on_def)
    show "?NS \<inter> ?S\<inverse> = {}" by (simp add: \<open>irrefl ?S\<close> co_rewrite_irrefl compat_NS_S)
    show "af_monotone (\<lambda>f. {}) ?S" 
      unfolding af_monotone_def by auto
    show "\<And> cm cc. isOK (no_complexity_check cm cc) \<Longrightarrow> deriv_bound_measure_class ?S cm cc" 
      by (auto simp: isOK_no_complexity)
    show "af_compatible (core_mat_af Alpha) ?NS"
      by (rule core_mat_af[OF p2], auto)
    show "af_compatible (core_mat_af Alpha) ?NS" by fact
  next
    case (10 sig) (* mono *)
    have pre3: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> E\<^sub>I (set I)" 
      apply (intro allI impI, rule Alpha_list_to_Alpha_D[OF def Alpha_def one_in_EI[OF pre(4,3)]])
       apply (insert 10, auto intro!: in_E\<^sub>I_criterion[OF pre(4,3)])
      by (insert valid, auto simp: check_valid_dims_def)
    with ctxt_closed_S show "ctxt.closed ?S" by simp
  next
    case (1 rule)
    hence "check_lpoly_EI_PI ?I I (alpha_lhs_minus_rhs Alpha rule)" 
      by simp
    from check_lpoly_EI_PI[OF pre(4,3) wf_alpha_lhs_minus_rhs refl this]
    have "\<forall>\<beta>. range \<beta> \<subseteq> E\<^sub>I (set I) \<longrightarrow>
      eval_lpoly mat_sq_ring \<beta> (alpha_lhs_minus_rhs Alpha rule) \<in> P\<^sub>I (set I)"
      .
    thus ?case by (subst coreAlgebra_S_A_def[OF p2], auto)
  qed (insert NS_crit, auto)
qed

definition core_MI_rel_impl :: "nat list \<Rightarrow> ('f :: showl,'a)fun_coeffs \<Rightarrow> ('f, 'v :: showl) rel_impl" where 
  "core_MI_rel_impl I fk_cs = (let 
   def = (\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n;
   Alpha = Alpha_list_to_Alpha def fk_cs;
   checkNS = (\<lambda> lr. check (case alpha_lhs_minus_rhs Alpha lr of LPoly c cs \<Rightarrow> 
          (\<forall> a \<in> set (c # map snd cs). in_N a)) 
       (showsl (STR ''could not weakly orient rule '') o showsl_rule lr o
        showsl_nl o showsl (STR ''where lhs - rhs evaluates to '') o showsl (alpha_lhs_minus_rhs Alpha lr))) in
   \<lparr>rel_impl.valid = do {check (\<delta> > 0) (showsl (STR ''delta must be positive''));
       check (Ball (set I) (\<lambda> i. i < n)) (showsl (STR ''indices in I must be below matrix dimension''));
       check (I \<noteq> []) (showsl (STR ''indices I must be non-empty''));
       check_allm check_valid_dims fk_cs;
       check_allm (\<lambda> (fk,_). check (case inter_lpoly Alpha fk of 
          LPoly c cs \<Rightarrow> (\<forall> a \<in> set (c # map snd cs). in_N a) \<and> (\<forall> i \<in> set I. \<exists> a \<in> set (c # map snd cs). \<exists> j \<in> set I. a $$ (i,j) \<ge> 1)) 
        (showsl (STR ''cannot ensure that interpretation of symbol '') o showsl (fst fk) o showsl (STR '' is function from M-I^* to M-I''))) fk_cs
     },
     standard = succeed,
     desc = show_core_matrix_inter_main (STR ''M_I'') n I fk_cs,
     s = (\<lambda> lr. check (case alpha_lhs_minus_rhs Alpha lr of LPoly c cs \<Rightarrow> 
          (\<forall> a \<in> set (c # map snd cs). in_N a) \<and> (\<forall> i \<in> set I. \<exists> a \<in> set (c # map snd cs). \<exists> j \<in> set I. a $$ (i,j) \<ge> \<delta>)) 
       (showsl (STR ''could not strictly orient rule '') o showsl_rule lr o
        showsl_nl o showsl (STR ''where lhs - rhs evaluates to '') o showsl (alpha_lhs_minus_rhs Alpha lr))),
     ns = checkNS, 
     nst = checkNS,
     af = core_mat_af Alpha,
     top_af = core_mat_af Alpha,
     SN = succeed,
     subst_s = succeed,
     ce_compat = succeed,
     co_rewr = succeed,
     top_mono = succeed,
     top_refl = succeed,
     mono_af = (\<lambda> f. {}), \<comment> \<open>IGNORE: not yet implemented\<close>
     mono = (\<lambda> _. check_allm (\<lambda> (_,csc). check (Ball (set (fst csc)) (in_MI I)) 
       (showsl (STR '' require monotone coefficient in M-I''))) fk_cs),
     not_wst = None, \<comment> \<open>IGNORE: not yet implemented\<close>
     not_sst = None, \<comment> \<open>IGNORE: not yet implemented\<close>
     cpx = no_complexity_check \<rparr>)"

lemma core_MI_rel_impl: "rel_impl (core_MI_rel_impl I fk_cs)" 
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?I = "set I"
  let ?def = "(\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n" 
  have def: "?def \<in> carrier_mat n n" by auto
  define Alpha where "Alpha = Alpha_list_to_Alpha ?def fk_cs" 
  note valid = 1[unfolded core_MI_rel_impl_def Let_def, simplified, folded Alpha_def]
  have pre: "0 < \<delta>" "0 \<le> \<delta>" "?I \<subseteq> {..<n}" "?I \<noteq> {}" using valid by auto
  have pre1: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
  proof (intro allI impI, rule Alpha_list_to_Alpha_dim[OF def Alpha_def], goal_cases)
    case (1 f' k' cs' c' f k cs c)
    from valid 1 have "isOK (check_valid_dims ((f, k), cs, c))" by auto
    from this[unfolded check_valid_dims_def split]
    show ?case by (auto simp: N_def)
  qed
  note eval_lpoly_member_via_MI = eval_lpoly_member_via_MI[OF pre(4,3) pre1 pre(2)]
  note M\<^sub>IN = M\<^sub>IN[OF pre(4,3)]
  note L\<^sub>IP = L\<^sub>IP[OF pre(4,3)]
  note N_L\<^sub>I_closed = N_L\<^sub>I_closed[OF pre(4,3)]
  note MI_LI_mult = MI_LI_mult[OF pre(4,3,1)]
  note LI_MI_mult = LI_MI_mult[OF pre(4,3,1)]
  note MI_MI_mult = MI_MI_mult[OF pre(4,3,1)]
  note N_MI_add = N_MI_add[OF pre(4,3,1)]

  have defM: "?def \<in> M\<^sub>I (set I)" using pre(2)
  proof (auto simp: M\<^sub>I_def N_def, goal_cases)
    case (1 i)
    thus ?case using pre by (auto intro!: bexI[of _ i])
  qed
  have defL: "?def \<in> L\<^sub>I (set I)" using pre(2)
  proof (auto simp: L\<^sub>I_def N_def, goal_cases)
    case (1 i)
    thus ?case using pre by (auto intro!: bexI[of _ i])
  qed
  note p1 = pre1 pre(3,2)
  note p1' = pre(4,3) pre1 pre(2)
  let ?S = "wf_algebra.S_A (S (L\<^sub>I (set I)) (M\<^sub>I (set I))) (M\<^sub>I (set I)) (alpha Alpha)" 
  let ?NS = "wf_algebra.NS_A (NS (M\<^sub>I (set I))) (M\<^sub>I (set I)) (alpha Alpha)"
  have pre2: "\<forall>as f. set as \<subseteq> M\<^sub>I (set I) \<longrightarrow> alpha Alpha f as \<in> M\<^sub>I (set I)"
  proof (intro allI impI)
    fix f as 
    assume as: "set as \<subseteq> M\<^sub>I (set I)" 
    define k where "k = length as" 
    show "alpha Alpha f as \<in> M\<^sub>I (set I)" 
    proof (cases "map_of fk_cs (f, k)")
      case None
      obtain cs c where Alph: "Alpha (f,k) = (cs,c)" by force
      note Alpha = Alph[unfolded Alpha_def Alpha_list_to_Alpha_def]
      with None Alpha have "default_Alpha ((\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n) (f, k) = (cs, c)" by auto
      hence "c = ?def" by (auto simp: default_Alpha_def)
      with ensure_Dk_to_D_local[OF pre1 pre(1) M\<^sub>IN L\<^sub>IP N_L\<^sub>I_closed MI_LI_mult LI_MI_mult MI_MI_mult N_MI_add Alph _ _ k_def[symmetric] as]
        defM M\<^sub>IN show ?thesis by auto
    next
      case (Some pair)
      from map_of_SomeD[OF Some, unfolded this]
      have mem: "((f, k), pair) \<in> set fk_cs" by auto
      from defM have MI_ne: "M\<^sub>I (set I) \<noteq> {}" by auto
      obtain c xcs where inter: "inter_lpoly Alpha (f,k) = LPoly c xcs" (is "?e = _") by (cases ?e, auto)
      from valid mem inter 
      have check: "insert c (snd ` set xcs) \<subseteq> N" "(\<forall>i\<in>set I. \<exists>a\<in> insert c (snd ` set xcs). \<exists>j\<in>set I. 1 \<le> a $$ (i, j))" 
        by fastforce+
      from eval_lpoly_member_via_MI[OF wf_inter_lpoly[OF pre1] _ _ inter check, of "M\<^sub>I (set I)" True]
      have ran: "range \<gamma> \<subseteq> M\<^sub>I (set I) \<Longrightarrow> eval_lpoly mat_sq_ring \<gamma> (inter_lpoly Alpha (f, k)) \<in> M\<^sub>I (set I)" for \<gamma>
        by auto
      show ?thesis 
        by (rule inter_lpoly[OF pre1 MI_ne M\<^sub>I_carrier[OF pre(4,3,1)] _ k_def[symmetric] as],
          insert ran, auto)
    qed
  qed
  note p2 = pre1 pre(1) M\<^sub>IN L\<^sub>IP N_L\<^sub>I_closed MI_LI_mult pre2
  have redtrip: "redtriple_order ?S ?NS ?NS" 
    by (rule coreAlgebra_redtriple_order[OF p2])
  have ce: "ce_compatible ?S" "ce_compatible ?NS" 
    using ce_compat[OF p2 Alpha_def defL] by auto
  note ctxt_closed_S = ctxt_closed_S[OF p2]

  interpret redtriple_order ?S ?NS ?NS by fact

  {
    fix rule :: "('b,'c)rule" 
    obtain c cs where alph: "alpha_lhs_minus_rhs Alpha rule = LPoly c cs" 
      by (cases "alpha_lhs_minus_rhs Alpha rule", auto)
    assume "case alpha_lhs_minus_rhs Alpha rule of
        LPoly c cs \<Rightarrow>
          Ball (set (c # map snd cs)) in_N" 
    from this[unfolded alph] 
    have inN: "insert c (snd ` set cs) \<subseteq> N"
      "insert c (snd ` set cs) \<inter> N \<noteq> {}" by auto
    from eval_lpoly_member_via_D[OF p2(1-6) LI_MI_mult 
        MI_MI_mult N_MI_add wf_alpha_lhs_minus_rhs[OF pre1] _ alph inN]  
    have "\<forall>\<beta>. range \<beta> \<subseteq> M\<^sub>I (set I) \<longrightarrow>
      eval_lpoly mat_sq_ring \<beta> (alpha_lhs_minus_rhs Alpha rule) \<in> N"
      by auto
    hence "rule \<in> ?NS" 
      by (subst coreAlgebra_NS_A_def[OF p2], auto)
  } note NS_crit = this
  show ?case unfolding core_MI_rel_impl_def Let_def rel_impl.simps Alpha_def[symmetric]
  proof (rule exI[of _ ?S], intro exI[of _ ?NS], intro conjI impI allI
      refl_NST ctxt_NS subst_NS subst_S full_af not_subterm_rel_info.simps ce
          compat_S_NS compat_NS_S trans_S trans_NS S_imp_NS SN top_mono_same, goal_cases)
    show "irrefl ?S" using SN by (metis SN_on_irrefl irrefl_on_def)
    show "?NS \<inter> ?S\<inverse> = {}" by (simp add: \<open>irrefl ?S\<close> co_rewrite_irrefl compat_NS_S)
    show "af_monotone (\<lambda>f. {}) ?S" 
      unfolding af_monotone_def by auto
    show "\<And> cm cc. isOK (no_complexity_check cm cc) \<Longrightarrow> deriv_bound_measure_class ?S cm cc" 
      by (auto simp: isOK_no_complexity)
    show "af_compatible (core_mat_af Alpha) ?NS"
      by (rule core_mat_af[OF p2], auto)
    show "af_compatible (core_mat_af Alpha) ?NS" by fact
  next
    case (1 rule)
    obtain c cs where alph: "alpha_lhs_minus_rhs Alpha rule = LPoly c cs" 
      by (cases "alpha_lhs_minus_rhs Alpha rule", auto)
    from 1[unfolded alph, simplified]
    have inN: "insert c (snd ` set cs) \<subseteq> N" and 
      inLI: "\<forall>i\<in>set I. (\<exists>a\<in> insert c (snd ` set cs). \<exists>j\<in>set I. \<delta> \<le> a $$ (i, j))" by auto
    from eval_lpoly_member_via_MI[OF wf_alpha_lhs_minus_rhs[OF pre1] _ _ alph inN inLI,
        of "L\<^sub>I (set I)" False] 
    have "\<forall>\<beta>. range \<beta> \<subseteq> M\<^sub>I (set I) \<longrightarrow>
      eval_lpoly mat_sq_ring \<beta> (alpha_lhs_minus_rhs Alpha rule) \<in> L\<^sub>I (set I)"
      by auto
    thus "rule \<in> ?S" 
      by (subst coreAlgebra_S_A_def[OF p2], auto)    
  next
    case (10 sig) (* mono *)
    have pre3: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> M\<^sub>I (set I)" 
      apply (intro allI impI, rule Alpha_list_to_Alpha_D[OF def Alpha_def one_in_MI[OF pre(4,3)]])
      by (insert 10, auto)
    with ctxt_closed_S show "ctxt.closed ?S" by simp
  qed (insert NS_crit, auto)
qed

fun core_rel_impl :: "core_matrix_mode \<Rightarrow> nat list \<Rightarrow> ('f :: showl,'a)fun_coeffs \<Rightarrow> ('f, 'v :: showl) rel_impl"
  where "core_rel_impl E_I = core_EI_rel_impl" 
  | "core_rel_impl M_I = core_MI_rel_impl" 

lemma core_rel_impl: "rel_impl (core_rel_impl mode I fk_cs)"
proof (cases mode)
  case E_I
  from core_EI_rel_impl show ?thesis unfolding E_I by auto
next
  case M_I
  from core_MI_rel_impl show ?thesis unfolding M_I by auto
qed

end

lemmas core_mat_inter_impl_code =
  core_mat_inter_impl.core_EI_rel_impl_def
  core_mat_inter_impl.core_MI_rel_impl_def
  core_mat_inter_impl.core_rel_impl.simps
  core_mat_inter_impl.check_valid_dims_def
  core_mat_inter_impl.in_N_code
  core_mat_inter_impl.in_MI_code
  core_mat_inter_impl.in_LI_code

declare core_mat_inter_impl_code[code]

datatype ('f,'a) core_matrix_inter = Core_Matrix_Inter core_matrix_mode nat "nat list" "('f,'a) fun_coeffs"

definition create_core_matrix_fract where 
  "create_core_matrix_fract (delta :: 'a :: {floor_ceiling,showl}) rel = (case rel of 
    Core_Matrix_Inter mode n I fk_cs \<Rightarrow> core_mat_inter_impl.core_rel_impl n delta mode I fk_cs)" 

lemma create_core_matrix_fract: "rel_impl (create_core_matrix_fract delta rel)"
proof (cases rel)
  case *: (Core_Matrix_Inter mode n I fk_cs)
  show ?thesis unfolding create_core_matrix_fract_def * core_matrix_inter.simps
    by (rule core_mat_inter_impl.core_rel_impl)
qed

definition create_core_matrix_int where 
  "create_core_matrix_int rel = (case rel of 
    Core_Matrix_Inter mode n I fk_cs \<Rightarrow> core_mat_inter_impl.core_rel_impl n (1 :: int) mode I fk_cs)" 

lemma create_core_matrix_int: "rel_impl (create_core_matrix_int rel)"
proof (cases rel)
  case *: (Core_Matrix_Inter mode n I fk_cs)
  have id: "1 \<le> x - (y :: int) = (x > y)" for x y by linarith
  show ?thesis unfolding create_core_matrix_int_def * core_matrix_inter.simps
    by (rule core_mat_inter_impl.core_rel_impl)
qed
end