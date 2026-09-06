(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory GM04_Complete_Checker
  imports
    GM04_Complete_Transformation
    CSR_GM_Transformation
    CSR_Check_Loops
    TRS.Trs_Impl_More
begin

definition gm04_list_set_eq where
  "gm04_list_set_eq xs ys \<longleftrightarrow>
    list_all (\<lambda>x. x \<in> set ys) xs \<and> list_all (\<lambda>y. y \<in> set xs) ys"

lemma gm04_list_set_eq_iff[simp]:
  "gm04_list_set_eq xs ys \<longleftrightarrow> set xs = set ys"
  unfolding gm04_list_set_eq_def list_all_iff by auto

definition gm04_rules_variant_eq where
  "gm04_rules_variant_eq P P' \<longleftrightarrow>
    list_all (\<lambda>p. list_ex (eq_rule_mod_vars p) P') P \<and>
    list_all (\<lambda>p'. list_ex (eq_rule_mod_vars p') P) P'"

lemma gm04_rules_variant_eq_left:
  assumes "gm04_rules_variant_eq P P'" and "p \<in> set P"
  shows "\<exists>p'\<in>set P'. p =\<^sub>v p'"
  using assms unfolding gm04_rules_variant_eq_def
  by (auto simp: list_all_iff list_ex_iff)

lemma gm04_rules_variant_eq_right:
  assumes "gm04_rules_variant_eq P P'" and "p' \<in> set P'"
  shows "\<exists>p\<in>set P. p' =\<^sub>v p"
  using assms unfolding gm04_rules_variant_eq_def
  by (auto simp: list_all_iff list_ex_iff)

definition gm04_rules_variant_subset where
  "gm04_rules_variant_subset P P' \<longleftrightarrow>
    list_all (\<lambda>p'. list_ex (eq_rule_mod_vars p') P) P'"

lemma gm04_rules_variant_subset_right:
  assumes "gm04_rules_variant_subset P P'" and "p' \<in> set P'"
  shows "\<exists>p\<in>set P. p' =\<^sub>v p"
  using assms unfolding gm04_rules_variant_subset_def
  by (auto simp: list_all_iff list_ex_iff)

definition gm04_roles_fresh_list where
  "gm04_roles_fresh_list active mark proper ok top_sym F \<longleftrightarrow>
    distinct [active,mark,proper,ok,top_sym] \<and>
    list_all (\<lambda>(f,n). f \<notin> {active,mark,proper,ok,top_sym}) F"

fun gm04_extra_nullaries where
  "gm04_extra_nullaries proper ok F [] = []"
| "gm04_extra_nullaries proper ok F
      ((Fun p [Fun c []], Fun q [Fun d []]) # R) =
    (if p = proper \<and> q = ok \<and> c = d \<and> (c,0) \<notin> set F
     then (c,0) # gm04_extra_nullaries proper ok F R
     else gm04_extra_nullaries proper ok F R)"
| "gm04_extra_nullaries proper ok F (r # R) =
    gm04_extra_nullaries proper ok F R"

fun gm04_source_proof_is_global where
  "gm04_source_proof_is_global (Existing_CSR_Proof old) =
    extended_csr_proof_is_global old"
| "gm04_source_proof_is_global p = False"

lemma gm04_roles_fresh_list_sound:
  assumes "gm04_roles_fresh_list active mark proper ok top_sym F"
  shows "gm04_roles_fresh active mark proper ok top_sym F"
  using assms unfolding gm04_roles_fresh_list_def gm04_roles_fresh_def
    list_all_iff by auto

definition gm04_schema_signature_list where
  "gm04_schema_signature_list active mark proper ok F S \<longleftrightarrow>
    list_all (\<lambda>(f,n). (f,n) \<in> set F \<or>
      (f,n) \<in> {(active,1),(mark,1),(proper,1),(ok,1)})
      (funas_trs_list S)"

lemma gm04_schema_signature_list_sound:
  assumes "gm04_schema_signature_list active mark proper ok F S"
  shows "funas_trs (set S) \<subseteq> set F \<union>
    {(active,1),(mark,1),(proper,1),(ok,1)}"
  using assms unfolding gm04_schema_signature_list_def list_all_iff by auto

definition gm04_pair_args_signature_list where
  "gm04_pair_args_signature_list top_sharp P S \<longleftrightarrow>
    list_all (\<lambda>fn. fn \<in> set (funas_trs_list S))
      (funas_args_trs_list P)"

lemma gm04_pair_args_signature_list_sound:
  assumes exact: "set P =
      set (gm04_top_pairs active mark proper ok top_sharp)"
    and check: "gm04_pair_args_signature_list top_sharp P S"
  shows "funas_args_trs
      (set (gm04_top_pairs active mark proper ok top_sharp))
      \<subseteq> funas_trs (set S)"
  using check exact unfolding gm04_pair_args_signature_list_def
    list_all_iff by auto

fun gm04_residual_assm ::
  "('f::compare_order,'l::compare_order,'v) trsLL \<Rightarrow>
    ('f,'l,'v) trsLL \<Rightarrow> ('f,'l,'v) termsLL \<Rightarrow>
    ('f,'l,'v) assm list \<Rightarrow> bool"
where
  "gm04_residual_assm P S Q
      [Finite_assm [] (True,m,P',Pw,Q',R,Rw)] =
    (gm04_rules_variant_eq P P' \<and> Pw = [] \<and>
     isOK (check_NF_terms_eq Q Q') \<and> R = [] \<and>
     gm04_rules_variant_subset S Rw)"
| "gm04_residual_assm P S Q _ = False"

lemma finite_dpp_strict_rules_imp_weak_rules:
  assumes "finite_dpp (nfs,m,P,{},Q,S,{})"
  shows "finite_dpp (nfs,m,P,{},Q,{},S)"
  by (rule finite_dpp_mono[OF assms]) auto

lemma gm04_finite_residual_variants:
  assumes fin: "finite_dpp (True,m,set P,{},set Q,set S,{})"
    and pairs: "gm04_rules_variant_eq P P'"
    and q: "isOK (check_NF_terms_eq Q Q')"
    and rules: "gm04_rules_variant_eq S Rw"
  shows "finite_dpp (True,m,set P',{},set Q',{},set Rw)"
proof -
  have weak: "finite_dpp (True,m,set P,{},set Q,{},set S)"
    by (rule finite_dpp_strict_rules_imp_weak_rules[OF fin])
  from q have qeq: "NF_terms (set Q) = NF_terms (set Q')" by simp
  have finq: "finite_dpp (True,m,set P,{},set Q',{},set S)"
    by (rule finite_dpp_mono[OF weak]) (use qeq in auto)
  have psub: "rqrstep True (set Q') (set P') \<subseteq>
      rqrstep True (set Q') (set P)"
    by (rule rqrstep_rename_vars)
       (use gm04_rules_variant_eq_right[OF pairs] in blast)
  have rsub: "qrstep True (set Q') (set Rw) \<subseteq>
      qrstep True (set Q') (set S)"
    by (rule qrstep_rename_vars)
       (use gm04_rules_variant_eq_right[OF rules] in blast)
  have rsub': "qrstep True (set Q') (set S) \<subseteq>
      qrstep True (set Q') (set Rw)"
    by (rule qrstep_rename_vars)
       (use gm04_rules_variant_eq_left[OF rules] in blast)
  show ?thesis
    apply (rule finite_dpp_mono_plain[OF finq])
       apply (use psub in simp)
      apply (use psub in simp)
     apply simp
    apply (use rsub rsub' in auto)
    done
qed

lemma gm04_finite_residual_rule_subset:
  assumes fin: "\<And>m. finite_dpp (True,m,set P,{},set Q,set S,{})"
    and pairs: "gm04_rules_variant_eq P P'"
    and q: "isOK (check_NF_terms_eq Q Q')"
    and rules: "gm04_rules_variant_subset S Rw"
  shows "finite_dpp (True,m,set P',{},set Q',{},set Rw)"
proof -
  have rules_refl: "gm04_rules_variant_eq S S"
  proof (unfold gm04_rules_variant_eq_def, intro conjI)
    show "list_all (\<lambda>p. list_ex (eq_rule_mod_vars p) S) S"
      unfolding list_all_iff list_ex_iff
      using eq_rule_mod_vars_refl by blast
    show "list_all (\<lambda>p'. list_ex (eq_rule_mod_vars p') S) S"
      unfolding list_all_iff list_ex_iff
      using eq_rule_mod_vars_refl by blast
  qed
  have full: "finite_dpp (True,False,set P',{},set Q',{},set S)"
    by (rule gm04_finite_residual_variants[OF fin[of False] pairs q rules_refl])
  show ?thesis
    unfolding finite_dpp_def
  proof (clarify)
    fix s t \<sigma>
    assume target: "min_ichain (True,m,set P',{},set Q',{},set Rw) s t \<sigma>"
    then have target_i: "ichain (True,m,set P',{},set Q',{},set Rw) s t \<sigma>"
      by simp
    have target_i_false: "ichain (True,False,set P',{},set Q',{},set Rw) s t \<sigma>"
      using target_i unfolding ichain.simps by simp
    have rsub: "qrstep True (set Q') (set Rw) \<subseteq>
        qrstep True (set Q') (set S)"
      by (rule qrstep_rename_vars)
         (use gm04_rules_variant_subset_right[OF rules] in blast)
    have source_i: "ichain (True,False,set P',{},set Q',{},set S) s t \<sigma>"
      by (rule ichain_mono_plain[OF target_i_false]) (use rsub in auto)
    then have "min_ichain (True,False,set P',{},set Q',{},set S) s t \<sigma>"
      by (simp add: minimal_cond_def)
    with full show False unfolding finite_dpp_def by blast
  qed
qed

lemma gm04_residual_assm_holds:
  assumes fin: "\<And>m. finite_dpp
      (True,m,set P,{},set Q,set S,{})"
    and check: "gm04_residual_assm P S Q assms"
  shows "\<forall>a\<in>set assms. holds a"
proof (cases assms)
  case Nil
  then show ?thesis by simp
next
  case (Cons a tail)
  have tail: "tail = []"
    using check Cons by (cases tail) simp_all
  show ?thesis
  proof (cases a)
    case (Finite_assm obligations dpp)
    obtain nfs m P' Pw Q' R' Rw where
      dpp: "dpp = (nfs,m,P',Pw,Q',R',Rw)"
      by (cases dpp) auto
    show ?thesis
      using check fin Cons tail Finite_assm dpp
    by (cases obligations; cases nfs; cases Pw; cases R';
          simp_all add: gm04_finite_residual_rule_subset[OF fin])
  next
    case SN_assm
    then show ?thesis using check Cons tail by simp
  next
    case SN_FP_assm
    then show ?thesis using check Cons tail by simp
  next
    case Unknown_assm
    then show ?thesis using check Cons tail by simp
  next
    case Not_SN_assm
    then show ?thesis using check Cons tail by simp
  next
    case Not_RelSN_assm
    then show ?thesis using check Cons tail by simp
  next
    case Not_SN_FP_assm
    then show ?thesis using check Cons tail by simp
  next
    case Infinite_assm
    then show ?thesis using check Cons tail by simp
  next
    case Complexity_assm
    then show ?thesis using check Cons tail by simp
  qed
qed

datatype ('f,'l,'v) gm04_complete_transformation_proof =
  GM04_Complete_Transformation_Proof
    "('f,'l) lab muL"
    "('f,'l,'v) trsLL"
    "('f,'l) lab" "('f,'l) lab" "('f,'l) lab" "('f,'l) lab"
    "('f,'l) lab" "('f,'l) lab"
    "('f,'l,'v) trs_termination_proof"
    "('f,'l,'v) gm_extended_csr_termination_proof"

datatype ('f,'l,'v) gm04_complete_nontermination_proof =
  GM04_Complete_Nontermination_Proof
    "('f,'l) lab muL"
    "('f,'l,'v) trsLL"
    "('f,'l) lab" "('f,'l) lab" "('f,'l) lab" "('f,'l) lab"
    "('f,'l) lab"
    "(('f,'l) lab,'v) trs_loop_prf"

fun check_gm04_complete_nontermination_proof ::
  "showsl \<Rightarrow> bool \<Rightarrow>
   ('f::{showl,compare_order,countable},label_type,string) termsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) gm04_complete_nontermination_proof \<Rightarrow>
   showsl check"
where
  "check_gm04_complete_nontermination_proof i nfs Q T Tw
      (GM04_Complete_Nontermination_Proof \<mu> R active mark proper ok
        top_sym source_loop) =
    debug i (STR ''complete Giesl-Middeldorp nontermination transformation'') (do {
      check (\<not> nfs) (showsl_lit (STR ''transformed problem is not full rewriting''));
      check (Q = []) (showsl_lit (STR ''transformed problem has a nonempty Q component''));
      check (Tw = []) (showsl_lit (STR ''transformed problem has weak rules''));
      check_wf_trs R;
      let F = remdups (funas_trs_list R);
      check (list_ex (\<lambda>(_,n). n = 0) F)
        (showsl_lit (STR ''source signature has no constant for grounding''));
      check (gm04_roles_fresh_list active mark proper ok top_sym F)
        (showsl_lit (STR ''GM04 administrative symbols are not fresh''));
      let C = gm04_complete_rules (mu_of \<mu>) active mark proper ok top_sym F R;
      check_variants_trs T C;
      check_variants_trs C T;
      check_csr_loop \<mu> R source_loop
    })"

lemma check_gm04_complete_nontermination_proof_sound:
  assumes checked: "isOK (check_gm04_complete_nontermination_proof
      i nfs Q T Tw p)"
  shows "\<not> SN_qrel (nfs,set Q,set T,set Tw)"
proof (cases p)
  case (GM04_Complete_Nontermination_Proof \<mu> R active mark proper ok_sym
      top_sym source_loop)
  let ?F = "remdups (funas_trs_list R)"
  let ?C = "gm04_complete_rules (mu_of \<mu>) active mark proper ok_sym
    top_sym ?F R"
  from checked GM04_Complete_Nontermination_Proof have nfs: "\<not> nfs"
    and q: "Q = []" and weak: "Tw = []"
    and has_constant: "list_ex (\<lambda>(_,n). n = 0) ?F"
    and fresh_list:
      "gm04_roles_fresh_list active mark proper ok_sym top_sym ?F"
    and variants_tc: "isOK (check_variants_trs T ?C)"
    and variants_ct: "isOK (check_variants_trs ?C T)"
    and source_ok: "isOK (check_csr_loop \<mu> R source_loop)"
    by (auto simp: Let_def)
  from has_constant obtain c where c: "(c,0) \<in> set ?F"
    by (auto simp: list_ex_iff)
  have fresh: "gm04_roles_fresh active mark proper ok_sym top_sym ?F"
    by (rule gm04_roles_fresh_list_sound[OF fresh_list])
  have source_signature: "funas_trs (set R) \<subseteq> set ?F" by simp
  have schema: "gm04_complete_schema_check (mu_of \<mu>) active mark proper
      ok_sym top_sym ?F R ?C"
    unfolding gm04_complete_schema_check_def
    using fresh source_signature by simp
  have finite_mu: "\<And>fn. finite (mu_of \<mu> fn)"
  proof -
    fix fn
    show "finite (mu_of \<mu> fn)"
    proof (cases fn)
      case (Pair f n)
      then show ?thesis
        unfolding mu_of_def Let_def
        by (cases "map_of \<mu> (f,n)") simp_all
    qed
  qed
  have source_not: "\<not> SN (sig_step (set ?F)
      (csstep (mu_of \<mu>) (set R)))"
    using check_csr_loop_sound[OF source_ok] by simp
  show ?thesis
  proof
    assume root: "SN_qrel (nfs,set Q,set T,set Tw)"
    from root nfs q weak have transformed: "SN (rstep (set T))"
      unfolding SN_qrel_def by simp
    have transformed_c: "SN (rstep (set ?C))"
      by (rule SN_subset[OF transformed check_variants_trs_rstep[OF variants_ct]])
    from gm04_complete_SN_imp_source_SN[
      OF transformed_c c finite_mu schema subset_refl] source_not
    show False by contradiction
  qed
qed

fun check_gm04_complete_transformation_proof ::
  "('tp, ('f::{showl,compare_order,countable},label_type) lab,string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab,string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> bool \<Rightarrow>
   ('f,label_type,string) termsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) gm04_complete_transformation_proof \<Rightarrow>
   showsl check"
where
  "check_gm04_complete_transformation_proof I J i nfs Q T Tw
      (GM04_Complete_Transformation_Proof \<mu> R active mark proper ok
        top_sym top_sharp child source_child) =
    debug i (STR ''complete Giesl-Middeldorp inverse transformation'') (do {
      check nfs (showsl_lit (STR ''transformed problem is not innermost''));
      check (Tw = []) (showsl_lit (STR ''transformed problem has weak rules''));
      check_wf_trs R;
      let F0 = remdups (funas_trs_list R);
      let F = remdups (F0 @ gm04_extra_nullaries proper ok F0 T);
      check (F = F0 \<or> gm04_source_proof_is_global source_child)
        (showsl_lit (STR ''GM04 signature extension requires a global source proof''));
      check (gm04_roles_fresh_list active mark proper ok top_sym F)
        (showsl_lit (STR ''GM04 administrative symbols are not fresh''));
      let S = gm04_non_top_rules (mu_of \<mu>) active mark proper ok F R;
      let P = gm04_top_pairs active mark proper ok top_sharp;
      let C = gm04_complete_rules (mu_of \<mu>) active mark proper ok top_sym F R;
      check_variants_trs T C;
      check_variants_trs C T;
      check (gm04_schema_signature_list active mark proper ok F S)
        (showsl_lit (STR ''GM04 non-top signature is invalid''));
      check (gm04_pair_args_signature_list top_sharp P S)
        (showsl_lit (STR ''GM04 residual pair arguments are outside the non-top signature''));
      check (list_all (\<lambda>(f,n). f \<noteq> top_sharp) (funas_trs_list S))
        (showsl_lit (STR ''GM04 residual sharp symbol is not fresh''));
      check_gm_extended_csr_termination_proof I J False (add_index i 1)
        \<mu> R source_child;
      check_trs_termination_proof I J True (add_index i 2)
        (tp_ops.mk I nfs Q T Tw) child;
      check (gm04_residual_assm P S (map fst S) (sn_assms True child))
        (showsl_lit (STR ''ordinary proof does not have exactly the certified GM04 residual''))
    })"

lemma check_gm04_complete_transformation_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_gm04_complete_transformation_proof
      I J i nfs Q T Tw p)"
  shows "SN_qrel (nfs,set Q,set T,set Tw)"
proof (cases p)
  case (GM04_Complete_Transformation_Proof \<mu> R active mark proper ok_sym
      top_sym top_sharp child source_child)
  let ?BaseSig = "remdups (funas_trs_list R)"
  let ?F = "remdups (?BaseSig @ gm04_extra_nullaries proper ok_sym ?BaseSig T)"
  let ?S = "gm04_non_top_rules (mu_of \<mu>) active mark proper ok_sym ?F R"
  let ?P = "gm04_top_pairs active mark proper ok_sym top_sharp"
  have child_raw:
      "isOK (check_trs_termination_proof I J True (add_index i 2)
        (tp_ops.mk I nfs Q T Tw) child)"
    using ok GM04_Complete_Transformation_Proof
    by (auto simp: Let_def)
  have global_or_same:
      "?F = ?BaseSig \<or> gm04_source_proof_is_global source_child"
    using ok GM04_Complete_Transformation_Proof
    by (simp add: Let_def)
  from ok GM04_Complete_Transformation_Proof have nfs: nfs
    and weak: "Tw = []"
    and wf_source: "wf_trs (set R)"
    and fresh_list:
      "gm04_roles_fresh_list active mark proper ok_sym top_sym ?F"
    and schema_check:
      "gm04_schema_signature_list active mark proper ok_sym ?F ?S"
    and pair_check:
      "gm04_pair_args_signature_list top_sharp ?P ?S"
    and sharp_fresh:
      "list_all (\<lambda>(f,n). f \<noteq> top_sharp) (funas_trs_list ?S)"
    and source_ok:
      "isOK (check_gm_extended_csr_termination_proof I J False
        (add_index i 1) \<mu> R source_child)"
    and residual:
      "gm04_residual_assm ?P ?S (map fst ?S) (sn_assms True child)"
    by (simp_all add: Let_def)
  have child_ok:
      "isOK (check_trs_termination_proof I J True (add_index i 2)
        (tp_ops.mk I True Q T []) child)"
    using child_raw nfs weak by simp
  have F0raw: "set ?BaseSig = set (funas_trs_list R)"
    by simp
  have source: "SN (sig_step (set ?F)
      (csstep (mu_of \<mu>) (set R)))"
  proof (cases "?F = ?BaseSig")
    case True
    have source0: "SN (sig_step (set (funas_trs_list R))
        (csstep (mu_of \<mu>) (set R)))"
      by (rule check_gm_extended_csr_termination_proof_sound[OF I J source_ok])
    have FF0: "set ?F = set ?BaseSig"
      by (rule arg_cong[OF True])
    have Fraw: "set ?F = set (funas_trs_list R)"
      using FF0 F0raw by blast
    show ?thesis
      by (subst Fraw, rule source0)
  next
    case False
    with global_or_same have global:
      "gm04_source_proof_is_global source_child" by blast
    then obtain old where source_child:
      "source_child = Existing_CSR_Proof old"
      and old_global: "extended_csr_proof_is_global old"
      by (cases source_child) auto
    have global_source: "SN (csstep (mu_of \<mu>) (set R))"
      using check_gm_existing_global_sound[OF I J _ old_global]
        source_ok source_child by simp
    show ?thesis
      by (rule SN_subset[OF global_source], unfold sig_step_def, auto)
  qed
  have fresh: "gm04_roles_fresh active mark proper ok_sym top_sym ?F"
    by (rule gm04_roles_fresh_list_sound[OF fresh_list])
  have signature: "funas_trs (set R) \<subseteq> set ?F" by simp
  have wf_S: "wf_trs (set ?S)"
    by (rule gm04_non_top_rules_wf[OF wf_source])
  have fresh_top: "\<not> defined (set ?S) (top_sharp,1)"
  proof
    assume def: "defined (set ?S) (top_sharp,1)"
    from defined_funas_trs[OF def]
    have "(top_sharp,1) \<in> set (funas_trs_list ?S)" by simp
    with sharp_fresh show False
      by (auto simp: list_all_iff)
  qed
  have pair_args: "funas_args_trs (set ?P) \<subseteq> funas_trs (set ?S)"
    by (rule gm04_pair_args_signature_list_sound[OF refl pair_check])
  have schema_sig: "funas_trs (set ?S) \<subseteq> set ?F \<union>
      {(active,1),(mark,1),(proper,1),(ok_sym,1)}"
    by (rule gm04_schema_signature_list_sound[OF schema_check])
  have finite_mu: "\<And>f n. finite (mu_of \<mu> (f,n))"
  proof -
    fix f n
    show "finite (mu_of \<mu> (f,n))"
      unfolding mu_of_def Let_def
      by (cases "map_of \<mu> (f,n)") simp_all
  qed
  have fin: "\<And>m. finite_dpp
      (True,m,set ?P,{},set (map fst ?S),set ?S,{})"
  proof -
    fix m
    have q: "set (map fst ?S) = lhss (set ?S)"
      by auto
    show "finite_dpp
        (True,m,set ?P,{},set (map fst ?S),set ?S,{})"
      unfolding q
      by (rule gm04_finite_schema_top_pairs_q_sig[
          OF gm04_inj_clean_string source refl fresh signature wf_source
            wf_S finite_mu fresh_top pair_args schema_sig])
  qed
  have assumptions: "\<forall>a\<in>set (sn_assms True child). holds a"
    by (rule gm04_residual_assm_holds[OF fin residual])
  have root: "SN_qrel (tp_ops.qreltrs I (tp_ops.mk I True Q T []))"
    by (rule check_trs_termination_proof_with_assms[
      OF I J child_ok assumptions])
  interpret tp_spec I by (rule I)
  from root nfs weak show ?thesis by simp
qed

end
