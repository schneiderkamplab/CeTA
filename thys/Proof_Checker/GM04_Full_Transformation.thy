(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory GM04_Full_Transformation
  imports
    Proof_Checker.GM04_Sanitizing_Phase
    Proof_Checker_Base.Check_Termination
begin

text \<open>
  Full-rewriting completeness for the complete Giesl--Middeldorp
  transformation.  This layer is intentionally separate from the established
  innermost inverse checker while its persistence argument is developed.
\<close>

theorem aaecc_structural_termination:
  fixes R1 R2 :: "('f,'v::infinite) trs" and F :: "'f sig"
  assumes sep: "aaecc_signature_separated F R1 R2"
    and wf: "wf_trs (R1 \<union> R2)"
    and structural_SN: "SN (sig_step_below (- F) (rrstep R2) \<union>
      sig_step_below (- F) (rstep R1))"
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
    for a b :: "('f,'v) term"
    using step_preserves_SN_on[OF ab] a by auto
  have X_subterm_closed: "b \<in> ?X" if a: "a \<in> ?X" and ba: "b \<lhd> a"
    for a b :: "('f,'v) term"
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
  let ?E = "\<lambda>i. Term.root (f i) \<notin> Some ` F \<and>
    Term.root (f (Suc i)) \<in> Some ` F"
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
  have rooted_step: "Term.root (f (Suc i)) \<in> Some ` F"
    if "Term.root (f i) \<in> Some ` F" for i
    by (rule aaecc_root_in_signature_preserved[OF sep wf steps[of i] that])
  have no_exception_tail: "\<exists>m. \<forall>i>m. \<not> ?E i"
  proof (cases "\<exists>k. Term.root (f k) \<in> Some ` F")
    case False
    show ?thesis
    proof (intro exI[of _ 0] allI impI notI)
      fix i
      assume "i > 0" and "?E i"
      with False show False by auto
    qed
  next
    case True
    then obtain k where rooted: "Term.root (f k) \<in> Some ` F" by auto
    have rooted_tail: "Term.root (f (k+n)) \<in> Some ` F" for n
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
      have "Term.root (f i) \<in> Some ` F"
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

definition gm04_swap_symbols where
  "gm04_swap_symbols a b f =
    (if f = a then b else if f = b then a else f)"

lemma gm04_swap_symbols_fixed:
  assumes "f \<noteq> a" "f \<noteq> b"
  shows "gm04_swap_symbols a b f = f"
  using assms unfolding gm04_swap_symbols_def by simp

lemma gm04_swap_top_root_step:
  assumes distinct: "top_sym \<noteq> top_sharp"
    and roles: "active \<notin> {top_sym,top_sharp}"
      "mark \<notin> {top_sym,top_sharp}"
      "proper \<notin> {top_sym,top_sharp}"
      "ok \<notin> {top_sym,top_sharp}"
    and step: "(s,t) \<in> rrstep
      (set (gm04_top_rules active mark proper ok top_sym))"
  shows "(map_funs_term (gm04_swap_symbols top_sym top_sharp) s,
      map_funs_term (gm04_swap_symbols top_sym top_sharp) t)
    \<in> subst.closure
      (set (gm04_top_pairs active mark proper ok top_sharp))"
proof -
  from step obtain l r \<sigma> where
      lr: "(l,r) \<in> set (gm04_top_rules active mark proper ok top_sym)"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by blast
  from lr consider
      (mark) "l = Fun top_sym [Fun mark [Var ''__gm04_x'']]"
        "r = Fun top_sym [Fun proper [Var ''__gm04_x'']]"
    | (ok) "l = Fun top_sym [Fun ok [Var ''__gm04_x'']]"
        "r = Fun top_sym [Fun active [Var ''__gm04_x'']]"
    unfolding gm04_top_rules_def by auto
  then show ?thesis
  proof cases
    case mark
    have pair: "(Fun top_sharp [Fun mark [Var ''__gm04_x'']],
        Fun top_sharp [Fun proper [Var ''__gm04_x'']])
      \<in> set (gm04_top_pairs active mark proper ok top_sharp)"
      unfolding gm04_top_pairs_def by simp
    have inst: "(Fun top_sharp [Fun mark [Var ''__gm04_x'']]
          \<cdot> map_funs_subst (gm04_swap_symbols top_sym top_sharp) \<sigma>,
        Fun top_sharp [Fun proper [Var ''__gm04_x'']]
          \<cdot> map_funs_subst (gm04_swap_symbols top_sym top_sharp) \<sigma>)
      \<in> subst.closure
        (set (gm04_top_pairs active mark proper ok top_sharp))"
      by (rule subst.closure.intros[OF pair])
    from inst distinct roles show ?thesis
      unfolding s t mark gm04_swap_symbols_def
      by (simp add: map_funs_subst_distrib)
  next
    case ok
    have pair: "(Fun top_sharp [Fun ok [Var ''__gm04_x'']],
        Fun top_sharp [Fun active [Var ''__gm04_x'']])
      \<in> set (gm04_top_pairs active mark proper ok top_sharp)"
      unfolding gm04_top_pairs_def by simp
    have inst: "(Fun top_sharp [Fun ok [Var ''__gm04_x'']]
          \<cdot> map_funs_subst (gm04_swap_symbols top_sym top_sharp) \<sigma>,
        Fun top_sharp [Fun active [Var ''__gm04_x'']]
          \<cdot> map_funs_subst (gm04_swap_symbols top_sym top_sharp) \<sigma>)
      \<in> subst.closure
        (set (gm04_top_pairs active mark proper ok top_sharp))"
      by (rule subst.closure.intros[OF pair])
    from inst distinct roles show ?thesis
      unfolding s t ok gm04_swap_symbols_def
      by (simp add: map_funs_subst_distrib)
  qed
qed

lemma gm04_swap_administrative_step:
  assumes no_top: "top_sym \<notin> funs_trs S"
    and no_sharp: "top_sharp \<notin> funs_trs S"
    and step: "(s,t) \<in> rstep S"
  shows "(map_funs_term (gm04_swap_symbols top_sym top_sharp) s,
      map_funs_term (gm04_swap_symbols top_sym top_sharp) t) \<in> rstep S"
proof (rule rstep_map_funs_term[OF _ step])
  fix f
  assume "f \<in> funs_trs S"
  with no_top no_sharp show
    "gm04_swap_symbols top_sym top_sharp f = f"
    unfolding gm04_swap_symbols_def by auto
qed

lemma gm04_finite_top_pairs_imp_relative_top_rules:
  assumes distinct: "top_sym \<noteq> top_sharp"
    and roles: "active \<notin> {top_sym,top_sharp}"
      "mark \<notin> {top_sym,top_sharp}"
      "proper \<notin> {top_sym,top_sharp}"
      "ok \<notin> {top_sym,top_sharp}"
    and no_top: "top_sym \<notin> funs_trs S"
    and no_sharp: "top_sharp \<notin> funs_trs S"
    and finite: "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
  shows "SN_rel
    (rrstep (set (gm04_top_rules active mark proper ok top_sym)))
    (rstep S)"
proof -
  from finite have target: "SN_rel
      (subst.closure
        (set (gm04_top_pairs active mark proper ok top_sharp)))
      (rstep S)"
    unfolding finite_dpp_iff_SN_rel by simp
  show ?thesis
  proof (rule SN_rel_map[OF target,
      where f="map_funs_term
        (gm04_swap_symbols top_sym top_sharp)"])
    fix s t
    assume step: "(s,t) \<in> rrstep
      (set (gm04_top_rules active mark proper ok top_sym))"
    from gm04_swap_top_root_step[OF distinct roles step]
    show "(map_funs_term (gm04_swap_symbols top_sym top_sharp) s,
        map_funs_term (gm04_swap_symbols top_sym top_sharp) t)
      \<in> (subst.closure
          (set (gm04_top_pairs active mark proper ok top_sharp)) \<union>
          rstep S)\<^sup>* O
        subst.closure
          (set (gm04_top_pairs active mark proper ok top_sharp)) O
        (subst.closure
          (set (gm04_top_pairs active mark proper ok top_sharp)) \<union>
          rstep S)\<^sup>*"
      by regexp
  next
    fix s t
    assume step: "(s,t) \<in> rstep S"
    from gm04_swap_administrative_step[OF no_top no_sharp step]
    show "(map_funs_term (gm04_swap_symbols top_sym top_sharp) s,
        map_funs_term (gm04_swap_symbols top_sym top_sharp) t)
      \<in> (subst.closure
          (set (gm04_top_pairs active mark proper ok top_sharp)) \<union>
          rstep S)\<^sup>*"
      by regexp
  qed
qed

theorem gm04_complete_SN_from_innermost_top_pairs:
  fixes S :: "('f,string) trs"
  assumes distinct: "top_sym \<noteq> top_sharp"
    and roles: "active \<notin> {top_sym,top_sharp}"
      "mark \<notin> {top_sym,top_sharp}"
      "proper \<notin> {top_sym,top_sharp}"
      "ok \<notin> {top_sym,top_sharp}"
    and no_top: "top_sym \<notin> funs_trs S"
    and no_sharp: "top_sharp \<notin> funs_trs S"
    and wf: "wf_trs S"
    and administrative: "SN (rstep S)"
    and wcr: "WCR_on (qrstep True {} S)
      {t. SN_on (qrstep True {} S) {t}}"
    and no_overlap: "critical_pairs ren
      (set (gm04_top_pairs active mark proper ok top_sharp)) S = {}"
    and finite_innermost: "finite_dpp (True,True,
      set (gm04_top_pairs active mark proper ok top_sharp),{},lhss S,{},S)"
  shows "SN
    (sig_step_below (- {(top_sym,1)})
        (rrstep (set (gm04_top_rules active mark proper ok top_sym))) \<union>
     sig_step_below (- {(top_sym,1)}) (rstep S))"
proof -
  have lhs_fun: "\<And>l r. (l,r) \<in> S \<Longrightarrow> is_Fun l"
    using wf unfolding wf_trs_def by blast
  have nf_subset: "NF_trs S \<subseteq> NF_terms {}" by simp
  have no_overlap': "critical_pairs ren
      (set (gm04_top_pairs active mark proper ok top_sharp) \<union> {}) S = {}"
    using no_overlap by simp
  have finite_minimal: "finite_dpp (True,True,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
    by (rule switch_to_innermost_proc[
        OF wcr nf_subset no_overlap' TrueI _ finite_innermost],
      use lhs_fun in auto)
  have all_SN: "\<And>t. SN_on (rstep S) {t}"
    using administrative unfolding SN_on_def by blast
  have finite_ordinary: "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
    using finite_minimal all_SN
    unfolding finite_dpp_iff_SN_rel by simp
  have relative: "SN_rel
      (rrstep (set (gm04_top_rules active mark proper ok top_sym)))
      (rstep S)"
    by (rule gm04_finite_top_pairs_imp_relative_top_rules[
        OF distinct roles no_top no_sharp finite_ordinary])
  from gm04_SN_rel_and_SN_imp_SN_union[OF relative administrative]
  have combined: "SN
      (rrstep (set (gm04_top_rules active mark proper ok top_sym)) \<union>
       rstep S)" .
  show ?thesis
    by (rule SN_subset[OF combined], unfold sig_step_below_def, auto)
qed

lemma gm04_non_top_excludes_top:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and rule: "lr \<in> set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
  shows "(top_sym,n) \<notin> funas_rule lr"
proof -
  from rule consider
      (source) "lr \<in> set (gm04_source_rules active mark R)"
    | (active) "lr \<in> set (gm04_active_rules \<mu> active F)"
    | (mark) "lr \<in> set (gm04_mark_rules \<mu> mark F)"
    | (proper) "lr \<in> set (map (gm04_proper_rule proper ok) F)"
    | (ok) "lr \<in> set (map (gm04_ok_rule proper ok)
        (filter (\<lambda>fn. snd fn > 0) F))"
    unfolding gm04_non_top_rules_def by auto
  then show ?thesis
  proof cases
    case source
    then obtain l r where lr: "lr = (Fun active [l],Fun mark [r])"
      and source_rule: "(l,r) \<in> set R"
      unfolding gm04_source_rules_def by auto
    from fresh have roles: "top_sym \<noteq> active" "top_sym \<noteq> mark"
      unfolding gm04_roles_fresh_def by auto
    show ?thesis
    proof (rule notI)
      assume top: "(top_sym,n) \<in> funas_rule lr"
      from top lr roles have top_source: "(top_sym,n) \<in> funas_rule (l,r)"
        unfolding funas_rule_def by auto
      from source_rule top_source signature have top_F: "(top_sym,n) \<in> set F"
        unfolding funas_trs_def by auto
      from fresh top_F show False
        unfolding gm04_roles_fresh_def by auto
    qed
  next
    case active
    then obtain f arity i where fn: "(f,arity) \<in> set F"
      and ipos: "i < arity"
      and lr: "lr = gm04_active_rule active (f,arity) i"
      unfolding gm04_active_rules_def by auto
    from fresh fn have neq: "top_sym \<noteq> active" "top_sym \<noteq> f"
      unfolding gm04_roles_fresh_def by auto
    have nth_var: "gm04_vars arity ! i = Var (x\<^sub>1_to_x\<^sub>n arity ! i)"
      using ipos unfolding gm04_vars_def by simp
    have updated: "set ((gm04_vars arity)
        [i := Fun active [(gm04_vars arity) ! i]])
        \<subseteq> insert (Fun active [(gm04_vars arity) ! i])
          (set (gm04_vars arity))"
      by (rule set_update_subset_insert)
    from lr neq updated ipos nth_var show ?thesis
      unfolding gm04_active_rule_def gm04_vars_def funas_rule_def
      by (auto simp: Let_def)
  next
    case mark
    then obtain f arity i where fn: "(f,arity) \<in> set F"
      and ipos: "i < arity"
      and lr: "lr = gm04_mark_rule mark (f,arity) i"
      unfolding gm04_mark_rules_def by auto
    from fresh fn have neq: "top_sym \<noteq> mark" "top_sym \<noteq> f"
      unfolding gm04_roles_fresh_def by auto
    have nth_var: "gm04_vars arity ! i = Var (x\<^sub>1_to_x\<^sub>n arity ! i)"
      using ipos unfolding gm04_vars_def by simp
    have updated: "set ((gm04_vars arity)
        [i := Fun mark [(gm04_vars arity) ! i]])
        \<subseteq> insert (Fun mark [(gm04_vars arity) ! i])
          (set (gm04_vars arity))"
      by (rule set_update_subset_insert)
    from lr neq updated ipos nth_var show ?thesis
      unfolding gm04_mark_rule_def gm04_vars_def funas_rule_def
      by (auto simp: Let_def)
  next
    case proper
    then obtain f arity where fn: "(f,arity) \<in> set F"
      and lr: "lr = gm04_proper_rule proper ok (f,arity)" by auto
    from fresh fn have neq: "top_sym \<noteq> proper" "top_sym \<noteq> ok"
        "top_sym \<noteq> f"
      unfolding gm04_roles_fresh_def by auto
    with lr show ?thesis
      unfolding gm04_proper_rule_def gm04_vars_def funas_rule_def
      by (auto simp: Let_def split: if_splits)
  next
    case ok
    then obtain f arity where fn: "(f,arity) \<in> set F"
      and lr: "lr = gm04_ok_rule proper ok (f,arity)" by auto
    from fresh fn have neq: "top_sym \<noteq> proper" "top_sym \<noteq> ok"
        "top_sym \<noteq> f"
      unfolding gm04_roles_fresh_def by auto
    with lr show ?thesis
      unfolding gm04_ok_rule_def gm04_vars_def funas_rule_def
      by (auto simp: Let_def split: if_splits)
  qed
qed

lemma gm04_top_signature_separated:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
  shows "aaecc_signature_separated {(top_sym,1)}
    (set (gm04_non_top_rules \<mu> active mark proper ok F R))
    (set (gm04_top_rules active mark proper ok top_sym))"
  unfolding aaecc_signature_separated_def
proof (intro conjI ballI)
  show "funas_trs (set (gm04_non_top_rules
      \<mu> active mark proper ok F R)) \<inter> {(top_sym,1)} = {}"
    unfolding funas_trs_def
    using gm04_non_top_excludes_top[OF fresh signature] by auto
next
  fix lr
  assume "lr \<in> set (gm04_top_rules active mark proper ok top_sym)"
  then show "case lr of (l,r) \<Rightarrow>
      is_Fun r \<and> Term.root l \<in> Some ` {(top_sym,1)} \<and>
      Term.root r \<in> Some ` {(top_sym,1)} \<and>
      funas_args_term l \<inter> {(top_sym,1)} = {} \<and>
      funas_args_term r \<inter> {(top_sym,1)} = {}"
    using fresh unfolding gm04_top_rules_def gm04_roles_fresh_def
      funas_args_term_def by auto
qed

lemma gm04_top_rules_wf:
  "wf_trs (set (gm04_top_rules active mark proper ok top_sym))"
  unfolding gm04_top_rules_def wf_trs_def by auto

lemma gm04_complete_union_wf:
  assumes source_wf: "wf_trs (set R)"
  shows "wf_trs
    (set (gm04_non_top_rules \<mu> active mark proper ok F R) \<union>
     set (gm04_top_rules active mark proper ok top_sym))"
proof -
  have non_top: "wf_trs (set (gm04_non_top_rules
      \<mu> active mark proper ok F R))"
    by (rule gm04_non_top_rules_wf[OF source_wf])
  have top: "wf_trs (set (gm04_top_rules
      active mark proper ok top_sym))"
    by (rule gm04_top_rules_wf)
  show ?thesis using non_top top unfolding wf_trs_def by blast
qed

theorem gm04_complete_SN_from_structural:
  assumes fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and source_wf: "wf_trs (set R)"
    and structural_SN:
      "SN (sig_step_below (- {(top_sym,1)})
          (rrstep (set (gm04_top_rules active mark proper ok top_sym))) \<union>
        sig_step_below (- {(top_sym,1)})
          (rstep (set (gm04_non_top_rules
            \<mu> active mark proper ok F R))))"
  shows "SN (rstep (set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)))"
proof -
  have separated: "aaecc_signature_separated {(top_sym,1)}
      (set (gm04_non_top_rules \<mu> active mark proper ok F R))
      (set (gm04_top_rules active mark proper ok top_sym))"
    by (rule gm04_top_signature_separated[OF fresh signature])
  have wf: "wf_trs
      (set (gm04_non_top_rules \<mu> active mark proper ok F R) \<union>
       set (gm04_top_rules active mark proper ok top_sym))"
    by (rule gm04_complete_union_wf[OF source_wf])
  show ?thesis unfolding gm04_complete_rules_set
    by (rule aaecc_structural_termination[OF separated wf structural_SN])
qed

theorem gm04_complete_full_SN_from_full_top_pairs:
  fixes R :: "('f,string) rule list" and S :: "('f,string) trs"
  assumes S_def: "S = set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and source_wf: "wf_trs (set R)"
    and sharp_roles:
      "top_sharp \<notin> {active,mark,proper,ok,top_sym}"
    and sharp_absent: "top_sharp \<notin> funs_trs S"
    and administrative: "SN (rstep S)"
    and finite: "finite_dpp (False,False,
      set (gm04_top_pairs active mark proper ok top_sharp),{},{},{},S)"
  shows "SN (rstep (set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)))"
proof -
  have top_absent_arity: "\<And>n. (top_sym,n) \<notin> funas_trs S"
  proof (unfold S_def funas_trs_def, intro notI)
    fix n
    assume member: "(top_sym,n) \<in>
      (\<Union>r\<in>set (gm04_non_top_rules
        \<mu> active mark proper ok F R). funas_rule r)"
    then obtain lr where
      lr: "lr \<in> set (gm04_non_top_rules
        \<mu> active mark proper ok F R)"
      and top: "(top_sym,n) \<in> funas_rule lr" by auto
    from gm04_non_top_excludes_top[OF fresh signature lr] top
    show False by contradiction
  qed
  have top_absent: "top_sym \<notin> funs_trs S"
    unfolding funs_trs_funas_trs using top_absent_arity by auto
  have role_distinct:
      "active \<notin> {top_sym,top_sharp}"
      "mark \<notin> {top_sym,top_sharp}"
      "proper \<notin> {top_sym,top_sharp}"
      "ok \<notin> {top_sym,top_sharp}"
      "top_sym \<noteq> top_sharp"
    using fresh sharp_roles unfolding gm04_roles_fresh_def by auto
  have relative: "SN_rel
      (rrstep (set (gm04_top_rules active mark proper ok top_sym)))
      (rstep S)"
    by (rule gm04_finite_top_pairs_imp_relative_top_rules[
        OF role_distinct(5) role_distinct(1-4) top_absent sharp_absent finite])
  from gm04_SN_rel_and_SN_imp_SN_union[OF relative administrative]
  have combined: "SN
      (rrstep (set (gm04_top_rules active mark proper ok top_sym)) \<union>
       rstep S)" .
  have structural: "SN
      (sig_step_below (- {(top_sym,1)})
          (rrstep (set (gm04_top_rules active mark proper ok top_sym))) \<union>
       sig_step_below (- {(top_sym,1)}) (rstep S))"
    by (rule SN_subset[OF combined], unfold sig_step_below_def, auto)
  show ?thesis
    by (rule gm04_complete_SN_from_structural[
        OF fresh signature source_wf], unfold S_def[symmetric], rule structural)
qed

theorem gm04_complete_full_SN_from_innermost_residual:
  fixes R :: "('f,string) rule list" and S :: "('f,string) trs"
  assumes S_def: "S = set (gm04_non_top_rules
      \<mu> active mark proper ok F R)"
    and fresh: "gm04_roles_fresh active mark proper ok top_sym F"
    and signature: "funas_trs (set R) \<subseteq> set F"
    and source_wf: "wf_trs (set R)"
    and sharp_roles:
      "top_sharp \<notin> {active,mark,proper,ok,top_sym}"
    and sharp_absent: "top_sharp \<notin> funs_trs S"
    and administrative: "SN (rstep S)"
    and wcr: "WCR_on (qrstep True {} S)
      {t. SN_on (qrstep True {} S) {t}}"
    and no_overlap: "critical_pairs ren
      (set (gm04_top_pairs active mark proper ok top_sharp)) S = {}"
    and finite_innermost: "finite_dpp (True,True,
      set (gm04_top_pairs active mark proper ok top_sharp),{},lhss S,{},S)"
  shows "SN (rstep (set (gm04_complete_rules
    \<mu> active mark proper ok top_sym F R)))"
proof -
  have top_absent_arity: "\<And>n. (top_sym,n) \<notin> funas_trs S"
  proof (unfold S_def funas_trs_def, intro notI)
    fix n
    assume member: "(top_sym,n) \<in>
      (\<Union>r\<in>set (gm04_non_top_rules
        \<mu> active mark proper ok F R). funas_rule r)"
    then obtain lr where
      lr: "lr \<in> set (gm04_non_top_rules
        \<mu> active mark proper ok F R)"
      and top: "(top_sym,n) \<in> funas_rule lr" by auto
    from gm04_non_top_excludes_top[OF fresh signature lr] top
    show False by contradiction
  qed
  have top_absent: "top_sym \<notin> funs_trs S"
    unfolding funs_trs_funas_trs using top_absent_arity by auto
  have role_distinct:
      "active \<notin> {top_sym,top_sharp}"
      "mark \<notin> {top_sym,top_sharp}"
      "proper \<notin> {top_sym,top_sharp}"
      "ok \<notin> {top_sym,top_sharp}"
      "top_sym \<noteq> top_sharp"
    using fresh sharp_roles unfolding gm04_roles_fresh_def by auto
  have wf_S: "wf_trs S"
    unfolding S_def by (rule gm04_non_top_rules_wf[OF source_wf])
  have structural: "SN
      (sig_step_below (- {(top_sym,1)})
          (rrstep (set (gm04_top_rules active mark proper ok top_sym))) \<union>
       sig_step_below (- {(top_sym,1)}) (rstep S))"
    by (rule gm04_complete_SN_from_innermost_top_pairs[
        OF role_distinct(5) role_distinct(1-4) top_absent sharp_absent
          wf_S administrative wcr no_overlap finite_innermost])
  show ?thesis
    by (rule gm04_complete_SN_from_structural[
        OF fresh signature source_wf], unfold S_def[symmetric], rule structural)
qed

end
