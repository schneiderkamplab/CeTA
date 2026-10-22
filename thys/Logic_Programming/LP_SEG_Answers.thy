theory LP_SEG_Answers
  imports LP_Symbolic_Evaluation
begin

text \<open>Answer-sensitive sequencing for PPDP-style graph continuations.
  The environment records the effect on variables shared with the continuation.
  Runtime substitutions may contain infinite trees: no occurs check or finite
  answer assumption is hidden in this relation.\<close>

inductive_set lp_seg_answer_step ::
  "('f,'v) lp_clause list \<Rightarrow>
    (('f,'w) lp_iatom list \<times> ('a \<Rightarrow> ('f,'w) lp_iterm)) rel"
  for P where
  resolve: "c < length P \<Longrightarrow>
    lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu> \<Longrightarrow>
    ((a # gs, \<rho>),
      (map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
       map (\<lambda>b. lp_iatom_subst b \<sigma>) gs,
       \<lambda>x. lp_isubst (\<rho> x) \<sigma>)) \<in> lp_seg_answer_step P"

lemma lp_seg_answer_step_erases:
  "((gs,\<rho>),(hs,\<eta>)) \<in> lp_seg_answer_step P \<Longrightarrow>
    (gs,hs) \<in> lp_ild P"
  by (cases rule: lp_seg_answer_step.cases) (auto intro: lp_ild.resolve)

lemma lp_seg_answer_step_append:
  assumes st: "((gs,\<rho>),(hs,\<eta>)) \<in> lp_seg_answer_step P"
  shows "
    (gs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,
     hs @ map (\<lambda>a. lp_atom_eval a \<eta>) rest) \<in> lp_ild P"
proof -
  obtain c a \<sigma> \<nu> tail where c: "c < length P"
    and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    and gs: "gs = a # tail"
    and hs: "hs = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
    and env: "\<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    using st by (cases rule: lp_seg_answer_step.cases) blast
  have step: "(a # (tail @ map (\<lambda>b. lp_atom_eval b \<rho>) rest),
      map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>)
        (tail @ map (\<lambda>b. lp_atom_eval b \<rho>) rest)) \<in> lp_ild P"
    by (rule lp_ild.resolve[OF c eq])
  show ?thesis using step by (simp add: gs hs env o_def)
qed

lemma lp_seg_answer_steps_append:
  "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
    (gs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,
     hs @ map (\<lambda>a. lp_atom_eval a \<eta>) rest) \<in> (lp_ild P)\<^sup>*"
proof (induct rule: rtrancl_induct2)
  case refl then show ?case by simp
next
  case (step hs \<eta> ks \<tau>)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3)
    lp_seg_answer_step_append[OF step.hyps(2)]])
qed

lemma lp_seg_answer_step_environment:
  fixes \<rho> \<eta> :: "'a \<Rightarrow> ('f,'w) lp_iterm"
  assumes st: "((gs,\<rho>),(hs,\<eta>)) \<in> lp_seg_answer_step P"
  shows "\<exists>\<sigma>. \<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) \<and>
    (\<forall>\<zeta> :: 'b \<Rightarrow> ('f,'w) lp_iterm.
      ((gs,\<zeta>),(hs,\<lambda>x. lp_isubst (\<zeta> x) \<sigma>)) \<in> lp_seg_answer_step P)"
  using st by (cases rule: lp_seg_answer_step.cases)
    (auto intro!: exI intro: lp_seg_answer_step.resolve)

lemma lp_seg_answer_steps_environment:
  fixes \<rho> \<eta> :: "'a \<Rightarrow> ('f,'w) lp_iterm"
  assumes path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "\<exists>\<sigma>. \<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) \<and>
    (\<forall>\<zeta> :: 'b \<Rightarrow> ('f,'w) lp_iterm.
      ((gs,\<zeta>),(hs,\<lambda>x. lp_isubst (\<zeta> x) \<sigma>)) \<in> (lp_seg_answer_step P)\<^sup>*)"
  using path
proof (induct rule: rtrancl_induct2)
  case refl show ?case by (rule exI[of _ LPIVar]) simp
next
  case (step hs \<eta> ks \<tau>)
  obtain \<sigma> where eta: "\<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    and before: "\<forall>\<zeta> :: 'b \<Rightarrow> ('f,'w) lp_iterm.
      ((gs,\<zeta>),(hs,\<lambda>x. lp_isubst (\<zeta> x) \<sigma>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    using step.hyps(3) by blast
  obtain \<delta> where tau: "\<tau> = (\<lambda>x. lp_isubst (\<eta> x) \<delta>)"
    and after: "\<forall>\<zeta> :: 'b \<Rightarrow> ('f,'w) lp_iterm.
      ((hs,\<zeta>),(ks,\<lambda>x. lp_isubst (\<zeta> x) \<delta>)) \<in> lp_seg_answer_step P"
    using lp_seg_answer_step_environment[OF step.hyps(2)] by blast
  show ?case
  proof (rule exI[of _ "\<lambda>x. lp_isubst (\<sigma> x) \<delta>"], intro conjI allI)
    show "\<tau> = (\<lambda>x. lp_isubst (\<rho> x) (\<lambda>x. lp_isubst (\<sigma> x) \<delta>))"
      by (simp add: tau eta lp_seg_isubst_comp)
    fix \<zeta> :: "'b \<Rightarrow> ('f,'w) lp_iterm"
    have a: "((gs,\<zeta>),(hs,\<lambda>x. lp_isubst (\<zeta> x) \<sigma>)) \<in> (lp_seg_answer_step P)\<^sup>*"
      using before by blast
    have b: "((hs,\<lambda>x. lp_isubst (\<zeta> x) \<sigma>),
      (ks,\<lambda>x. lp_isubst (lp_isubst (\<zeta> x) \<sigma>) \<delta>)) \<in> lp_seg_answer_step P"
      using after by blast
    show "((gs,\<zeta>),(ks,\<lambda>x. lp_isubst (\<zeta> x) (\<lambda>x. lp_isubst (\<sigma> x) \<delta>)))
      \<in> (lp_seg_answer_step P)\<^sup>*"
      using rtrancl_into_rtrancl[OF a b] by (simp add: lp_seg_isubst_comp)
  qed
qed

lemma lp_seg_answer_steps_preserve_ground:
  assumes path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    and ground: "lp_seg_ground (\<rho> x)"
  shows "\<eta> x = \<rho> x"
  using lp_seg_answer_steps_environment[OF path] ground
  by (auto simp: lp_seg_ground_subst)

lemma lp_seg_answer_steps_split:
  assumes path: "((ps,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "\<forall>prefix rest. ps = prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest \<longrightarrow>
    (\<exists>\<mu>. ((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>* \<and>
       ((map (\<lambda>a. lp_atom_eval a \<mu>) rest,\<mu>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*)"
  using path
proof (induct rule: converse_rtrancl_induct2)
  case refl then show ?case by auto
next
  case (step gs \<rho> hs \<tau>)
  show ?case
  proof (intro allI impI)
    fix prefix rest
    assume gs: "gs = prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest"
    show "\<exists>\<mu>. ((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>* \<and>
      ((map (\<lambda>a. lp_atom_eval a \<mu>) rest,\<mu>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
    proof (cases prefix)
      case Nil
      have path: "((gs,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
        by (rule converse_rtrancl_into_rtrancl[OF step.hyps(1,2)])
      show ?thesis by (rule exI[of _ \<rho>]) (use path gs Nil in auto)
    next
      case (Cons a tail)
      obtain c \<sigma> \<nu> where c: "c < length P"
        and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
        and hs: "hs = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
          map (\<lambda>b. lp_iatom_subst b \<sigma>) (tail @ map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
        and tau: "\<tau> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
        using step.hyps(1) gs Cons by (cases rule: lp_seg_answer_step.cases) auto
      let ?qs = "map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
        map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
      have st: "((prefix,\<rho>),(?qs,\<tau>)) \<in> lp_seg_answer_step P"
        unfolding Cons tau by (rule lp_seg_answer_step.resolve[OF c eq])
      have hs': "hs = ?qs @ map (\<lambda>b. lp_atom_eval b \<tau>) rest"
        by (simp add: hs tau o_def)
      obtain \<mu> where first: "((?qs,\<tau>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>*"
        and second: "((map (\<lambda>a. lp_atom_eval a \<mu>) rest,\<mu>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
        using step.hyps(3) hs' by blast
      have "((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>*"
        by (rule converse_rtrancl_into_rtrancl[OF st first])
      then show ?thesis using second by blast
    qed
  qed
qed

text \<open>Only actual successful answers need a terminating continuation.
  In contrast to the conservative Split rule, its precondition need not be
  stable under arbitrary substitutions: it may describe computed outputs.\<close>

theorem lp_seg_append_sn_answers:
  fixes P :: "('f,string) lp_clause list"
    and prefix :: "('f,string) lp_iatom list"
    and rest :: "('f,string) lp_atom list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes sn: "SN_on (lp_ild P) {prefix}"
    and suffix: "\<And>\<eta>. ((prefix,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
      \<Longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest}"
  shows "SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
proof -
  have all: "\<forall>\<rho>. (\<forall>\<eta>. ((prefix,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
      \<longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest})
    \<longrightarrow> SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix ps :: "('f,string) lp_iatom list"
    assume ih: "\<And>qs. (ps,qs) \<in> lp_ild P \<Longrightarrow>
      \<forall>\<rho>. (\<forall>\<eta>. ((qs,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
        \<longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest})
      \<longrightarrow> SN_on (lp_ild P) {qs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    show "\<forall>\<rho>. (\<forall>\<eta>. ((ps,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
        \<longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest})
      \<longrightarrow> SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    proof (intro allI impI)
      fix \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
      assume answers: "\<forall>\<eta>. ((ps,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
        \<longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest}"
      show "SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
      proof (cases ps)
        case Nil then show ?thesis using answers by auto
      next
        case (Cons a tail)
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix hs assume st: "(ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,hs) \<in> lp_ild P"
          obtain c \<sigma> \<nu> where c: "c < length P"
            and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
            and hs: "hs = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
              map (\<lambda>b. lp_iatom_subst b \<sigma>) (tail @ map (\<lambda>a. lp_atom_eval a \<rho>) rest)"
            using lp_ild_cons_cases st unfolding Cons append_Cons by blast
          let ?qs = "map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
            map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
          let ?post = "\<lambda>x. lp_isubst (\<rho> x) \<sigma>"
          have transition: "(ps,?qs) \<in> lp_ild P"
            unfolding Cons by (rule lp_ild.resolve[OF c eq])
          have ast: "((ps,\<rho>),(?qs,?post)) \<in> lp_seg_answer_step P"
            unfolding Cons by (rule lp_seg_answer_step.resolve[OF c eq])
          have post_answers: "\<forall>\<eta>. ((?qs,?post),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
            \<longrightarrow> SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest}"
          proof (intro allI impI)
            fix \<eta> assume path: "((?qs,?post),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
            have "((ps,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
              by (rule converse_rtrancl_into_rtrancl[OF ast path])
            then show "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<eta>) rest}"
              using answers by blast
          qed
          have "SN_on (lp_ild P) {?qs @ map (\<lambda>a. lp_atom_eval a ?post) rest}"
            using ih[OF transition] post_answers by blast
          then show "SN_on (lp_ild P) {hs}" by (simp add: hs o_def)
        qed
      qed
    qed
  qed
  show ?thesis using all suffix by blast
qed

end
