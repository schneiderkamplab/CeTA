theory LP_SEG_Residual
  imports LP_SEG_Expansion LP_SEG_Answers
begin

text \<open>Symbolic graph specialization preserves source LD termination.
  Residual predicates carry the complete symbolic interface, not just a guessed
  groundness projection. Argument filtering is checked separately by TOCL09.
  All runtime substitutions in this simulation may contain infinite trees.\<close>

inductive lp_seg_represents for I N V F where
  empty: "lp_seg_represents I N V F [] []"
| cons: "i\<in>I \<Longrightarrow> lp_seg_represents I N V F qs gs \<Longrightarrow>
    lp_seg_represents I N V F ((F i,map \<rho> (V i))#qs)
      (map (\<lambda>a. lp_atom_eval a \<rho>) (N i) @ gs)"

lemma lp_seg_represents_subst:
  assumes "lp_seg_represents I N V F qs gs"
  shows "lp_seg_represents I N V F
    (map (\<lambda>a. lp_iatom_subst a \<sigma>) qs)
    (map (\<lambda>a. lp_iatom_subst a \<sigma>) gs)"
  using assms
proof (induct rule: lp_seg_represents.induct)
  case empty then show ?case by (simp add: lp_seg_represents.empty)
next
  case (cons i qs gs \<rho>)
  have head: "lp_iatom_subst (F i,map \<rho> (V i)) \<sigma> =
    (F i,map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) (V i))"
    by (simp add: lp_iatom_subst_def o_def)
  show ?case using lp_seg_represents.cons[OF cons.hyps(1) cons.hyps(3),
    of "\<lambda>x. lp_isubst (\<rho> x) \<sigma>"]
    by (simp add: head o_def)
qed

inductive lp_seg_residual_valid for P Q I N V F where
  success: "N i=[] \<Longrightarrow> ((F i,map Var (V i)),[])\<in>set Q \<Longrightarrow>
    lp_seg_residual_valid P Q I N V F i"
| inst: "j\<in>I \<Longrightarrow> N i=map (\<lambda>a. lp_atom_subst a \<mu>) (N j) \<Longrightarrow>
    ((F i,map Var (V i)),[(F j,map \<mu> (V j))])\<in>set Q \<Longrightarrow>
    lp_seg_residual_valid P Q I N V F i"
| split: "a\<in>I \<Longrightarrow> b\<in>I \<Longrightarrow> N i=N a@N b \<Longrightarrow>
    ((F i,map Var (V i)),[(F a,map Var (V a)),(F b,map Var (V b))])\<in>set Q \<Longrightarrow>
    lp_seg_residual_valid P Q I N V F i"
| resolve: "N i\<noteq>[] \<Longrightarrow> lp_short_goals k (N i@[(anchor,map Var (V i))]) \<Longrightarrow>
    (\<forall>c<length P. \<exists>result.
      lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=Some result) \<Longrightarrow>
    (\<forall>c<length P. \<forall>child inputs.
      lp_source_branch fuel k (N i@[(anchor,map Var (V i))]) (P!c)=
        Some (Some (child@[(anchor,inputs)])) \<longrightarrow>
      (\<exists>j\<in>I. N j=child \<and> ((F i,inputs),[(F j,map Var (V j))])\<in>set Q)) \<Longrightarrow>
    lp_seg_residual_valid P Q I N V F i"

lemma lp_seg_residual_step:
  assumes clause: "(head,body)\<in>set Q"
    and match: "lp_iatom_subst a \<sigma> = lp_atom_eval head \<rho>"
  shows "(a#rest,map (\<lambda>b. lp_atom_eval b \<rho>) body @
    map (\<lambda>b. lp_iatom_subst b \<sigma>) rest)\<in>lp_ild Q"
proof -
  obtain c where c: "c<length Q" and eq: "Q!c=(head,body)"
    using clause by (metis in_set_conv_nth)
  show ?thesis using lp_ild.resolve[OF c, of a \<sigma> \<rho> rest] match
    by (simp add: eq)
qed

lemma lp_seg_residual_expansion:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> \<sigma> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes fresh: "lp_short_goals k (a#rest@[(anchor,map Var vs)])"
    and ready: "\<And>c. c<length P \<Longrightarrow> \<exists>result.
      lp_source_branch fuel k (a#rest@[(anchor,map Var vs)]) (P!c)=Some result"
    and c: "c<length P"
    and eq: "lp_iatom_subst (lp_atom_eval a \<rho>) \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
  obtains j child inputs \<eta> where "j<length P"
    "lp_source_branch fuel k (a#rest@[(anchor,map Var vs)]) (P!j)=Some (Some (child@[(anchor,inputs)]))"
    "map (\<lambda>b. lp_atom_eval b \<eta>) child =
      map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
    "map (\<lambda>t. lp_ieval t \<eta>) inputs=map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) vs"
proof -
  let ?hs = "map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
    map (\<lambda>b. lp_iatom_subst b \<sigma>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
  let ?vals = "map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) vs"
  have step: "(map (\<lambda>b. lp_atom_eval b \<rho>) (a#rest@[(anchor,map Var vs)]),
    ?hs@[(anchor,?vals)])\<in>lp_ild P"
    using lp_ild.resolve[OF c eq, of "map (\<lambda>b. lp_atom_eval b \<rho>) rest @ [(anchor,map \<rho> vs)]"]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
  obtain j flat \<eta> where j: "j<length P"
    and branch: "lp_source_branch fuel k (a#rest@[(anchor,map Var vs)]) (P!j)=Some (Some flat)"
    and projected: "map (\<lambda>b. lp_atom_eval b \<eta>) flat=?hs@[(anchor,?vals)]"
    by (rule lp_seg_expansion_step[OF fresh _ _ ready step, where G="[]"]) auto
  have ne: "flat\<noteq>[]" using projected by auto
  obtain child last_atom where flat: "flat=child@[last_atom]"
    using ne by (metis append_butlast_last_id)
  obtain p inputs where last: "last_atom=(p,inputs)" by (cases last_atom) auto
  have child: "map (\<lambda>b. lp_atom_eval b \<eta>) child=?hs"
    and pred: "p=anchor" and vals: "map (\<lambda>t. lp_ieval t \<eta>) inputs=?vals"
    using projected by (simp_all add: flat last lp_atom_eval_def)
  show thesis by (rule that[OF j _ child vals])
    (use branch in \<open>simp add: flat last pred\<close>)
qed

lemma lp_seg_residual_node_sound:
  fixes P Q :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes valid: "lp_seg_residual_valid P Q I N V F i"
    and tail: "lp_seg_represents I N V F qs gs"
    and ih: "\<And>ys hs. ((F i,map \<rho> (V i))#qs,ys)\<in>lp_ild Q \<Longrightarrow>
      lp_seg_represents I N V F ys hs \<Longrightarrow> SN_on (lp_ild P) {hs}"
  shows "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) (N i) @ gs}"
  using valid
proof cases
  case success
  have step: "((F i,map \<rho> (V i))#qs,qs)\<in>lp_ild Q"
    using lp_seg_residual_step[OF success(2), where \<sigma>=LPIVar and \<rho>=\<rho> and rest=qs]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
  show ?thesis using ih[OF step tail] success(1) by simp
next
  case (inst j \<mu>)
  let ?eta = "\<lambda>x. lp_ieval (\<mu> x) \<rho>"
  have step: "((F i,map \<rho> (V i))#qs,(F j,map ?eta (V j))#qs)\<in>lp_ild Q"
    using lp_seg_residual_step[OF inst(3), where \<sigma>=LPIVar and \<rho>=\<rho> and rest=qs]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
  have represented: "lp_seg_represents I N V F ((F j,map ?eta (V j))#qs)
    (map (\<lambda>a. lp_atom_eval a ?eta) (N j) @ gs)"
    by (rule lp_seg_represents.cons[OF inst(1) tail])
  show ?thesis using ih[OF step represented]
    by (simp add: inst(2) lp_atom_eval_finite_subst o_def)
next
  case (split a b)
  have step: "((F i,map \<rho> (V i))#qs,
    (F a,map \<rho> (V a))#(F b,map \<rho> (V b))#qs)\<in>lp_ild Q"
    using lp_seg_residual_step[OF split(4), where \<sigma>=LPIVar and \<rho>=\<rho> and rest=qs]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
  have represented: "lp_seg_represents I N V F
    ((F a,map \<rho> (V a))#(F b,map \<rho> (V b))#qs)
    (map (\<lambda>a. lp_atom_eval a \<rho>) (N a) @
      map (\<lambda>a. lp_atom_eval a \<rho>) (N b) @ gs)"
    by (rule lp_seg_represents.cons[OF split(1)], rule lp_seg_represents.cons[OF split(2) tail])
  show ?thesis using ih[OF step represented] by (simp add: split(3))
next
  case (resolve k anchor fuel)
  obtain a rest where ni: "N i=a#rest" using resolve(1) by (cases "N i") auto
  have fresh: "lp_short_goals k (a#rest@[(anchor,map Var (V i))])"
    using resolve(2) by (simp add: ni)
  have ready: "\<And>c. c<length P \<Longrightarrow> \<exists>result.
    lp_source_branch fuel k (a#rest@[(anchor,map Var (V i))]) (P!c)=Some result"
    using resolve(3) by (simp add: ni)
  show ?thesis
  proof (rule step_reflects_SN_on)
    fix hs assume st: "(map (\<lambda>a. lp_atom_eval a \<rho>) (N i) @ gs,hs)\<in>lp_ild P"
    obtain c \<sigma> \<nu> where c: "c<length P"
      and eq: "lp_iatom_subst (lp_atom_eval a \<rho>) \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
      and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
        map (\<lambda>b. lp_iatom_subst b \<sigma>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest @ gs)"
      using lp_ild_cons_cases st unfolding ni list.map append_Cons by blast
    obtain ci child inputs \<eta> where ci: "ci<length P"
      and branch: "lp_source_branch fuel k (a#rest@[(anchor,map Var (V i))]) (P!ci)=
        Some (Some (child@[(anchor,inputs)]))"
      and projected: "map (\<lambda>b. lp_atom_eval b \<eta>) child=
        map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
        map (\<lambda>b. lp_iatom_subst b \<sigma>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
      and inputs: "map (\<lambda>t. lp_ieval t \<eta>) inputs=map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) (V i)"
      by (rule lp_seg_residual_expansion[OF fresh ready c eq]) blast
    have covered: "\<exists>j\<in>I. N j=child \<and> ((F i,inputs),[(F j,map Var (V j))])\<in>set Q"
      by (rule resolve(4)[rule_format, OF ci]) (simp add: ni branch)
    obtain j where j: "j\<in>I" and nj: "N j=child"
      and clause: "((F i,inputs),[(F j,map Var (V j))])\<in>set Q"
      using covered by blast
    have match: "lp_iatom_subst (F i,map \<rho> (V i)) \<sigma> = lp_atom_eval (F i,inputs) \<eta>"
      using inputs by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
    have step: "((F i,map \<rho> (V i))#qs,
      (F j,map \<eta> (V j))#map (\<lambda>b. lp_iatom_subst b \<sigma>) qs)\<in>lp_ild Q"
      using lp_seg_residual_step[OF clause match, of qs] by (simp add: lp_atom_eval_def o_def)
    have mapped_tail: "lp_seg_represents I N V F
      (map (\<lambda>b. lp_iatom_subst b \<sigma>) qs)
      (map (\<lambda>b. lp_iatom_subst b \<sigma>) gs)"
      by (rule lp_seg_represents_subst[OF tail])
    have represented: "lp_seg_represents I N V F
      ((F j,map \<eta> (V j))#map (\<lambda>b. lp_iatom_subst b \<sigma>) qs) hs"
      using lp_seg_represents.cons[OF j mapped_tail, of \<eta>] projected
      by (simp add: hs nj)
    show "SN_on (lp_ild P) {hs}" by (rule ih[OF step represented])
  qed
qed

theorem lp_seg_residual_termination:
  fixes P Q :: "('f,string) lp_clause list"
    and qs gs :: "('f,string) lp_iatom list"
  assumes valid: "\<And>i. i\<in>I \<Longrightarrow> lp_seg_residual_valid P Q I N V F i"
    and sn: "SN_on (lp_ild Q) {qs}"
    and rep: "lp_seg_represents I N V F qs gs"
  shows "SN_on (lp_ild P) {gs}"
proof -
  have all: "\<forall>gs. lp_seg_represents I N V F qs gs \<longrightarrow> SN_on (lp_ild P) {gs}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix xs :: "('f,string) lp_iatom list"
    assume ih: "\<And>ys. (xs,ys)\<in>lp_ild Q \<Longrightarrow>
      \<forall>hs. lp_seg_represents I N V F ys hs \<longrightarrow> SN_on (lp_ild P) {hs}"
    show "\<forall>gs. lp_seg_represents I N V F xs gs \<longrightarrow> SN_on (lp_ild P) {gs}"
    proof (intro allI impI)
      fix gs assume represented: "lp_seg_represents I N V F xs gs"
      show "SN_on (lp_ild P) {gs}"
      proof (cases rule: lp_seg_represents.cases[OF represented, case_names empty cons])
        case empty
        show ?thesis unfolding empty by (rule step_reflects_SN_on) (auto elim: lp_ild.cases)
      next
        case (cons i ys hs \<rho>)
        show ?thesis unfolding cons(2)
          by (rule lp_seg_residual_node_sound[OF valid[OF cons(3)] cons(4)])
            (use ih cons(1) in blast)
      qed
    qed
  qed
  show ?thesis using all rep by blast
qed

end
