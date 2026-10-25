theory LP_Dependency_Triple_Chains
  imports LP_Dependency_Triples
begin

text \<open>The supporting program discharges successful prefixes. It is
  separate from the triples defining recursive calls. No ordinary DP
  minimality or finite-runtime-tree assumption is made.\<close>

definition lp_triple_calls ::
  "('f,'v) lp_dependency_triple set \<Rightarrow> ('f,'u) lp_clause list \<Rightarrow>
    ('f,'w) lp_iatom rel" where
  "lp_triple_calls D P = {(a, lp_atom_eval b \<eta>) | a h ps b \<sigma> \<rho> \<eta>.
    (h,ps,b) \<in> D \<and> lp_iatom_subst a \<sigma> = lp_atom_eval h \<rho> \<and>
    ((map (\<lambda>g. lp_atom_eval g \<rho>) ps,\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>*}"

lemma lp_triple_answer_append:
  assumes path: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "((gs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,\<rho>),
      (hs @ map (\<lambda>a. lp_atom_eval a \<eta>) rest,\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct2)
  case refl then show ?case by simp
next
  case (step hs \<eta> ks \<tau>)
  obtain c a \<sigma> \<nu> tail where c: "c < length P"
    and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    and hs: "hs = a # tail"
    and ks: "ks = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
    and tau: "\<tau> = (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    using step.hyps(2) by (cases rule: lp_seg_answer_step.cases) blast
  have lifted: "((a # (tail @ map (\<lambda>b. lp_atom_eval b \<eta>) rest),\<eta>),
    (map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
     map (\<lambda>b. lp_iatom_subst b \<sigma>) (tail @ map (\<lambda>b. lp_atom_eval b \<eta>) rest),
     \<lambda>x. lp_isubst (\<eta> x) \<sigma>)) \<in> lp_seg_answer_step P"
    by (rule lp_seg_answer_step.resolve[OF c eq])
  have local: "((hs @ map (\<lambda>a. lp_atom_eval a \<eta>) rest,\<eta>),
      (ks @ map (\<lambda>a. lp_atom_eval a \<tau>) rest,\<tau>))
      \<in> lp_seg_answer_step P"
    using lifted by (simp add: hs ks tau o_def)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) local])
qed

lemma lp_triple_body_sn:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes calls: "\<And>i \<eta>. i < length bs \<Longrightarrow>
    ((map (\<lambda>g. lp_atom_eval g \<rho>) (take i bs),\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
    SN_on (lp_ild P) {[lp_atom_eval (bs!i) \<eta>]}"
  shows "SN_on (lp_ild P) {map (\<lambda>g. lp_atom_eval g \<rho>) bs}"
  using calls
proof (induct bs arbitrary: \<rho>)
  case Nil
  show ?case by (rule step_reflects_SN_on) (auto elim: lp_ild.cases)
next
  case (Cons b bs)
  have head: "SN_on (lp_ild P) {[lp_atom_eval b \<rho>]}"
    using Cons.prems[of 0 \<rho>] by simp
  have tail: "SN_on (lp_ild P) {map (\<lambda>g. lp_atom_eval g \<rho>) [b] @
      map (\<lambda>g. lp_atom_eval g \<rho>) bs}"
  proof (rule lp_seg_append_sn_answers)
    show "SN_on (lp_ild P) {map (\<lambda>g. lp_atom_eval g \<rho>) [b]}"
      using head by simp
    fix \<mu>
    assume success: "((map (\<lambda>g. lp_atom_eval g \<rho>) [b],\<rho>),([],\<mu>))
      \<in> (lp_seg_answer_step P)\<^sup>*"
    show "SN_on (lp_ild P) {map (\<lambda>g. lp_atom_eval g \<mu>) bs}"
    proof (rule Cons.hyps)
      fix i \<eta> assume i: "i < length bs"
        and after: "((map (\<lambda>g. lp_atom_eval g \<mu>) (take i bs),\<mu>),([],\<eta>))
          \<in> (lp_seg_answer_step P)\<^sup>*"
      have before: "((map (\<lambda>g. lp_atom_eval g \<rho>) (take (Suc i) (b#bs)),\<rho>),
          (map (\<lambda>g. lp_atom_eval g \<mu>) (take i bs),\<mu>))
          \<in> (lp_seg_answer_step P)\<^sup>*"
        using lp_triple_answer_append[OF success, of "take i bs"] by simp
      have combined: "((map (\<lambda>g. lp_atom_eval g \<rho>) (take (Suc i) (b#bs)),\<rho>),([],\<eta>))
          \<in> (lp_seg_answer_step P)\<^sup>*"
        by (rule rtrancl_trans[OF before after])
      show "SN_on (lp_ild P) {[lp_atom_eval (bs!i) \<eta>]}"
        using Cons.prems[of "Suc i" \<eta>] i combined by simp
    qed
  qed
  show ?case using tail by simp
qed

theorem lp_triple_calls_imply_source_termination:
  fixes P :: "('f,string) lp_clause list" and a :: "('f,string) lp_iatom"
  assumes sn: "SN_on (lp_triple_calls (set (lp_dependency_triples P)) P) {a}"
  shows "SN_on (lp_ild P) {[a]}"
proof (rule SN_on_induct[OF sn singletonI])
  fix a :: "('f,string) lp_iatom"
  assume ih: "\<And>b. (a,b) \<in> lp_triple_calls (set (lp_dependency_triples P)) P
    \<Longrightarrow> SN_on (lp_ild P) {[b]}"
  show "SN_on (lp_ild P) {[a]}"
  proof (rule step_reflects_SN_on)
    fix gs assume step: "([a],gs) \<in> lp_ild P"
    obtain c \<sigma> \<rho> where c: "c < length P"
      and match: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<rho>"
      and gs: "gs = map (\<lambda>b. lp_atom_eval b \<rho>) (snd (P!c))"
      using step by (cases rule: lp_ild.cases) auto
    show "SN_on (lp_ild P) {gs}"
      unfolding gs
    proof (rule lp_triple_body_sn)
      fix i \<eta> assume i: "i < length (snd (P!c))"
        and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) (take i (snd (P!c))),\<rho>),([],\<eta>))
          \<in> (lp_seg_answer_step P)\<^sup>*"
      have triple: "(fst (P!c),take i (snd (P!c)),snd (P!c)!i)
          \<in> set (lp_dependency_triples P)"
        using c i by (auto simp: lp_dependency_triples_exact)
      have call: "(a,lp_atom_eval (snd (P!c)!i) \<eta>)
          \<in> lp_triple_calls (set (lp_dependency_triples P)) P"
        unfolding lp_triple_calls_def using triple match success by blast
      show "SN_on (lp_ild P) {[lp_atom_eval (snd (P!c)!i) \<eta>]}"
        by (rule ih[OF call])
    qed
  qed
qed

end
