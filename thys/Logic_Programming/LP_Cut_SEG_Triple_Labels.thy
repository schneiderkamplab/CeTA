theory LP_Cut_SEG_Triple_Labels
  imports LP_Cut_SEG_Regions LP_Dependency_Triple_Chains
begin

text \<open>Triple labels need not be ground. A finite local path may
instantiate them, but must use one shared substitution for all captured
arguments. The ordinary ground-measure preservation lemma cannot justify
discarding those instantiations. This version retains them explicitly.\<close>

lemma lpc_seg_template_step_instance:
  assumes checked: "lpc_seg_template_program templates C"
    and step: "([a],gs)\<in>lp_ild C"
  shows "\<exists>b sigma. gs=[b] \<and>
    lpc_seg_template_value templates b = lp_isubst (lpc_seg_template_value templates a) sigma"
proof -
  obtain c eta sigma where c: "c<length C"
    and unified: "lp_iatom_subst a sigma=lp_atom_eval (fst (C!c)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (C!c))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (C!c))=1"
    and edge: "lpc_seg_template_edge templates (fst (C!c)) (hd (snd (C!c)))"
    using checked c by (auto simp: lpc_seg_template_program_def list_all_iff split_def)
  obtain b where body: "snd (C!c)=[b]"
    using len by (cases "snd (C!c)") auto
  have same: "lpc_seg_template_value templates (lp_atom_eval b eta) =
    lpc_seg_template_value templates (lp_atom_eval (fst (C!c)) eta)"
    using edge body by (simp add: lpc_seg_template_edge_def lpc_seg_template_eval)
  have instantiated: "lpc_seg_template_value templates (lp_atom_eval b eta) =
    lp_isubst (lpc_seg_template_value templates a) sigma"
    using same by (simp only: unified[symmetric] lpc_seg_template_subst)
  show ?thesis using gs body instantiated by auto
qed

lemma lpc_seg_template_path_instance:
  assumes checked: "lpc_seg_template_program templates C"
    and path: "([a],gs)\<in>(lp_ild C)\<^sup>*"
  shows "\<exists>b sigma. gs=[b] \<and>
    lpc_seg_template_value templates b = lp_isubst (lpc_seg_template_value templates a) sigma"
  using path
proof (induct rule: rtrancl_induct)
  case base
  show ?case by (rule exI[of _ a], rule exI[of _ LPIVar]) simp
next
  case (step ys zs)
  obtain b sigma where ys: "ys=[b]"
    and before: "lpc_seg_template_value templates b =
      lp_isubst (lpc_seg_template_value templates a) sigma"
    using step.hyps(3) by blast
  have local: "([b],zs)\<in>lp_ild C" using step.hyps(2) ys by simp
  obtain d delta where zs: "zs=[d]"
    and after: "lpc_seg_template_value templates d =
      lp_isubst (lpc_seg_template_value templates b) delta"
    using lpc_seg_template_step_instance[OF checked local] by blast
  show ?case
    by (rule exI[of _ d], rule exI[of _ "\<lambda>x. lp_isubst (sigma x) delta"])
      (simp add: zs after before lp_seg_isubst_comp)
qed

text \<open>At a boundary, a syntactically checked triple head and a successful
prefix suffice to obtain the strict recursive edge. The path instantiation
and the prefix answer are not replaced by independent substitutions.\<close>

lemma lpc_seg_template_path_triple_edge:
  assumes checked: "lpc_seg_template_program templates C"
    and path: "([control],[endpoint])\<in>(lp_ild C)\<^sup>*"
    and initial: "lpc_seg_template_value templates control=lp_itag id a"
    and head: "lpc_seg_template_value templates endpoint=lp_ieval (Fun (fst h) (snd h)) rho"
    and triple: "(h,ps,b)\<in>set D"
    and prefix: "((map (\<lambda>g. lp_atom_eval g rho) ps,rho),([],eta))
      \<in>(lp_seg_answer_step Q)\<^sup>*"
  shows "(a,lp_atom_eval b eta)\<in>lp_triple_calls (set D) Q"
proof -
  obtain sigma where label: "lpc_seg_template_value templates endpoint =
      lp_isubst (lpc_seg_template_value templates control) sigma"
    using lpc_seg_template_path_instance[OF checked path] by auto
  have tagged: "lp_itag id (lp_iatom_subst a sigma)=lp_itag id (lp_atom_eval h rho)"
    using label by (simp add: initial head lp_itag_def lp_iatom_subst_def lp_atom_eval_def)
  have matching: "lp_iatom_subst a sigma=lp_atom_eval h rho"
    using tagged by (simp add: lp_itag_def prod_eq_iff)
  show ?thesis using triple matching prefix unfolding lp_triple_calls_def by blast
qed

text \<open>Successful-program clauses are consumed with their actual prefix
answers. The conclusion records the composed answer substitution, including
the instantiation made when entering the clause.\<close>

lemma lpc_triple_success_clause_answers:
  fixes zeta :: "'z \<Rightarrow> ('f,'w) lp_iterm"
  assumes clause: "(h,ps)\<in>set Q"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval h rho"
    and prefix: "((map (\<lambda>g. lp_atom_eval g rho) ps,rho),([],eta))
      \<in>(lp_seg_answer_step Q)\<^sup>*"
  shows "\<exists>delta. eta=(\<lambda>x. lp_isubst (rho x) delta) \<and>
    (([a],zeta),([],\<lambda>x. lp_isubst (lp_isubst (zeta x) sigma) delta))
      \<in>(lp_seg_answer_step Q)\<^sup>+"
proof -
  obtain c where index: "c<length Q" and selected: "Q!c=(h,ps)"
    using clause by (auto simp: in_set_conv_nth)
  have match: "lp_iatom_subst a sigma=lp_atom_eval (fst (Q!c)) rho"
    using matching by (simp add: selected)
  have enter: "(([a],zeta),(map (\<lambda>g. lp_atom_eval g rho) ps,
      \<lambda>x. lp_isubst (zeta x) sigma))\<in>lp_seg_answer_step Q"
    using lp_seg_answer_step.resolve[OF index match, of "[]" zeta]
    by (simp add: selected)
  obtain delta where answer: "eta=(\<lambda>x. lp_isubst (rho x) delta)"
    and all: "\<forall>env :: 'z \<Rightarrow> ('f,'w) lp_iterm. ((map (\<lambda>g. lp_atom_eval g rho) ps,env),
      ([],\<lambda>x. lp_isubst (env x) delta))\<in>(lp_seg_answer_step Q)\<^sup>*"
    using lp_seg_answer_steps_environment[OF prefix] by blast
  have tail: "((map (\<lambda>g. lp_atom_eval g rho) ps,\<lambda>x. lp_isubst (zeta x) sigma),
      ([],\<lambda>x. lp_isubst (lp_isubst (zeta x) sigma) delta))\<in>(lp_seg_answer_step Q)\<^sup>*"
    using all by blast
  have complete: "(([a],zeta),([],\<lambda>x. lp_isubst (lp_isubst (zeta x) sigma) delta))
      \<in>(lp_seg_answer_step Q)\<^sup>+"
    by (rule trancl_rtrancl_trancl[OF r_into_trancl[OF enter] tail])
  show ?thesis using answer complete by blast
qed

end
