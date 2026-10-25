theory LP_Dependency_Triple_Models
  imports LP_Dependency_Triple_Chains LP_Answer_Groundness
begin

text \<open>Already instantiated successful prefixes can be represented by
the least answer model. This is a finite proof predicate, not an assumption
that search in the supporting program terminates. Model membership is stable
under substitutions and supplies an actual identity-answer derivation.\<close>

lemma lp_identity_answers_list:
  fixes env :: "'z \<Rightarrow> ('f,'w) lp_iterm"
  assumes calls: "\<And>a tail. a\<in>set gs \<Longrightarrow>
    ((a#tail,env),(tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
  shows "((gs@tail,env),(tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
  using calls
proof (induct gs)
  case Nil show ?case by simp
next
  case (Cons a gs)
  have first: "((a#(gs@tail),env),(gs@tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
    by (rule Cons.prems) simp
  have rest: "((gs@tail,env),(tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using rtrancl_trans[OF first rest] by simp
qed

lemma lp_answer_model_identity_answers:
  fixes env :: "'z \<Rightarrow> ('f,'w) lp_iterm"
  assumes model: "lp_answer_model Q a"
  shows "((a#tail,env),(tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
  using model
proof (induct arbitrary: tail rule: lp_answer_model.induct)
  case (clause c nu)
  have matching: "lp_iatom_subst (lp_atom_eval (fst (Q!c)) nu) LPIVar =
    lp_atom_eval (fst (Q!c)) nu" by simp
  have enter: "((lp_atom_eval (fst (Q!c)) nu#tail,env),
    (map (\<lambda>b. lp_atom_eval b nu) (snd (Q!c))@tail,env))\<in>lp_seg_answer_step Q"
    using lp_seg_answer_step.resolve[OF clause.hyps(1) matching, of tail env] by simp
  have body: "((map (\<lambda>b. lp_atom_eval b nu) (snd (Q!c))@tail,env),
    (tail,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
  proof (rule lp_identity_answers_list)
    fix b rest assume "b\<in>set (map (\<lambda>b. lp_atom_eval b nu) (snd (Q!c)))"
    then show "((b#rest,env),(rest,env))\<in>(lp_seg_answer_step Q)\<^sup>*"
      using clause.hyps by auto
  qed
  show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF enter] body])
qed

lemma lp_answer_models_prefix:
  assumes models: "\<And>g. g\<in>set ps \<Longrightarrow> lp_answer_model Q (lp_atom_eval g eta)"
  shows "((map (\<lambda>g. lp_atom_eval g eta) ps,eta),([],eta))
    \<in>(lp_seg_answer_step Q)\<^sup>*"
proof -
  have "((map (\<lambda>g. lp_atom_eval g eta) ps@[],eta),([],eta))
    \<in>(lp_seg_answer_step Q)\<^sup>*"
  proof (rule lp_identity_answers_list)
    fix a tail assume "a\<in>set (map (\<lambda>g. lp_atom_eval g eta) ps)"
    then obtain g where member: "g\<in>set ps" and a: "a=lp_atom_eval g eta" by auto
    show "((a#tail,eta),(tail,eta))\<in>(lp_seg_answer_step Q)\<^sup>*"
      unfolding a by (rule lp_answer_model_identity_answers[OF models[OF member]])
  qed
  then show ?thesis by simp
qed

lemma lp_triple_calls_modelI:
  assumes triple: "(h,ps,b)\<in>D"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval h eta"
    and models: "\<And>g. g\<in>set ps \<Longrightarrow> lp_answer_model Q (lp_atom_eval g eta)"
  shows "(a,lp_atom_eval b eta)\<in>lp_triple_calls D Q"
  using triple matching lp_answer_models_prefix[OF models]
  unfolding lp_triple_calls_def by blast

end
