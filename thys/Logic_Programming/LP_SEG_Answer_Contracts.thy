theory LP_SEG_Answer_Contracts
  imports LP_SEG_Answers
begin

text \<open>A node contract combines termination with simulation of every
  successful answer. Output encodings depend on the actual final environment,
  not on a guessed answer or a substituted initial mode.\<close>

definition lp_seg_return_contract where
  "lp_seg_return_contract P gs \<rho> R t ret =
    (SN_on (lp_ild P) {gs} \<and>
     (\<forall>\<eta>. ((gs,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*
       \<longrightarrow> (t,ret \<eta>) \<in> (rstep R)\<^sup>*))"

lemma lp_seg_return_contract_empty:
  assumes "(t,ret \<rho>) \<in> (rstep R)\<^sup>*"
  shows "lp_seg_return_contract P [] \<rho> R t ret"
proof -
  have terminal: "\<And>\<eta>. (([],\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow> \<eta>=\<rho>"
    by (erule converse_rtranclE) (auto elim: lp_seg_answer_step.cases)
  have sn: "SN_on (lp_ild P) {[]}"
    by (rule step_reflects_SN_on) (auto elim: lp_ild.cases)
  show ?thesis using assms sn terminal unfolding lp_seg_return_contract_def by blast
qed

text \<open>The three Split rules preserve the returned values and their
  correlations with the input. The continuation context may depend on the first
  answer, and the final output must describe the second answer. This is the
  compositional proof obligation behind PPDP Definition 15.\<close>

theorem lp_seg_return_contract_split:
  fixes P :: "('f,string) lp_clause list"
    and prefix :: "('f,string) lp_iatom list"
    and rest :: "('f,string) lp_atom list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
    and C1 :: "('g,string) ctxt"
    and C2 :: "(string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> ('g,string) ctxt"
  assumes first: "lp_seg_return_contract P prefix \<rho> R t1 O1"
    and entry: "(t,C1\<langle>t1\<rangle>) \<in> (rstep R)\<^sup>*"
    and second: "\<And>\<mu>. ((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
      lp_seg_return_contract P (map (\<lambda>a. lp_atom_eval a \<mu>) rest) \<mu> R (I2 \<mu>) (O2 \<mu>)"
    and middle: "\<And>\<mu>. ((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
      (C1\<langle>O1 \<mu>\<rangle>,(C2 \<mu>)\<langle>I2 \<mu>\<rangle>) \<in> (rstep R)\<^sup>*"
    and finish: "\<And>\<mu> \<eta>. ((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
      ((map (\<lambda>a. lp_atom_eval a \<mu>) rest,\<mu>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow>
      ((C2 \<mu>)\<langle>O2 \<mu> \<eta>\<rangle>,ret \<eta>) \<in> (rstep R)\<^sup>*"
  shows "lp_seg_return_contract P (prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest) \<rho> R t ret"
proof -
  have sn1: "SN_on (lp_ild P) {prefix}"
    using first unfolding lp_seg_return_contract_def by blast
  have sn: "SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    by (rule lp_seg_append_sn_answers[OF sn1])
      (use second in \<open>auto simp: lp_seg_return_contract_def\<close>)
  have returns: "\<And>\<eta>. ((prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>* \<Longrightarrow> (t,ret \<eta>) \<in> (rstep R)\<^sup>*"
  proof -
    fix \<eta> assume path: "((prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>*"
    obtain \<mu> where a: "((prefix,\<rho>),([],\<mu>)) \<in> (lp_seg_answer_step P)\<^sup>*"
      and b: "((map (\<lambda>a. lp_atom_eval a \<mu>) rest,\<mu>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
      using lp_seg_answer_steps_split[OF path] by blast
    have ret1: "(t1,O1 \<mu>) \<in> (rstep R)\<^sup>*"
      using first a unfolding lp_seg_return_contract_def by blast
    have ret2: "(I2 \<mu>,O2 \<mu> \<eta>) \<in> (rstep R)\<^sup>*"
      using second[OF a] b unfolding lp_seg_return_contract_def by blast
    have lift1: "(C1\<langle>t1\<rangle>,C1\<langle>O1 \<mu>\<rangle>) \<in> (rstep R)\<^sup>*"
      by (rule ctxt.closedD[OF ctxt_closed_rsteps ret1])
    have lift2: "((C2 \<mu>)\<langle>I2 \<mu>\<rangle>,(C2 \<mu>)\<langle>O2 \<mu> \<eta>\<rangle>) \<in> (rstep R)\<^sup>*"
      by (rule ctxt.closedD[OF ctxt_closed_rsteps ret2])
    have left: "(t,(C2 \<mu>)\<langle>I2 \<mu>\<rangle>) \<in> (rstep R)\<^sup>*"
      by (rule rtrancl_trans[OF rtrancl_trans[OF entry lift1] middle[OF a]])
    show "(t,ret \<eta>) \<in> (rstep R)\<^sup>*"
      by (rule rtrancl_trans[OF rtrancl_trans[OF left lift2] finish[OF a b]])
  qed
  show ?thesis using sn returns unfolding lp_seg_return_contract_def by blast
qed

end
