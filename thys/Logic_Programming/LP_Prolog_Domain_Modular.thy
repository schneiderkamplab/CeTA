theory LP_Prolog_Domain_Modular
 imports LP_Prolog_Context_Graph LP_Prolog_Return_Modular
begin

lemma lpp_domain_bad_entry:
  "lpp_builtin_domain_bad B D (e#xs)=lpp_builtin_domain_bad B D (e#ys)"
  by (cases "(B,D,e#xs)" rule: lpp_builtin_domain_bad.cases) auto

lemma lpp_domain_bad_append:
  assumes nonempty: "ss\<noteq>[]"
  shows "lpp_builtin_domain_bad B D (map fst (ss@bs)) = lpp_builtin_domain_bad B D (map fst ss)"
proof (cases ss)
  case Nil then show ?thesis using nonempty by simp
next
  case (Cons a xs)
  show ?thesis using lpp_domain_bad_entry[of B D "fst a" "map fst xs @ map fst bs" "map fst xs"]
    by (simp only: Cons append_Cons list.map map_append)
qed

lemma lpp_domain_append_suffix:
  assumes nonempty: "ss\<noteq>[]" and step: "lpp_domain_answers P B U D (ss@bs) event result"
  shows "\<exists>tt n. lpp_domain_answers P B U D ss event tt \<and> result=tt@drop n bs"
proof (cases "lpp_answer_transition P B U (ss@bs) event result")
  case True
  obtain tt n where "lpp_answer_transition P B U ss event tt" "result=tt@drop n bs"
    using lpp_answer_append_suffix[OF nonempty True] by blast
  then show ?thesis by (auto simp: lpp_domain_answers_def)
next
  case False
  have "lpp_builtin_domain_bad B D (map fst ss)" "event=None" "result=ss@bs"
    using step False lpp_domain_bad_append[OF nonempty, of B D bs]
    by (auto simp: lpp_domain_answers_def)
  then show ?thesis by (intro exI[of _ ss] exI[of _ 0]) (simp add: lpp_domain_answers_def)
qed

lemma lpp_domain_barriers_contract:
  "lp_cut_barriers (map fst bs) \<Longrightarrow> lp_answer_contract (lpp_domain_answers P B U D) bs R t ret"
proof (induct bs)
  case Nil
  show ?case by (rule lp_answer_contract_intro)
    (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)
next
  case (Cons frame bs)
  obtain m eta where frame: "frame=(LPCBarrier m,eta)"
    using Cons.prems by (cases frame; cases "fst frame"; auto)
  have tail: "lp_answer_contract (lpp_domain_answers P B U D) bs R t ret"
    using Cons by (simp add: frame)
  show ?case
  proof (rule lp_answer_contract_intro)
    fix event tt assume step: "lpp_domain_answers P B U D (frame#bs) event tt"
    have base: "lpp_answer_transition P B U ((LPCBarrier m,eta)#bs) event tt"
      using step by (simp add: frame lpp_domain_answers_def)
    have shape: "event=None" "tt=bs"
      using base by (cases rule: lpp_answer_transition.cases; auto elim: lpc_answer_transition.cases)+
    show "(\<forall>rho. event=Some rho \<longrightarrow> (t,ret rho)\<in>R\<^sup>*) \<and>
      lp_answer_contract (lpp_domain_answers P B U D) tt R t ret"
      using tail shape by simp
  qed
qed

lemma lpp_domain_contract_append_barriers:
  assumes contract: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and barriers: "lp_cut_barriers (map fst bs)"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (ss@bs) R t ret"
proof (rule lp_answer_contract_append_silent[where K="\<lambda>bs. lp_cut_barriers (map fst bs)"])
  show "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret" by (rule contract)
  show "lp_cut_barriers (map fst bs)" by (rule barriers)
  show "\<And>cs. lp_cut_barriers (map fst cs) \<Longrightarrow> lp_answer_contract (lpp_domain_answers P B U D) cs R t ret"
    by (rule lpp_domain_barriers_contract)
  show "\<And>cs n. lp_cut_barriers (map fst cs) \<Longrightarrow> lp_cut_barriers (map fst (drop n cs))"
    by (auto simp: list_all_iff dest: in_set_dropD)
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow> lpp_domain_answers P B U D (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lpp_domain_answers P B U D us event vs \<and> result=vs@drop n cs"
    by (rule lpp_domain_append_suffix)
qed

lemma lpp_domain_contract_singletons:
  assumes singletons: "\<And>e. e\<in>set ss \<Longrightarrow> lp_answer_contract (lpp_domain_answers P B U D) [e] R t ret"
  shows "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
proof (rule lp_answer_contract_singletons)
  show "\<And>e. e\<in>set ss \<Longrightarrow> lp_answer_contract (lpp_domain_answers P B U D) [e] R t ret"
    by (rule singletons)
  show "lp_answer_contract (lpp_domain_answers P B U D) [] R t ret"
    by (rule lpp_domain_barriers_contract) simp
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow> lpp_domain_answers P B U D (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lpp_domain_answers P B U D us event vs \<and> result=vs@drop n cs"
    by (rule lpp_domain_append_suffix)
qed

lemma lpp_domain_contract_scopes:
  assumes program: "lp_cut_source_program P" and contract: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_scope_word swaps ss) R t ret"
proof (rule lp_answer_contract_reflect[where f="lpc_return_scope_word (rev swaps)"])
  show "lp_answer_contract (lpp_domain_answers P B U D) (lpc_return_scope_word (rev swaps) (lpc_return_scope_word swaps ss)) R t ret"
    using contract by (simp add: lpc_return_scope_word_inverse)
  show "\<And>us event vs. lpp_domain_answers P B U D us event vs \<Longrightarrow>
    lpp_domain_answers P B U D (lpc_return_scope_word (rev swaps) us) event (lpc_return_scope_word (rev swaps) vs)"
    by (auto simp: lpp_domain_answers_def lpp_builtin_domain_bad_scopes intro: lpp_answer_transition_scope_word[OF _ program])
qed
end
