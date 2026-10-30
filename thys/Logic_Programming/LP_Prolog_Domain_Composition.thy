theory LP_Prolog_Domain_Composition
 imports LP_Prolog_Return_Composition LP_Prolog_Domain_Modular
begin

lemma lpp_domain_bad_attach:
  assumes active: "lpc_prefix_active ss"
  shows "lpp_builtin_domain_bad B D (map fst (lpc_attach_answers rest ss)) =
    lpp_builtin_domain_bad B D (map fst ss)"
proof -
  obtain e eta es where ss: "ss = (e,eta)#es"
    using active by (cases ss; auto split: prod.splits)
  show ?thesis
  proof (cases e)
    case (LPCGoals gs)
    show ?thesis
    proof (cases gs)
      case Nil then show ?thesis using active LPCGoals by (simp add: ss)
    next
      case (Cons g tail)
      show ?thesis
      proof (cases g)
        case (LPCAtom a)
        show ?thesis
        proof (cases a)
          case (LPIFun f args)
          then show ?thesis using LPCGoals Cons LPCAtom
            by (cases f; auto simp: ss lpc_attach_answers_def)
        qed (use LPCGoals Cons LPCAtom in \<open>auto simp: ss lpc_attach_answers_def\<close>)
      qed (use LPCGoals Cons in \<open>auto simp: ss lpc_attach_answers_def\<close>)
    qed
  qed (auto simp: ss lpc_attach_answers_def)
qed

lemma lpp_domain_owned_append:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es)) = {}"
    and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and suffix: "lp_answer_contract (lpp_domain_answers P B U D) es R t ret"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (ss@es) R t ret"
proof (rule lp_answer_contract_append[where K="\<lambda>us. lpc_owned_stack E (map fst us)",
    OF prefix suffix owned])
  show "\<And>us event vs. lpc_owned_stack E (map fst us) \<Longrightarrow>
    lpp_domain_answers P B U D us event vs \<Longrightarrow> lpc_owned_stack E (map fst vs)"
    by (auto simp: lpp_domain_answers_def dest: lpp_owned_answer_preserved[OF program])
  fix us event result
  assume nonempty: "us\<noteq>[]" and owned: "lpc_owned_stack E (map fst us)"
    and step: "lpp_domain_answers P B U D (us@es) event result"
  show "\<exists>vs. lpp_domain_answers P B U D us event vs \<and> (result = vs@es \<or> result = vs)"
  proof (cases "lpp_answer_transition P B U (us@es) event result")
    case True
    obtain vs where "lpp_answer_transition P B U us event vs" "result = vs@es \<or> result = vs"
      using lpp_owned_answer_append[OF nonempty owned separated True] by blast
    then show ?thesis by (auto simp: lpp_domain_answers_def)
  next
    case False
    have bad: "lpp_builtin_domain_bad B D (map fst us)" and shape: "event = None" "result = us@es"
      using step False lpp_domain_bad_append[OF nonempty, of B D es]
      by (auto simp: lpp_domain_answers_def)
    show ?thesis by (rule exI[of _ us]) (use bad shape in \<open>simp add: lpp_domain_answers_def\<close>)
  qed
qed

lemma lpp_domain_attach_reflect:
  assumes active: "lpc_prefix_active ss"
    and step: "lpp_domain_answers P B U D (lpc_attach_answers rest ss) event result"
  shows "event = None \<and> (\<exists>vs. lpp_domain_answers P B U D ss None vs \<and>
    result = lpc_attach_answers rest vs)"
proof (cases "lpp_answer_transition P B U (lpc_attach_answers rest ss) event result")
  case True
  show ?thesis using lpp_attach_answers_active_reflect[OF active True]
    by (auto simp: lpp_domain_answers_def)
next
  case False
  have "lpp_builtin_domain_bad B D (map fst ss)" "event = None" "result = lpc_attach_answers rest ss"
    using step False lpp_domain_bad_attach[OF active, of B D rest]
    by (auto simp: lpp_domain_answers_def)
  then show ?thesis by (auto simp: lpp_domain_answers_def)
qed

theorem lpp_domain_contract_compose:
  assumes program: "lp_cut_source_program P"
    and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>eta. (t,ret eta)\<in>R\<^sup>* \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P B U D)
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_attach_answers rest ss) R t final"
proof (rule lp_scoped_answer_contract_compose[OF prefix valid separated continuation])
  show "\<And>us ev vs. lpp_domain_answers P B U D us ev vs \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
    by (auto simp: lpp_domain_answers_def dest: lpp_clause_nonempty_preserved)
  show "\<And>us ev result. lpc_prefix_active us \<Longrightarrow>
    lpp_domain_answers P B U D (lpc_attach_answers rest us) ev result \<Longrightarrow>
    ev = None \<and> (\<exists>vs. lpp_domain_answers P B U D us None vs \<and> result = lpc_attach_answers rest vs)"
    by (rule lpp_domain_attach_reflect)
  show "\<And>us ev vs. lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {} \<Longrightarrow>
    lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
  proof -
    fix us ev vs
    assume sep: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {}"
      and step: "lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)"
    show "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
    proof (cases "lpp_answer_transition P B U (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)")
      case True
      have source: "(lpc_attach rest us,lpc_attach rest vs)\<in>lpp_atomic_source P B U"
        using lpp_answer_transition_erases[OF True] by (simp add: lpc_attach_answers_erases)
      show ?thesis using lpp_attach_barriers_preserved[OF sep source] by (simp add: lpc_attach_barriers)
    next
      case False
      have eq: "lpc_attach_answers rest vs = lpc_attach_answers rest us"
        using step False by (simp add: lpp_domain_answers_def)
      have "lpc_barrier_ids (map fst vs) = lpc_barrier_ids (map fst us)"
        using arg_cong[OF eq, of "\<lambda>xs. lpc_barrier_ids (map fst xs)"]
        by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
      then show ?thesis using sep by simp
    qed
  qed
  show "\<And>ev vs. \<not>lpp_domain_answers P B U D [] ev vs"
    by (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)
  show "\<And>eta vs. lpp_domain_answers P B U D ((LPCGoals [],eta)#vs) (Some eta) vs"
    by (auto simp: lpp_domain_answers_def lpp_builtin_active_def
      intro: lpp_answer_transition.base lpc_answer_transition.success)
  show "\<And>us vs. lpc_owned_stack (lpc_rest_scopes rest) (map fst us) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {} \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) us R t final \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) vs R t final \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) (us@vs) R t final"
    by (rule lpp_domain_owned_append[OF program])
qed

end
