theory LP_Prolog_Stopped_Composition
  imports LP_Prolog_Stopped_Modular LP_Prolog_Domain_Composition
begin

lemma lpp_stopped_owned_append:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E (map fst ss)"
    and separated: "E\<inter>set (lpc_barrier_ids (map fst es)) = {}"
    and prefix: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret"
    and suffix: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) es R t ret"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (ss@es) R t ret"
proof (rule lp_answer_contract_append[where K="\<lambda>us. lpc_owned_stack E (map fst us)",
    OF prefix suffix owned])
  show "\<And>us event vs. lpc_owned_stack E (map fst us) \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us event vs \<Longrightarrow> lpc_owned_stack E (map fst vs)"
    by (auto simp: lp_answer_stop_def lpp_domain_answers_def dest: lpp_owned_answer_preserved[OF program] split: if_splits)
  fix us event result
  assume nonempty: "us\<noteq>[]" and owned: "lpc_owned_stack E (map fst us)"
    and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (us@es) event result"
  show "\<exists>vs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us event vs \<and> (result = vs@es \<or> result = vs)"
  proof (cases "lpp_undefined_answer_stop P B us")
    case True
    have step0: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us None []"
      using True nonempty by (simp add: lp_answer_stop_def)
    have result: "event=None" "result=[]"
      using step True lpp_undefined_stop_append[OF nonempty, of P B es]
      by (simp_all add: lp_answer_stop_def)
    show ?thesis using step0 result by blast
  next
    case False
    have original: "lpp_domain_answers P B U D (us@es) event result"
      using step False lpp_undefined_stop_append[OF nonempty, of P B es]
      by (simp add: lp_answer_stop_def)
    obtain vs where local: "lpp_domain_answers P B U D us event vs"
      and result: "result=vs@es \<or> result=vs"
    proof (cases "lpp_answer_transition P B U (us@es) event result")
      case True
      show thesis using lpp_owned_answer_append[OF nonempty owned separated True]
        that by (auto simp: lpp_domain_answers_def)
    next
      case False
      have bad: "lpp_builtin_domain_bad B D (map fst us)" and shape: "event=None" "result=us@es"
        using original False lpp_domain_bad_append[OF nonempty, of B D es]
        by (auto simp: lpp_domain_answers_def)
      show thesis by (rule that[of us]) (use bad shape in \<open>auto simp: lpp_domain_answers_def\<close>)
    qed
    show ?thesis using local result nonempty False by (auto simp: lp_answer_stop_def)
  qed
qed

lemma lpp_stopped_attach_reflect:
  assumes active: "lpc_prefix_active ss"
    and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_attach_answers rest ss) event result"
  shows "event=None \<and> (\<exists>vs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ss None vs \<and>
    result=lpc_attach_answers rest vs)"
  by (rule lp_answer_stop_attach_reflect[where T="lpp_domain_answers P B U D"
    and stop="lpp_undefined_answer_stop P B", OF active lpp_undefined_stop_attach[OF active] _ step])
    (rule lpp_domain_attach_reflect[OF active])

theorem lpp_stopped_contract_compose_actual:
  assumes program: "lp_cut_source_program P"
    and prefix: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>eta. lp_actual_answer (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss eta \<Longrightarrow>
      lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (lpc_attach_answers rest ss) R t final"
proof (rule lp_scoped_answer_contract_compose_actual[OF prefix valid separated continuation])
  show "\<And>us ev vs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us ev vs \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
    by (auto simp: lp_answer_stop_def lpp_domain_answers_def dest: lpp_clause_nonempty_preserved split: if_splits)
  show "\<And>us ev result. lpc_prefix_active us \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_attach_answers rest us) ev result \<Longrightarrow>
    ev = None \<and> (\<exists>vs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us None vs \<and> result = lpc_attach_answers rest vs)"
    by (rule lpp_stopped_attach_reflect)
  show "\<And>us ev vs. lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {} \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
  proof -
    fix us ev vs
    assume sep: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {}"
      and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)"
    show "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
    proof (cases "lpp_undefined_answer_stop P B (lpc_attach_answers rest us)")
      case True
      have "vs=[]" using step True by (auto simp: lp_answer_stop_def lpc_attach_answers_def)
      then show ?thesis by simp
    next
      case False
      have original: "lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)"
        using step False by (simp add: lp_answer_stop_def)
      show ?thesis
      proof (cases "lpp_answer_transition P B U (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)")
      case True
      have source: "(lpc_attach rest us,lpc_attach rest vs)\<in>lpp_atomic_source P B U"
        using lpp_answer_transition_erases[OF True] by (simp add: lpc_attach_answers_erases)
      show ?thesis using lpp_attach_barriers_preserved[OF sep source] by (simp add: lpc_attach_barriers)
    next
      case False
      have eq: "lpc_attach_answers rest vs = lpc_attach_answers rest us"
        using original False by (simp add: lpp_domain_answers_def)
      have "lpc_barrier_ids (map fst vs) = lpc_barrier_ids (map fst us)"
        using arg_cong[OF eq, of "\<lambda>xs. lpc_barrier_ids (map fst xs)"]
        by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
      then show ?thesis using sep by simp
    qed
    qed
  qed
  show "\<And>ev vs. \<not>lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) [] ev vs"
    by (auto simp: lp_answer_stop_def lpp_domain_answers_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)
  show "\<And>eta vs. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ((LPCGoals [],eta)#vs) (Some eta) vs"
    by (auto simp: lp_answer_stop_def lpp_undefined_answer_stop_def lpp_undefined_def lpp_domain_answers_def lpp_builtin_active_def
      intro: lpp_answer_transition.base lpc_answer_transition.success)
  show "\<And>us vs. lpc_owned_stack (lpc_rest_scopes rest) (map fst us) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {} \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) us R t final \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) vs R t final \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (us@vs) R t final"
    by (rule lpp_stopped_owned_append[OF program])
qed

ML \<open>
val checked = [@{thm lpp_stopped_owned_append}, @{thm lpp_stopped_contract_compose_actual}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped Split composition dependency" else ();
\<close>
end
