theory LP_Prolog_Stopped_Modular
  imports LP_Prolog_Stopped_Answers LP_Prolog_Domain_Modular
begin

lemma lpp_undefined_stop_append:
  "ss\<noteq>[] \<Longrightarrow> lpp_undefined_answer_stop P B (ss@bs)=lpp_undefined_answer_stop P B ss"
  by (cases ss) (auto simp: lpp_undefined_answer_stop_def lpp_undefined_def lpp_builtin_active_def)

lemma lpp_stopped_append_suffix:
  assumes nonempty: "ss\<noteq>[]"
    and step: "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (ss@bs) event result"
  shows "\<exists>tt n. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ss event tt \<and>
    result=tt@drop n bs"
  by (rule lp_answer_stop_append_suffix[where T="lpp_domain_answers P B U D" and stop="lpp_undefined_answer_stop P B" and ss=ss and bs=bs, OF nonempty lpp_undefined_stop_append[OF nonempty] _ step])
    (rule lpp_domain_append_suffix[OF nonempty])

lemma lpp_stopped_barriers_contract:
  "lp_cut_barriers (map fst bs) \<Longrightarrow>
   lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) bs R t ret"
  by (rule lp_answer_stop_contract, rule lpp_domain_barriers_contract)

lemma lpp_stopped_contract_append_barriers:
  assumes contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret"
    and barriers: "lp_cut_barriers (map fst bs)"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) (ss@bs) R t ret"
proof (rule lp_answer_contract_append_silent[where K="\<lambda>bs. lp_cut_barriers (map fst bs)"])
  show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret" by (rule contract)
  show "lp_cut_barriers (map fst bs)" by (rule barriers)
  show "\<And>cs. lp_cut_barriers (map fst cs) \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) cs R t ret"
    by (rule lpp_stopped_barriers_contract)
  show "\<And>cs n. lp_cut_barriers (map fst cs) \<Longrightarrow> lp_cut_barriers (map fst (drop n cs))"
    by (auto simp: list_all_iff dest: in_set_dropD)
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us event vs \<and>
      result=vs@drop n cs"
    by (rule lpp_stopped_append_suffix)
qed

lemma lpp_stopped_contract_singletons:
  assumes singletons: "\<And>e. e\<in>set ss \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) [e] R t ret"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) ss R t ret"
proof (rule lp_answer_contract_singletons)
  show "\<And>e. e\<in>set ss \<Longrightarrow>
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) [e] R t ret"
    by (rule singletons)
  show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)) [] R t ret"
    by (rule lpp_stopped_barriers_contract) simp
  show "\<And>us cs event result. us\<noteq>[] \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) (us@cs) event result \<Longrightarrow>
    \<exists>vs n. lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) us event vs \<and>
      result=vs@drop n cs"
    by (rule lpp_stopped_append_suffix)
qed
ML \<open>
val audited = [@{thm lpp_stopped_append_suffix}, @{thm lpp_stopped_contract_append_barriers},
  @{thm lpp_stopped_contract_singletons}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted stopped modular contract dependency" else ();
\<close>
end
