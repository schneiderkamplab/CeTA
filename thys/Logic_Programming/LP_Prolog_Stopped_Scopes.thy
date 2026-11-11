theory LP_Prolog_Stopped_Scopes
  imports LP_Prolog_Stopped_Modular
begin

lemma lpp_undefined_stop_scope:
  "lpp_undefined_answer_stop P B (map (map_prod (lp_cut_scope_entry r) id) ss) =
    lpp_undefined_answer_stop P B ss"
  by (cases ss)
    (auto simp: lpp_undefined_answer_stop_def lpp_undefined_def lpp_builtin_active_def
      lpp_scope_entry_atom split: prod.splits)

lemma lpp_undefined_stop_scope_word:
  "lpp_undefined_answer_stop P B (lpc_return_scope_word swaps ss) =
    lpp_undefined_answer_stop P B ss"
proof (induct swaps arbitrary: ss)
  case Nil then show ?case by simp
next
  case (Cons pair swaps)
  obtain a b where pair: "pair=(a,b)" by (cases pair) simp
  show ?case using Cons.hyps[of "map (map_prod (lp_cut_scope_entry (lp_cut_scope_swap a b)) id) ss"]
    by (simp only: pair lpc_return_scope_word.simps lpp_undefined_stop_scope)
qed

lemma lpp_stopped_scope_length:
  "length (lpc_return_scope_word swaps ss)=length ss"
  by (induct swaps arbitrary: ss) (auto split: prod.splits)

lemma lpp_stopped_scope_empty:
  "lpc_return_scope_word swaps ss=[] \<longleftrightarrow> ss=[]"
  using lpp_stopped_scope_length[of swaps ss] by (metis length_0_conv)

lemma lpp_stopped_scope_nil:
  "lpc_return_scope_word swaps []=[]"
  by (simp only: lpp_stopped_scope_empty)

lemma lpp_stopped_contract_scopes:
  assumes program: "lp_cut_source_program P"
    and contract: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D)
      (lpp_undefined_answer_stop P B)) ss R t ret"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D)
    (lpp_undefined_answer_stop P B)) (lpc_return_scope_word swaps ss) R t ret"
proof (rule lp_answer_contract_reflect[where f="lpc_return_scope_word (rev swaps)"])
  show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P B U D)
      (lpp_undefined_answer_stop P B))
      (lpc_return_scope_word (rev swaps) (lpc_return_scope_word swaps ss)) R t ret"
    using contract by (simp add: lpc_return_scope_word_inverse)
  show "\<And>us event vs. lp_answer_stop (lpp_domain_answers P B U D)
      (lpp_undefined_answer_stop P B) us event vs \<Longrightarrow>
    lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B)
      (lpc_return_scope_word (rev swaps) us) event (lpc_return_scope_word (rev swaps) vs)"
    by (auto simp: lp_answer_stop_def lpp_undefined_stop_scope_word
      lpp_domain_answers_def lpp_builtin_domain_bad_scopes lpp_stopped_scope_empty lpp_stopped_scope_nil
      intro: lpp_answer_transition_scope_word[OF _ program])
qed

ML \<open>
val checked = [@{thm lpp_stopped_contract_scopes}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped scope dependency" else ();
\<close>
end
