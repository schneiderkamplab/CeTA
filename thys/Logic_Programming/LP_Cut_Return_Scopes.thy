theory LP_Cut_Return_Scopes
  imports LP_Cut_Return_Link LP_Cut_MGU_Scopes
begin

abbreviation lpc_return_scope where
  "lpc_return_scope r ss \<equiv> map (map_prod (lp_cut_scope_entry r) id) ss"

lemma lpc_answer_prune_scope:
  assumes "inj r"
  shows "lpc_answer_prune (r m) (lpc_return_scope r ss) =
    lpc_return_scope r (lpc_answer_prune m ss)"
  using assms by (induct ss) (auto simp: inj_eq split: prod.splits lp_cut_entry.splits)

lemma lpc_answer_transition_scope:
  assumes step: "lpc_answer_transition P ss event tt"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "lpc_answer_transition P (lpc_return_scope r ss) event (lpc_return_scope r tt)"
  using step
proof (induct rule: lpc_answer_transition.induct)
  case (barrier m eta es)
  show ?case by (simp add: lpc_answer_transition.barrier)
next
  case (success eta es)
  show ?case by (simp add: lpc_answer_transition.success)
next
  case (truth gs eta es)
  show ?case by (simp add: lpc_answer_transition.truth)
next
  case (failure gs eta es)
  show ?case by (simp add: lpc_answer_transition.failure)
next
  case (cut m gs eta es)
  show ?case using lpc_answer_transition.cut[of P "r m" "map (lp_cut_scope_goal r) gs" eta "lpc_return_scope r es"]
    lpc_answer_prune_scope[OF injective, of m es]
    by (auto simp: id_def)
next
  case (case_call m f ts gs es eta)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) (map fst es))"
    using case_call.hyps lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es"] by simp
  have fresh': "lp_cut_fresh (r m)
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs)#map fst (lpc_return_scope r es))"
    using fresh by (simp add: map_map o_def map_prod_def split_def)
  show ?case using lpc_answer_transition.case_call[OF fresh', of P eta]
    by (simp add: map_map o_def map_prod_def split_def id_def)
next
  case (resolve c a gs sigma rho m eta es)
  have body: "map (lp_cut_scope_goal r)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c))) =
    map (lp_cut_bind (r m) (\<lambda>t. lp_ieval t rho)) (snd (P!c))"
    using program resolve.hyps(1)
    by (auto simp: lp_cut_source_program_def list_all_iff map_map o_def
      intro!: map_cong lp_cut_scope_bind)
  have mgu: "lpc_mgu_resolve a (map (lp_cut_scope_goal r) gs) (fst (P!c)) (snd (P!c)) sigma rho"
    by (rule lpc_mgu_resolve_scope[OF resolve.hyps(2)])
  show ?case using lpc_answer_transition.resolve[OF resolve.hyps(1) mgu, of "r m" eta "lpc_return_scope r es"]
    by (simp add: body[unfolded map_map o_def] map_map o_def lp_cut_scope_goal_map id_def)
next
  case (backtrack c a gs m eta es)
  show ?case using lpc_answer_transition.backtrack[OF backtrack.hyps,
    of "map (lp_cut_scope_goal r) gs" "r m" eta "lpc_return_scope r es"] by (simp add: id_def)
next
  case (unify a b gs sigma eta es)
  have mgu: "lpc_mgu_unify a b (map (lp_cut_scope_goal r) gs) sigma"
    by (rule lpc_mgu_unify_scope[OF unify.hyps])
  show ?case using lpc_answer_transition.unify[OF mgu, of P eta "lpc_return_scope r es"]
    by (simp add: map_map o_def lp_cut_scope_goal_map id_def)
next
  case (unify_fail a b gs eta es)
  show ?case using lpc_answer_transition.unify_fail[OF unify_fail.hyps,
    of P "map (lp_cut_scope_goal r) gs" eta "lpc_return_scope r es"] by (simp add: id_def)
next
  case (meta m a gs es body eta)
  have fresh: "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map (lp_cut_scope_entry r) (map fst es))"
    using meta.hyps(1) lp_cut_scope_fresh[OF injective, of m
      "LPCGoals (LPCMeta a#gs)#map fst es"] by simp
  have fresh': "lp_cut_fresh (r m)
    (LPCGoals (LPCMeta a#map (lp_cut_scope_goal r) gs)#map fst (lpc_return_scope r es))"
    using fresh by (simp add: map_map o_def map_prod_def split_def)
  show ?case using lpc_answer_transition.meta[OF fresh' lp_cut_scope_lower[OF meta.hyps(2), of r], of P eta]
    by (simp add: map_map o_def map_prod_def split_def id_def)
next
  case (meta_unlowerable a gs eta es)
  show ?case using lpc_answer_transition.meta_unlowerable[OF meta_unlowerable.hyps,
    of P "map (lp_cut_scope_goal r) gs" eta "lpc_return_scope r es"] by (simp add: id_def)
qed

lemma lpc_return_scope_word_append:
  "lpc_return_scope_word (xs@ys) ss = lpc_return_scope_word ys (lpc_return_scope_word xs ss)"
  by (induct xs arbitrary: ss) (auto split: prod.splits)

lemma lpc_return_scope_goal_id:
  "lp_cut_scope_goal (\<lambda>x. x) g = g"
  by (cases g) simp_all

lemma lpc_return_scope_entry_id:
  "lp_cut_scope_entry (\<lambda>x. x) e = e"
  by (cases e) (auto intro!: map_idI simp: lpc_return_scope_goal_id)

lemma lpc_return_scope_swap_twice:
  "lpc_return_scope (lp_cut_scope_swap a b) (lpc_return_scope (lp_cut_scope_swap a b) ss) = ss"
  by (simp add: map_map o_def map_prod_def split_def lp_cut_scope_entry_comp
    lp_cut_scope_swap_inverse lpc_return_scope_entry_id)

lemma lpc_return_scope_word_inverse:
  "lpc_return_scope_word (rev swaps) (lpc_return_scope_word swaps ss) = ss"
proof (induct swaps arbitrary: ss)
  case Nil then show ?case by simp
next
  case (Cons ab swaps)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  show ?case by (simp only: ab rev.simps lpc_return_scope_word_append
    lpc_return_scope_word.simps Cons.hyps lpc_return_scope_swap_twice)
qed

lemma lpc_answer_transition_scope_word:
  assumes "lpc_answer_transition P ss event tt" "lp_cut_source_program P"
  shows "lpc_answer_transition P (lpc_return_scope_word swaps ss) event (lpc_return_scope_word swaps tt)"
  using assms(1)
proof (induct swaps arbitrary: ss tt)
  case Nil then show ?case by simp
next
  case (Cons ab swaps)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "lpc_answer_transition P (lpc_return_scope (lp_cut_scope_swap a b) ss) event
    (lpc_return_scope (lp_cut_scope_swap a b) tt)"
    by (rule lpc_answer_transition_scope[OF Cons.prems lp_cut_scope_swap_injective assms(2)])
  show ?case using Cons.hyps[OF first] by (simp only: ab lpc_return_scope_word.simps)
qed

text \<open>Fresh scope labels are administrative choices, not oracle keys.
Local receipts may close against a scope-renamed child. This theorem turns
that finite representation into the unrestricted source return contract.\<close>

theorem lpc_return_graph_scope_valid:
  assumes program: "lp_cut_source_program P"
    and local: "\<And>ss t event tt. rep ss t \<Longrightarrow> lpc_answer_transition P ss event tt \<Longrightarrow>
      (\<exists>u swaps. (t,u)\<in>R\<^sup>+ \<and> rep (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*)"
  shows "lpc_return_graph_valid P R (\<lambda>ss t. \<exists>swaps. rep (lpc_return_scope_word swaps ss) t) ret (\<lambda>_. 0)"
proof (unfold lpc_return_graph_valid_def, intro allI impI)
  fix ss t event tt
  assume represented: "\<exists>swaps. rep (lpc_return_scope_word swaps ss) t"
    and step: "lpc_answer_transition P ss event tt"
  obtain swaps where rep: "rep (lpc_return_scope_word swaps ss) t" using represented by blast
  have scoped: "lpc_answer_transition P (lpc_return_scope_word swaps ss) event (lpc_return_scope_word swaps tt)"
    by (rule lpc_answer_transition_scope_word[OF step program])
  obtain u more where edge: "(t,u)\<in>R\<^sup>+"
    and child: "rep (lpc_return_scope_word more (lpc_return_scope_word swaps tt)) u"
    and emit: "\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*"
    using local[OF rep scoped] by blast
  have child': "\<exists>rs. rep (lpc_return_scope_word rs tt) u"
    by (rule exI[of _ "swaps@more"]) (simp add: lpc_return_scope_word_append child)
  show "((\<exists>u. (t,u)\<in>R\<^sup>+ \<and> (\<exists>swaps. rep (lpc_return_scope_word swaps tt) u)) \<or>
    (\<exists>swaps. rep (lpc_return_scope_word swaps tt) t) \<and> (0::nat)<0) \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*)"
    using edge child' emit by blast
qed

end
