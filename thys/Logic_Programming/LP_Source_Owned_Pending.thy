theory LP_Source_Owned_Pending
 imports LP_Prolog_NO_Pending LP_Cut_NO_Return_Attachment
begin

text \<open>An executed cut may retain a caller suffix when its barrier is
already inside the checked prefix. Missing barriers are rejected: otherwise
pruning can cross the boundary and discard caller alternatives.\<close>

fun lpc_no_owned_suffix where
 "lpc_no_owned_suffix (LPCGoals (LPCCut m#gs)#es) = (LPCBarrier m\<in>set es)"
| "lpc_no_owned_suffix s = True"

lemma lpc_no_cut_free_owned:
 "lpc_no_suffix_safe s \<Longrightarrow> lpc_no_owned_suffix s"
 by (cases s rule: lpc_no_suffix_safe.cases) auto

lemma lpc_no_owned_admin_pending:
 assumes "lp_cut_admin s = Some t" "lpc_no_owned_suffix s"
 shows "lp_cut_admin (s@bs) = Some (t@bs)"
 using assms
 by (induct s rule: lp_cut_admin.induct)
   (auto simp: lp_cut_prune_append split: lp_cut_goal.splits)

lemma lpc_no_owned_source_pending:
 assumes step: "(s,t)\<in>lp_cut_mgu_source P"
   and owned: "lpc_no_owned_suffix s"
   and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
     (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(s@bs,t@bs)\<in>lp_cut_mgu_source P"
 using step fresh owned
proof (cases rule: lp_cut_mgu_source.cases)
 case admin
 show ?thesis using lpc_no_owned_admin_pending[OF admin owned]
   by (rule lp_cut_mgu_source.admin)
qed (force simp: lp_cut_fresh_def append_assoc
 intro: lp_cut_mgu_source.case_call lp_cut_mgu_source.resolve lp_cut_mgu_source.backtrack
   lp_cut_mgu_source.unify lp_cut_mgu_source.unify_fail lp_cut_mgu_source.meta
   lp_cut_mgu_source.meta_unlowerable)+

lemma lpp_builtin_owned_source_pending:
 assumes step: "(s,t)\<in>lpp_builtin_source P U"
   and nonempty: "t\<noteq>[]"
   and owned: "lpc_no_owned_suffix s"
   and fresh: "(\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
     (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(s@bs,t@bs)\<in>lpp_builtin_source P U"
proof (cases "lpc_no_suffix_safe s")
 case True
 show ?thesis by (rule lpp_builtin_source_pending[OF step nonempty True fresh])
next
 case False
 then obtain m gs es where shape: "s=LPCGoals (LPCCut m#gs)#es"
   by (cases s rule: lpc_no_suffix_safe.cases) auto
 have ordinary: "(s,t)\<in>lp_cut_mgu_source P"
   using step by (simp add: shape lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
 have extended: "(s@bs,t@bs)\<in>lp_cut_mgu_source P"
   by (rule lpc_no_owned_source_pending[OF ordinary owned fresh])
 show ?thesis using extended
   by (simp add: shape lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
qed

lemma lpc_no_owned_scope_transport:
 assumes injective: "inj r"
 shows "lpc_no_owned_suffix (map (lp_cut_scope_entry r) s) = lpc_no_owned_suffix s"
proof -
 have member: "(LPCBarrier (r m)\<in>set (map (lp_cut_scope_entry r) es)) =
   (LPCBarrier m\<in>set es)" for m es
 proof (induct es)
   case Nil then show ?case by simp
 next
   case (Cons e es)
   then show ?case by (cases e) (auto simp: inj_eq[OF injective])
 qed
 show ?thesis by (cases s rule: lpc_no_owned_suffix.cases)
   (simp_all add: member del: set_map)
qed

lemma lpc_owned_answer_admin_pending:
 assumes checked: "lpc_return_admin ss = Some (None,tt)"
   and owned: "lpc_no_owned_suffix (map fst ss)"
 shows "lpc_return_admin (ss@saved) = Some (None,tt@saved)"
 using checked owned
 by (induct ss rule: lpc_return_admin.induct)
   (auto simp: lpc_answer_prune_append split: lp_cut_goal.splits)

lemma lpc_fresh_scope_transport:
 assumes finite: "finite E"
 shows "\<exists>r :: nat \<Rightarrow> nat. inj r \<and>
   (\<forall>ss :: 'a lp_cut_entry list.
     (\<Union>e\<in>set (map (lp_cut_scope_entry r) ss). lp_cut_entry_scopes e) \<inter> E = {})"
proof -
 let ?N = "Suc (Lattices_Big.linorder_class.Max (insert 0 E))"
 let ?r = "\<lambda>m. ?N+m"
 have bound: "m < ?N" if "m\<in>E" for m
 proof -
   have fin: "finite (insert 0 E)" using finite by simp
   have member: "m\<in>insert 0 E" using that by simp
   show ?thesis using Max_ge[OF fin member] by simp
 qed
 have outside: "?r m\<notin>E" for m
   using bound[of "?r m"] by arith
 have injective: "inj ?r" by (simp add: inj_on_def)
 have separated: "(\<Union>e\<in>set (map (lp_cut_scope_entry ?r) ss). lp_cut_entry_scopes e) \<inter> E = {}"
   for ss :: "'a lp_cut_entry list"
   using outside by (auto simp: lp_cut_scope_entry_scopes)
 show ?thesis by (rule exI[of _ ?r]) (use injective separated in blast)
qed

ML \<open>
val checked = [@{thm lpc_no_cut_free_owned}, @{thm lpc_no_owned_source_pending},
 @{thm lpp_builtin_owned_source_pending}, @{thm lpc_no_owned_scope_transport},
 @{thm lpc_owned_answer_admin_pending}, @{thm lpc_fresh_scope_transport}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted owned cut suffix dependency" else ();
\<close>
end
