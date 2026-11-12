theory LP_Prolog_NO_Scope_Permutation
 imports LP_Cut_NO_Finite_Attachment LP_Source_Owned_Pending LP_Prolog_NO_Pumping
begin

text \<open>A finite trace namespace is exchanged with fresh scopes. Unlike a
one-way shift, the permutation has an inverse on every caller scope.\<close>

lemma lpc_no_fresh_scope_permutation:
 assumes finS: "finite (S :: nat set)" and finE: "finite E"
 shows "\<exists>r. (\<forall>x. r (r x) = x) \<and> bij r \<and> r ` S \<inter> E = {}"
proof -
 have fin: "finite (S \<union> E)" using finS finE by simp
 obtain q :: "nat \<Rightarrow> nat" where inj: "inj q" and fresh:
  "\<forall>ss :: unit lp_cut_entry list.
    (\<Union>e\<in>set (map (lp_cut_scope_entry q) ss). lp_cut_entry_scopes e) \<inter> (S \<union> E) = {}"
  using lpc_fresh_scope_transport[OF fin] by (elim exE conjE) assumption
 have outside: "q m \<notin> S \<union> E" for m
  using fresh[rule_format, of "[LPCBarrier m]"] by simp
 have injective: "inj_on q S" using inj by (auto simp: inj_on_def)
 have disjoint: "S \<inter> q ` S = {}" using outside by auto
 let ?r = "lpc_exchange_support S q"
 have inverse: "\<forall>x. ?r (?r x) = x"
  using lpc_exchange_support_involution[OF injective disjoint] by simp
 have bijective: "bij ?r" by (rule lpc_exchange_support_bij[OF injective disjoint])
 have separated: "?r ` S \<inter> E = {}"
  using outside by (auto simp: lpc_exchange_support_def)
 show ?thesis
  by (rule exI[of _ ?r], intro conjI; (rule inverse | rule bijective | rule separated))
qed

lemma lpp_no_source_scope_progress:
 assumes path: "(s,t)\<in>(lpp_builtin_source P U)\<^sup>+"
   and injective: "inj r" and program: "lp_cut_source_program P"
 shows "(map (lp_cut_scope_entry r) s,map (lp_cut_scope_entry r) t)
   \<in>(lpp_builtin_source P U)\<^sup>+"
 using path
 by (induct rule: trancl_induct)
    (meson lpp_builtin_source_scope[OF _ injective program] r_into_trancl trancl_trans)+


lemma lpc_no_scope_preimage_separate:
 assumes inverse: "\<forall>x. r (r x) = x" and separated: "r ` S \<inter> E = {}"
 shows "S \<inter> r ` E = {}"
proof (rule ccontr)
 assume "S \<inter> r ` E \<noteq> {}"
 then obtain x y where facts: "x\<in>S" "y\<in>E" "x = r y" by auto
 have "r x = y" using inverse facts(3) by simp
 with facts separated show False by auto
qed

lemma lpc_no_scope_restore_goals:
 assumes inverse: "\<forall>x. r (r x) = x"
 shows "map (lp_cut_scope_goal r) (map (lp_cut_scope_goal r) gs) = gs"
proof -
 have twice: "lp_cut_scope_goal r (lp_cut_scope_goal r g) = g" for g
  by (cases g) (simp_all add: inverse)
 show ?thesis by (simp add: map_map o_def twice)
qed

lemma lpc_no_scope_restore_state:
 assumes inverse: "\<forall>x. r (r x) = x"
 shows "map (lp_cut_scope_entry r) (map (lp_cut_scope_entry r) ss) = ss"
proof -
 have twice: "lp_cut_scope_entry r (lp_cut_scope_entry r e) = e" for e
  by (cases e) (simp_all only: lp_cut_scope_entry.simps lpc_no_scope_restore_goals[OF inverse] inverse)
 show ?thesis by (simp add: map_map o_def twice)
qed

ML \<open>
val checked = [@{thm lpc_no_fresh_scope_permutation}, @{thm lpp_no_source_scope_progress},
 @{thm lpc_no_scope_preimage_separate}, @{thm lpc_no_scope_restore_goals},
 @{thm lpc_no_scope_restore_state}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scope permutation" else ();
\<close>
end
