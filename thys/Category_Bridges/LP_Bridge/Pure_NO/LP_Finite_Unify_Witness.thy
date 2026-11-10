theory LP_Finite_Unify_Witness
  imports LP_Finite_MGU_Lifting Category_LP_Library.LP_Source_Unify_XML
begin
abbreviation lp_finite_eval where "lp_finite_eval t sigma \<equiv> t\<cdot>sigma"
abbreviation lp_finite_atom_eval where "lp_finite_atom_eval a sigma \<equiv> lp_atom_subst a sigma"

text \<open>These proofs follow the finite substitutions carried by the certificate.
They establish finite all-unifier executions; the separate lifting theorem then
supplies exact most-general executions.\<close>

lemma lp_finite_unify_next_sound:
  assumes checked: "lp_unify_next P gs step=Some hs"
  obtains tail' where
    "(map (\<lambda>a. lp_finite_atom_eval a Var) gs @ tail,
      map (\<lambda>a. lp_finite_atom_eval a Var) hs @ tail')\<in>lp_ld P"
proof -
  obtain c sb rb where step: "step=(c,sb,rb)" by (cases step) auto
  obtain a rest where gs: "gs=a#rest" using checked by (cases gs) (auto simp: step)
  let ?s = "lp_trace_subst sb" let ?r = "lp_trace_subst rb"
  have c: "c<length P" and eq: "lp_atom_subst a ?s=lp_atom_subst (fst (P!c)) ?r"
    and hs: "hs=map (\<lambda>b. lp_atom_subst b ?r) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b ?s) rest"
    using checked by (auto simp: gs step split: if_splits)
  have match: "lp_atom_subst (lp_finite_atom_eval a Var) (\<lambda>x. ?s x) =
    lp_finite_atom_eval (fst (P!c)) (\<lambda>x. ?r x)"
    using arg_cong[OF eq, of "\<lambda>b. lp_finite_atom_eval b Var"]
    by (simp add: lp_atom_subst_comp)
  show thesis
    by (rule that[of "map (\<lambda>b. lp_atom_subst b (\<lambda>x. ?s x)) tail"])
      (use lp_ld.resolve[OF c match, of "map (\<lambda>a. lp_finite_atom_eval a Var) rest @ tail"]
        in \<open>simp add: gs hs map_map o_def lp_atom_subst_comp\<close>)
qed

lemma lp_finite_unify_run_sound:
  assumes run: "lp_unify_run P gs steps=Some hs"
  obtains tail' where
    "(map (\<lambda>a. lp_finite_atom_eval a Var) gs @ tail,
      map (\<lambda>a. lp_finite_atom_eval a Var) hs @ tail')\<in>(lp_ld P)\<^sup>*"
  using run
proof (induct steps arbitrary: gs tail thesis)
  case Nil then show ?case by auto
next
  case (Cons s ss)
  obtain mid where first: "lp_unify_next P gs s=Some mid"
    and rest: "lp_unify_run P mid ss=Some hs"
    using Cons.prems(2) by (auto split: option.splits)
  obtain tail1 where first': "(map (\<lambda>a. lp_finite_atom_eval a Var) gs @ tail,
    map (\<lambda>a. lp_finite_atom_eval a Var) mid @ tail1)\<in>lp_ld P"
    by (rule lp_finite_unify_next_sound[OF first]) blast
  obtain tail2 where rest': "(map (\<lambda>a. lp_finite_atom_eval a Var) mid @ tail1,
    map (\<lambda>a. lp_finite_atom_eval a Var) hs @ tail2)\<in>(lp_ld P)\<^sup>*"
    by (rule Cons.hyps[OF _ rest]) blast
  show ?case by (rule Cons.prems(1)[OF converse_rtrancl_into_rtrancl[OF first' rest']])
qed

lemma lp_finite_unify_run_general_start:
  assumes run: "lp_unify_run P [h] steps=Some hs" and progress: "steps\<noteq>[]"
    and inst: "h=lp_atom_subst b \<tau>"
  obtains tail' where
    "(lp_finite_atom_eval b Var#tail,
      map (\<lambda>a. lp_finite_atom_eval a Var) hs @ tail')\<in>(lp_ld P)\<^sup>+"
proof -
  obtain c sb rb rest where steps: "steps=(c,sb,rb)#rest"
    using progress by (cases steps) auto
  let ?s = "lp_trace_subst sb" let ?r = "lp_trace_subst rb"
  let ?mid = "map (\<lambda>a. lp_atom_subst a ?r) (snd (P!c))"
  have c: "c<length P" and eq: "lp_atom_subst h ?s=lp_atom_subst (fst (P!c)) ?r"
    and rest: "lp_unify_run P ?mid rest=Some hs"
    using run by (auto simp: steps split: if_splits option.splits)
  let ?sigma = "\<lambda>x. \<tau> x\<cdot>?s"
  have match: "lp_atom_subst (lp_finite_atom_eval b Var) ?sigma =
    lp_finite_atom_eval (fst (P!c)) (\<lambda>x. ?r x)"
    using arg_cong[OF eq, of "\<lambda>a. lp_finite_atom_eval a Var"]
    by (simp add: inst lp_atom_subst_comp)
  have first: "(lp_finite_atom_eval b Var#tail,
      map (\<lambda>a. lp_finite_atom_eval a Var) ?mid @ map (\<lambda>a. lp_atom_subst a ?sigma) tail)\<in>lp_ld P"
    using lp_ld.resolve[OF c match, of tail]
    by (simp add: map_map o_def lp_atom_subst_comp)
  obtain tail' where path: "(map (\<lambda>a. lp_finite_atom_eval a Var) ?mid @ map (\<lambda>a. lp_atom_subst a ?sigma) tail,
      map (\<lambda>a. lp_finite_atom_eval a Var) hs @ tail')\<in>(lp_ld P)\<^sup>*"
    by (rule lp_finite_unify_run_sound[OF rest]) blast
  show thesis by (rule that[OF rtrancl_into_trancl2[OF first path]])
qed

theorem lp_finite_unify_cycle:
  assumes run: "lp_unify_run P [h] steps=Some (b#bs)" and progress: "steps\<noteq>[]"
    and repeat: "h=lp_atom_subst b \<tau>"
  shows "\<not>SN_on (lp_ld P) {lp_finite_atom_eval h Var#tail}"
proof -
  let ?X = "{gs. \<exists>tail. gs=lp_finite_atom_eval b Var#tail}"
  have bad: "\<And>tail. \<not>SN_on ((lp_ld P)\<^sup>+) {lp_finite_atom_eval b Var#tail}"
  proof -
    fix tail show "\<not>SN_on ((lp_ld P)\<^sup>+) {lp_finite_atom_eval b Var#tail}"
    proof (rule lp_serial_not_SN[where X="?X"])
      show "lp_finite_atom_eval b Var#tail\<in>?X" by blast
    next
      fix gs assume "gs\<in>?X"
      then obtain tail where gs: "gs=lp_finite_atom_eval b Var#tail" by blast
      obtain tail' where step: "(gs,map (\<lambda>a. lp_finite_atom_eval a Var) (b#bs) @ tail')\<in>(lp_ld P)\<^sup>+"
        unfolding gs by (rule lp_finite_unify_run_general_start[OF run progress repeat]) blast
      show "\<exists>t\<in>?X. (gs,t)\<in>(lp_ld P)\<^sup>+" using step by auto
    qed
  qed
  obtain tail' where path: "(lp_finite_atom_eval h Var#tail,
    map (\<lambda>a. lp_finite_atom_eval a Var) (b#bs) @ tail')\<in>(lp_ld P)\<^sup>*"
    using lp_finite_unify_run_sound[OF run, of tail] by auto
  show ?thesis
  proof
    assume sn: "SN_on (lp_ld P) {lp_finite_atom_eval h Var#tail}"
    have end_sn: "SN_on (lp_ld P) {map (\<lambda>a. lp_finite_atom_eval a Var) (b#bs) @ tail'}"
      using lp_SN_reachable[OF sn path] .
    show False using bad[of "map (\<lambda>a. lp_finite_atom_eval a Var) bs @ tail'"]
      SN_on_trancl[OF end_sn] by simp
  qed
qed
theorem lp_source_unify_check_finite_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_source_unify_check P q n positions a0 entry_steps steps bindings"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  obtain h tail b bs where prefix: "lp_unify_run P [a0] entry_steps=Some (h#tail)"
    and run: "lp_unify_run P [h] steps=Some (b#bs)" and progress: "steps\<noteq>[]"
    and repeat: "h=lp_atom_subst b (lp_trace_subst bindings)"
    and query: "fst a0=q" "length (snd a0)=n"
      "\<forall>i\<in>set positions. i<n \<and> ground (snd a0!i)"
    using ok unfolding lp_source_unify_check_def
    by (auto simp: list_all_iff split: option.splits list.splits)
  obtain tail' where path: "([lp_finite_atom_eval a0 Var],
    map (\<lambda>a. lp_finite_atom_eval a Var) (h#tail) @ tail')\<in>(lp_ld P)\<^sup>*"
    using lp_finite_unify_run_sound[OF prefix, of "[]"] by auto
  have bad: "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval a0 Var]}"
    using lp_finite_unify_cycle[OF run progress repeat, of "map (\<lambda>a. lp_finite_atom_eval a Var) tail @ tail'"]
      lp_SN_reachable[OF _ path] by auto
  show ?thesis by (rule exI[of _ "snd a0"])
    (use query bad in \<open>simp add: lp_atom_subst_def\<close>)
qed

end
