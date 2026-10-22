theory LP_Source_Unify
  imports LP_Source_Trace
begin

lemma lp_SN_reachable:
  assumes sn: "SN_on R {s}" and path: "(s,t)\<in>R\<^sup>*"
  shows "SN_on R {t}"
  by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use path in auto)

text \<open>Explicit finite unification derivations, including a finite entry
  path. Only the indicated query arguments must be ground. A cycle closes
  when its final selected atom subsumes its initial atom. Substitutions are
  checked independently of discovery; no transformed-TRS NO is used.\<close>

fun lp_unify_next where
  "lp_unify_next P gs (c, sb, rb) =
    (if c<length P \<and> gs\<noteq>[] \<and>
      lp_atom_subst (hd gs) (lp_trace_subst sb) =
      lp_atom_subst (fst (P!c)) (lp_trace_subst rb)
     then Some (map (\<lambda>b. lp_atom_subst b (lp_trace_subst rb)) (snd (P!c)) @
       map (\<lambda>b. lp_atom_subst b (lp_trace_subst sb)) (tl gs))
     else None)"

fun lp_unify_run where
  "lp_unify_run P gs [] = Some gs"
| "lp_unify_run P gs (s#ss) =
    (case lp_unify_next P gs s of None \<Rightarrow> None
      | Some hs \<Rightarrow> lp_unify_run P hs ss)"

lemma lp_unify_next_sound:
  assumes checked: "lp_unify_next P gs step=Some hs"
  obtains tail' where
    "(map (\<lambda>a. lp_atom_eval a LPIVar) gs @ tail,
      map (\<lambda>a. lp_atom_eval a LPIVar) hs @ tail')\<in>lp_ild P"
proof -
  obtain c sb rb where step: "step=(c,sb,rb)" by (cases step) auto
  obtain a rest where gs: "gs=a#rest" using checked by (cases gs) (auto simp: step)
  let ?s = "lp_trace_subst sb" let ?r = "lp_trace_subst rb"
  have c: "c<length P" and eq: "lp_atom_subst a ?s=lp_atom_subst (fst (P!c)) ?r"
    and hs: "hs=map (\<lambda>b. lp_atom_subst b ?r) (snd (P!c)) @ map (\<lambda>b. lp_atom_subst b ?s) rest"
    using checked by (auto simp: gs step split: if_splits)
  have match: "lp_iatom_subst (lp_atom_eval a LPIVar) (\<lambda>x. lp_ieval (?s x) LPIVar) =
    lp_atom_eval (fst (P!c)) (\<lambda>x. lp_ieval (?r x) LPIVar)"
    using arg_cong[OF eq, of "\<lambda>b. lp_atom_eval b LPIVar"]
    by (simp add: lp_atom_eval_finite_subst)
  show thesis
    by (rule that[of "map (\<lambda>b. lp_iatom_subst b (\<lambda>x. lp_ieval (?s x) LPIVar)) tail"])
      (use lp_ild.resolve[OF c match, of "map (\<lambda>a. lp_atom_eval a LPIVar) rest @ tail"]
        in \<open>simp add: gs hs map_map o_def lp_atom_eval_finite_subst\<close>)
qed

lemma lp_unify_run_sound:
  assumes run: "lp_unify_run P gs steps=Some hs"
  obtains tail' where
    "(map (\<lambda>a. lp_atom_eval a LPIVar) gs @ tail,
      map (\<lambda>a. lp_atom_eval a LPIVar) hs @ tail')\<in>(lp_ild P)\<^sup>*"
  using run
proof (induct steps arbitrary: gs tail thesis)
  case Nil then show ?case by auto
next
  case (Cons s ss)
  obtain mid where first: "lp_unify_next P gs s=Some mid"
    and rest: "lp_unify_run P mid ss=Some hs"
    using Cons.prems(2) by (auto split: option.splits)
  obtain tail1 where first': "(map (\<lambda>a. lp_atom_eval a LPIVar) gs @ tail,
    map (\<lambda>a. lp_atom_eval a LPIVar) mid @ tail1)\<in>lp_ild P"
    by (rule lp_unify_next_sound[OF first]) blast
  obtain tail2 where rest': "(map (\<lambda>a. lp_atom_eval a LPIVar) mid @ tail1,
    map (\<lambda>a. lp_atom_eval a LPIVar) hs @ tail2)\<in>(lp_ild P)\<^sup>*"
    by (rule Cons.hyps[OF _ rest]) blast
  show ?case by (rule Cons.prems(1)[OF converse_rtrancl_into_rtrancl[OF first' rest']])
qed

lemma lp_unify_run_general_start:
  assumes run: "lp_unify_run P [h] steps=Some hs" and progress: "steps\<noteq>[]"
    and inst: "h=lp_atom_subst b \<tau>"
  obtains tail' where
    "(lp_atom_eval b LPIVar#tail,
      map (\<lambda>a. lp_atom_eval a LPIVar) hs @ tail')\<in>(lp_ild P)\<^sup>+"
proof -
  obtain c sb rb rest where steps: "steps=(c,sb,rb)#rest"
    using progress by (cases steps) auto
  let ?s = "lp_trace_subst sb" let ?r = "lp_trace_subst rb"
  let ?mid = "map (\<lambda>a. lp_atom_subst a ?r) (snd (P!c))"
  have c: "c<length P" and eq: "lp_atom_subst h ?s=lp_atom_subst (fst (P!c)) ?r"
    and rest: "lp_unify_run P ?mid rest=Some hs"
    using run by (auto simp: steps split: if_splits option.splits)
  let ?sigma = "\<lambda>x. lp_ieval (\<tau> x\<cdot>?s) LPIVar"
  have match: "lp_iatom_subst (lp_atom_eval b LPIVar) ?sigma =
    lp_atom_eval (fst (P!c)) (\<lambda>x. lp_ieval (?r x) LPIVar)"
    using arg_cong[OF eq, of "\<lambda>a. lp_atom_eval a LPIVar"]
    by (simp add: inst lp_atom_eval_finite_subst)
  have first: "(lp_atom_eval b LPIVar#tail,
      map (\<lambda>a. lp_atom_eval a LPIVar) ?mid @ map (\<lambda>a. lp_iatom_subst a ?sigma) tail)\<in>lp_ild P"
    using lp_ild.resolve[OF c match, of tail]
    by (simp add: map_map o_def lp_atom_eval_finite_subst)
  obtain tail' where path: "(map (\<lambda>a. lp_atom_eval a LPIVar) ?mid @ map (\<lambda>a. lp_iatom_subst a ?sigma) tail,
      map (\<lambda>a. lp_atom_eval a LPIVar) hs @ tail')\<in>(lp_ild P)\<^sup>*"
    by (rule lp_unify_run_sound[OF rest]) blast
  show thesis by (rule that[OF rtrancl_into_trancl2[OF first path]])
qed

theorem lp_unify_cycle:
  assumes run: "lp_unify_run P [h] steps=Some (b#bs)" and progress: "steps\<noteq>[]"
    and repeat: "h=lp_atom_subst b \<tau>"
  shows "\<not>SN_on (lp_ild P) {lp_atom_eval h LPIVar#tail}"
proof -
  let ?X = "{gs. \<exists>tail. gs=lp_atom_eval b LPIVar#tail}"
  have bad: "\<And>tail. \<not>SN_on ((lp_ild P)\<^sup>+) {lp_atom_eval b LPIVar#tail}"
  proof -
    fix tail show "\<not>SN_on ((lp_ild P)\<^sup>+) {lp_atom_eval b LPIVar#tail}"
    proof (rule lp_serial_not_SN[where X="?X"])
      show "lp_atom_eval b LPIVar#tail\<in>?X" by blast
    next
      fix gs assume "gs\<in>?X"
      then obtain tail where gs: "gs=lp_atom_eval b LPIVar#tail" by blast
      obtain tail' where step: "(gs,map (\<lambda>a. lp_atom_eval a LPIVar) (b#bs) @ tail')\<in>(lp_ild P)\<^sup>+"
        unfolding gs by (rule lp_unify_run_general_start[OF run progress repeat]) blast
      show "\<exists>t\<in>?X. (gs,t)\<in>(lp_ild P)\<^sup>+" using step by auto
    qed
  qed
  obtain tail' where path: "(lp_atom_eval h LPIVar#tail,
    map (\<lambda>a. lp_atom_eval a LPIVar) (b#bs) @ tail')\<in>(lp_ild P)\<^sup>*"
    using lp_unify_run_sound[OF run, of tail] by auto
  show ?thesis
  proof
    assume sn: "SN_on (lp_ild P) {lp_atom_eval h LPIVar#tail}"
    have end_sn: "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a LPIVar) (b#bs) @ tail'}"
      using lp_SN_reachable[OF sn path] .
    show False using bad[of "map (\<lambda>a. lp_atom_eval a LPIVar) bs @ tail'"]
      SN_on_trancl[OF end_sn] by simp
  qed
qed

definition lp_source_unify_check where
  "lp_source_unify_check P q n positions a0 entry_steps steps bindings =
    (fst a0=q \<and> length (snd a0)=n \<and>
     list_all (\<lambda>i. i<n \<and> ground (snd a0!i)) positions \<and>
     steps\<noteq>[] \<and>
     (case lp_unify_run P [a0] entry_steps of Some (h#tail) \<Rightarrow>
       (case lp_unify_run P [h] steps of Some (b#bs) \<Rightarrow>
         h=lp_atom_subst b (lp_trace_subst bindings) | _ \<Rightarrow> False)
      | _ \<Rightarrow> False))"

theorem lp_source_unify_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_source_unify_check P q n positions a0 entry_steps steps bindings"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  obtain h tail b bs where prefix: "lp_unify_run P [a0] entry_steps=Some (h#tail)"
    and run: "lp_unify_run P [h] steps=Some (b#bs)" and progress: "steps\<noteq>[]"
    and repeat: "h=lp_atom_subst b (lp_trace_subst bindings)"
    and query: "fst a0=q" "length (snd a0)=n"
      "\<forall>i\<in>set positions. i<n \<and> ground (snd a0!i)"
    using ok unfolding lp_source_unify_check_def
    by (auto simp: list_all_iff split: option.splits list.splits)
  obtain tail' where path: "([lp_atom_eval a0 LPIVar],
    map (\<lambda>a. lp_atom_eval a LPIVar) (h#tail) @ tail')\<in>(lp_ild P)\<^sup>*"
    using lp_unify_run_sound[OF prefix, of "[]"] by auto
  have bad: "\<not>SN_on (lp_ild P) {[lp_atom_eval a0 LPIVar]}"
    using lp_unify_cycle[OF run progress repeat, of "map (\<lambda>a. lp_atom_eval a LPIVar) tail @ tail'"]
      lp_SN_reachable[OF _ path] by auto
  show ?thesis by (rule exI[of _ "snd a0"])
    (use query bad in \<open>simp add: lp_atom_eval_def\<close>)
qed

end
