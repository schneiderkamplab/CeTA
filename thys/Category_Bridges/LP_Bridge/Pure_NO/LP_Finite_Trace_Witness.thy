theory LP_Finite_Trace_Witness
  imports LP_Finite_Unify_Witness
begin

lemma lp_finite_match_run_sound:
  assumes run: "lp_match_run P gs steps = Some hs"
  shows "(map (\<lambda>a. lp_finite_atom_eval a \<rho>) gs @ tail,
          map (\<lambda>a. lp_finite_atom_eval a \<rho>) hs @ tail) \<in> (lp_ld P)\<^sup>*"
  using run
proof (induct steps arbitrary: gs)
  case Nil then show ?case by simp
next
  case (Cons step steps)
  obtain c bindings where step: "step=(c,bindings)" by (cases step) auto
  have c: "c<length P" and nonempty: "gs\<noteq>[]"
    and eq: "hd gs = lp_atom_subst (fst (P!c)) (lp_trace_subst bindings)"
    and rest: "lp_match_run P
      (map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs) steps = Some hs"
    using Cons.prems by (auto simp: step split: if_splits)
  let ?next = "map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs"
  have first: "(map (\<lambda>a. lp_finite_atom_eval a \<rho>) gs @ tail,
      map (\<lambda>a. lp_finite_atom_eval a \<rho>) ?next @ tail) \<in> lp_ld P"
  proof -
    obtain a rest where form: "gs=a#rest" using nonempty by (cases gs) auto
    have match: "lp_atom_subst (lp_finite_atom_eval a \<rho>) Var =
      lp_finite_atom_eval (fst (P!c)) (\<lambda>x. lp_finite_eval (lp_trace_subst bindings x) \<rho>)"
      using eq by (simp add: form lp_atom_subst_comp)
    show ?thesis using lp_ld.resolve[OF c match,
      of "map (\<lambda>a. lp_finite_atom_eval a \<rho>) rest @ tail"]
      by (simp add: form lp_atom_subst_comp o_def)
  qed
  show ?case by (rule converse_rtrancl_into_rtrancl[OF first Cons.hyps[OF rest]])
qed

lemma lp_finite_match_run_nonempty_sound:
  assumes run: "lp_match_run P gs steps = Some hs" and nonempty: "steps\<noteq>[]"
  shows "(map (\<lambda>a. lp_finite_atom_eval a \<rho>) gs @ tail,
          map (\<lambda>a. lp_finite_atom_eval a \<rho>) hs @ tail) \<in> (lp_ld P)\<^sup>+"
proof -
  obtain c bindings rest where steps: "steps=(c,bindings)#rest"
    using nonempty by (cases steps) auto
  have c: "c<length P" and nonempty: "gs\<noteq>[]"
    and eq: "hd gs = lp_atom_subst (fst (P!c)) (lp_trace_subst bindings)"
    and run': "lp_match_run P
      (map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs) rest = Some hs"
    using run by (auto simp: steps split: if_splits)
  let ?next = "map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs"
  have first: "(map (\<lambda>a. lp_finite_atom_eval a \<rho>) gs @ tail,
      map (\<lambda>a. lp_finite_atom_eval a \<rho>) ?next @ tail) \<in> lp_ld P"
  proof -
    obtain a rest where form: "gs=a#rest" using nonempty by (cases gs) auto
    have match: "lp_atom_subst (lp_finite_atom_eval a \<rho>) Var =
      lp_finite_atom_eval (fst (P!c)) (\<lambda>x. lp_finite_eval (lp_trace_subst bindings x) \<rho>)"
      using eq by (simp add: form lp_atom_subst_comp)
    show ?thesis using lp_ld.resolve[OF c match,
      of "map (\<lambda>a. lp_finite_atom_eval a \<rho>) rest @ tail"]
      by (simp add: form lp_atom_subst_comp o_def)
  qed
  show ?thesis using first lp_finite_match_run_sound[OF run', of \<rho> tail]
    by (rule rtrancl_into_trancl2)
qed

theorem lp_finite_match_trace_loop:
  fixes P :: "('f,'v) lp_clause list" and \<rho> :: "'v \<Rightarrow> ('f,'v) term"
  assumes run: "lp_match_run P [h] steps = Some (b#bs)"
    and progress: "steps\<noteq>[]" and repeat: "b=lp_atom_subst h \<tau>"
  shows "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval h \<rho>]}"
proof
  assume sn: "SN_on (lp_ld P) {[lp_finite_atom_eval h \<rho>]}"
  let ?X = "{gs :: ('f,'v) lp_atom list. \<exists>\<sigma> tail. gs=lp_finite_atom_eval h \<sigma>#tail}"
  have not_sn: "\<not>SN_on ((lp_ld P)\<^sup>+) {[lp_finite_atom_eval h \<rho>]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[lp_finite_atom_eval h \<rho>]\<in>?X" by blast
  next
    fix gs assume "gs\<in>?X"
    then obtain \<sigma> tail where gs: "gs=lp_finite_atom_eval h \<sigma>#tail" by blast
    let ?next = "map (\<lambda>a. lp_finite_atom_eval a \<sigma>) (b#bs) @ tail"
    have path: "(gs,?next)\<in>(lp_ld P)\<^sup>+"
      using lp_finite_match_run_nonempty_sound[OF run progress, of \<sigma> tail] by (simp add: gs)
    have member: "?next\<in>?X" by (auto simp: repeat lp_atom_subst_comp)
    show "\<exists>t\<in>?X. (gs,t)\<in>(lp_ld P)\<^sup>+" using member path by blast
  qed
  show False using not_sn SN_on_trancl[OF sn] by contradiction
qed

theorem lp_source_trace_check_finite_sound:
  fixes P :: "('f,'v) lp_clause list" and seed :: 'f
  assumes ok: "lp_source_trace_check P q n positions h steps bindings"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> list_all ground ts \<and>
    \<not>SN_on (lp_ld P) {[(q,ts)]}"
proof -
  obtain b bs where run: "lp_match_run P [h] steps=Some (b#bs)"
    and progress: "steps\<noteq>[]" and repeat: "b=lp_atom_subst h (lp_trace_subst bindings)"
    and pred: "fst h=q" and len: "length (snd h)=n"
    using ok unfolding lp_source_trace_check_def by (auto split: option.splits list.splits)
  let ?rho = "\<lambda>x. Fun seed [] :: ('f,'v) term"
  let ?ts = "map (\<lambda>t. t\<cdot>?rho) (snd h)"
  have bad: "\<not>SN_on (lp_ld P) {[lp_atom_subst h ?rho]}"
    by (rule lp_finite_match_trace_loop[OF run progress repeat])
  have ground: "\<And>t :: ('f,'v) term. ground (t\<cdot>?rho)"
    by (simp add: ground_vars_term_empty vars_term_subst)
  show ?thesis by (rule exI[of _ ?ts])
    (use bad ground len pred in \<open>auto simp: lp_atom_subst_def list_all_iff\<close>)
qed
end
