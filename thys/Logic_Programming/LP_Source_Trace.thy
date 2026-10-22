theory LP_Source_Trace
  imports LP_Source_Loop
begin

text \<open>A finite, matching derivation is uniform in all runtime values.
  It may resolve successful prefixes and cross several clauses. Its final
  selected atom must be an instance of the initial atom; the suffix need
  never succeed. The search may use finite unification, but the theorem makes
  no occurs-check assumption about the runtime relation.\<close>

definition lp_trace_subst where
  "lp_trace_subst bindings x = the_default (Var x) (map_of bindings x)"

fun lp_match_run where
  "lp_match_run P gs [] = Some gs"
| "lp_match_run P gs ((c,bindings)#steps) =
    (if c<length P \<and> gs\<noteq>[] \<and>
        hd gs = lp_atom_subst (fst (P!c)) (lp_trace_subst bindings)
     then lp_match_run P
       (map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs) steps
     else None)"

lemma lp_match_run_sound:
  assumes run: "lp_match_run P gs steps = Some hs"
  shows "(map (\<lambda>a. lp_atom_eval a \<rho>) gs @ tail,
          map (\<lambda>a. lp_atom_eval a \<rho>) hs @ tail) \<in> (lp_ild P)\<^sup>*"
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
  have first: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs @ tail,
      map (\<lambda>a. lp_atom_eval a \<rho>) ?next @ tail) \<in> lp_ild P"
  proof -
    obtain a rest where form: "gs=a#rest" using nonempty by (cases gs) auto
    have match: "lp_iatom_subst (lp_atom_eval a \<rho>) LPIVar =
      lp_atom_eval (fst (P!c)) (\<lambda>x. lp_ieval (lp_trace_subst bindings x) \<rho>)"
      using eq by (simp add: form lp_atom_eval_finite_subst)
    show ?thesis using lp_ild.resolve[OF c match,
      of "map (\<lambda>a. lp_atom_eval a \<rho>) rest @ tail"]
      by (simp add: form lp_atom_eval_finite_subst o_def)
  qed
  show ?case by (rule converse_rtrancl_into_rtrancl[OF first Cons.hyps[OF rest]])
qed

lemma lp_match_run_nonempty_sound:
  assumes run: "lp_match_run P gs steps = Some hs" and nonempty: "steps\<noteq>[]"
  shows "(map (\<lambda>a. lp_atom_eval a \<rho>) gs @ tail,
          map (\<lambda>a. lp_atom_eval a \<rho>) hs @ tail) \<in> (lp_ild P)\<^sup>+"
proof -
  obtain c bindings rest where steps: "steps=(c,bindings)#rest"
    using nonempty by (cases steps) auto
  have c: "c<length P" and nonempty: "gs\<noteq>[]"
    and eq: "hd gs = lp_atom_subst (fst (P!c)) (lp_trace_subst bindings)"
    and run': "lp_match_run P
      (map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs) rest = Some hs"
    using run by (auto simp: steps split: if_splits)
  let ?next = "map (\<lambda>b. lp_atom_subst b (lp_trace_subst bindings)) (snd (P!c)) @ tl gs"
  have first: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs @ tail,
      map (\<lambda>a. lp_atom_eval a \<rho>) ?next @ tail) \<in> lp_ild P"
  proof -
    obtain a rest where form: "gs=a#rest" using nonempty by (cases gs) auto
    have match: "lp_iatom_subst (lp_atom_eval a \<rho>) LPIVar =
      lp_atom_eval (fst (P!c)) (\<lambda>x. lp_ieval (lp_trace_subst bindings x) \<rho>)"
      using eq by (simp add: form lp_atom_eval_finite_subst)
    show ?thesis using lp_ild.resolve[OF c match,
      of "map (\<lambda>a. lp_atom_eval a \<rho>) rest @ tail"]
      by (simp add: form lp_atom_eval_finite_subst o_def)
  qed
  show ?thesis using first lp_match_run_sound[OF run', of \<rho> tail]
    by (rule rtrancl_into_trancl2)
qed

theorem lp_match_trace_loop:
  assumes run: "lp_match_run P [h] steps = Some (b#bs)"
    and progress: "steps\<noteq>[]" and repeat: "b=lp_atom_subst h \<tau>"
  shows "\<not>SN_on (lp_ild P) {[lp_atom_eval h \<rho>]}"
proof
  assume sn: "SN_on (lp_ild P) {[lp_atom_eval h \<rho>]}"
  let ?X = "{gs. \<exists>\<sigma> tail. gs=lp_atom_eval h \<sigma>#tail}"
  have not_sn: "\<not>SN_on ((lp_ild P)\<^sup>+) {[lp_atom_eval h \<rho>]}"
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[lp_atom_eval h \<rho>]\<in>?X" by blast
  next
    fix gs assume "gs\<in>?X"
    then obtain \<sigma> tail where gs: "gs=lp_atom_eval h \<sigma>#tail" by blast
    let ?next = "map (\<lambda>a. lp_atom_eval a \<sigma>) (b#bs) @ tail"
    have path: "(gs,?next)\<in>(lp_ild P)\<^sup>+"
      using lp_match_run_nonempty_sound[OF run progress, of \<sigma> tail] by (simp add: gs)
    have member: "?next\<in>?X" by (auto simp: repeat lp_atom_eval_finite_subst)
    show "\<exists>t\<in>?X. (gs,t)\<in>(lp_ild P)\<^sup>+" using member path by blast
  qed
  show False using not_sn SN_on_trancl[OF sn] by contradiction
qed

end
