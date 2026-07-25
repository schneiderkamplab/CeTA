(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Matchbounds_Impl 
  imports
    TA.Tree_Automata_Impl
    Raise_Consistency
    First_Order_Rewriting.Trs_Impl
    TRS.Signature_Extension
    Framework.QDP_Framework_Impl
    Rewriting
    Right_Forward_Closures.Right_Forward_Closure
    Auxx.Multiset_Code
    Auxx.Map_Choice
    "HOL-Library.Mapping" 
begin

lemma rm_\<alpha>_to_lookup: "rm.\<alpha> = RBT.lookup" 
  unfolding icf_rec_unf ..

(* notation from Autoref clashes with TA_rule *)
no_notation Relators.fun_rel_syn (infixr "\<rightarrow>" 60)

lemma [code]:
  "Matchbounds.roof (l, r) = (
    let xs = vars_term_list r in (\<lambda>t.
      let xt = vars_term t in
      (\<forall>x\<in>set xs. x \<in> xt)))"
  unfolding Let_def roof.simps by (rule ext, simp) blast

definition ta_bounded :: "('q, 'f \<times> nat) ta \<Rightarrow> nat \<Rightarrow> bool" where
  "ta_bounded TA c \<equiv> \<forall> f n. (f,n) \<in> ta_syms TA \<longrightarrow> height f \<le> c"

context
  fixes R :: "('f \<times> nat, 'v) trs"
    and TA :: "('q, 'f \<times> nat) ta"
    and L :: "('f, 'v) terms"
    and rel :: "'q rel"
    and c :: nat
  assumes choice: "left_linear_trs R \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel R"
    and coh: "state_coherent TA rel"
    and incl: "(lift_term 0) ` L \<subseteq> ta_lang TA" 
    and tab: "ta_bounded TA c"
begin
lemma raise_step_boundedI: assumes var_cond: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  shows "raise_step_bounded c R L"
proof -
  let ?ta_lang = "ta_lang :: ('q, 'f \<times> nat) ta \<Rightarrow> ('f \<times> nat, 'v) term set"
  let ?choice = "left_linear_trs R"
  define step where "step = (if ?choice then rstep R else raise_step R)"
  define G where "G = (\<Union>(funas_term ` ?ta_lang TA))"
  from ta_syms_lang[of _ TA] have sub: "\<Union>(funas_term ` (ta_lang TA)) \<subseteq> ta_syms TA" by auto
  from finite_subset[OF this finite_ta_syms[OF fin]] have fin: "finite G" unfolding G_def .
  note raise = state_raise_compatible[OF _ coh _ compat var_cond subset_refl]
  note ll = state_compatible[OF compat coh disjI1 var_cond subset_refl]
  have G: "\<Union>(funas_term ` {t. \<exists> s . s \<in> lift_term 0 ` L \<and> (s,t) \<in> step^*}) \<subseteq> G" 
    using choice incl raise ll unfolding G_def step_def
    by (cases ?choice, force+)
  from finite_list[OF fin] obtain Gl where fin: "G = set Gl" by auto
  let ?h = "(\<lambda>(f,n). height f)"
  {
    fix s t f n
    assume "s \<in> lift_term 0 ` L" "(s,t) \<in> step^*" "(f,n) \<in> funas_term t"
    then have "(f,n) \<in> funas_term t" and "funas_term t \<subseteq> G" using G unfolding fin by auto
    from this sub have "(f,n) \<in> ta_syms TA" unfolding G_def by auto
    with tab[unfolded ta_bounded_def]
    have "height f \<le> c" by blast
  } note bound = this
  show "raise_step_bounded c R L"
  proof (cases ?choice)
    case False
    with bound show ?thesis
      unfolding bounded_defs step_def by auto
  next
    case True
    with bound show ?thesis
      by (intro rstep_bounded_left_linear_imp_raise_bounded[OF _ True],
        unfold bounded_defs step_def, auto)
  qed
qed


lemma e_bounds:
  assumes SN: "locally_terminating (cover e Strict_TRS RR \<union> Matchbounds.raise)"
    and F: "finite F"
    and RR: "finite RR"
    and R: "R = cover e Strict_TRS RR"
    and var_cond: "\<And> l r. (l,r) \<in> RR \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and L: "\<Union>(funas_term ` L) \<subseteq> F"
  shows "SN_on (rstep RR) L"
proof -
  from raise_step_boundedI[unfolded R, OF cover_var_condition[OF var_cond]] 
  have "e_raise_bounded e c RR L" unfolding e_raise_bounded_def .
  from e_raise_bounded[OF var_cond SN RR F L this] 
  show "SN_on (rstep RR) L" .
qed
end

definition cover_bound where 
  "cover_bound c e ee R \<equiv> {(l,r). (l,r) \<in> cover e ee R \<and> (\<forall> f n. (f,n) \<in> funas_term l \<longrightarrow> height f \<le> c)}"

lemma ta_contains_ground_terms_of: assumes "ta_contains F H TA qfin"
  shows "ground_terms_of F H \<subseteq> ta_lang TA"
  using ta_contains_both[OF assms] unfolding ground_terms_of_def by auto

context
  fixes TA :: "('q,'f \<times> nat)ta"
  and qfin :: "'q set"
  and c :: nat
  and G H :: "'f sig"
  and rel :: "'q rel"
  assumes fin: "finite (ta_rules TA)"
  and coh: "state_coherent TA rel"
  and finG: "finite G" and finH: "finite H"
  and contain: "ta_contains ((\<lambda>(f,n). (lift 0 f,n)) ` G) ((\<lambda>(f,n). (lift 0 f,n)) ` H) TA qfin" 
  and qfin_final: "qfin \<subseteq> ta_final TA"
  and qfin: "\<exists> q \<in> qfin. q \<in> ta_rhs_states TA"
  and tab: "ta_bounded TA c"
  and inf: "infinite (UNIV :: 'f set)"
begin
lemma create_constant_in_ta_generic: fixes R :: "('f,'v)rules"
  assumes 
      choice: "left_linear_trs (set R) \<or> ta_det TA \<and> state_raise_consistent TA rel"
  shows "\<exists> q const F F' TA'. q \<in> qfin \<and> G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F' \<and>
       (\<forall> e ee S. S \<subseteq> set R \<longrightarrow>  state_compatible TA rel (cover_bound c e ee S) \<longrightarrow>
       state_compatible TA' rel (cover e ee S)) 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)    
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
proof -
  let ?lz = "(\<lambda>(f,n). (lift 0 f,n))"
  from qfin obtain q where q: "q \<in> qfin \<and> q \<in> ta_rhs_states TA" by auto
  define FF where "FF = (fst ` r_sym ` ta_rules TA \<union> funas_trs (set R))"
  from finite_set[of "funas_trs_list R"] have finR: "finite (funas_trs (set R))" by simp
  from finite_list[OF finG] obtain G' where G': "set G' = G" by auto
  from finite_list[OF finH] obtain H' where H': "set H' = H" by auto
  have "finite (fst ` r_sym ` ta_rules TA)" using fin by auto
  then have "finite (fst ` FF)" using finG finH finR FF_def by auto
  from ex_new_if_finite[OF inf this] obtain const where nconst: "const \<notin> (fst ` FF)" by auto
  then have "(const,0) \<notin> FF" by force
  then have constR: "(const,0) \<notin> funas_trs (set R)" unfolding FF_def by auto
  let ?TA = "\<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA  \<rparr>"
  obtain TA' where TA': "TA' = ?TA" by auto
  let ?F = "(const,0) # G'"
  let ?F' = "(const,0) # H'"
  obtain F where F: "F = ?F" by simp
  obtain F' where F': "F' = ?F'" by simp
  have const: "(const,0) \<in> set F" by (simp add: F)
  have main: "(\<forall> e ee S. S \<subseteq> set R \<longrightarrow> state_compatible TA rel (cover_bound c e ee S) \<longrightarrow>
       state_compatible TA' rel (cover e ee S)) 
    \<and> ta_contains (?lz ` set F) (?lz ` set F') TA' qfin 
    \<and> state_coherent TA' rel
    \<and> ta_bounded TA' c
    \<and> (left_linear_trs (set R) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)
    " (is "?comp \<and> ?cont \<and> ?coh \<and> ?tab \<and> ?choice")
  proof - 
    note coh = coh[unfolded state_coherent_def]
    from TA' coh have coh1: "rel `` ta_final TA' \<subseteq> ta_final TA'" by auto
    have ?choice
    proof (cases "left_linear_trs (set R)")
      case False      
      with choice have det: "ta_det TA" and raise: "state_raise_consistent TA rel" by auto
      {
        fix qs q' h
        assume "((const,h) qs \<rightarrow> q') \<in> ta_rules TA"
        then have "((const,h),length qs) \<in> r_sym ` ta_rules TA" by force
        then have "\<And> f. f (((const,h),length qs)) \<in> f ` (r_sym ` ta_rules TA)" by auto
        from this[of "fst o fst"] have "const \<in> fst ` FF" unfolding FF_def by auto
        with nconst have False by auto
      } note no_const = this        
      from raise have raise: "state_raise_consistent TA' rel" using no_const unfolding TA'
        state_raise_consistent_def by auto blast
      from det no_const have det: "ta_det TA'" unfolding ta_det_def TA' by auto
      from raise det show ?thesis by auto
    qed auto
    have ?coh unfolding state_coherent_def
    proof (rule conjI, rule conjI[OF coh1], intro allI impI)
      fix f qs q i qi
      assume rule: "(f qs \<rightarrow> q) \<in> ta_rules TA'" and ass: "i < length qs" "(qs ! i, qi) \<in> rel" 
      from rule[unfolded TA'] ass have "(f qs \<rightarrow> q) \<in> ta_rules TA" by auto
      from coh[THEN conjunct1, THEN conjunct2, rule_format, OF this ass]
      show "\<exists>q'. (f qs[i := qi] \<rightarrow> q') \<in> ta_rules TA' \<and> (q, q') \<in> rel" unfolding TA' by auto
    next
      show "rel\<inverse> O ta_eps TA' \<subseteq> (ta_eps TA')\<^sup>* O rel\<inverse>" using coh TA' by auto
    qed
    note d = ta_contains_def
    {
      fix G H Q
      assume contain: "ta_contains_aux (?lz ` G) qfin TA Q" and H: "H = insert (const,0) G" and Q: "qfin \<subseteq> Q"
      note d = ta_contains_aux_def
      {
        fix f n 
        assume fn: "(f,n) \<in> ?lz ` H"
        then have "\<forall> qs'. length qs' = n \<and> set qs' \<subseteq> qfin \<longrightarrow> (\<exists> q q'. (f qs' \<rightarrow> q) \<in> ta_rules ?TA \<and> q' \<in> Q \<and> (q,q') \<in> (ta_eps ?TA)^* )"
        proof (cases "(f,n) = ((const,0),0)")
          case True
          then show ?thesis using q Q by auto
        next
          case False
          with fn have fn: "(f,n) \<in> ?lz ` G" unfolding H by auto
          then have fn: "(f,n) \<in> ?lz ` G" by auto
          then obtain g where f: "f = (g,0)" and g: "(g,n) \<in> G" by auto
          show ?thesis
          proof (intro allI impI)
            fix qs'
            assume len: "length qs' = n \<and> set qs' \<subseteq> qfin"
            from contain[unfolded d, simplified, rule_format, of g 0 qs'] g len
            obtain q q' where "(g, 0) qs' \<rightarrow> q \<in> ta_rules TA \<and> q' \<in> Q \<and> (q, q') \<in> (ta_eps TA)\<^sup>*" by force
            then show "\<exists> q q'. (f qs' \<rightarrow> q) \<in> ta_rules ?TA \<and> q' \<in> Q \<and> (q,q') \<in> (ta_eps ?TA)^*"
              unfolding f by auto
          qed
        qed
      }
      then have "ta_contains_aux (?lz ` H) qfin ?TA Q" unfolding d ta.simps by blast
    } note convert = this
    from contain[unfolded d]
    have aux: "ta_contains_aux (?lz ` G) qfin TA qfin"
         "ta_contains_aux (?lz ` H) qfin TA (ta_final TA)" by auto
    have fin: "ta_final ?TA = ta_final TA" by simp
    have "ta_contains_aux (?lz ` set F) qfin ?TA qfin"
      by (rule convert[OF aux(1)], insert G' F, auto)
    moreover have "ta_contains_aux (?lz ` set F') qfin ?TA (ta_final ?TA)" unfolding fin
      by (rule convert[OF aux(2)], insert qfin_final H' F', auto)
    ultimately have cont: "ta_contains (?lz ` set F) (?lz ` set F') ?TA qfin" unfolding d
      unfolding ta_contains_def by auto
    have ?tab using tab unfolding TA' ta_bounded_def by (auto simp: ta_syms_def)
    have ?comp
    proof (intro allI impI)
      fix e ee S
      assume SR: "S \<subseteq> set R" and compat: "state_compatible TA rel (cover_bound c e ee S)"      
      have "state_compatible ?TA rel (cover e ee S)"
        unfolding state_compatible_def
      proof (clarify)
        fix l r
        assume lr: "(l,r) \<in> cover e ee S"
          and lsyms: "funas_term l \<subseteq> ta_syms ?TA"
        from tab[unfolded ta_bounded_def, rule_format] have c: "\<And> f n. (f,n) \<in> ta_syms TA' \<Longrightarrow> height f \<le> c" unfolding TA'
          by (auto simp: ta_syms_def)
        from c lsyms lr have lr: "(l,r) \<in> cover_bound c e ee S" unfolding cover_bound_def TA'[symmetric]
          by blast
        from lsyms have lsyms: "funas_term l \<subseteq> insert ((const,0),0) (ta_syms TA)" unfolding ta_syms_def by auto
        from lr obtain ll rr where llrr:"(ll,rr) \<in> S" and base:"ll = base_term l"
          unfolding cover_bound_def cover_def by auto
        {
          assume "((const,0),0) \<in> funas_term l" 
          then have "base ((const,0),0) \<in> funas_term ll" unfolding base 
            unfolding funas_term_map_funs_term by force
          then have "(const,0) \<in> funas_term ll" by auto
          with set_mp[OF SR llrr] constR have False unfolding funas_trs_def funas_rule_def [abs_def] by auto
        } then have const_new: "((const,0),0) \<notin> funas_term l" ..
        with lsyms have lsyms: "funas_term l \<subseteq> ta_syms TA" by auto
        from compat[unfolded state_compatible_def] lr lsyms have 
          compat: "rule_state_compatible TA rel (l,r)" by auto      
        {
          fix q'
          assume q': "(q,q') \<in> (ta_eps TA)^*"
          from q[unfolded ta_rhs_states_def] obtain q'' rule where
            q: "(q'',q) \<in> (ta_eps TA)^*" and rule: "rule \<in> ta_rules TA" and sym: "r_rhs rule = q''" by auto
          from q' q have q': "(q'',q') \<in> (ta_eps TA)^*" by auto
          with rule sym 
          have "q' \<in> ta_rhs_states TA" unfolding ta_rhs_states_def by blast
        }        
        then have ta_rhs_states: "ta_rhs_states ?TA = ta_rhs_states TA" unfolding ta_rhs_states_def by auto
        show "rule_state_compatible ?TA rel (l,r)" 
          unfolding rule_state_compatible_def ta_rhs_states
        proof (rule, intro allI impI)
          fix \<tau>
          assume \<tau>: "\<tau> ` vars_term l \<subseteq> ta_rhs_states TA"
          obtain rr where rr: "map_vars_term \<tau> r = rr" by auto
          show "ta_res ?TA (map_vars_term \<tau> l) \<subseteq> rel^-1 `` ta_res ?TA (map_vars_term \<tau> r)"
          proof
            fix q'
            assume "q' \<in> ta_res ?TA (map_vars_term \<tau> l)"
            then have "q' \<in> ta_res TA (map_vars_term \<tau> l)" using const_new
            proof (induct l arbitrary: q')
              case (Var x) then show ?case by auto
            next
              case (Fun f ls)
              from Fun(3) have f: "(f,length ls) \<noteq> ((const,0),0)" by auto
              from Fun(2)[unfolded term.map ta_res.simps]
              obtain q2 qs where rule: "(f qs \<rightarrow> q2) \<in> ta_rules ?TA" and len: "length qs = length (map (map_vars_term \<tau>) ls)"
                and ind: "\<forall>i < length ls. qs ! i \<in> map (ta_res ?TA) (map (map_vars_term \<tau>) ls) ! i" 
                and q2: "(q2,q') \<in> (ta_eps TA)^*" by auto
              from rule len f have rule: "(f qs \<rightarrow> q2) \<in> ta_rules TA" by auto
              show ?case
              proof (unfold term.map ta_res.simps, rule, intro exI conjI, rule HOL.refl, rule rule, rule q2,
                rule len, intro allI impI)
                fix i
                assume i: "i < length (map (map_vars_term \<tau>) ls)"
                then have i': "i < length ls" by auto
                from i' have mem: "ls ! i \<in> set ls" by auto
                with Fun(3) have nmem: "((const,0),0) \<notin> funas_term (ls ! i)" by auto
                show "qs ! i \<in> map (ta_res TA) (map (map_vars_term \<tau>) ls) ! i"
                  unfolding nth_map[OF i] nth_map[OF i']
                  by (rule Fun(1)[OF mem _ nmem], insert ind i', auto)
              qed
            qed                        
            with compat[unfolded rule_state_compatible_def] \<tau>
            have "q' \<in> rel^-1 `` ta_res TA (map_vars_term \<tau> r)" by auto
            then obtain q'' where rel: "(q',q'') \<in> rel" and q'': "q'' \<in> ta_res TA (map_vars_term \<tau> r)" by auto
            from q'' have "q'' \<in> ta_res ?TA (map_vars_term \<tau> r)" unfolding rr
            proof (induct rr arbitrary: q'')
              case (Var q) then show ?case by auto
            next
              case (Fun f ts q')
              from Fun(2) obtain q2 qs where rule: "(f qs \<rightarrow> q2) \<in> ta_rules ?TA"
                and len: "length qs = length ts"
                and rec: "\<And>i. i < length ts \<Longrightarrow> qs ! i \<in> ta_res TA (ts ! i)"
                and q: "(q2,q') \<in> (ta_eps TA)^*"
                by auto
              {
                fix i
                assume i: "i < length ts"
                then have "ts ! i \<in> set ts" by auto
                from Fun(1)[OF this rec[OF i]]
                have "qs ! i \<in> ta_res ?TA (ts ! i)" by auto
              }
              with rule len q show ?case by auto
            qed
            with rel
            show "q' \<in> rel^-1 `` ta_res ?TA (map_vars_term \<tau> r)" by auto
          qed
        qed
      qed
      then show "state_compatible TA' rel (cover e ee S)" unfolding TA' .
    qed
    then show ?thesis using contain \<open>?coh\<close> \<open>?choice\<close> \<open>?tab\<close> cont unfolding TA' by auto
  qed
  then have ?comp and ?cont by auto
  have lift: "lift_term 0 ` ground_terms_of (set F) (set F') \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)term set)" (is "?L \<subseteq> _ ")
  proof (rule subset_trans[OF _ ta_contains_both[OF \<open>?cont\<close>]], rule, clarify)
    fix s
    assume s: "s \<in> ground_terms_of (set F) (set F')"
    let ?F = "?lz ` set F"
    let ?ls = "lift_term 0 s"
    from s[unfolded ground_terms_of_def, simplified]
    have F: "(\<Union>x\<in>set (args s). funas_term x) \<subseteq> set F"
      and root: "the (root s) \<in> set F'" and gs: "ground s" by auto
    from gs obtain g ts where s: "s = Fun g ts" by (cases s, auto)
    from F s have F: "(\<Union>x\<in>set ts. funas_term x) \<subseteq> set F" by auto
    from root s have root: "(g,length ts) \<in> set F'" by auto
    let ?ts = "map (lift_term 0) ts"
    from s have ls: "?ls = Fun (g, 0) ?ts" by simp
    from ls root have root: "the (root ?ls) \<in> ?lz ` set F'" by auto
    {
      fix lt
      assume "lt \<in> set (args ?ls)"
      then obtain t where lt: "lt = lift_term 0 t" and t: "t \<in> set ts" unfolding s by auto
      from t F gs s have "funas_term t \<subseteq> set F" "ground t" by auto
      then have "ground lt \<and> funas_term lt \<subseteq> ?F" unfolding lt
      proof (induct t)
        case (Fun f ss)
        {
          fix s
          assume s: "s \<in> set ss"
          from Fun(3) s have g: "ground s" by auto
          from Fun(2) s have wf: "funas_term s \<subseteq> set F" by auto
          from Fun(1)[OF s wf g] have "ground (lift_term 0 s)" "funas_term (lift_term 0 s) \<subseteq> ?F"
            by force+
        } note ind = this
        from Fun(2) have f: "((f,0), length ss) \<in> ?F" by auto
        from ind f
        show ?case by force
      qed simp
    }
    with root
    show "\<Union>(funas_term ` set (args ?ls)) \<subseteq> ?F \<and>
            the (root ?ls) \<in> ?lz ` set F' \<and>
            ground ?ls" unfolding s by force
  qed
  show ?thesis
    by (rule exI[of _ q], rule exI[of _ const], rule exI[of _ "set F"], rule exI[of _ "set F'"], rule exI[of _ TA'],
    insert \<open>?comp\<close> \<open>?cont\<close> lift main q, auto simp: F finG G' TA' F' H')
qed

lemma create_constant_in_ta: fixes R :: "('f,'v)rules"
  assumes 
      choice: "left_linear_trs (set R) \<or> ta_det TA \<and> state_raise_consistent TA rel"
  and compat: "state_compatible TA rel (cover_bound c e ee (set R))" (is "state_compatible _ _ ?R")
  shows "\<exists> q const F F' TA'. q \<in> qfin \<and> G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F'
    \<and> state_compatible TA' rel (cover e ee (set R))
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)    
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
proof -
  let ?Q = "\<lambda> TA'. \<forall> e ee S. S \<subseteq> set R \<longrightarrow> state_compatible TA rel (cover_bound c e ee S) \<longrightarrow>
       state_compatible TA' rel (cover e ee S)"
  define P where "P = (\<lambda> q const F F' TA'. q \<in> qfin \<and> G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F' \<and>
       ?Q TA' 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)    
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>)"
  from create_constant_in_ta_generic[OF choice]  
  have "\<exists> q const F F' TA'. P q const F F' TA'" unfolding P_def .
  then obtain q const F F' TA' where main: "P q const F F' TA'" by blast
  then have Q: "?Q TA'" unfolding P_def by blast
  note * = Q[rule_format, OF _ compat] main[unfolded P_def]
  show ?thesis 
    by (rule exI[of _ q], rule exI[of _ const], rule exI[of _ F], rule exI[of _ F'], rule exI[of _ TA'],
    insert *, auto)
qed

lemma create_constant_in_ta_two: fixes R1 R2 :: "('f,'v)rules" 
  assumes 
      choice: "left_linear_trs (set (R1 @ R2)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
  and compat1: "state_compatible TA rel (cover_bound c e1 ee1 (set R1))" (is "state_compatible _ _ ?R1")
  and compat2: "state_compatible TA rel (cover_bound c e2 ee2 (set R2))" (is "state_compatible _ _ ?R2")
  shows "\<exists> q const F F' TA'. q \<in> qfin \<and> G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F'
    \<and> state_compatible TA' rel (cover e1 ee1 (set R1))
    \<and> state_compatible TA' rel (cover e2 ee2 (set R2))
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R1 \<union> set R2) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)    
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
proof -
  let ?Q = "\<lambda> TA'. \<forall> e ee S. S \<subseteq> set (R1 @ R2) \<longrightarrow> state_compatible TA rel (cover_bound c e ee S) \<longrightarrow>
       state_compatible TA' rel (cover e ee S)"
  define P where "P = (\<lambda> q const F F' TA'. q \<in> qfin \<and> G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F' \<and>
       ?Q TA' 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat,'v)terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set (R1 @ R2)) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)    
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>)"
  from create_constant_in_ta_generic[OF choice]  
  have "\<exists> q const F F' TA'. P q const F F' TA'" unfolding P_def .
  then obtain q const F F' TA' where main: "P q const F F' TA'" by blast
  then have "?Q TA'" unfolding P_def by blast
  note * = this[rule_format, OF _ compat1]
    this[rule_format, OF _ compat2] 
    main[unfolded P_def]
  show ?thesis 
    by (rule exI[of _ q], rule exI[of _ const], rule exI[of _ F], rule exI[of _ F'], rule exI[of _ TA'],
    insert *, auto)
qed
end
  
lemma funas_term_ground_terms_of: "\<Union>(funas_term ` ground_terms_of F F') \<subseteq> F \<union> F'"
proof -
  {
    fix t
    assume "t \<in> ground_terms_of F F'"
    note * = this[unfolded ground_terms_of_def]
    from * obtain f ts where t: "t = Fun f ts" by (cases t, auto)
    with * have "funas_term t \<subseteq> F \<union> F'" by auto
  }
  then show ?thesis by auto
qed

lemma funas_term_const_subst:
  fixes const :: "'f"
  shows "funas_term (t \<cdot> (\<lambda>_. Fun const [])) \<subseteq> funas_term t \<union> {(const,0)}"
  by (induct t) auto

locale bounds_impl = 
  fixes R S :: "('f,'v)rules" and TA and rel :: "'q rel" and e and c and c_opt and G H :: "'f sig" and qfin 
  assumes
      choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
  and fin: "finite (ta_rules TA)"
  and compat: "state_compatible TA rel (cover_bound c e Strict_TRS (set R))" 
  and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))" 
  and coh: "state_coherent TA rel"
  and tab: "ta_bounded TA c"
  and qfin: "\<exists> q \<in> qfin. q \<in> ta_rhs_states TA"
  and qfin_final: "qfin \<subseteq> ta_final TA"
  and inf: "infinite (UNIV :: 'f set)"
  and finG: "finite G"
  and finH: "finite H"
  and contain: "ta_contains ((\<lambda>(f,n). (lift 0 f,n)) ` G) ((\<lambda>(f,n). (lift 0 f,n)) ` H) TA qfin" 
  and wf: "wf_trs (set R \<union> set S)" 
begin
lemma match_bounds_linear_impl: 
  assumes match: "e = Matchbounds.match"
  and non_duplicating: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and rcm: "set (roots_of_cm cm) \<subseteq> H"
  and scm: "set (stackable_of_cm cm) \<subseteq> G"
  shows "deriv_bound_measure_class (rstep (set R)) cm (Comp_Poly 1)"
proof -
  let ?match = Matchbounds.match
  from wf[unfolded wf_trs_def] have varcond: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto
  from create_constant_in_ta_two[OF fin coh finG finH contain qfin_final qfin tab inf choice compat compat2,
    unfolded match] 
  obtain q const F F' TA' where "G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F'
    \<and> state_compatible TA' rel (cover ?match Strict_TRS (set R)) 
    \<and> state_compatible TA' rel (cover ?match (Weak_TRS c_opt) (set S)) 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat, 'v) terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R \<union> set S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>
    " (is "?GF \<and> ?HF \<and> ?comp \<and> _ \<and> ?cont \<and> ?coh \<and> ?choice \<and> ?tab \<and> ?TA") by metis
  then have compat: ?comp and contain: ?cont and ?coh ?choice ?HF ?GF ?TA ?tab by auto
  let ?R = "cover Matchbounds.match Strict_TRS (set R)"
  from \<open>?choice\<close> cover_left_linear have choice: "left_linear_trs ?R \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    unfolding left_linear_trs_union by blast
  have finTA: "finite (ta_rules TA')"
    unfolding \<open>?TA\<close> using fin by auto
  have varcond: "\<And> l r. (l, r) \<in> ?R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    by (rule cover_var_condition[OF varcond])
  from raise_step_boundedI[OF choice finTA \<open>?comp\<close> \<open>?coh\<close> \<open>?cont\<close> \<open>?tab\<close> varcond] 
  have bounded: "e_raise_bounded Matchbounds.match c (set R) (ground_terms_of F F')" 
    unfolding e_raise_bounded_def by blast
  from \<open>?GF\<close> \<open>?HF\<close> rcm scm have cm: 
    "set (stackable_of_cm cm) \<subseteq> F"
    "set (roots_of_cm cm) \<subseteq> F'"
    and c: "(const,0) \<in> F"
    by auto
  show ?thesis
    by (rule match_raise_bounded_linear_complexity[OF _ finite_set funas_term_ground_terms_of _ cm c non_duplicating bounded],
    insert wf, auto simp: wf_trs_def)
qed

lemma match_bounds_linear_rel_impl: 
  assumes match: "e = Matchbounds.match"
  and non_duplicating: "\<And> l r. (l,r) \<in> set R \<union> set S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
  and scm: "set (stackable_of_cm cm) \<subseteq> G"
  and rcm: "set (roots_of_cm cm) \<subseteq> H"
  and c_opt: "weak_kind_condition c c_opt (set R)"
  shows "deriv_bound_measure_class (relto (rstep (set R)) (rstep (set S))) cm (Comp_Poly 1)"
proof -
  let ?match = Matchbounds.match
  from wf[unfolded wf_trs_def] have varcond: "\<And> l r. (l,r) \<in> set R \<union> set S \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto
  from create_constant_in_ta_two[OF fin coh finG finH contain qfin_final qfin tab inf choice compat compat2, unfolded match]
  obtain q const F F' TA' where "G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F'
    \<and> state_compatible TA' rel (cover ?match Strict_TRS (set R)) 
    \<and> state_compatible TA' rel (cover ?match (Weak_TRS c_opt) (set S)) 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat, 'v) terms)
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R \<union> set S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>
    " (is "?GF \<and> ?HF \<and> ?comp \<and> ?comp2 \<and> ?cont \<and> ?coh \<and> ?choice \<and> ?tab \<and> ?TA") by metis
  then have compat: ?comp ?comp2 and contain: ?cont and ?HF ?coh ?choice ?GF ?tab ?TA by auto
  let ?R = "cover Matchbounds.match Strict_TRS (set R)"
  let ?S = "cover Matchbounds.match (Weak_TRS c_opt) (set S)"
  from \<open>?choice\<close> have choice: "left_linear_trs (?R \<union> ?S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    unfolding left_linear_trs_union using cover_left_linear by blast
  have finTA: "finite (ta_rules TA')"
    unfolding \<open>?TA\<close> using fin by auto
  from compat have compat: "state_compatible TA' rel (?R \<union> ?S)" unfolding state_compatible_union by blast
  have varcond: "\<And> l r. (l, r) \<in> ?R \<union> ?S \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    using cover_var_condition[of _ _ _ ?match] varcond by blast
  from raise_step_boundedI[OF choice finTA compat \<open>?coh\<close> \<open>?cont\<close> \<open>?tab\<close> varcond]
  have bounded: "match_raise_rel_bounded c c_opt (set R) (set S) (ground_terms_of F F')" 
    unfolding match_raise_rel_bounded_def by blast
  from \<open>?GF\<close> \<open>?HF\<close> rcm scm have cm: 
    "set (stackable_of_cm cm) \<subseteq> F"
    "set (roots_of_cm cm) \<subseteq> F'"
    and c: "(const,0) \<in> F"
    by auto
  show ?thesis
    by (rule match_raise_bounded_linear_complexity_rel[OF wf _ funas_term_ground_terms_of 
      _ cm c c_opt non_duplicating bounded], insert
    finite_set[of "R @ S"] , auto)
qed
  

lemma e_bounds_impl: 
  assumes SN: "locally_terminating (cover e Strict_TRS (set R) \<union> Matchbounds.raise)"
  and GR: "funas_trs (set R) \<subseteq> G" and 
  G: "set (stackable_of_cm cm) \<subseteq> G" "set (roots_of_cm cm) \<subseteq> G"
  and H: "H = G"
  shows "SN (rstep (set R))"
proof -
  let ?R = "cover e Strict_TRS (set R)"
  from wf[unfolded wf_trs_def] have varcond: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by auto
  from create_constant_in_ta_two[OF fin coh finG finH contain qfin_final qfin tab inf choice compat compat2]
  obtain q const F F' TA' where "G \<union> {(const,0)} = F \<and> H \<union> {(const,0)} = F'
    \<and> state_compatible TA' rel ?R 
    \<and> lift_term 0 ` ground_terms_of F F' \<subseteq> (ta_lang TA' :: ('f \<times> nat, 'v) terms) 
    \<and> state_coherent TA' rel
    \<and> (left_linear_trs (set R \<union> set S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel)
    \<and> ta_bounded TA' c
    \<and> TA' = \<lparr> ta_final = (ta_final TA), ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>
    " (is "?GF \<and> ?HF \<and> ?comp \<and> ?cont \<and> ?coh \<and> ?choice \<and> ?tab \<and> ?TA") by metis  
  then have compat: ?comp and contain: ?cont and ?GF ?HF ?coh ?choice ?GF ?TA ?tab by auto
  from \<open>?choice\<close> have choice: "left_linear_trs ?R \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    unfolding left_linear_trs_union using cover_left_linear by blast
  have subF: "funas_trs (set R) \<subseteq> F" using GR \<open>?GF\<close> by auto
  have finR: "finite (set R)" by auto
  have c: "(const, 0) \<in> F" using \<open>?GF\<close> by auto
  let ?wF = "{t . funas_term t \<subseteq> F} :: ('f,'v)terms"
  let ?L = "{t. t \<in> ?wF \<and> ground t}" 
  from H \<open>?GF\<close> \<open>?HF\<close> have F': "F' = F" by auto
  have L: "?L \<subseteq> ground_terms_of F F'" unfolding F' 
  proof (clarify)
    fix t
    assume "ground t" and "funas_term t \<subseteq> F"
    then show "t \<in> ground_terms_of F F" unfolding ground_terms_of_def
      by (cases t, auto)
  qed
  from finG \<open>?GF\<close> have finF: "finite F" by auto
  show ?thesis
  proof (rule SN_wf_ground[OF c subF])
    fix t :: "('f,'v)term"
    assume "funas_term t \<subseteq> F" "ground t"
    then have t: "t \<in> ?L" by auto
    have "SN_on (rstep (set R)) ?L"
    proof (rule e_bounds[OF choice _ \<open>?comp\<close> \<open>?coh\<close> _ \<open>?tab\<close> SN finF finR])
      show "lift_term 0 ` {t \<in> ?wF. ground t} \<subseteq> ta_lang TA'" using \<open>?cont\<close> L by auto
      show "finite (ta_rules TA')"
        unfolding \<open>?TA\<close> using fin by auto
    qed (insert wf[unfolded wf_trs_def], auto)
    then show "SN_on (rstep (set R)) {t}" using t unfolding SN_on_def by blast
  qed
qed

end

fun flatten_term_enum_filter :: "(('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f list,'v)term \<Rightarrow> ('f,'v)term list"
where "flatten_term_enum_filter f (Var x) = (let tx = Var x in if f tx then [tx] else [])"
   |  "flatten_term_enum_filter f (Fun fs ts) = (
          let lts = map (flatten_term_enum_filter f) ts 
            in (if Bex (set lts) (\<lambda> ts. ts = []) then [] else 
              (let ss = concat_lists lts
            in filter f (concat (map (\<lambda> f. map (Fun f) ss) fs)))))"

  
lemma flatten_term_enum_filter: 
  shows "set (flatten_term_enum_filter f t) = {u. instance_term u (map_funs_term set t) \<and> (\<forall> v \<unlhd> u. f v)}"
proof (induct t)
  case (Var x)
  show ?case (is "_ = ?R")
  proof -
    {
      fix t 
      assume "t \<in> ?R"
      then have "t = Var x" by (cases t, auto)
    } 
    then show ?thesis using supteq_Var_id[of x] by (auto simp: Let_def)
  qed
next
  case (Fun fs ts)
  show ?case (is "?L = ?R")
  proof -
    {
      fix i
      assume "i < length ts"
      then have "ts ! i \<in> set ts" by auto
      note Fun[OF this]
    } note ind = this
    have idL: "?L = {Fun g ss | g ss. g \<in> set fs  \<and> length ss = length ts \<and> f (Fun g ss) \<and> (\<forall>i<length ts. ss ! i \<in> set (flatten_term_enum_filter f (ts ! i)))}" (is "_ = ?M1") by (simp add: Let_def set_conv_nth[of ts], auto)
    let ?R1 = "{Fun g ss | g ss. g \<in> set fs \<and> length ss = length ts \<and> f (Fun g ss) \<and> (\<forall> i<length ss. instance_term (ss ! i) (map_funs_term set (ts ! i)) \<and> (\<forall> u \<unlhd> (ss ! i). f u))}"
    {
      fix u
      have "(u \<in> ?R) = (u \<in> ?R1)" 
      proof (cases u)
        case (Fun g ss)
        show ?thesis unfolding Fun 
          by (auto simp: Fun_supteq set_conv_nth[of ss])
      qed auto        
    }
    then have idR: "?R = ?R1" by auto
    show ?case unfolding idL idR using ind by auto
  qed
qed

definition inverse_base_term :: "('f,'v)term \<Rightarrow> nat \<Rightarrow> ('f \<times> nat,'v)term list"
  where "inverse_base_term l c \<equiv> let hs = [0..< Suc c] in flatten_term_enum (map_funs_term (\<lambda> f. map (\<lambda> h. lift h f) hs) l)"

lemma inverse_base_term: "set (inverse_base_term l c) = 
  {l'. base_term l' = (l :: ('f,'v)term) \<and> (\<forall> f n. (f,n) \<in> funas_term l' \<longrightarrow> height f \<le> c)}"
proof -
  obtain cs where cs: "cs = [0..<Suc c]" by auto
  let ?m = "map_funs_term (\<lambda>f. set (map (\<lambda>h. lift h f) cs))"
  let ?i = "\<lambda> u l. instance_term u (?m l)"
  let ?h = "\<lambda>l. (\<forall> f n. (f,n) \<in> funas_term l \<longrightarrow> height f \<le> c)"
  let ?b = "\<lambda>l' l. base_term l' = l \<and> ?h l'"
  let ?I = "\<lambda>l. {u. ?i u l}"
  let ?B = "\<lambda>l. {u. ?b u l}"
  have "?I l = ?B l" 
  proof (induct l)
    case (Var x)
    have "(u \<in> ?I (Var x)) = (u \<in> ?B (Var x))" for u
      by (cases u, auto)
    then show ?case by auto
  next
    case (Fun f ss) note ind = this
    let ?s = "Fun f ss"
    have "(u \<in> (?I ?s)) = (u \<in> (?B ?s))" for u
    proof (cases u)
      case (Var x)
      then show ?thesis by auto
    next
      case (Fun g ts)
      let ?t = "Fun g ts"
      obtain gg cc where g: "g = (gg,cc)" by (cases g, auto)
      show ?thesis 
      proof (cases "length ts = length ss \<and> gg = f \<and> cc \<le> c")
        case False
        then show ?thesis unfolding Fun g cs by auto
      next
        case True
        then have len: "length ts = length ss" and u: "u = Fun (f,cc) ts"
          and cc: "cc \<le> c" and cc2: "cc \<in> set cs" using Fun g unfolding cs by auto
        {
          fix i 
          assume "i < length ss"
          then have "ss ! i \<in> set ss" by auto
          from ind[OF this] 
          have "?i (ts ! i) (ss ! i) = ?b (ts ! i) (ss ! i)" by auto
        } note ind = this          
        have "?i u ?s = ?b u ?s" unfolding u term.map funas_term.simps
            set_map set_conv_nth[of ts]
          by (simp add: len cc cc2, unfold map_nth_eq_conv[OF len, of base_term] , insert ind, simp, blast)
        then show ?thesis by auto
      qed
    qed
    then show ?case by simp
  qed
  then show ?thesis   unfolding inverse_base_term_def Let_def flatten_term_enum cs map_funs_term_comp o_def .
qed

definition inverse_base_term_filter :: "(('f \<times> nat,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term \<Rightarrow> nat \<Rightarrow> ('f \<times> nat,'v)term list"
  where "inverse_base_term_filter filt l c \<equiv> let hs = [0..< Suc c] in flatten_term_enum_filter filt (map_funs_term (\<lambda> f. map (\<lambda> h. lift h f) hs) l)"

lemma inverse_base_term_filter: "set (inverse_base_term_filter filt l c) = 
  {l'. base_term l' = (l :: ('f,'v)term) \<and> (\<forall> u \<unlhd> l'. filt u) \<and> (\<forall> f n. (f,n) \<in> funas_term l' \<longrightarrow> height f \<le> c)}"
proof -
  obtain cs where cs: "cs = [0..<Suc c]" by auto
  let ?m = "map_funs_term (\<lambda>f. set (map (\<lambda>h. lift h f) cs))"
  let ?f = "\<lambda> u. (\<forall> v \<unlhd> u. filt v)"
  let ?i' = "\<lambda> u l. instance_term u (?m l)"
  let ?i = "\<lambda> u l. ?i' u l \<and> ?f u"
  let ?h = "\<lambda>l. (\<forall> f n. (f,n) \<in> funas_term l \<longrightarrow> height f \<le> c)"
  let ?b' = "\<lambda>l' l. base_term l' = l \<and> ?h l'"
  let ?b = "\<lambda>l' l. base_term l' = l \<and> ?f l' \<and> ?h l'"
  let ?I = "\<lambda>l. {u. ?i u l}"
  let ?B = "\<lambda>l. {u. ?b u l}"
  { 
    fix u
    have "?i u l = ?b u l"
    proof (induct l arbitrary: u)
      case (Var x u)
      show ?case by (cases u, auto)
    next
      case (Fun f ss u) note ind = this
      let ?s = "Fun f ss"
      show ?case
      proof (cases u)
        case (Var x)
        then show ?thesis by auto
      next
        case (Fun g ts)
        let ?t = "Fun g ts"
        obtain gg cc where g: "g = (gg,cc)" by (cases g, auto)
        show ?thesis 
        proof (cases "length ts = length ss \<and> gg = f \<and> cc \<le> c \<and> ?f ?t")
          case False
          then show ?thesis unfolding Fun g cs by auto
        next
          case True
          then have len: "length ts = length ss" and u: "u = Fun (f,cc) ts"
            and cc: "cc \<le> c" and cc2: "cc \<in> set cs" and ff: "?f (Fun (f,cc) ts)" using Fun g unfolding cs by auto
          {
            fix i 
            assume i: "i < length ss"
            with len have "ts ! i \<in> set ts" by auto
            then have sub: "Fun (f,cc) ts \<unrhd> ts ! i" by auto
            have ff: "?f (ts ! i)"
            proof(intro allI impI)
              fix v
              assume "ts ! i \<unrhd> v" 
              with sub have "Fun (f,cc) ts \<unrhd> v" by (rule supteq_trans)
              with ff show "filt v"  by auto
            qed
            from i have "ss ! i \<in> set ss" by auto
            from ind[OF this, of "ts ! i"] ff 
            have "?i' (ts ! i) (ss ! i) = ?b' (ts ! i) (ss ! i)"              
              by auto
          } note ind = this
          show "?i u ?s = ?b u ?s" unfolding u term.map funas_term.simps
            set_map set_conv_nth[of ts]
            by (simp add: len cc cc2, unfold map_nth_eq_conv[OF len, of base_term] , insert ind, simp, blast)
        qed
      qed
    qed
  }
  then show ?thesis   unfolding inverse_base_term_filter_def Let_def flatten_term_enum_filter cs map_funs_term_comp o_def by auto
qed

declare compute_height.simps[code del]
hide_const br

lemma compute_height_code[code]: 
  "compute_height Strict_TRS bl br = (\<lambda> l x. Suc x)"
  "compute_height (Weak_TRS (Some c)) bl br = (if size (funs_term_ms bl) \<ge> size (funs_term_ms br) then 
    (\<lambda> l x. if lift_term x bl = l then min c x else min c (Suc x)) else 
    (\<lambda> l x. min c (Suc x)))"
  "compute_height (Weak_TRS None) bl br = (if size (funs_term_ms bl) \<ge> size (funs_term_ms br) then 
    (\<lambda> l x. if lift_term x bl = l then x else (Suc x)) else 
    (\<lambda> l x. Suc x))"
  by (intro ext, simp)+
    
(* TODO: one can improve the efficiency of the the generator even further, 
   if partial results of the filter can be reused *)
definition cover_bound_list_filter :: "(('f \<times> nat,'v)term \<Rightarrow> bool) \<Rightarrow> (('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> relation_kind \<Rightarrow> nat \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f \<times> nat,'v)rule list"
  where "cover_bound_list_filter filt ff gg c R \<equiv> concat (map (\<lambda>(l,r). 
            let ch = compute_height gg l r;
                ee = ff (l,r) in map
                   (\<lambda> l'. ((l', lift_term 
                        (ch l' (min_list (map height (sym_collect (\<lambda> t'. ee (base_term t')) l')))) r)))
              (inverse_base_term_filter filt l c))
    R)"


lemma cover_bound_list_filter: "set (cover_bound_list_filter ff e ee c (R :: ('f,'v)rules)) = (cover_bound c e ee (set R) \<inter> {(l,r). (\<forall> u \<unlhd> l. ff u)})" (is "?L = ?R")
proof -
  obtain h where h: "h = (\<lambda> l' l r. compute_height ee l r l' (min_list (map height (sym_collect (\<lambda>t'. e (l,r) (base_term t')) l'))))" by auto
  obtain RR where RR: "cover_bound c e ee (set R) \<inter> {(l,r). (\<forall> u \<unlhd> l. ff u)} = RR" by auto
  let ?f = "\<lambda>l. (\<forall> u \<unlhd> l. ff u)"
  {
    fix l' r' 
    assume l'r': "(l',r') \<in> ?L"
    from l'r'[unfolded cover_bound_list_filter_def Let_def]
    obtain l r where lr: "(l,r) \<in> set R" and
      l'r': "(l',r') \<in> set (map (\<lambda>l'. (l', lift_term (h l' l r) r)) (inverse_base_term_filter ff l c))"
      unfolding h set_concat  set_map by force
    then have 
      r': "r' = lift_term (h l' l r) r"
      and l': "l' \<in> set (inverse_base_term_filter ff l c)"
      by auto
    from l'[unfolded inverse_base_term_filter]
    have l': "base_term l' = l"
      and c: "\<forall> f n. (f,n) \<in> funas_term l' \<longrightarrow> height f \<le> c" 
      and f: "?f l'" by auto
    from lr r' l' c have cover: "(l',r') \<in> cover e ee (set R)" unfolding cover_def h by auto
    have "(l',r') \<in> ?R" using c cover f unfolding cover_bound_def by auto
  }
  moreover
  {
    fix l' r' 
    assume "(l',r') \<in> ?R"
    then have cover: "(l',r') \<in> cover e ee (set R)" 
      and c: "\<forall> f n. (f,n) \<in> funas_term l' \<longrightarrow> height f \<le> c"      
      and f: "?f l'"
      unfolding cover_bound_def by auto
    from cover[unfolded cover_def]
    obtain l r where
      lr: "(l,r) \<in> set R"
      and r': "r' = lift_term (h l' l r) r"
      and l': "base_term l' = l"
      unfolding h by simp blast      
    from c l' f have l': "l' \<in> set (inverse_base_term_filter ff l c)" 
      unfolding inverse_base_term_filter by auto
    have "(l',r') \<in> ?L"
      by (unfold cover_bound_list_filter_def Let_def set_concat set_map, rule, rule, rule lr, unfold set_map r' h, rule, rule refl, rule l')
  }
  ultimately show ?thesis unfolding RR by force
qed

lemma remove_compatible_rules: 
  assumes compat: "state_compatible TA rel (cover_bound e ee c R \<inter> {(l,r). ff l r})"
  and filter: "\<And> l r. \<not> ff l r \<Longrightarrow> rule_state_compatible TA rel (l,r)"
  shows "state_compatible TA rel (cover_bound e ee c R)"
  using assms unfolding state_compatible_def by blast

datatype boundstype = Roof | Match

fun boundstype_fun :: "boundstype \<Rightarrow> ('f,'v) rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
  where "boundstype_fun Roof = Matchbounds.roof"
      | "boundstype_fun Match = Matchbounds.match"

fun bounds_condition :: "boundstype \<Rightarrow> ('f :: showl ,'v :: showl)rules \<Rightarrow> showsl check"
where "bounds_condition Roof _ = succeed"
   |  "bounds_condition Match R = (check_all (\<lambda>(l,r). vars_term_ms r \<subseteq># vars_term_ms l) R
              <+? (\<lambda> (l,r). showsl_lit (STR ''rule '') \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '' is duplicating'')))"

lemma bounds_condition: assumes ok: "isOK(bounds_condition type R)"
  and wf: "wf_trs (set R)"
  shows "locally_terminating (cover (boundstype_fun type) Strict_TRS (set R) \<union> Matchbounds.raise)"
proof (cases type)
  case Roof
  show ?thesis unfolding Roof
    using roof_raise_locally_SN[OF wf]
    by auto
next
  case Match
  show ?thesis unfolding Match
    by (unfold boundstype_fun.simps, rule match_raise_locally_SN[OF wf],
    insert ok[unfolded Match], auto)
qed

context
begin
private fun relation_as_list :: "'q ta_relation \<Rightarrow> showsl + ('q \<times> 'q) list" where
  "relation_as_list (Some_Relation rel) = return rel"
| "relation_as_list Id_Relation = return []"
| "relation_as_list Decision_Proc = error (showsl_lit (STR ''decision procedure not available for non-left linear TRSs''))"
| "relation_as_list Decision_Proc_Old = error (showsl_lit (STR ''decision procedure not available for non-left linear TRSs''))"

definition check_state_raise_consistent :: "('q :: {linorder,showl},('f :: showl) \<times> nat)tree_automaton \<Rightarrow> ('q \<times> 'q) list \<Rightarrow> showsl check" where
  "check_state_raise_consistent TA rel = do {
     let rels = set rel;
     let rls = ta_rules_impl' TA;
     check_allm (\<lambda> r1. case r1 of TA_rule (f1,i1) qs1 q1 \<Rightarrow>
       check_allm (\<lambda> r2. case r2 of TA_rule (f2,i2) qs2 q2 \<Rightarrow>
         if (f1 = f2 \<and> i1 < i2 \<and> qs1 = qs2) then check ((q1,q2) \<in> rels)
           (showsl_lit (STR ''problem with raise consistency because of automaton-rules\<newline> '')
             \<circ> showsl r1 \<circ> showsl_nl \<circ> showsl r2 \<circ> showsl_nl \<circ> showsl q1 \<circ> showsl_lit (STR '' is not >>^* '') 
             \<circ> showsl q2) else succeed) rls) rls
   }"

lemma check_state_raise_consistent[simp]:
  "isOK(check_state_raise_consistent TA rel) = state_raise_consistent (ta_of_ta TA) (set rel)"
  unfolding check_state_raise_consistent_def Let_def state_raise_consistent_def 
  unfolding isOK_update_error isOK_forallM ta_rule.case_distrib prod.case_distrib isOK_if isOK_check
  by (cases TA, fastforce split: ta_rule.splits)

definition check_ta_bounded where 
  "check_ta_bounded TA c \<equiv> check_all (\<lambda> (f,n). height f \<le> c) (map fst (rm.to_list (ta_rules_impl TA)))
        <+? (\<lambda> (f,n). showsl f \<circ> showsl_lit (STR '' is symbol in TA with height larger than c = '') \<circ> showsl c)"

datatype ('f,'q)bounds_info = Bounds_Info (boundstype: boundstype) nat "'q list" "('q, 'f \<times> nat) tree_automaton" "'q ta_relation"

(* dup suffix to indicate potential duplicates *)
fun states_of_tree_automata_dup :: "('q, 'f) tree_automaton \<Rightarrow> 'q list" where
  "states_of_tree_automata_dup (Tree_Automaton qfin rules eps) = 
      qfin @ map fst eps @ map snd eps @ concat (map r_lhs_states rules) @ map r_rhs rules" 

fun states_of_ta_relation_dup :: "'q ta_relation \<Rightarrow> 'q list" where
  "states_of_ta_relation_dup (Some_Relation rel) = map fst rel @ map snd rel" 
| "states_of_ta_relation_dup Id_Relation= []" 
| "states_of_ta_relation_dup Decision_Proc_Old = []" 
| "states_of_ta_relation_dup Decision_Proc = []" 

fun states_of_bounds_info_dup :: "('f,'q)bounds_info \<Rightarrow> 'q list" where
  "states_of_bounds_info_dup (Bounds_Info bt b qs ta rel) = qs @ states_of_tree_automata_dup ta @ states_of_ta_relation_dup rel" 

fun create_renaming_main :: "'q list \<Rightarrow> integer \<Rightarrow> ('q,integer)mapping \<times> (integer \<times> 'q)list \<Rightarrow> ('q,integer)mapping \<times> (integer \<times> 'q)list" where
  "create_renaming_main [] i (qi, iq) = (qi, rev iq)" 
| "create_renaming_main (q # qs) i (qi, iq) = (case Mapping.lookup qi q of Some _ \<Rightarrow> create_renaming_main qs i (qi, iq)
     | None \<Rightarrow> create_renaming_main qs (i + 1) (Mapping.update q i qi, (i,q) # iq))" 

definition create_renaming_of_states :: "'q list \<Rightarrow> ('q \<Rightarrow> integer) \<times> (integer \<times> 'q) list" where
  "create_renaming_of_states qs = (case create_renaming_main qs 0 (Mapping.empty, []) of
     (qi, iq) \<Rightarrow> (\<lambda> q. the (Mapping.lookup qi q), iq))" 

context
  fixes ren :: "'q \<Rightarrow> 'p"
begin
fun rename_ta_rule :: "('q,'f)ta_rule \<Rightarrow> ('p,'f)ta_rule" where
  "rename_ta_rule (TA_rule f qs q) = TA_rule f (map ren qs) (ren q)" 

fun rename_tree_automaton :: "('q, 'f) tree_automaton \<Rightarrow> ('p, 'f) tree_automaton" where
  "rename_tree_automaton (Tree_Automaton qfin rules eps) = (Tree_Automaton (map ren qfin) (map rename_ta_rule rules) (map (map_prod ren ren) eps))"

fun rename_ta_relation :: "'q ta_relation \<Rightarrow> 'p ta_relation" where
  "rename_ta_relation (Some_Relation rel) = Some_Relation (map (map_prod ren ren) rel)" 
| "rename_ta_relation Decision_Proc_Old = Decision_Proc_Old" 
| "rename_ta_relation Decision_Proc = Decision_Proc" 
| "rename_ta_relation Id_Relation = Id_Relation" 

fun rename_bounds_info :: "('f,'q)bounds_info \<Rightarrow> ('f,'p)bounds_info" where
  "rename_bounds_info (Bounds_Info bt b qs ta rel) = Bounds_Info bt b (map ren qs) (rename_tree_automaton ta) (rename_ta_relation rel)"
end

definition get_integer_bounds_info :: "('f,'q)bounds_info \<Rightarrow> ('f,integer)bounds_info \<times> (integer \<times> 'q) list" where
  "get_integer_bounds_info bi = ( 
     case create_renaming_of_states (states_of_bounds_info_dup bi) of
       (qi, iq) \<Rightarrow>
       (rename_bounds_info qi bi, iq))" 

lemma boundstype_get_integer_bounds_info: "get_integer_bounds_info bi = (info,ren) \<Longrightarrow> boundstype info = boundstype bi"
  unfolding get_integer_bounds_info_def
  by (cases bi, auto split: prod.splits)
  

fun get_renaming_info :: "(integer \<times> 'q :: showl)list \<Rightarrow> showsl" where
  "get_renaming_info ren = (let fun = (\<lambda> (i,q). showsl i o showsl_lit (STR '': '') o showsl q)
     in showsl_lit (STR ''renaming information: the states in the certificate have been numbered as follows:\<newline>\<newline>'')
       o showsl_sep fun showsl_nl ren o showsl_nl o showsl_nl)" 


definition construct_c_opt :: "nat \<Rightarrow> ('f,'v)rules \<Rightarrow> nat option" where
  "construct_c_opt c R = (if non_collapsing_impl R then Some c else None)"

lemma construct_c_opt[simp]: "weak_kind_condition c (construct_c_opt c R) (set R)"
  unfolding construct_c_opt_def
  by (auto split: if_splits)

definition check_bounds_generic :: "('f :: {showl,linorder},'q :: {showl,linorder})bounds_info \<Rightarrow> 
  ('f,'v :: {showl,linorder})rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
  ('f \<times> nat)list \<Rightarrow> ('f \<times> nat)list \<Rightarrow> showsl check" where
  "check_bounds_generic bi R S F G = (case get_integer_bounds_info bi of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
     let c_opt = construct_c_opt c R;
     let RS = R @ S;
     TA \<leftarrow> generate_ta_cond preTA rel;
     let rell = rel_checker rel;
     check_wf_trs RS;
     check (set qfin \<subseteq> rs.\<alpha> (ta_final_impl TA)) (showsl_lit (STR ''explicitly mentioned final states must be final''));
     (if isOK(check_left_linear_trs RS) then succeed else 
       do {
         check_det preTA <+? (\<lambda> s. showsl_lit (STR ''for non left-linear TRS we require det. automaton\<newline>'') \<circ> s);
         rel_list \<leftarrow> relation_as_list rel;
         check_state_raise_consistent preTA rel_list
       });
     bounds_condition type RS;
     check_ta_bounded TA c;
     check (Bex (set qfin) (\<lambda> q. rs.memb q (ta_rhs_states_set TA))) (showsl_lit (STR ''did not find mentioned final state in TA''));
     ta_contains_impl (map (\<lambda>(f,n). (lift 0 f,n)) F) (map (\<lambda>(f,n). (lift 0 f,n)) G) TA qfin
        <+? (\<lambda> fqs. showsl_lit (STR ''it could not be guaranteed that lift0(T(Sigma)) is accepted by TA\<newline>'') \<circ>
              (showsl_lit (STR ''there is no transition from '') \<circ> showsl fqs \<circ> showsl_lit (STR '' to a final state'')));
     state_compatible_eff_list TA rell (cover_bound_list_filter (\<lambda> l. \<not> rule_state_compatible_heuristic TA l) (boundstype_fun type) Strict_TRS c R)
        <+? (\<lambda> (lr,lr_rhs,q). showsl_lit (STR ''TA is not compatible with TRS\<newline>'') 
             \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
             \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
             \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''));
     state_compatible_eff_list TA rell (cover_bound_list_filter (\<lambda> l. \<not> rule_state_compatible_heuristic TA l) Matchbounds.match (Weak_TRS c_opt) c S)
        <+? (\<lambda> (lr,lr_rhs,q). showsl_lit (STR ''TA is not compatible with relative TRS\<newline>'') 
             \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
             \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
             \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''))
   } <+? (\<lambda> s. showsl_lit (STR ''problem during checking bounds of automaton\<newline>'') o get_renaming_info ren o showsl_lit (STR ''\<newline>error:\<newline>'') o s))"

definition check_bounds_generic_without_contains :: "('f :: {showl,linorder},'q :: {showl,linorder})bounds_info \<Rightarrow>
  ('f,'v :: {showl,linorder})rules \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check" where
  "check_bounds_generic_without_contains bi R S = (case get_integer_bounds_info bi of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
     let c_opt = construct_c_opt c R;
     let RS = R @ S;
     TA \<leftarrow> generate_ta_cond preTA rel;
     let rell = rel_checker rel;
     check_wf_trs RS;
     check (set qfin \<subseteq> rs.\<alpha> (ta_final_impl TA)) (showsl_lit (STR ''explicitly mentioned final states must be final''));
     (if isOK(check_left_linear_trs RS) then succeed else
       do {
         check_det preTA <+? (\<lambda> s. showsl_lit (STR ''for non left-linear TRS we require det. automaton\<newline>'') \<circ> s);
         rel_list \<leftarrow> relation_as_list rel;
         check_state_raise_consistent preTA rel_list
       });
     bounds_condition type RS;
     check_ta_bounded TA c;
     check (Bex (set qfin) (\<lambda> q. rs.memb q (ta_rhs_states_set TA))) (showsl_lit (STR ''did not find mentioned final state in TA''));
     state_compatible_eff_list TA rell (cover_bound_list_filter (\<lambda> l. \<not> rule_state_compatible_heuristic TA l) (boundstype_fun type) Strict_TRS c R)
        <+? (\<lambda> (lr,lr_rhs,q). showsl_lit (STR ''TA is not compatible with TRS\<newline>'')
             \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
             \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
             \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''));
     state_compatible_eff_list TA rell (cover_bound_list_filter (\<lambda> l. \<not> rule_state_compatible_heuristic TA l) Matchbounds.match (Weak_TRS c_opt) c S)
        <+? (\<lambda> (lr,lr_rhs,q). showsl_lit (STR ''TA is not compatible with relative TRS\<newline>'')
             \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
             \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
             \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''))
   } <+? (\<lambda> s. showsl_lit (STR ''problem during checking local bounds conditions of automaton\<newline>'') o get_renaming_info ren o showsl_lit (STR ''\<newline>error:\<newline>'') o s))"
 
lemma check_bounds_generic: assumes ok: "isOK(check_bounds_generic 
  (info :: ('f,'q :: {linorder,showl})bounds_info) (R :: ('f :: {linorder,showl},'v :: {linorder, showl})rules) 
  S F G)"
  and inf: "infinite (UNIV :: 'f set)"
  shows "(\<exists> ta rel qfin c c_opt. 
      bounds_impl R S (ta :: (integer,'f \<times> nat)ta) rel (boundstype_fun (boundstype info)) c c_opt (set F) (set G) qfin
      \<and> weak_kind_condition c c_opt (set R))
   \<and> isOK (bounds_condition (boundstype info) (R @ S))"
proof -
  obtain bi ren where ren: "get_integer_bounds_info info = (bi, ren)" (is "?e = _") by (cases ?e, auto)
  from boundstype_get_integer_bounds_info[OF this]
  have bt_info[simp]: "boundstype info = boundstype bi" by auto
  obtain type c qfin preTA rel where info: "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, blast+)
  let ?c_opt = "construct_c_opt c R"
  let ?rel = "rel_checker rel"
  let ?rell = "relation_of rel"
  note ok = ok[unfolded ren info check_bounds_generic_def, simplified]
  from ok obtain TA where TA: "generate_ta_cond preTA rel = return TA" by auto
  from generate_ta_cond[OF this] have inv: "ta_inv TA ?rel ?rell" and TA2: "TA = generate_ta preTA" by auto
  let ?filt = "\<lambda> l. \<not> rule_state_compatible_heuristic TA l"
  let ?sfilt = "\<lambda> l. (\<forall> u \<unlhd> l. ?filt u)"
  let ?relll = "relation_as_list rel"
  let ?e = "(boundstype_fun type)"
  let ?e2 = Matchbounds.match
  interpret ta_inv TA ?rel ?rell by fact
  have [simp]: "ta_of_ta preTA = TA'" unfolding TA2 generate_ta by simp
  note ok = ok[unfolded TA, simplified]
  from ok have 
    wf: "wf_trs (set R \<union> set S)"
    and choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA)
      \<and> isOK ?relll \<and> state_raise_consistent (ta_of TA) (set (projr ?relll))" (is "_ \<or> ?det")
    and qfin: "\<exists> q \<in> set qfin. rs.memb q (ta_rhs_states_set TA)"
    and c: "isOK(check_ta_bounded TA c)"
    and cond: "isOK(bounds_condition type (R @ S))"
    and contain: "isOK(ta_contains_impl (map (\<lambda>(f,n). (lift 0 f,n)) F) (map (\<lambda>(f,n). (lift 0 f,n)) G) TA qfin)"
    and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e Strict_TRS c R))"  
    and compat2: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e2 (Weak_TRS ?c_opt) c S))"  
    and final: "set qfin \<subseteq> ta_final (ta_of TA)"
    by (auto simp: ta_final)
  from choice have choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA) \<and> state_raise_consistent (ta_of TA) ?rell"
  proof 
    assume ?det
    have "state_raise_consistent (ta_of TA) ?rell"
    proof (cases rel)
      case Id_Relation
      with \<open>?det\<close> show ?thesis by (auto simp: state_raise_consistent_def)
    qed (insert \<open>?det\<close>, auto)
    with \<open>?det\<close> show ?thesis by simp
  qed auto
  from qfin have qfin: "\<exists> q \<in> set qfin. q \<in> ta_rhs_states TA'" using ta_rhs_states_set by (auto simp: rs.correct)
  let ?C = "cover_bound c ?e Strict_TRS (set R)"
  let ?Cf = "cover_bound c ?e Strict_TRS (set R) \<inter> {(l,r). ?sfilt l}"
  from c have c': "\<And> fn. fn \<in> set (rm.to_list (ta_rules_impl TA)) \<Longrightarrow> case fst fn of (f,n) \<Rightarrow> height f \<le> c"
    unfolding check_ta_bounded_def by auto
  {
    fix f n
    assume "(f,n) \<in> ta_syms TA'"
    then obtain rule where rule: "rule \<in> ta_rules TA'" and n: "r_sym rule = (f,n)"
      unfolding ta_syms_def by auto        
    let ?crule = "conv_ta_rule (ta_epss_impl TA) rule"
    from rule have crule: "?crule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'" by auto 
    from n have n: "r_sym_impl ?crule = (f,n)" by (cases rule, auto)
    let ?rm = "ta_rules_impl TA"
    from rm_set_lookup3[OF crule, unfolded n]
    obtain rls where "rm.\<alpha> ?rm (f,n) = Some rls" by (force simp: rm_\<alpha>_to_lookup)
    then have "map_of (rm.to_list ?rm) (f,n) = Some rls" by (auto simp: rm.correct)
    from map_of_SomeD[OF this]
    have "((f,n),rls) \<in> set (rm.to_list ?rm)" .
    from c'[OF this] have "height f \<le> c" by simp
  } note c = this
  then have tab: "ta_bounded TA' c" unfolding ta_bounded_def by auto
  note var_cond = wf[unfolded wf_trs_def]
  {
    fix U e ee
    assume sub: "set U \<subseteq> set (R @ S)" 
      and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt e ee c U))"
    let ?C = "cover_bound c e ee (set U)"
    let ?Cf = "?C \<inter> {(l, r). \<forall>u\<unlhd>l. \<not> rule_state_compatible_heuristic TA u}"
    have "state_compatible TA' ?rell ?Cf" 
    proof (rule state_compatible_eff_list[OF _ compat, unfolded cover_bound_list_filter])
      fix l r
      assume "(l,r) \<in> ?Cf"
      then have "(l,r) \<in> cover e ee (set U)" unfolding cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond sub
      show "vars_term r \<subseteq> vars_term l" by auto
    qed 
    then have compat: "state_compatible TA' ?rell ?C"
      by (rule remove_compatible_rules, insert rule_state_compatible_heuristic_subteq, blast)
  } note compat_conv = this
  from compat_conv[OF _ compat]
  have compat: "state_compatible TA' ?rell ?C" by auto
  from compat_conv[OF _ compat2]
  have compatS: "state_compatible TA' ?rell (cover_bound c Matchbounds.match (Weak_TRS ?c_opt) (set S))" by auto
  obtain fin rls eps where preTA: "preTA = Tree_Automaton fin rls eps" by (cases preTA, auto)
  from generate_ta_rules[of fin rls eps] have "ta_rules (ta_of TA) = set rls" using TA2 preTA by auto
  then have fin: "finite (ta_rules (ta_of TA))" by auto
  have wkc: "weak_kind_condition c ?c_opt (set R)" by simp
  have "bounds_impl R S TA' ?rell ?e c ?c_opt (set F) (set G) (set qfin)"
    by (unfold_locales, insert final choice fin compat compatS coherent tab qfin inf finite_set wf 
      ta_contains_impl[OF contain], auto)  
  with wkc have bounds: "\<exists> ta rel qfin c c_opt. bounds_impl R S (ta :: (integer,'f \<times> nat)ta) rel 
    (boundstype_fun (boundstype info)) c c_opt (set F) (set G) qfin
    \<and> weak_kind_condition c c_opt (set R)"  
    unfolding bt_info unfolding info by force
  from cond have cond: "isOK (bounds_condition (boundstype info) (R @ S))" using info by simp
  from bounds cond show ?thesis by blast
qed

lemma check_bounds_generic_exact:
  assumes ok: "isOK(check_bounds_generic
    (info :: ('f,'q :: {linorder,showl})bounds_info) (R :: ('f :: {linorder,showl},'v :: {linorder, showl})rules)
    S F G)"
    and inf: "infinite (UNIV :: 'f set)"
    and info_def: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel_info, ren)"
  shows "\<exists> rel c_opt.
      bounds_impl R S (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel (boundstype_fun (boundstype info)) c c_opt (set F) (set G) (set qfin)
      \<and> weak_kind_condition c c_opt (set R)
      \<and> isOK (bounds_condition (boundstype info) (R @ S))"
proof -
  from boundstype_get_integer_bounds_info[OF info_def]
  have bt_info[simp]: "boundstype info = type" by auto
  let ?c_opt = "construct_c_opt c R"
  let ?rel = "rel_checker rel_info"
  let ?rell = "relation_of rel_info"
  note ok = ok[unfolded info_def check_bounds_generic_def, simplified]
  from ok obtain TA where TA: "generate_ta_cond preTA rel_info = return TA" by auto
  from generate_ta_cond[OF this] have inv: "ta_inv TA ?rel ?rell" and TA2: "TA = generate_ta preTA" by auto
  let ?filt = "\<lambda> l. \<not> rule_state_compatible_heuristic TA l"
  let ?sfilt = "\<lambda> l. (\<forall> u \<unlhd> l. ?filt u)"
  let ?relll = "relation_as_list rel_info"
  let ?e = "(boundstype_fun type)"
  let ?e2 = Matchbounds.match
  interpret ta_inv TA ?rel ?rell by fact
  have [simp]: "ta_of_ta preTA = TA'" unfolding TA2 generate_ta by simp
  note ok = ok[unfolded TA, simplified]
  from ok have
    wf: "wf_trs (set R \<union> set S)"
    and choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA)
      \<and> isOK ?relll \<and> state_raise_consistent (ta_of TA) (set (projr ?relll))" (is "_ \<or> ?det")
    and qfin: "\<exists> q \<in> set qfin. rs.memb q (ta_rhs_states_set TA)"
    and c: "isOK(check_ta_bounded TA c)"
    and cond: "isOK(bounds_condition type (R @ S))"
    and contain: "isOK(ta_contains_impl (map (\<lambda>(f,n). (lift 0 f,n)) F) (map (\<lambda>(f,n). (lift 0 f,n)) G) TA qfin)"
    and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e Strict_TRS c R))"
    and compat2: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e2 (Weak_TRS ?c_opt) c S))"
    and final: "set qfin \<subseteq> ta_final (ta_of TA)"
    by (auto simp: ta_final)
  from choice have choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA) \<and> state_raise_consistent (ta_of TA) ?rell"
  proof
    assume ?det
    have "state_raise_consistent (ta_of TA) ?rell"
    proof (cases rel_info)
      case Id_Relation
      with \<open>?det\<close> show ?thesis by (auto simp: state_raise_consistent_def)
    qed (insert \<open>?det\<close>, auto)
    with \<open>?det\<close> show ?thesis by simp
  qed auto
  from qfin have qfin: "\<exists> q \<in> set qfin. q \<in> ta_rhs_states TA'" using ta_rhs_states_set by (auto simp: rs.correct)
  let ?C = "cover_bound c ?e Strict_TRS (set R)"
  let ?Cf = "cover_bound c ?e Strict_TRS (set R) \<inter> {(l,r). ?sfilt l}"
  from c have c': "\<And> fn. fn \<in> set (rm.to_list (ta_rules_impl TA)) \<Longrightarrow> case fst fn of (f,n) \<Rightarrow> height f \<le> c"
    unfolding check_ta_bounded_def by auto
  {
    fix f n
    assume "(f,n) \<in> ta_syms TA'"
    then obtain rule where rule: "rule \<in> ta_rules TA'" and n: "r_sym rule = (f,n)"
      unfolding ta_syms_def by auto
    let ?crule = "conv_ta_rule (ta_epss_impl TA) rule"
    from rule have crule: "?crule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'" by auto
    from n have n: "r_sym_impl ?crule = (f,n)" by (cases rule, auto)
    let ?rm = "ta_rules_impl TA"
    from rm_set_lookup3[OF crule, unfolded n]
    obtain rls where "rm.\<alpha> ?rm (f,n) = Some rls" by (force simp: rm_\<alpha>_to_lookup)
    then have "map_of (rm.to_list ?rm) (f,n) = Some rls" by (auto simp: rm.correct)
    from map_of_SomeD[OF this]
    have "((f,n),rls) \<in> set (rm.to_list ?rm)" .
    from c'[OF this] have "height f \<le> c" by simp
  } note c = this
  then have tab: "ta_bounded TA' c" unfolding ta_bounded_def by auto
  note var_cond = wf[unfolded wf_trs_def]
  {
    fix U e ee
    assume sub: "set U \<subseteq> set (R @ S)"
      and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt e ee c U))"
    let ?C = "cover_bound c e ee (set U)"
    let ?Cf = "?C \<inter> {(l, r). \<forall>u\<unlhd>l. \<not> rule_state_compatible_heuristic TA u}"
    have "state_compatible TA' ?rell ?Cf"
    proof (rule state_compatible_eff_list[OF _ compat, unfolded cover_bound_list_filter])
      fix l r
      assume "(l,r) \<in> ?Cf"
      then have "(l,r) \<in> cover e ee (set U)" unfolding cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond sub
      show "vars_term r \<subseteq> vars_term l" by auto
    qed
    then have compat: "state_compatible TA' ?rell ?C"
      by (rule remove_compatible_rules, insert rule_state_compatible_heuristic_subteq, blast)
  } note compat_conv = this
  from compat_conv[OF _ compat]
  have compat: "state_compatible TA' ?rell ?C" by auto
  from compat_conv[OF _ compat2]
  have compatS: "state_compatible TA' ?rell (cover_bound c Matchbounds.match (Weak_TRS ?c_opt) (set S))" by auto
  obtain fin rls eps where preTA: "preTA = Tree_Automaton fin rls eps" by (cases preTA, auto)
  from generate_ta_rules[of fin rls eps] have "ta_rules (ta_of TA) = set rls" using TA2 preTA by auto
  then have fin: "finite (ta_rules (ta_of TA))" by auto
  have wkc: "weak_kind_condition c ?c_opt (set R)" by simp
  have bounds: "bounds_impl R S TA' ?rell ?e c ?c_opt (set F) (set G) (set qfin)"
    by (unfold_locales, insert final choice fin compat compatS coherent tab qfin inf finite_set wf
      ta_contains_impl[OF contain], auto)
  show ?thesis
  proof (intro exI conjI)
    show "bounds_impl R S (ta_of (generate_ta preTA)) ?rell (boundstype_fun (boundstype info)) c ?c_opt (set F) (set G) (set qfin)"
      using bounds unfolding TA2 by simp
    show "weak_kind_condition c ?c_opt (set R)" by (rule wkc)
    show "isOK (bounds_condition (boundstype info) (R @ S))" using cond by simp
  qed
qed

lemma check_bounds_generic_without_contains_exact:
  assumes ok: "isOK(check_bounds_generic_without_contains
    (info :: ('f,'q :: {linorder,showl})bounds_info) (R :: ('f :: {linorder,showl},'v :: {linorder, showl})rules)
    S)"
    and info_def: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel_info, ren)"
  shows "\<exists>rel c_opt.
      (left_linear_trs (set (R @ S)) \<or>
        ta_det (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<and>
        state_raise_consistent (ta_of (generate_ta preTA)) rel)
      \<and> finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
        (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set R))
      \<and> state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
        (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))
      \<and> state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
      \<and> ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c
      \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)
      \<and> wf_trs (set R \<union> set S)
      \<and> isOK (bounds_condition (boundstype info) (R @ S))"
proof -
  from boundstype_get_integer_bounds_info[OF info_def]
  have bt_info[simp]: "boundstype info = type" by auto
  let ?c_opt = "construct_c_opt c R"
  let ?rel = "rel_checker rel_info"
  let ?rell = "relation_of rel_info"
  note ok = ok[unfolded info_def check_bounds_generic_without_contains_def, simplified]
  from ok obtain TA where TA: "generate_ta_cond preTA rel_info = return TA" by auto
  from generate_ta_cond[OF this] have inv: "ta_inv TA ?rel ?rell" and TA2: "TA = generate_ta preTA" by auto
  let ?filt = "\<lambda> l. \<not> rule_state_compatible_heuristic TA l"
  let ?sfilt = "\<lambda> l. (\<forall> u \<unlhd> l. ?filt u)"
  let ?relll = "relation_as_list rel_info"
  let ?e = "boundstype_fun type"
  let ?e2 = Matchbounds.match
  interpret ta_inv TA ?rel ?rell by fact
  have [simp]: "ta_of_ta preTA = TA'" unfolding TA2 generate_ta by simp
  note ok = ok[unfolded TA, simplified]
  from ok have
    wf: "wf_trs (set R \<union> set S)"
    and choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA)
      \<and> isOK ?relll \<and> state_raise_consistent (ta_of TA) (set (projr ?relll))" (is "_ \<or> ?det")
    and qfin: "\<exists> q \<in> set qfin. rs.memb q (ta_rhs_states_set TA)"
    and c: "isOK(check_ta_bounded TA c)"
    and cond: "isOK(bounds_condition type (R @ S))"
    and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e Strict_TRS c R))"
    and compat2: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt ?e2 (Weak_TRS ?c_opt) c S))"
    and final: "set qfin \<subseteq> ta_final (ta_of TA)"
    by (auto simp: ta_final)
  from choice have choice: "left_linear_trs (set (R @ S)) \<or> ta_det (ta_of TA) \<and> state_raise_consistent (ta_of TA) ?rell"
  proof
    assume ?det
    have "state_raise_consistent (ta_of TA) ?rell"
    proof (cases rel_info)
      case Id_Relation
      with \<open>?det\<close> show ?thesis by (auto simp: state_raise_consistent_def)
    qed (insert \<open>?det\<close>, auto)
    with \<open>?det\<close> show ?thesis by simp
  qed auto
  from qfin have qfin: "\<exists> q \<in> set qfin. q \<in> ta_rhs_states TA'" using ta_rhs_states_set by (auto simp: rs.correct)
  from c have c': "\<And> fn. fn \<in> set (rm.to_list (ta_rules_impl TA)) \<Longrightarrow> case fst fn of (f,n) \<Rightarrow> height f \<le> c"
    unfolding check_ta_bounded_def by auto
  {
    fix f n
    assume "(f,n) \<in> ta_syms TA'"
    then obtain rule where rule: "rule \<in> ta_rules TA'" and n: "r_sym rule = (f,n)"
      unfolding ta_syms_def by auto
    let ?crule = "conv_ta_rule (ta_epss_impl TA) rule"
    from rule have crule: "?crule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'" by auto
    from n have n: "r_sym_impl ?crule = (f,n)" by (cases rule, auto)
    let ?rm = "ta_rules_impl TA"
    from rm_set_lookup3[OF crule, unfolded n]
    obtain rls where "rm.\<alpha> ?rm (f,n) = Some rls" by (force simp: rm_\<alpha>_to_lookup)
    then have "map_of (rm.to_list ?rm) (f,n) = Some rls" by (auto simp: rm.correct)
    from map_of_SomeD[OF this]
    have "((f,n),rls) \<in> set (rm.to_list ?rm)" .
    from c'[OF this] have "height f \<le> c" by simp
  } note c = this
  then have tab: "ta_bounded TA' c" unfolding ta_bounded_def by auto
  note var_cond = wf[unfolded wf_trs_def]
  {
    fix U e ee
    assume sub: "set U \<subseteq> set (R @ S)"
      and compat: "isOK(state_compatible_eff_list TA ?rel (cover_bound_list_filter ?filt e ee c U))"
    let ?C = "cover_bound c e ee (set U)"
    let ?Cf = "?C \<inter> {(l, r). \<forall>u\<unlhd>l. \<not> rule_state_compatible_heuristic TA u}"
    have "state_compatible TA' ?rell ?Cf"
    proof (rule state_compatible_eff_list[OF _ compat, unfolded cover_bound_list_filter])
      fix l r
      assume "(l,r) \<in> ?Cf"
      then have "(l,r) \<in> cover e ee (set U)" unfolding cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond sub
      show "vars_term r \<subseteq> vars_term l" by auto
    qed
    then have "state_compatible TA' ?rell ?C"
      by (rule remove_compatible_rules, insert rule_state_compatible_heuristic_subteq, blast)
  } note compat_conv = this
  from compat_conv[OF _ compat]
  have compat: "state_compatible TA' ?rell (cover_bound c ?e Strict_TRS (set R))" by auto
  from compat_conv[OF _ compat2]
  have compatS: "state_compatible TA' ?rell (cover_bound c Matchbounds.match (Weak_TRS ?c_opt) (set S))" by auto
  obtain fin rls eps where preTA: "preTA = Tree_Automaton fin rls eps" by (cases preTA, auto)
  from generate_ta_rules[of fin rls eps] have "ta_rules (ta_of TA) = set rls" using TA2 preTA by auto
  then have fin: "finite (ta_rules (ta_of TA))" by auto
  show ?thesis
    by (intro exI[of _ ?rell] exI[of _ ?c_opt] conjI,
      insert choice fin compat compatS coherent tab qfin final wf cond TA2, auto)
qed

lemma check_bounds: assumes ok: "isOK(check_bounds_generic (info :: ('f,'q :: {linorder,showl})bounds_info) 
  (R :: ('f :: {linorder,showl},'v :: {linorder, showl})rules) []
  (funas_trs_list R) (funas_trs_list R))"
  and inf: "infinite (UNIV :: 'f set)"
  shows "SN (rstep (set R))"
proof -
  let ?S = "[]"
  let ?bt = "boundstype info"
  let ?F = "set (funas_trs_list R)"
  from check_bounds_generic[OF ok inf] obtain ta :: "(integer,'f \<times> nat)ta" and rel qfin c c_opt where 
    bounds: "bounds_impl R ?S ta rel (boundstype_fun ?bt) c c_opt ?F ?F qfin" 
    and cond: "isOK (bounds_condition ?bt R)" by auto
  interpret bounds_impl R ?S ta rel "boundstype_fun ?bt" c c_opt ?F ?F qfin by fact  
  show ?thesis
    by (rule e_bounds_impl[where cm = "Derivational_Complexity (funas_trs_list R)", 
        OF bounds_condition[OF cond]], insert wf, auto)
qed      

lemma check_bounds_complexity: assumes ok: "isOK(check_bounds_generic (info :: ('f,'q :: {linorder,showl})bounds_info) 
  (R :: ('f :: {linorder,showl},'v ::  {linorder,showl})rules) [] 
  (stackable_of_cm cm) (roots_of_cm cm))"
  and inf: "infinite (UNIV :: 'f set)"
  and bt: "boundstype info = Match"
  shows "deriv_bound_measure_class (rstep (set R)) cm (Comp_Poly 1)"
proof -
  let ?S = "[]"
  let ?scm = "stackable_of_cm cm"
  let ?rcm = "roots_of_cm cm"
  from check_bounds_generic[OF ok inf, unfolded bt] obtain ta :: "(integer,'f \<times> nat)ta" and rel qfin c c_opt where 
    bounds: "bounds_impl R ?S ta rel (boundstype_fun Match) c c_opt (set ?scm) (set ?rcm) qfin" 
    and cond: "isOK (bounds_condition Match R)" by auto
  interpret bounds_impl R ?S ta rel "boundstype_fun Match" c c_opt "set ?scm" "set ?rcm" qfin by fact
  from match_bounds_linear_impl[of cm] cond show ?thesis by auto
qed      

lemma check_bounds_complexity_rel: assumes ok: "isOK(check_bounds_generic (info :: ('f,'q :: {linorder,showl})bounds_info) 
  (R :: ('f :: {linorder,showl},'v ::  {linorder,showl})rules) S 
  (stackable_of_cm cm) (roots_of_cm cm))"
  and inf: "infinite (UNIV :: 'f set)"
  and bt: "boundstype info = Match"
  shows "deriv_bound_measure_class (relto (rstep (set R)) (rstep (set S))) cm (Comp_Poly 1)"
proof -
  let ?scm = "stackable_of_cm cm"
  let ?rcm = "roots_of_cm cm"
  from check_bounds_generic[OF ok inf, unfolded bt] obtain ta :: "(integer,'f \<times> nat)ta" and rel qfin c c_opt where 
    bounds: "bounds_impl R S ta rel (boundstype_fun Match) c c_opt (set ?scm) (set ?rcm) qfin" 
    and cond: "isOK (bounds_condition Match (R @ S))" 
    and wkc: "weak_kind_condition c c_opt (set R)" by auto
  interpret bounds_impl R S ta rel "boundstype_fun Match" c c_opt "set ?scm" "set ?rcm" qfin by fact
  show ?thesis
    by (rule match_bounds_linear_rel_impl[of cm], insert cond wkc, auto)
qed
end
  

(* silently convert weak to strict rules *)
definition
  bounds_tt ::
    "('tp, 'f, 'v :: {linorder,showl}) tp_ops \<Rightarrow>
    ('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    'tp \<Rightarrow> showsl check"
where
  "bounds_tt I info tp \<equiv> do {
      let r = tp_ops.rules I tp;
      let f = funas_trs_list r;
      check_bounds_generic info r [] f f
   }"

lemma bounds_tt: fixes info :: "('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I" and ok: "isOK (bounds_tt I info tp)"
  and inf: "infinite (UNIV :: 'f set)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  from check_bounds[OF ok[unfolded bounds_tt_def Let_def, simplified] inf]
    have SN: "SN_qrel (NFS tp, {}, set (R tp) \<union> set (Rw tp), {})" by simp
  show ?thesis unfolding qreltrs_sound
    by (rule SN_qrel_mono[OF _ _ _ SN]) simp_all
qed

definition
  bounds_rel_tt ::
    "('tp, 'f, 'v :: {showl,compare_order}) tp_ops \<Rightarrow>
    ('f::{showl,compare_order}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,'v)rules \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "bounds_rel_tt I info Rdelete tp \<equiv> do {
      let R = tp_ops.R I tp;
      let Rw = tp_ops.Rw I tp;
      let R2 = ceta_list_diff R Rdelete;
      check_subseteq Rdelete (tp_ops.rules I tp) \<comment> \<open>this is not required, just for early error detection\<close>
         <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' in current termination problem''));
      check (boundstype info = Match) (showsl_lit (STR ''relative termination bounds require boundstype match''));
      let all = tp_ops.rules I tp;
      check_bounds_generic info Rdelete (Rw @ R2) (funas_trs_list all) (funas_trs_list all);
      return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete))
   }  <+? (\<lambda> s. showsl_lit (STR ''problem in ensuring relative match boundedness of\<newline>'') \<circ>
        showsl_tp I tp \<circ> showsl_lit (STR ''\<newline>with deletion of rules\<newline>'') \<circ> showsl_trs Rdelete \<circ> s)"

lemma bounds_rel_tt: fixes info :: "('f::{showl,compare_order}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I" and res: "bounds_rel_tt I info Rdelete tp = return tp'"
  and inf: "infinite (UNIV :: 'f set)"
  and rec: "SN_qrel (tp_ops.qreltrs I tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  note isOK_if [simp]
  let ?R = "R tp"
  let ?Rw = "Rw tp"
  let ?diff = "ceta_list_diff ?R Rdelete"
  let ?union = "list_union ?Rw Rdelete"
  from res[unfolded bounds_rel_tt_def Let_def, simplified]
  have bt: "boundstype info = Match"
    and ok: "isOK (check_bounds_generic info Rdelete (?Rw @ ?diff) (funas_trs_list (rules tp)) (funas_trs_list (rules tp)))"
    and tp': "tp' = mk (NFS tp) (Q tp) ?diff ?union" by auto
  let ?cm = "Derivational_Complexity (funas_trs_list (rules tp))"
  have ok_cm: "isOK (check_bounds_generic info Rdelete (?Rw @ ?diff) (stackable_of_cm ?cm) (roots_of_cm ?cm))"
    using ok by simp
  from check_bounds_complexity_rel[OF ok_cm inf bt]
  have bnd: "deriv_bound_measure_class (relto (rstep (set Rdelete)) (rstep (set (?Rw @ ?diff))))
    ?cm (Comp_Poly 1)" .
  from deriv_bound_measure_class_SN_on[OF bnd]
  have bnd_SN_on: "SN_on (relto (rstep (set Rdelete)) (rstep (set (?Rw @ ?diff))))
    (terms_of ?cm)" .
  let ?F = "set (funas_trs_list (rules tp))"
  have sig_SN_on: "SN_on (relto (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff)))))
    (terms_of ?cm)"
    by (rule SN_on_mono[OF bnd_SN_on relto_mono], unfold sig_step_def, auto)
  have sig_rtrancl_source: "\<And>R s t. (s,t) \<in> (sig_step ?F R)\<^sup>* \<Longrightarrow> t \<in> terms_of ?cm \<Longrightarrow> s \<in> terms_of ?cm"
  proof -
    fix R s t
    assume st: "(s,t) \<in> (sig_step ?F R)\<^sup>*"
    from st show "t \<in> terms_of ?cm \<Longrightarrow> s \<in> terms_of ?cm"
    proof (induct)
      case base
      then show ?case .
    next
      case (step y z)
      have "y \<in> terms_of ?cm"
        using step.hyps(2) unfolding terms_of.simps sig_step_def by auto
      from step.hyps(3)[OF this] show ?case .
    qed
  qed
  have sig_source: "\<And>s t. (s,t) \<in> relto (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff))))
    \<Longrightarrow> s \<in> terms_of ?cm"
  proof -
    fix s t
    assume "(s,t) \<in> relto (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff))))"
    then obtain u v where su: "(s,u) \<in> (sig_step ?F (rstep (set (?Rw @ ?diff))))\<^sup>*"
      and uv: "(u,v) \<in> sig_step ?F (rstep (set Rdelete))" by auto
    have "u \<in> terms_of ?cm"
      using uv unfolding terms_of.simps sig_step_def by auto
    from sig_rtrancl_source[OF su this] show "s \<in> terms_of ?cm" .
  qed
  have sig_SN: "SN_rel (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff))))"
  proof (unfold SN_rel_defs SN_on_def, rule notI)
    assume "\<exists>f. f 0 \<in> UNIV \<and> chain (relto (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff))))) f"
    then obtain f where ch: "chain (relto (sig_step ?F (rstep (set Rdelete))) (sig_step ?F (rstep (set (?Rw @ ?diff))))) f" by auto
    from sig_source[OF ch[rule_format, of 0]]
    have "f 0 \<in> terms_of ?cm" .
    with sig_SN_on[unfolded SN_on_def] ch show False by blast
  qed
  from check_bounds_generic[OF ok_cm inf, unfolded bt]
  have cond: "isOK (bounds_condition Match (Rdelete @ (?Rw @ ?diff)))"
    by auto
  have cond_ms: "\<And> l r. (l, r) \<in> set (Rdelete @ (?Rw @ ?diff)) \<Longrightarrow>
    vars_term_ms r \<subseteq># vars_term_ms l"
    using cond by (auto simp: isOK_check_allm)
  have ms_vars_subset: "\<And> l r. vars_term_ms r \<subseteq># vars_term_ms l \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    by (metis set_mset_mono set_mset_vars_term_ms)
  have var_cond: "\<And> l r. (l, r) \<in> set (?Rw @ ?diff) \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    by (rule ms_vars_subset, rule cond_ms, auto)
  have funas_trs_list_set: "\<And>rs. funas_trs (set rs) = set (funas_trs_list rs)"
    by (induct_tac rs, auto simp: funas_trs_def funas_rule_def)
  have Rdelete: "set Rdelete \<subseteq> set (rules tp)"
    using res[unfolded bounds_rel_tt_def Let_def, simplified] by auto
  have weak_rules: "set (?Rw @ ?diff) \<subseteq> set (rules tp)"
    by auto
  have full_SN: "SN_rel (rstep (set Rdelete)) (rstep (set (?Rw @ ?diff)))"
  proof (rule sig_ext_relative_rewriting_var_cond[OF var_cond _ _ sig_SN])
    show "funas_trs (set Rdelete) \<subseteq> ?F"
      using Rdelete unfolding funas_trs_list_set[symmetric] funas_trs_def funas_rule_def by force
  next
    show "funas_trs (set (?Rw @ ?diff)) \<subseteq> ?F"
      using weak_rules unfolding funas_trs_list_set[symmetric] funas_trs_def funas_rule_def by force
  qed
  have bnd_SN: "SN_qrel (NFS tp, set (Q tp),
    set Rdelete \<inter> (set ?R \<union> set ?Rw), set ?R \<union> set ?Rw - set Rdelete)"
    unfolding SN_qrel_def split
    by (rule SN_rel_mono[OF _ _ full_SN], auto intro: qrstep_subset_rstep)
  from rec[unfolded tp', simplified]
  have rec: "SN_qrel (NFS tp, set (Q tp), set ?R - set Rdelete, set ?Rw \<union> set Rdelete)" .
  show ?thesis unfolding qreltrs_sound
  proof (rule SN_qrel_split[where D = "set Rdelete"])
    show "SN_qrel (NFS tp, set (Q tp), set Rdelete \<inter> (set ?R \<union> set ?Rw), set ?R \<union> set ?Rw - set Rdelete)"
      by (rule bnd_SN)
  next
    show "SN_qrel (NFS tp, set (Q tp), set ?R - set Rdelete, set ?Rw - set Rdelete)"
      by (rule SN_qrel_mono[OF _ _ _ rec], auto)
  qed
qed

definition
  rfc_narrows_impl :: "('f,string)rules \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)term list"
where
  "rfc_narrows_impl R t \<equiv> concat (map (\<lambda>p. let tp = t |_ p in
     if is_Fun tp then [(replace_at (t \<cdot> \<mu>1) p (r \<cdot> \<mu>2)).
       (l,r) \<leftarrow> R, (\<mu>1,\<mu>2) \<leftarrow> option_to_list (mgu_vd_string tp l)]
     else []) (poss_list t))"

definition
  rfc_narrow_step :: "('f,string)rules \<Rightarrow> ('f,string)trs"
where
  "rfc_narrow_step R \<equiv> {(t,u). u \<in> set (rfc_narrows_impl R t)}"

definition
  rfc_forward_closure :: "('f,string)rules \<Rightarrow> ('f,string)terms"
where
  "rfc_forward_closure R \<equiv> (rfc_narrow_step R)\<^sup>* `` rhss (set R)"

lemma rfc_narrows_impl:
  "set (rfc_narrows_impl R t) =
    {u. \<exists>p l r \<mu>1 \<mu>2. p \<in> poss t \<and> is_Fun (t |_ p) \<and> (l,r) \<in> set R \<and>
       mgu_vd_string (t |_ p) l = Some (\<mu>1,\<mu>2) \<and>
       u = replace_at (t \<cdot> \<mu>1) p (r \<cdot> \<mu>2)}"
  unfolding rfc_narrows_impl_def
  by (force simp: Let_def poss_list_sound)

lemma rfc_narrow_step_eq:
  "rfc_narrow_step R = narrow_step string_rename (set R)"
proof
  show "rfc_narrow_step R \<subseteq> narrow_step string_rename (set R)"
  proof
    fix st
    assume "st \<in> rfc_narrow_step R"
    then obtain s u p l r \<mu>1 \<mu>2 where
      st: "st = (s,u)" and p: "p \<in> poss s" and is_fun: "is_Fun (s |_ p)"
      and lr: "(l,r) \<in> set R"
      and mgu: "mgu_vd_string (s |_ p) l = Some (\<mu>1,\<mu>2)"
      and u: "u = replace_at (s \<cdot> \<mu>1) p (r \<cdot> \<mu>2)"
      unfolding rfc_narrow_step_def
      by (auto simp: rfc_narrows_impl)
    show "st \<in> narrow_step string_rename (set R)"
      unfolding st narrow_step_def narrows_r_p_s_def
      using p is_fun lr mgu[unfolded mgu_vd_string_def] u by fastforce
  qed
next
  show "narrow_step string_rename (set R) \<subseteq> rfc_narrow_step R"
  proof
    fix st
    assume "st \<in> narrow_step string_rename (set R)"
    then obtain s u lr p \<mu>1 \<mu>2 where
      st: "st = (s,u)" and p: "p \<in> poss s" and is_fun: "is_Fun (s |_ p)"
      and lr: "lr \<in> set R"
      and mgu: "mgu_vd string_rename (s |_ p) (fst lr) = Some (\<mu>1,\<mu>2)"
      and u: "u = replace_at (s \<cdot> \<mu>1) p (snd lr \<cdot> \<mu>2)"
      unfolding narrow_step_def narrows_r_p_s_def by auto
    obtain l r where lr_def: "lr = (l,r)" by force
    have lr': "(l,r) \<in> set R" using lr unfolding lr_def by simp
    have mgu': "mgu_vd_string (s |_ p) l = Some (\<mu>1,\<mu>2)"
      using mgu unfolding lr_def mgu_vd_string_def by simp
    have u': "u = replace_at (s \<cdot> \<mu>1) p (r \<cdot> \<mu>2)"
      using u unfolding lr_def by simp
    have "u \<in> {u. \<exists>p l r \<mu>1 \<mu>2. p \<in> poss s \<and> is_Fun (s |_ p) \<and> (l,r) \<in> set R \<and>
       mgu_vd_string (s |_ p) l = Some (\<mu>1,\<mu>2) \<and>
       u = replace_at (s \<cdot> \<mu>1) p (r \<cdot> \<mu>2)}"
      using p is_fun lr' mgu' u' by blast
    then have "u \<in> set (rfc_narrows_impl R s)"
      using rfc_narrows_impl[of R s] by simp
    then show "st \<in> rfc_narrow_step R"
      unfolding st rfc_narrow_step_def by auto
  qed
qed

lemma rfc_forward_closure_eq:
  "rfc_forward_closure R = right_forw_closure string_rename (set R)"
  unfolding rfc_forward_closure_def right_forw_closure_def rfc_narrow_step_eq
  by simp

definition
  rfc_initial_covers :: "('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_covers R I \<equiv> list_all (\<lambda>(l,r). r \<in> set I) R"

definition
  rfc_initial_closed :: "('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_closed R I \<equiv> list_all (\<lambda>t. list_all (\<lambda>u. u \<in> set I) (rfc_narrows_impl R t)) I"

definition
  rfc_initial_ground :: "('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_ground I \<equiv> list_all ground I"

definition
  rfc_initial_single_var :: "('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_single_var I \<equiv>
    list_all (\<lambda>t. length (remdups (vars_term_list t)) \<le> 1) I"

definition
  rfc_initial_funas :: "('f \<times> nat) list \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_funas F I \<equiv> list_all (\<lambda>t. funas_term t \<subseteq> set F) I"

definition
  rfc_term_accepted_with_tail_states_impl ::
    "'f itself \<Rightarrow> ('q :: linorder,'f :: linorder \<times> nat)ta_impl \<Rightarrow> 'q list \<Rightarrow> ('f,string)term \<Rightarrow> bool"
where
  "rfc_term_accepted_with_tail_states_impl _ TA qfin t \<equiv>
    list_all (\<lambda>q.
      \<not> rs.isEmpty
        (rs.inter (ta_final_impl TA)
          (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
            (map_vars_term (\<lambda>_. q) (lift_term 0 t))))) qfin"

definition
  rfc_initial_accepted_with_tail_states_impl ::
    "'f itself \<Rightarrow> ('q :: linorder,'f :: linorder \<times> nat)ta_impl \<Rightarrow> 'q list \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_accepted_with_tail_states_impl _ TA qfin I \<equiv>
    list_all (\<lambda>t. list_all (\<lambda>q.
      \<not> rs.isEmpty
        (rs.inter (ta_final_impl TA)
          (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
            (map_vars_term (\<lambda>_. q) (lift_term 0 t))))) qfin) I"

definition
  rfc_term_accepted_impl ::
    "('q :: linorder, ('f :: linorder) \<times> nat) ta_impl \<Rightarrow> ('f,string)term \<Rightarrow> bool"
where
  "rfc_term_accepted_impl TA t \<equiv>
    ground t \<and>
    \<not> rs.isEmpty
      (rs.inter (ta_final_impl TA)
        (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (adapt_vars (lift_term 0 t))))"

definition
  rfc_initial_accepted_impl ::
    "('q :: linorder, ('f :: linorder) \<times> nat) ta_impl \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_accepted_impl TA I \<equiv> list_all (rfc_term_accepted_impl TA) I"

lemma rfc_initial_covers:
  assumes "rfc_initial_covers R I"
  shows "rhss (set R) \<subseteq> set I"
  using assms unfolding rfc_initial_covers_def by (force simp: list_all_iff)

lemma rfc_initial_closed:
  assumes "rfc_initial_closed R I"
  shows "rfc_narrow_step R `` set I \<subseteq> set I"
proof
  fix u
  assume "u \<in> rfc_narrow_step R `` set I"
  then obtain t where t: "t \<in> set I" and step: "u \<in> set (rfc_narrows_impl R t)"
    unfolding rfc_narrow_step_def by auto
  from assms t have all: "\<forall>u\<in>set (rfc_narrows_impl R t). u \<in> set I"
    unfolding rfc_initial_closed_def by (auto simp: list_all_iff)
  with step show "u \<in> set I" by auto
qed

lemma rfc_forward_closure_subset_if_initial_closed:
  assumes rhs: "rfc_initial_covers R I"
    and closed: "rfc_initial_closed R I"
  shows "rfc_forward_closure R \<subseteq> set I"
proof
  fix t
  assume "t \<in> rfc_forward_closure R"
  then obtain s where s: "s \<in> rhss (set R)"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    unfolding rfc_forward_closure_def by auto
  from rfc_initial_covers[OF rhs] s have "s \<in> set I" by auto
  from steps this show "t \<in> set I"
  proof (induct)
    case base
    then show ?case .
  next
    case (step y z)
    from rfc_initial_closed[OF closed] step have "z \<in> rfc_narrow_step R `` set I" by auto
    with rfc_initial_closed[OF closed] show ?case by auto
  qed
qed

lemma rfc_initial_ground:
  assumes "rfc_initial_ground I"
  shows "\<And>t. t \<in> set I \<Longrightarrow> ground t"
  using assms unfolding rfc_initial_ground_def by (auto simp: list_all_iff)

lemma rfc_initial_single_var:
  assumes "rfc_initial_single_var I" and "t \<in> set I"
  shows "length (remdups (vars_term_list t)) \<le> 1"
  using assms unfolding rfc_initial_single_var_def by (auto simp: list_all_iff)

lemma rfc_initial_funas:
  assumes "rfc_initial_funas F I"
  shows "\<Union> (funas_term ` set I) \<subseteq> set F"
  using assms unfolding rfc_initial_funas_def by (auto simp: list_all_iff)

lemma one_var_term_vars_eq:
  assumes one: "length (remdups (vars_term_list t)) \<le> 1"
    and x: "x \<in> vars_term t"
    and y: "y \<in> vars_term t"
  shows "x = y"
proof -
  let ?vs = "remdups (vars_term_list t)"
  from x y have xvs: "x \<in> set ?vs" and yvs: "y \<in> set ?vs" by auto
  show ?thesis
  proof (cases ?vs)
    case Nil
    with xvs show ?thesis by simp
  next
    case outer: (Cons z zs)
    show ?thesis
    proof (cases zs)
      case Nil
      with outer xvs yvs show ?thesis by auto
    next
      case inner: (Cons w ws)
      from one outer inner have False by simp
      then show ?thesis ..
    qed
  qed
qed

lemma list_all_member:
  assumes "list_all P xs" and "x \<in> set xs"
  shows "P x"
  using assms by (induct xs) (auto simp: list_all_Cons_iff)

lemma lift_term_subst:
  "lift_term h (t \<cdot> \<sigma>) = lift_term h t \<cdot> (\<lambda>x. lift_term h (\<sigma> x))"
  by (induct t) auto

lemma ta_contains_stackable_state:
  assumes contain: "ta_contains F F TA Q"
    and ground: "ground t"
    and funas: "funas_term t \<subseteq> F"
  shows "\<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars t)"
  using ground funas
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have rec: "\<And>i. i < length ts \<Longrightarrow>
    \<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars (ts ! i))"
  proof -
    fix i
    assume i: "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    with Fun.prems have gt: "ground (ts ! i)" and ft: "funas_term (ts ! i) \<subseteq> F"
      by auto
    from Fun(1)[OF \<open>ts ! i \<in> set ts\<close> gt ft] show "\<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars (ts ! i))" .
  qed
  have "\<forall>i. \<exists>q. i < length ts \<longrightarrow> q \<in> Q \<and> q \<in> ta_res TA ((map adapt_vars ts) ! i)"
    using rec by auto
  from choice[OF this] obtain qs where qs:
    "\<And>i. i < length ts \<Longrightarrow> qs i \<in> Q \<and> qs i \<in> ta_res TA ((map adapt_vars ts) ! i)"
    by auto
  let ?qs = "map qs [0..<length ts]"
  have set_qs: "set ?qs \<subseteq> Q"
    unfolding set_conv_nth using qs by auto
  have sym: "(f, length ?qs) \<in> F"
    using Fun.prems by auto
  from contain[unfolded ta_contains_def ta_contains_aux_def] set_qs sym
  obtain q' q where q: "q \<in> Q" and rule: "(f ?qs \<rightarrow> q') \<in> ta_rules TA"
    and eps: "(q', q) \<in> (ta_eps TA)\<^sup>*"
    by blast
  have "q \<in> ta_res TA (adapt_vars (Fun f ts))"
    unfolding adapt_vars_simps ta_res.simps
    by (rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ ?qs],
        insert rule eps qs, auto)
  with q show ?case by blast
qed

lemma rfc_term_accepted_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and acc: "rfc_term_accepted_impl TA t"
  shows "lift_term 0 t \<in> (ta_lang (ta_of TA) :: ('f \<times> nat,string)terms)"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  from acc obtain q where gr: "ground t"
    and qfin: "q \<in> rs.\<alpha> (ta_final_impl TA)"
    and qres: "q \<in> rs.\<alpha> (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (adapt_vars (lift_term 0 t)))"
    unfolding rfc_term_accepted_impl_def by (auto simp: rs.correct)
  have "q \<in> ta_final TA'" using qfin by (simp add: ta_final)
  moreover have "q \<in> ta_res TA' (adapt_vars (lift_term 0 t))"
    using qres by (simp add: ta_res_impl)
  moreover have "ground (lift_term 0 t)" using gr by auto
  ultimately show ?thesis
    by (metis ta_langI2)
qed

lemma rfc_initial_accepted_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and acc: "rfc_initial_accepted_impl TA I"
  shows "lift_term 0 ` set I \<subseteq> (ta_lang (ta_of TA) :: ('f \<times> nat,string)terms)"
  using rfc_term_accepted_impl[OF inv] acc
  unfolding rfc_initial_accepted_impl_def by (auto simp: list_all_iff)

lemma rs_not_isEmpty_alpha_nonempty:
  assumes "\<not> rs.isEmpty A"
  shows "rs.\<alpha> A \<noteq> {}"
  using assms by (auto simp: rs.correct)

lemma rs_inter_memberD:
  assumes "x \<in> rs.\<alpha> (rs.inter A B)"
  shows "x \<in> rs.\<alpha> A" "x \<in> rs.\<alpha> B"
  using assms by (auto simp: rs.correct)

lemma rfc_term_accepted_with_tail_states_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and acc: "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    and q: "q \<in> set qfin"
  shows "\<exists>qf\<in>ta_final (ta_of TA).
    qf \<in> ta_res (ta_of TA) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  note acc_all = acc[unfolded rfc_term_accepted_with_tail_states_impl_def]
  note nonempty_impl = list_all_member[OF acc_all q]
  interpret ta_inv TA rel rell by (rule inv)
  note inter_ne = rs_not_isEmpty_alpha_nonempty[OF nonempty_impl]
  note ex_qf = iffD2[OF ex_in_conv inter_ne]
  from ex_qf show ?thesis
  proof
    fix qf
    assume qf_inter: "qf \<in> rs.\<alpha> (rs.inter (ta_final_impl TA)
      (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))))"
    note inter_parts = rs_inter_memberD[OF qf_inter]
    note qfin = inter_parts(1)
    note qres = inter_parts(2)
    show ?thesis
      using qfin qres by (auto simp: ta_final ta_res_impl)
  qed
qed

lemma rfc_initial_accepted_with_tail_states_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and acc: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TA qfin I"
    and t: "t \<in> set I"
    and q: "q \<in> set qfin"
  shows "\<exists>qf\<in>ta_final (ta_of TA).
    qf \<in> ta_res (ta_of TA) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from list_all_member[OF acc[unfolded rfc_initial_accepted_with_tail_states_impl_def] t]
  have acct: "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    unfolding rfc_term_accepted_with_tail_states_impl_def .
  from rfc_term_accepted_with_tail_states_impl[OF inv acct q] show ?thesis .
qed

lemma adapt_vars_lift_term_subst:
  "adapt_vars (lift_term h (t \<cdot> \<sigma>)) =
    lift_term h t \<cdot> (\<lambda>x. adapt_vars (lift_term h (\<sigma> x)))"
  by (induct t) auto

lemma rfc_term_instance_accepted_with_tail_state:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
    and \<sigma> :: "string \<Rightarrow> ('f,string)term"
  assumes inv: "ta_inv TA rel rell"
    and acc: "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    and q: "q \<in> set qfin"
    and qvars: "\<And>x. x \<in> vars_term t \<Longrightarrow>
      q \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (\<sigma> x)))"
    and gvars: "\<And>x. x \<in> vars_term t \<Longrightarrow> ground (\<sigma> x)"
  shows "lift_term 0 (t \<cdot> \<sigma>) \<in> (ta_lang (ta_of TA) :: ('f \<times> nat,string)terms)"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  from rfc_term_accepted_with_tail_states_impl[OF inv acc q]
  obtain qf where qfin: "qf \<in> ta_final (ta_of TA)"
    and qres: "qf \<in> ta_res (ta_of TA) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    by auto
  have vars_lift: "\<And>x. x \<in> vars_term (lift_term 0 t) \<Longrightarrow> x \<in> vars_term t"
    by (induct t) auto
  have subst_res: "qf \<in> ta_res (ta_of TA)
      (lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x))))"
    by (rule ta_res_subst[OF _ qres], insert qvars vars_lift, auto)
  have ground_inst: "ground (lift_term 0 (t \<cdot> \<sigma>))"
    using gvars by (induct t) auto
  have subst_id: "adapt_vars (lift_term 0 (t \<cdot> \<sigma>)) =
      lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x)))"
    by (rule adapt_vars_lift_term_subst)
  have qres_inst: "qf \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (t \<cdot> \<sigma>)))"
    using subst_res unfolding subst_id .
  show ?thesis
    by (rule ta_langI2[OF ground_inst qfin qres_inst])
qed

lemma ta_contains_stackable_state_aux:
  assumes contain: "ta_contains_aux F Q TA Q"
    and ground: "ground t"
    and funas: "funas_term t \<subseteq> F"
  shows "\<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars t)"
  using ground funas
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have rec: "\<And>i. i < length ts \<Longrightarrow>
    \<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars (ts ! i))"
  proof -
    fix i
    assume i: "i < length ts"
    then have "ts ! i \<in> set ts" by auto
    with Fun.prems have gt: "ground (ts ! i)" and ft: "funas_term (ts ! i) \<subseteq> F"
      by auto
    from Fun(1)[OF \<open>ts ! i \<in> set ts\<close> gt ft] show "\<exists>q\<in>Q. q \<in> ta_res TA (adapt_vars (ts ! i))" .
  qed
  have "\<forall>i. \<exists>q. i < length ts \<longrightarrow> q \<in> Q \<and> q \<in> ta_res TA ((map adapt_vars ts) ! i)"
    using rec by auto
  from choice[OF this] obtain qs where qs:
    "\<And>i. i < length ts \<Longrightarrow> qs i \<in> Q \<and> qs i \<in> ta_res TA ((map adapt_vars ts) ! i)"
    by auto
  let ?qs = "map qs [0..<length ts]"
  have set_qs: "set ?qs \<subseteq> Q"
    unfolding set_conv_nth using qs by auto
  have sym: "(f, length ?qs) \<in> F"
    using Fun.prems by auto
  from contain[unfolded ta_contains_aux_def] set_qs sym
  obtain q' q where q: "q \<in> Q" and rule: "(f ?qs \<rightarrow> q') \<in> ta_rules TA"
    and eps: "(q', q) \<in> (ta_eps TA)\<^sup>*"
    by blast
  have "q \<in> ta_res TA (adapt_vars (Fun f ts))"
    unfolding adapt_vars_simps ta_res.simps
    by (rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ ?qs],
        insert rule eps qs, auto)
  with q show ?case by blast
qed

lemma rfc_term_instance_accepted_stackable:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat)ta_impl"
    and \<sigma> :: "string \<Rightarrow> ('f,string)term"
  assumes inv: "ta_inv TA rel rell"
    and contain: "ta_contains_aux F (set qfin) (ta_of TA) (set qfin)"
    and qfin_ne: "qfin \<noteq> []"
    and acc: "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    and one: "length (remdups (vars_term_list t)) \<le> 1"
    and gvars: "\<And>x. x \<in> vars_term t \<Longrightarrow> ground (\<sigma> x)"
    and fvars: "\<And>x. x \<in> vars_term t \<Longrightarrow> funas_term (lift_term 0 (\<sigma> x)) \<subseteq> F"
  shows "lift_term 0 (t \<cdot> \<sigma>) \<in> (ta_lang (ta_of TA) :: ('f \<times> nat,string)terms)"
proof (cases "vars_term t = {}")
  case True
  then obtain q where q: "q \<in> set qfin"
    using qfin_ne by (cases qfin) auto
  have qvars: "\<And>x. x \<in> vars_term t \<Longrightarrow>
      q \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (\<sigma> x)))"
    using True by auto
  show ?thesis
    by (rule rfc_term_instance_accepted_with_tail_state[OF inv acc q qvars gvars])
next
  case False
  then obtain x where x: "x \<in> vars_term t" by auto
  have gx: "ground (lift_term 0 (\<sigma> x))"
    using gvars[OF x] by auto
  from ta_contains_stackable_state_aux[OF contain gx fvars[OF x]]
  obtain q where q: "q \<in> set qfin"
    and qx: "q \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (\<sigma> x)))"
    by auto
  have qvars: "\<And>y. y \<in> vars_term t \<Longrightarrow>
      q \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (\<sigma> y)))"
  proof -
    fix y
    assume y: "y \<in> vars_term t"
    from one_var_term_vars_eq[OF one y x] have "y = x" .
    with qx show "q \<in> ta_res (ta_of TA) (adapt_vars (lift_term 0 (\<sigma> y)))" by simp
  qed
  show ?thesis
    by (rule rfc_term_instance_accepted_with_tail_state[OF inv acc q qvars gvars])
qed

lemma rfc_term_instance_accepted_stackable_sem:
  fixes TA :: "('q,'f \<times> nat)ta"
    and \<sigma> :: "string \<Rightarrow> ('f,string)term"
  assumes contain: "ta_contains_aux F Q TA Q"
    and final: "Q \<subseteq> ta_final TA"
    and qfin_ne: "Q \<noteq> {}"
    and acc: "\<And>q. q \<in> Q \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    and one: "length (remdups (vars_term_list t)) \<le> 1"
    and gvars: "\<And>x. x \<in> vars_term t \<Longrightarrow> ground (\<sigma> x)"
    and fvars: "\<And>x. x \<in> vars_term t \<Longrightarrow> funas_term (lift_term 0 (\<sigma> x)) \<subseteq> F"
  shows "lift_term 0 (t \<cdot> \<sigma>) \<in> (ta_lang TA :: ('f \<times> nat,string)terms)"
proof (cases "vars_term t = {}")
  case True
  then obtain q where q: "q \<in> Q" using qfin_ne by auto
  from acc[OF q] obtain qf where qfin: "qf \<in> ta_final TA"
    and qres: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    by auto
  have subst_res: "qf \<in> ta_res TA
      (lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x))))"
    by (rule ta_res_subst[OF _ qres], insert True, auto)
  have ground_inst: "ground (lift_term 0 (t \<cdot> \<sigma>))"
    using True by (induct t) auto
  have subst_id: "adapt_vars (lift_term 0 (t \<cdot> \<sigma>)) =
      lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x)))"
    by (rule adapt_vars_lift_term_subst)
  have qres_inst: "qf \<in> ta_res TA (adapt_vars (lift_term 0 (t \<cdot> \<sigma>)))"
    using subst_res unfolding subst_id .
  show ?thesis
    by (rule ta_langI2[OF ground_inst qfin qres_inst])
next
  case False
  then obtain x where x: "x \<in> vars_term t" by auto
  have gx: "ground (lift_term 0 (\<sigma> x))"
    using gvars[OF x] by auto
  from ta_contains_stackable_state_aux[OF contain gx fvars[OF x]]
  obtain q where q: "q \<in> Q"
    and qx: "q \<in> ta_res TA (adapt_vars (lift_term 0 (\<sigma> x)))"
    by auto
  from acc[OF q] obtain qf where qfin: "qf \<in> ta_final TA"
    and qres: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    by auto
  have qvars: "\<And>y. y \<in> vars_term (lift_term 0 t) \<Longrightarrow>
      q \<in> ta_res TA (adapt_vars (lift_term 0 (\<sigma> y)))"
  proof -
    fix y
    assume y: "y \<in> vars_term (lift_term 0 t)"
    then have yt: "y \<in> vars_term t" by (induct t) auto
    from one_var_term_vars_eq[OF one yt x] have "y = x" .
    with qx show "q \<in> ta_res TA (adapt_vars (lift_term 0 (\<sigma> y)))" by simp
  qed
  have subst_res: "qf \<in> ta_res TA
      (lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x))))"
    by (rule ta_res_subst[OF qvars qres])
  have ground_inst: "ground (lift_term 0 (t \<cdot> \<sigma>))"
    using gvars by (induct t) auto
  have subst_id: "adapt_vars (lift_term 0 (t \<cdot> \<sigma>)) =
      lift_term 0 t \<cdot> (\<lambda>x. adapt_vars (lift_term 0 (\<sigma> x)))"
    by (rule adapt_vars_lift_term_subst)
  have qres_inst: "qf \<in> ta_res TA (adapt_vars (lift_term 0 (t \<cdot> \<sigma>)))"
    using subst_res unfolding subst_id .
  show ?thesis
    by (rule ta_langI2[OF ground_inst qfin qres_inst])
qed

lemma rfc_bounds_impl:
  fixes R S :: "('f,string)rules"
    and TA :: "('q,'f \<times> nat)ta"
    and rel :: "'q rel"
    and I :: "('f,string)term list"
  assumes choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel (cover_bound c e Strict_TRS (set R))"
    and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))"
    and coh: "state_coherent TA rel"
    and tab: "ta_bounded TA c"
    and qfin: "\<exists>q\<in>qfin. q \<in> ta_rhs_states TA"
    and qfin_final: "qfin \<subseteq> ta_final TA"
    and inf: "infinite (UNIV :: 'f set)"
    and wf: "wf_trs (set R \<union> set S)"
    and SN: "locally_terminating (cover e Strict_TRS (set R) \<union> Matchbounds.raise)"
    and rhs_lin: "\<And>lr. lr \<in> set R \<Longrightarrow> linear_term (snd lr)"
    and initial_covers: "rfc_initial_covers R I"
    and initial_closed: "rfc_initial_closed R I"
    and initial_single: "rfc_initial_single_var I"
    and initial_acc: "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  shows "SN (rstep (set R))"
proof -
  let ?RR = "set R"
  let ?RFC = "rfc_forward_closure R"
  let ?lz = "(\<lambda>(f,n). (lift 0 f,n))"
  from wf have wf_R: "wf_trs ?RR"
    unfolding wf_trs_def by auto
  from wf[unfolded wf_trs_def] have varcond: "\<And>l r. (l,r) \<in> ?RR \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    by auto
  from rfc_forward_closure_subset_if_initial_closed[OF initial_covers initial_closed]
  have RFC_I: "?RFC \<subseteq> set I" .
  have empty_contain: "ta_contains (?lz ` {}) (?lz ` {}) TA qfin"
    unfolding ta_contains_def ta_contains_aux_def by auto
  from create_constant_in_ta_two[
    where G = "{}" and H = "{}",
    OF fin coh _ _ empty_contain qfin_final qfin tab inf choice compat compat2]
  obtain q const F F' TA' where q_in: "q \<in> qfin"
    and comp: "state_compatible TA' rel (cover e Strict_TRS ?RR)"
    and coh': "state_coherent TA' rel"
    and choice': "left_linear_trs (?RR \<union> set S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    and tab': "ta_bounded TA' c"
    and TA': "TA' = \<lparr> ta_final = ta_final TA,
      ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
    by blast
  have choice_R: "left_linear_trs (cover e Strict_TRS ?RR) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    using choice' cover_left_linear unfolding left_linear_trs_union by blast
  have finTA': "finite (ta_rules TA')" unfolding TA' using fin by auto
  have finF: "finite ((\<Union>(funas_term ` set I)) \<union> {(const,0)})"
    using finite_funas_term by auto
  have finR: "finite ?RR" by simp
  let ?\<sigma> = "\<lambda>_. Fun const []"
  let ?L = "{t \<cdot> ?\<sigma> | t. t \<in> set I}"
  have final_TA': "qfin \<subseteq> ta_final TA'" using qfin_final unfolding TA' by auto
  have qfin_ne: "qfin \<noteq> {}" using qfin by auto
  have acc_TA': "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final TA'. qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  proof -
    fix t q0
    assume t: "t \<in> set I" and q0: "q0 \<in> qfin"
    from initial_acc[OF t q0] obtain qf where qf: "qf \<in> ta_final TA"
      and res: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q0) (lift_term 0 t))"
      by auto
    have res': "qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q0) (lift_term 0 t))"
      using ta_res_mono'[of TA TA'] res unfolding TA' by auto
    show "\<exists>qf\<in>ta_final TA'. qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q0) (lift_term 0 t))"
      using qf res' unfolding TA' by auto
  qed
  have lift_L: "lift_term 0 ` ?L \<subseteq> (ta_lang TA' :: ('f \<times> nat,string)terms)"
  proof
    fix lt :: "('f \<times> nat,string)term"
    assume "lt \<in> lift_term 0 ` ?L"
    then obtain t where t: "t \<in> set I" and lt: "lt = lift_term 0 (t \<cdot> ?\<sigma>)"
      by auto
    from q_in have const_res: "q \<in> ta_res TA' (Fun (const,0) [])"
      unfolding TA' by auto
    from acc_TA'[OF t q_in] obtain qf where qf: "qf \<in> ta_final TA'"
      and qres: "qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      by auto
    have qvars: "\<And>x. x \<in> vars_term (lift_term 0 t) \<Longrightarrow>
        q \<in> ta_res TA' (Fun (const,0) [])"
      using const_res by auto
    have subst_res: "qf \<in> ta_res TA'
        (lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) []))"
      by (rule ta_res_subst[OF qvars qres])
    have ground_inst: "ground (lift_term 0 (t \<cdot> ?\<sigma>))"
      by (induct t) auto
    have subst_id: "adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)) =
        lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) [])"
      by (simp add: adapt_vars_lift_term_subst)
    have qres_inst: "qf \<in> ta_res TA' (adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)))"
      using subst_res unfolding subst_id .
    show "lt \<in> (ta_lang TA' :: ('f \<times> nat,string)terms)"
      unfolding lt by (rule ta_langI2[OF ground_inst qf qres_inst])
  qed
  have SN_L: "SN_on (rstep ?RR) ?L"
  proof (rule Matchbounds_Impl.e_bounds[
      where TA = TA' and rel = rel and c = c and R = "cover e Strict_TRS ?RR"
        and L = ?L and F = "(\<Union>(funas_term ` set I)) \<union> {(const,0)}" and RR = ?RR and e = e])
    show "left_linear_trs (cover e Strict_TRS ?RR) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
      by (rule choice_R)
    show "finite (ta_rules TA')" by (rule finTA')
    show "state_compatible TA' rel (cover e Strict_TRS ?RR)" by (rule comp)
    show "state_coherent TA' rel" by (rule coh')
    show "lift_term 0 ` ?L \<subseteq> (ta_lang TA' :: ('f \<times> nat,string)terms)"
      using lift_L .
    show "ta_bounded TA' c" by (rule tab')
    show "locally_terminating (cover e Strict_TRS ?RR \<union> Matchbounds.raise)" by (rule SN)
    show "finite ((\<Union>(funas_term ` set I)) \<union> {(const,0)})" by (rule finF)
    show "finite ?RR" by (rule finR)
    show "cover e Strict_TRS ?RR = cover e Strict_TRS ?RR" by simp
    show "\<And>l r. (l, r) \<in> ?RR \<Longrightarrow> vars_term r \<subseteq> vars_term l" by (rule varcond)
	    show "\<Union> (funas_term ` ?L) \<subseteq> (\<Union>(funas_term ` set I)) \<union> {(const,0)}"
	    proof (rule Union_least)
	      fix A
	      assume A: "A \<in> funas_term ` ?L"
	      from A show "A \<subseteq> (\<Union>(funas_term ` set I)) \<union> {(const,0)}"
	      proof (rule imageE)
	        fix u
	        assume Aeq: "A = funas_term u" and uL: "u \<in> ?L"
	        from uL obtain t where u: "u = t \<cdot> ?\<sigma>" and t: "t \<in> set I"
	          by auto
	        show "A \<subseteq> (\<Union>(funas_term ` set I)) \<union> {(const,0)}"
	        proof
	          fix fn
	          assume "fn \<in> A"
	          with Aeq have fn: "fn \<in> funas_term u" by simp
	          from funas_term_const_subst[of t const] fn t
	          show "fn \<in> (\<Union>(funas_term ` set I)) \<union> {(const,0)}"
	            unfolding u by auto
	        qed
	      qed
	    qed
  qed
  have SN_RFC: "SN_on (rstep ?RR) ?RFC"
  proof
    fix f
    assume f0: "f 0 \<in> ?RFC" and steps: "\<forall>i. (f i, f (Suc i)) \<in> rstep ?RR"
    from RFC_I f0 have f0I: "f 0 \<in> set I" by auto
    have inst: "f 0 \<cdot> ?\<sigma> \<in> ?L" using f0I by auto
	    have "SN_on (rstep ?RR) {f 0 \<cdot> ?\<sigma>}"
	      by (rule SN_on_subset2[OF _ SN_L], insert inst, auto)
    from SNinstance_imp_SN[OF this] steps f0 show False
      unfolding SN_on_def by auto
  qed
  from right_linear_SN_rstep_RFC[OF wf_R rhs_lin, of string_rename]
  show ?thesis
    unfolding rfc_forward_closure_eq[symmetric]
    using SN_RFC by blast
qed

definition
  rfc_bounds_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    'tp \<Rightarrow> showsl check"
where
  "rfc_bounds_tt I info initial_terms tp \<equiv> (case get_integer_bounds_info info of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
      TA \<leftarrow> generate_ta_cond preTA rel;
      check (tp_ops.Q_empty I tp) (showsl_lit (STR ''RFC bounds currently require an empty Q component''));
      check (tp_ops.Rw I tp = []) (showsl_lit (STR ''RFC bounds currently require no weak rules''));
      check (\<not> tp_ops.nfs I tp) (showsl_lit (STR ''RFC bounds currently certify full rewriting, not innermost rewriting''));
	      check_wf_trs (tp_ops.R I tp);
	      check (list_all (\<lambda>(l,r). linear_term r) (tp_ops.R I tp))
	        (showsl_lit (STR ''RFC bounds require right-linear rules''));
	      check (rfc_initial_single_var initial_terms)
	        (showsl_lit (STR ''RFC bounds finite initial language templates must contain at most one variable''));
	      check (rfc_initial_covers (tp_ops.R I tp) initial_terms)
	        (showsl_lit (STR ''RFC initial language does not contain all right-hand sides''));
	      check (rfc_initial_closed (tp_ops.R I tp) initial_terms)
	        (showsl_lit (STR ''RFC initial language is not closed under one-step right-forward narrowing''));
	      check (rfc_initial_accepted_with_tail_states_impl TYPE('f) TA qfin initial_terms)
	        (showsl_lit (STR ''RFC bounds finite initial language is not accepted by the automaton for all tail states''));
	      check_bounds_generic_without_contains info (tp_ops.R I tp) []
	   })"

lemma rfc_bounds_tt:
  fixes info :: "('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I" and ok: "isOK (rfc_bounds_tt I info initial_terms tp)"
  and inf: "infinite (UNIV :: 'f set)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  obtain bi ren where ren: "get_integer_bounds_info info = (bi, ren)"
    by (cases "get_integer_bounds_info info", auto)
	  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
	    by (cases bi, auto)
	  have info_eq: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel, ren)"
	    using ren info' by simp
	  from ok[unfolded rfc_bounds_tt_def ren info' Let_def]
	  obtain TA where TA: "generate_ta_cond preTA rel = return TA"
	    and okb: "isOK (check_bounds_generic_without_contains info (R tp) [])"
	    by auto
	  from generate_ta_cond[OF TA] have inv: "ta_inv TA (rel_checker rel) (relation_of rel)"
	    and TA_gen: "TA = generate_ta preTA" by auto
	  from ok[unfolded rfc_bounds_tt_def ren info' Let_def]
	  have Q: "set (Q tp) = {}" and Rw: "set (Rw tp) = {}"
	    and nfs: "\<not> NFS tp"
	    and rhs_lin_list: "list_all (\<lambda>(l, r). linear_term r) (R tp)"
	    and initial_single: "rfc_initial_single_var initial_terms"
	    and initial_covers: "rfc_initial_covers (R tp) initial_terms"
	    and initial_closed: "rfc_initial_closed (R tp) initial_terms"
	    and initial_acc_proj: "rfc_initial_accepted_with_tail_states_impl TYPE('f)
	      (projr (generate_ta_cond preTA rel)) qfin initial_terms"
	    by (auto simp: Q_empty_sound)
	  have rhs_lin: "\<And>lr. lr \<in> set (R tp) \<Longrightarrow> linear_term (snd lr)"
	    using rhs_lin_list by (auto simp: list_all_iff split: prod.splits)
	  have initial_acc_impl: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TA qfin initial_terms"
	    using initial_acc_proj TA by simp
	  from check_bounds_generic_without_contains_exact[
	    where R = "(R tp :: ('f,string)rules)"
	      and S = "([] :: ('f,string)rules)"
	      and info = info
	      and type = type
	      and c = c
	      and qfin = qfin
	      and preTA = preTA
	      and rel_info = rel
	      and ren = ren,
	    OF okb info_eq]
	  obtain b_rel where choice_b: "left_linear_trs (set (R tp @ [])) \<or>
	      ta_det (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<and>
	      state_raise_consistent (ta_of (generate_ta preTA)) b_rel"
	    and fin_b: "finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))"
	    and compat_b: "state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel
	      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))"
	    and coh_b: "state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel"
	    and tab_b: "ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c"
	    and qfin_b: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
	    and qfin_final_b: "set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
	    and wf_b: "wf_trs (set (R tp) \<union> set [])"
	    and cond_raw: "isOK (bounds_condition (boundstype info) (R tp @ []))"
	  proof -
	    assume cont: "\<And>b_rel.
	      left_linear_trs (set (R tp @ [])) \<or>
	      ta_det (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<and>
	      state_raise_consistent (ta_of (generate_ta preTA)) b_rel \<Longrightarrow>
	      finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)) \<Longrightarrow>
	      state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel
	        (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp))) \<Longrightarrow>
	      state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel \<Longrightarrow>
	      ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c \<Longrightarrow>
	      (\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)) \<Longrightarrow>
	      set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<Longrightarrow>
	      wf_trs (set (R tp) \<union> set []) \<Longrightarrow>
	      isOK (bounds_condition (boundstype info) (R tp @ [])) \<Longrightarrow> thesis"
	    from check_bounds_generic_without_contains_exact[
	      where R = "(R tp :: ('f,string)rules)"
	        and S = "([] :: ('f,string)rules)"
	        and info = info
	        and type = type
	        and c = c
	        and qfin = qfin
	        and preTA = preTA
	        and rel_info = rel
	        and ren = ren,
	      OF okb info_eq]
	    show thesis
	    proof (elim exE conjE)
	      fix rel0 c_opt0
	      assume choice0: "left_linear_trs (set (R tp @ [])) \<or>
	        ta_det (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<and>
	        state_raise_consistent (ta_of (generate_ta preTA)) rel0"
	        and fin0: "finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))"
	        and compat0: "state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel0
	          (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))"
	        and coh0: "state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel0"
	        and tab0: "ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c"
	        and qfin0: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
	        and qfin_final0: "set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
	        and wf0: "wf_trs (set (R tp) \<union> set [])"
	        and cond0: "isOK (bounds_condition (boundstype info) (R tp @ []))"
	      show thesis
	      proof (rule cont[of rel0])
	        show "left_linear_trs (set (R tp @ [])) \<or>
	          ta_det (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) \<and>
	          state_raise_consistent (ta_of (generate_ta preTA)) rel0" by (rule choice0)
	        show "finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))" by (rule fin0)
	        show "state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel0
	          (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))" by (rule compat0)
	        show "state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel0" by (rule coh0)
	        show "ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c" by (rule tab0)
	        show "\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)" by (rule qfin0)
	        show "set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)" by (rule qfin_final0)
	        show "wf_trs (set (R tp) \<union> set [])" by (rule wf0)
	        show "isOK (bounds_condition (boundstype info) (R tp @ []))" by (rule cond0)
	      qed
	    qed
	  qed
	  have cond: "isOK (bounds_condition (boundstype info) (R tp))"
	    using cond_raw by simp
	  have initial_acc: "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
	      \<exists>qf\<in>ta_final (ta_of (generate_ta preTA)).
	        qf \<in> ta_res (ta_of (generate_ta preTA)) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
	  proof -
	    fix t q
	    assume t: "t \<in> set initial_terms" and q: "q \<in> set qfin"
	    from rfc_initial_accepted_with_tail_states_impl[OF inv initial_acc_impl t q]
	    show "\<exists>qf\<in>ta_final (ta_of (generate_ta preTA)).
	        qf \<in> ta_res (ta_of (generate_ta preTA)) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
	      unfolding TA_gen .
	  qed
	  have wf_R: "wf_trs (set (R tp))" using wf_b by simp
	  have local_SN: "locally_terminating
	      (cover (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)) \<union> Matchbounds.raise)"
	    using bounds_condition[OF cond] wf_R by auto
	  have SN_r: "SN (rstep (set (R tp)))"
	  proof (rule rfc_bounds_impl[
	      where R = "R tp" and S = "[]" and TA = "(ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
	        and rel = b_rel and e = "boundstype_fun (boundstype info)" and c = c and c_opt = None
	        and qfin = "set qfin" and I = initial_terms])
	    show "left_linear_trs (set (R tp @ [])) \<or>
	      ta_det (ta_of (generate_ta preTA)) \<and>
	      state_raise_consistent (ta_of (generate_ta preTA)) b_rel" by (rule choice_b)
	    show "finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))" by (rule fin_b)
	    show "state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel
	      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))" by (rule compat_b)
	    show "state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel
	      (cover_bound c Matchbounds.match (Weak_TRS None) (set []))"
	      unfolding cover_bound_def state_compatible_def by auto
	    show "state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) b_rel" by (rule coh_b)
	    show "ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c" by (rule tab_b)
	    show "\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)" by (rule qfin_b)
	    show "set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)" by (rule qfin_final_b)
	    show "infinite (UNIV :: 'f set)" by (rule inf)
	    show "wf_trs (set (R tp) \<union> set [])" by (rule wf_b)
	    show "locally_terminating
	      (cover (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)) \<union> Matchbounds.raise)" by (rule local_SN)
	    show "\<And>lr. lr \<in> set (R tp) \<Longrightarrow> linear_term (snd lr)" by (rule rhs_lin)
	    show "rfc_initial_covers (R tp) initial_terms" by (rule initial_covers)
	    show "rfc_initial_closed (R tp) initial_terms" by (rule initial_closed)
	    show "rfc_initial_single_var initial_terms" by (rule initial_single)
	    show "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
	      \<exists>qf\<in>ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta).
	        qf \<in> ta_res (ta_of (generate_ta preTA)) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
	      by (rule initial_acc)
	  qed
	  then have SN: "SN_qrel (NFS tp, {}, set (R tp), {})"
	    using nfs by simp
	  show ?thesis unfolding qreltrs_sound Q Rw
	    by (rule SN)
	qed

definition
  bounds_complexity ::
    "('tp, 'f, 'v :: {linorder,showl}) tp_ops \<Rightarrow>
    ('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow>
    'tp \<Rightarrow> showsl check"
where
  "bounds_complexity I info cm cc tp \<equiv> do {
      check (Comp_Poly 1 \<le> cc) (showsl_lit (STR ''can only ensure linear complexity''));
      check (boundstype info = Match) (showsl_lit (STR ''complexity analysis requires boundstype match''));
      check_bounds_generic info (tp_ops.rules I tp) [] (stackable_of_cm cm) (roots_of_cm cm)
   }  <+? (\<lambda> s. showsl_lit (STR ''problem in ensuring match boundedness of\<newline>'') \<circ> 
        showsl_tp I tp \<circ> showsl_nl \<circ> s)"

lemma bounds_complexity: fixes info :: "('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I" and ok: "isOK (bounds_complexity I info cm cc tp)"
  and inf: "infinite (UNIV :: 'f set)"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  note isOK_if [simp]
  from ok[unfolded bounds_complexity_def Let_def, simplified]
  have cc: "O_of (Comp_Poly 1) \<subseteq> O_of cc" and bt: "boundstype info = Match" 
    and ok: "isOK (check_bounds_generic info (rules tp) [] (stackable_of_cm cm) (roots_of_cm cm))" by auto
  from check_bounds_complexity[OF ok inf bt] 
  have bound: "deriv_bound_measure_class (rstep (set (rules tp))) cm (Comp_Poly 1)" .
  show ?thesis
    by (rule deriv_bound_measure_class_trancl_mono[OF _ _ _ bound], simp, rule relto_trancl_subset, insert cc, auto)
qed

definition
  bounds_complexity_rel ::
    "('tp, 'f, 'v :: {showl,compare_order}) tp_ops \<Rightarrow>
    ('f::{showl,compare_order}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,'v)rules \<Rightarrow>
    ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "bounds_complexity_rel I info Rdelete cm cc tp \<equiv> do {
      let R = tp_ops.R I tp;
      let Rw = tp_ops.Rw I tp;
      let R2 = ceta_list_diff R Rdelete;
      check_subseteq Rdelete (tp_ops.rules I tp) \<comment> \<open>this is not required, just for early error detection\<close>
         <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' in current complexity problem''));
      check (Comp_Poly 1 \<le> cc) (showsl_lit (STR ''can only ensure linear complexity''));
      check (boundstype info = Match) (showsl_lit (STR ''complexity analysis requires boundstype match''));
      let all = tp_ops.rules I tp;
      check_bounds_generic info Rdelete (Rw @ R2) (stackable_of_cm cm) (roots_of_cm cm);
      return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete))
   }  <+? (\<lambda> s. showsl_lit (STR ''problem in ensuring match-RT boundedness of\<newline>'') \<circ> 
        showsl_tp I tp \<circ> showsl_lit (STR ''\<newline>with deletion of rules\<newline>'') \<circ> showsl_trs Rdelete \<circ> s)"

lemma bounds_complexity_rel: fixes info :: "('f::{showl,compare_order}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I" and res: "bounds_complexity_rel I info Rdelete cm cc tp = return tp'"
  and inf: "infinite (UNIV :: 'f set)"
  and rec: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  note isOK_if [simp]
  let ?R = "R tp"
  let ?Rw = "Rw tp"
  let ?diff = "ceta_list_diff ?R Rdelete"
  let ?union = "list_union ?Rw Rdelete"
  from res[unfolded bounds_complexity_rel_def Let_def, simplified]
  have cc: "O_of (Comp_Poly 1) \<subseteq> O_of cc" and bt: "boundstype info = Match" 
    and ok: "isOK (check_bounds_generic info Rdelete (?Rw @ ?diff) (stackable_of_cm cm) (roots_of_cm cm))" 
    and tp': "tp' = mk (NFS tp) (Q tp) ?diff ?union" by auto
  from rec[unfolded tp', simplified]
  have rec: "deriv_bound_measure_class
   (relto (qrstep (NFS tp) (set (Q tp)) (set (R tp) - set Rdelete))          
    (qrstep (NFS tp) (set (Q tp)) (set (Rw tp) \<union> set Rdelete)))
     cm cc" .
  from check_bounds_complexity_rel[OF ok inf bt]
  have bnd: "deriv_bound_measure_class (relto (rstep (set Rdelete)) (rstep (set (?Rw @ ?diff))))
   cm (Comp_Poly 1)" .
  have bnd: "deriv_bound_measure_class
   (relto 
    (qrstep (NFS tp) (set (Q tp)) (set (R tp) - set Rdelete) \<union> qrstep (NFS tp) (set (Q tp)) (set Rdelete))
    (qrstep (NFS tp) (set (Q tp)) (set (Rw tp))))
   cm cc"
    by (rule deriv_bound_relto_measure_class_union[OF rec[unfolded qrstep_union] 
    deriv_bound_measure_class_mono[OF relto_mono _ cc bnd]], auto)
  have qr_sub: "qrstep (NFS tp) (set (Q tp)) (set (R tp))
    \<subseteq> qrstep (NFS tp) (set (Q tp)) (set (R tp) - set Rdelete) \<union>
        qrstep (NFS tp) (set (Q tp)) (set Rdelete)"
    unfolding qrstep_union[symmetric]
    by (rule qrstep_mono, auto)
  show ?thesis unfolding qreltrs_sound split
  proof (rule deriv_bound_measure_class_mono[OF _ subset_refl subset_refl bnd])
    show "relto (qrstep (NFS tp) (set (Q tp)) (set (R tp))) (qrstep (NFS tp) (set (Q tp)) (set (Rw tp)))
      \<subseteq> relto
          (qrstep (NFS tp) (set (Q tp)) (set (R tp) - set Rdelete) \<union>
           qrstep (NFS tp) (set (Q tp)) (set Rdelete))
          (qrstep (NFS tp) (set (Q tp)) (set (Rw tp)))"
      by (rule relto_mono[OF qr_sub subset_refl])
  qed
qed

end
