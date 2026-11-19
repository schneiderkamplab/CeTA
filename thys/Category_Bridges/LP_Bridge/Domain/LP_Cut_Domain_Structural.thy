theory LP_Cut_Domain_Structural
  imports LP_Cut_Domain_Source Category_LP_Library.LP_Cut_Table_XML
begin

text \<open>Administrative, allocation, stack and plain-resolution arguments
use only the shape of source transitions. These domain-specific proofs follow
the corresponding native checker lemmas; all executable checks are reused.\<close>

context cut_runtime_domain
begin

lemma admin_source_unique:
  assumes admin: "lp_cut_admin s=Some t" and step: "(s,u)\<in>source P"
  shows "u=t"
  using step admin by (cases rule: source.cases) auto


theorem checked_admin_covers:
  assumes checked: "lp_cut_check_admin s t"
    and step: "(lp_cut_state_eval s \<eta>,u)\<in>source P"
  shows "u=lp_cut_state_eval t \<eta> \<and>
    lp_cut_weight u < lp_cut_weight (lp_cut_state_eval s \<eta>)"
proof -
  have admin: "lp_cut_admin (lp_cut_state_eval s \<eta>)=Some (lp_cut_state_eval t \<eta>)"
    using checked by (simp add: lp_cut_check_admin_def lp_cut_admin_map)
  have eq: "u=lp_cut_state_eval t \<eta>"
    by (rule admin_source_unique[OF admin step])
  show ?thesis using lp_cut_admin_decreases[OF admin] eq by simp
qed

lemma checked_admin_step:
  "lp_cut_check_admin s t \<Longrightarrow>
    (lp_cut_state_eval s \<eta>,lp_cut_state_eval t \<eta>)\<in>source P"
  by (rule source.admin) (simp add: lp_cut_check_admin_def lp_cut_admin_map)


theorem checked_case_covers:
  assumes checked: "lp_cut_check_case P m f ts gs es next"
    and step: "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) \<eta>,t)
      \<in>source P"
  shows "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) (lp_cut_state_eval next \<eta>)"
proof -
  let ?a = "LPIFun (LPCUser f) (map (\<lambda>u. lp_ieval u \<eta>) ts)"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  let ?cs = "lp_cut_slice P (LPCUser f) (length ts)"
  have source: "(LPCGoals (LPCAtom ?a#?gs)#?es,t)\<in>source P"
    using step by (simp add: lp_cut_state_map_def)
  then obtain n where fresh: "lp_cut_fresh n (LPCGoals (LPCAtom ?a#?gs)#?es)"
    and successor: "t=map (\<lambda>c. LPCClause (LPCAtom ?a#?gs) c n) ?cs @ LPCBarrier n#?es"
    by (cases rule: source.cases) auto
  have chosen: "lp_cut_fresh m (LPCGoals (LPCAtom ?a#?gs)#?es)"
    using checked lp_cut_fresh_state_map[of m "\<lambda>u. lp_ieval u \<eta>"
      "LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es"]
    by (simp add: lp_cut_check_case_def lp_cut_state_map_def)
  have represented: "lp_cut_state_eval next \<eta> =
      map (\<lambda>c. LPCClause (LPCAtom ?a#?gs) c m) ?cs @ LPCBarrier m#?es"
    using checked by (simp add: lp_cut_check_case_def lp_cut_state_map_def map_map o_def)
  show ?thesis
    by (rule exI[of _ n])
      (simp only: represented successor lp_cut_fresh_swap_call[OF chosen fresh])
qed


theorem checked_meta_covers:
  assumes checked: "lp_cut_check_meta m a gs es body"
    and step: "(lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#es) \<eta>,t)\<in>source P"
  shows "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>)"
proof -
  let ?a = "lp_ieval a \<eta>"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?body = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) body"
  let ?es = "lp_cut_state_eval es \<eta>"
  have source: "(LPCGoals (LPCMeta ?a#?gs)#?es,t)\<in>source P"
    using step by (simp add: lp_cut_state_map_def)
  have lowered: "lp_cut_lower m ?a ?body"
    by (rule lp_cut_lower_finite_sound) (use checked in \<open>simp add: lp_cut_check_meta_def\<close>)
  from source obtain n bs where fresh: "lp_cut_fresh n (LPCGoals (LPCMeta ?a#?gs)#?es)"
    and actual: "lp_cut_lower n ?a bs"
    and successor: "t=LPCGoals (bs@?gs)#LPCBarrier n#?es"
    using lowered by (cases rule: source.cases) auto
  have chosen: "lp_cut_fresh m (LPCGoals (LPCMeta ?a#?gs)#?es)"
    using checked lp_cut_fresh_state_map[of m "\<lambda>u. lp_ieval u \<eta>"
      "LPCGoals (LPCMeta a#gs)#es"]
    by (simp add: lp_cut_check_meta_def lp_cut_state_map_def)
  have represented: "lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta> =
      LPCGoals (?body@?gs)#LPCBarrier m#?es"
    by (simp add: lp_cut_state_map_def)
  show ?thesis
    by (rule exI[of _ n])
      (simp only: represented successor lp_cut_fresh_swap_meta[OF chosen fresh lowered actual])
qed


lemma source_append_barriers:
  assumes ne: "s\<noteq>[]" and bs: "lp_cut_barriers bs"
    and step: "(s@bs,t)\<in>source P"
  shows "\<exists>u cs. (s,u)\<in>source P \<and> lp_cut_barriers cs \<and> t=u@cs"
proof -
  obtain e es where s: "s=e#es" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lp_cut_admin_append_barriers[OF ne bs admin]
      by (blast intro: source.admin)
  qed (use bs in \<open>force simp: s lp_cut_fresh_def append_assoc
    intro: source.case_call source.resolve source.backtrack
      source.unify source.unify_fail source.meta source.meta_unlowerable\<close>)+
qed

lemma barriers_SN:
  "lp_cut_barriers bs \<Longrightarrow> SN_on (source P) {bs}"
proof (induct bs)
  case Nil
  show ?case by (rule step_reflects_SN_on) (auto elim: source.cases)
next
  case (Cons b bs)
  obtain m where b: "b=LPCBarrier m" using Cons.prems by (cases b) auto
  have tail: "SN_on (source P) {bs}" using Cons by simp
  show ?case by (rule step_reflects_SN_on)
    (use tail in \<open>auto simp: b elim: source.cases\<close>)
qed

theorem append_barriers_SN:
  fixes P :: "('f,string) lp_cut_program"
    and s bs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (source P) {s}" and barriers: "lp_cut_barriers bs"
  shows "SN_on (source P) {s@bs}"
proof -
  have all: "\<forall>bs. lp_cut_barriers bs \<longrightarrow> SN_on (source P) {s@bs}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s bs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
    assume ih: "\<And>t. (s,t)\<in>source P \<Longrightarrow>
      \<forall>cs. lp_cut_barriers cs \<longrightarrow> SN_on (source P) {t@cs}"
      and bs: "lp_cut_barriers bs"
    show "SN_on (source P) {s@bs}"
    proof (cases "s=[]")
      case True then show ?thesis using barriers_SN[OF bs, of P] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume step: "(s@bs,t)\<in>source P"
        obtain u cs where src: "(s,u)\<in>source P"
          and bar: "lp_cut_barriers cs" and shape: "t=u@cs"
          using source_append_barriers[OF False bs step] by blast
        show "SN_on (source P) {t}" using ih[OF src] bar shape by blast
      qed
    qed
  qed
  show ?thesis using all barriers by blast
qed

lemma source_append_suffix:
  assumes ne: "s\<noteq>[]" and step: "(s@es,t)\<in>source P"
  shows "\<exists>u n. (s,u)\<in>source P \<and> t=u@drop n es"
proof -
  obtain e ss where s: "s=e#ss" using ne by (cases s) auto
  from step show ?thesis
  proof cases
    case admin
    show ?thesis using lpc_admin_append_suffix[OF ne admin]
      by (blast intro: source.admin)
  qed (use s in \<open>force simp: lp_cut_fresh_def append_assoc
    intro: exI[of _ 0] source.case_call source.resolve
      source.backtrack source.unify source.unify_fail
      source.meta source.meta_unlowerable\<close>)+
qed

lemma append_all_suffixes_SN:
  fixes P :: "('f,string) lp_cut_program"
    and s es :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes sn: "SN_on (source P) {s}"
    and suffix: "\<And>n. SN_on (source P) {drop n es}"
  shows "SN_on (source P) {s@es}"
proof -
  have all: "\<forall>es. (\<forall>n. SN_on (source P) {drop n es}) \<longrightarrow>
      SN_on (source P) {s@es}"
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix s es :: "('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
    assume ih: "\<And>u. (s,u)\<in>source P \<Longrightarrow>
      \<forall>es. (\<forall>n. SN_on (source P) {drop n es}) \<longrightarrow>
      SN_on (source P) {u@es}"
      and tails: "\<forall>n. SN_on (source P) {drop n es}"
    show "SN_on (source P) {s@es}"
    proof (cases "s=[]")
      case True then show ?thesis using tails[rule_format, of 0] by simp
    next
      case False
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix t assume "(s@es,t)\<in>source P"
        then obtain u n where step: "(s,u)\<in>source P"
          and t: "t=u@drop n es" using source_append_suffix[OF False] by blast
        show "SN_on (source P) {t}"
          using ih[OF step, rule_format, of "drop n es"] tails
          by (simp add: t drop_drop)
      qed
    qed
  qed
  show ?thesis using all suffix by blast
qed

theorem singleton_stack_SN:
  assumes "\<And>e. e\<in>set es \<Longrightarrow> SN_on (source P) {[e]}"
  shows "SN_on (source P) {es}"
  using assms
proof (induct es rule: length_induct)
  case (1 es)
  show ?case
  proof (cases es)
    case Nil
    show ?thesis unfolding Nil
      by (rule step_reflects_SN_on) (auto elim: source.cases)
  next
    case (Cons e ss)
    have first: "SN_on (source P) {[e]}" using "1.prems" Cons by simp
    have tails: "SN_on (source P) {drop n ss}" for n
      by (rule "1.hyps"[rule_format]) (use Cons "1.prems" in \<open>auto dest: in_set_dropD\<close>)
    show ?thesis using append_all_suffixes_SN[OF first tails] Cons by simp
  qed
qed

lemma scope_word_SN:
  assumes program: "lp_cut_source_program P" and sn: "SN_on (source P) {s}"
  shows "SN_on (source P) {lp_cut_scope_word rs s}"
  using sn
proof (induct rs arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons ab rs)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "SN_on (source P) {map (lp_cut_scope_entry (lp_cut_scope_swap a b)) s}"
    by (rule scope_swap_SN[OF program Cons.prems])
  show ?case using Cons.hyps[OF first] by (simp add: ab)
qed


theorem checked_instance_SN:
  assumes program: "lp_cut_source_program P"
    and checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and sn: "SN_on (source P)
      {lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)}"
  shows "SN_on (source P) {lp_cut_state_eval s \<eta>}"
proof -
  have source: "s=lp_cut_scope_word swaps
      (lp_cut_state_map (\<lambda>u. u\<cdot>lp_cut_instance_subst bindings) t)"
    using checked by (auto simp: lp_cut_check_instance_def Let_def)
  have shape: "lp_cut_state_eval s \<eta> = lp_cut_scope_word swaps
      (lp_cut_state_eval t (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>))"
    by (simp add: source lp_cut_scope_word_map[symmetric]
      lp_cut_state_eval_subst)
  show ?thesis using scope_word_SN[OF program sn, of swaps] shape by simp
qed


theorem plain_goals_SN:
  fixes P :: "('f,string) lp_cut_program"
    and gs :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
  assumes program: "lpc_plain_program P Q F"
    and plain: "list_all (lpc_plain_igoal F) gs"
    and sn: "SN_on (lp_ild Q) {map lpc_plain_iatom gs}"
  shows "SN_on (source P) {[LPCGoals gs]}"
proof -
  have all: "\<forall>gs. list_all (lpc_plain_igoal F) gs \<longrightarrow>
      qs=map lpc_plain_iatom gs \<longrightarrow> SN_on (source P) {[LPCGoals gs]}"
    if sn: "SN_on (lp_ild Q) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs gs
    assume ih: "\<And>rs. (qs,rs)\<in>lp_ild Q \<Longrightarrow>
      \<forall>hs. list_all (lpc_plain_igoal F) hs \<longrightarrow>
       rs=map lpc_plain_iatom hs \<longrightarrow> SN_on (source P) {[LPCGoals hs]}"
      and gs: "list_all (lpc_plain_igoal F) gs" and qs: "qs=map lpc_plain_iatom gs"
    show "SN_on (source P) {[LPCGoals gs]}"
    proof (cases gs)
      case Nil
      have empty: "SN_on (source P) {[]}"
        by (rule step_reflects_SN_on) (auto elim: source.cases)
      show ?thesis by (rule step_reflects_SN_on)
        (use empty in \<open>auto simp: Nil elim: source.cases\<close>)
    next
      case (Cons g tail)
      obtain f ts where g: "g=LPCAtom (LPIFun (LPCUser f) ts)" and f: "f\<in>F"
        using gs Cons by (auto simp: lpc_plain_igoal_iff)
      have tail: "list_all (lpc_plain_igoal F) tail" using gs Cons by simp
      have barrier: "SN_on (source P) {[LPCBarrier m]}" for m
        by (rule barriers_SN) simp
      have clauses: "SN_on (source P) {[LPCClause gs c m]}" for c m
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCClause gs c m],s)\<in>source P"
        from st show "SN_on (source P) {s}"
        proof cases
          case (resolve a sigma rho)
          have shape: "a=LPIFun (LPCUser f) ts"
            using resolve Cons g by auto
          have bound: "c<length P" using resolve by auto
          note facts = lpc_plain_resolution[OF program f tail bound, of ts sigma rho m]
          show ?thesis using resolve facts ih qs Cons g shape by auto
        next
          case backtrack
          show ?thesis by (rule step_reflects_SN_on)
            (use backtrack in \<open>auto elim: source.cases\<close>)
        qed (use Cons g in auto)
      qed
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix s assume st: "([LPCGoals gs],s)\<in>source P"
        from st show "SN_on (source P) {s}"
        proof cases
          case case_call
          show ?thesis
            by (rule singleton_stack_SN)
              (use clauses case_call Cons g barrier in auto)
        qed (use Cons g in auto)
      qed
    qed
  qed
  show ?thesis using all[OF sn] plain by blast
qed

theorem check_plain_sound:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_plain P Q nd Fs roles"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map \<eta> (lpcn_vars nd))]}"
  shows "SN_on (source P) {lp_cut_state_eval (lpcn_state nd) \<eta>}"
proof -
  obtain gs where state: "lpcn_state nd=[LPCGoals gs]"
    and plain: "list_all (lpc_plain_goal (set Fs)) gs"
    and program: "lpc_plain_program P (lpc_plain_extract P Fs) (set Fs)"
    and subset: "set (lp_roles_program (lpc_plain_role roles) id (lpc_plain_extract P Fs)) \<subseteq> set Q"
    and clause: "((lpcn_pred nd,map Var (lpcn_vars nd)),
      map (lp_roles_atom (lpc_plain_role roles) id) (map lpc_plain_atom gs))\<in>set Q"
    using checked by (auto simp: lpc_check_plain_def split: list.splits lp_cut_entry.splits;
      metis list.exhaust)
  let ?body = "map (\<lambda>a. lp_atom_eval a \<eta>)
    (map (lp_roles_atom (lpc_plain_role roles) id) (map lpc_plain_atom gs))"
  have step: "([(lpcn_pred nd,map \<eta> (lpcn_vars nd))],?body)\<in>lp_ild Q"
    using lp_seg_residual_step[OF clause, of "(lpcn_pred nd,map \<eta> (lpcn_vars nd))" LPIVar \<eta> "[]"]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
  have body_sn: "SN_on (lp_ild Q) {?body}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use step in auto)
  have restricted: "SN_on (lp_ild (lp_roles_program (lpc_plain_role roles) id (lpc_plain_extract P Fs))) {?body}"
    by (rule SN_on_subset1[OF body_sn lpc_ild_mono[OF subset]])
  have ordinary: "SN_on (lp_ild (lpc_plain_extract P Fs))
    {map (\<lambda>a. lp_atom_eval a \<eta>) (map lpc_plain_atom gs)}"
    by (rule lp_roles_termination_reflect[where p="lpc_plain_role roles" and d=id])
      (use restricted in \<open>simp add: map_map o_def lp_roles_eval lp_iterm.map_id\<close>)
  have source: "SN_on (source P)
    {[LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs)]}"
    by (rule plain_goals_SN[OF program lpc_plain_eval(1)[OF plain]])
      (use ordinary in \<open>simp only: lpc_plain_eval(2)[OF plain]\<close>)
  show ?thesis using source by (simp add: state lp_cut_state_map_def)
qed

end
end
