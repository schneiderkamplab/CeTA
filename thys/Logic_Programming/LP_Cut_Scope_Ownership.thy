theory LP_Cut_Scope_Ownership
  imports LP_Cut_Return_Attachment LP_Cut_Scope_Source
begin

text \<open>Scope ownership records the order of barriers, not merely membership
in their set. A cut can remove inner barriers, so later goals must remain valid
after that removal. E contains external scopes owned by the caller.\<close>

fun lpc_barrier_ids where
  "lpc_barrier_ids [] = []"
| "lpc_barrier_ids (LPCBarrier m#es) = m#lpc_barrier_ids es"
| "lpc_barrier_ids (e#es) = lpc_barrier_ids es"

lemma lpc_barrier_ids_Cons:
  "lpc_barrier_ids (e#es) = (case e of LPCBarrier m \<Rightarrow> m#lpc_barrier_ids es
    | _ \<Rightarrow> lpc_barrier_ids es)"
  by (cases e) simp_all

fun lpc_owned_goals where
  "lpc_owned_goals E B [] = True"
| "lpc_owned_goals E B (LPCCut m#gs) =
    (m\<in>E\<union>set B \<and> lpc_owned_goals E (dropWhile (\<lambda>n. n\<noteq>m) B) gs)"
| "lpc_owned_goals E B (g#gs) = lpc_owned_goals E B gs"

fun lpc_owned_stack where
  "lpc_owned_stack E [] = True"
| "lpc_owned_stack E (LPCGoals gs#es) =
    (lpc_owned_goals E (lpc_barrier_ids es) gs \<and> lpc_owned_stack E es)"
| "lpc_owned_stack E (LPCClause gs c m#es) =
    (m\<in>E\<union>set (lpc_barrier_ids es) \<and>
     lpc_owned_goals E (lpc_barrier_ids es) gs \<and>
     lpc_owned_goals E (dropWhile (\<lambda>n. n\<noteq>m) (lpc_barrier_ids es)) gs \<and>
     lpc_owned_stack E es)"
| "lpc_owned_stack E (LPCBarrier m#es) = lpc_owned_stack E es"

lemma lpc_barrier_ids_prune:
  "lpc_barrier_ids (lp_cut_prune m es) = dropWhile (\<lambda>n. n\<noteq>m) (lpc_barrier_ids es)"
  by (induct es) (auto split: lp_cut_entry.splits)

lemma lpc_barrier_ids_member:
  "m\<in>set (lpc_barrier_ids es) \<longleftrightarrow> LPCBarrier m\<in>set es"
  by (induct es) (auto simp: lpc_barrier_ids_Cons split: lp_cut_entry.splits)

lemma lpc_owned_prune:
  "lpc_owned_stack E es \<Longrightarrow> lpc_owned_stack E (lp_cut_prune m es)"
  by (induct es) (auto split: lp_cut_entry.splits)

lemma lpc_owned_goals_map:
  "lpc_owned_goals E B (map (lp_cut_map f) gs) = lpc_owned_goals E B gs"
proof (induct gs arbitrary: B)
  case Nil then show ?case by simp
next
  case (Cons g gs) then show ?case by (cases g) auto
qed

lemma lpc_owned_fresh_barrier:
  assumes "m\<notin>\<Union>(lp_cut_goal_scopes ` set gs)"
  shows "lpc_owned_goals E (m#B) gs = lpc_owned_goals E B gs"
  using assms
proof (induct gs arbitrary: B)
  case Nil then show ?case by simp
next
  case (Cons g gs) then show ?case by (cases g) auto
qed

lemma lpc_cut_barrier_retained[simp]:
  "m\<in>set (dropWhile (\<lambda>n. n\<noteq>m) B) \<longleftrightarrow> m\<in>set B"
  by (induct B) auto

lemma lpc_owned_bound_body:
  assumes body: "list_all lp_cut_source_goal bs"
    and scope: "m\<in>E\<union>set B"
    and before: "lpc_owned_goals E B gs"
    and tail: "lpc_owned_goals E (dropWhile (\<lambda>n. n\<noteq>m) B) gs"
  shows "lpc_owned_goals E B (map (lp_cut_bind m f) bs @ gs)"
  using body scope before tail
proof (induct bs arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case using Cons by (cases b) auto
qed

lemma lpc_owned_admin:
  assumes "lpc_owned_stack E ss" "lp_cut_admin ss=Some tt"
  shows "lpc_owned_stack E tt"
  using assms
proof (induct ss rule: lp_cut_admin.induct)
  case (5 g gs es)
  then show ?case by (cases g)
    (auto simp: lpc_barrier_ids_prune intro: lpc_owned_prune)
qed auto

lemma lpc_barrier_ids_cases[simp]:
  "lpc_barrier_ids (map (\<lambda>c. LPCClause gs c m) cs @ es) = lpc_barrier_ids es"
  by (induct cs) auto

lemma lpc_owned_case_stack:
  assumes fresh: "m\<notin>\<Union>(lp_cut_goal_scopes ` set gs)"
    and goals: "lpc_owned_goals E (lpc_barrier_ids es) gs"
    and stack: "lpc_owned_stack E es"
  shows "lpc_owned_stack E (map (\<lambda>c. LPCClause gs c m) cs @ LPCBarrier m#es)"
  using assms by (induct cs) (auto simp: lpc_owned_fresh_barrier)

lemma lpc_owned_lower:
  assumes lower: "lp_cut_lower m a body"
    and scope: "m\<in>E\<union>set B"
    and before: "lpc_owned_goals E B gs"
    and after: "lpc_owned_goals E (dropWhile (\<lambda>n. n\<noteq>m) B) gs"
  shows "lpc_owned_goals E B (body@gs)"
  using lower scope before after
  by (induct arbitrary: B gs rule: lp_cut_lower.induct) auto

theorem lpc_owned_source_preserved:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E ss"
    and step: "(ss,tt)\<in>lp_cut_mgu_source P"
  shows "lpc_owned_stack E tt"
  using step
proof (cases rule: lp_cut_mgu_source.cases)
  case admin
  then show ?thesis using owned by (auto intro: lpc_owned_admin)
next
  case (case_call m f ts gs es)
  have fresh: "m\<notin>\<Union>(lp_cut_goal_scopes ` set (LPCAtom (LPIFun (LPCUser f) ts)#gs))"
    using case_call by (auto simp: lp_cut_fresh_def)
  show ?thesis using owned case_call lpc_owned_case_stack[OF fresh, of E es]
    by simp
next
  case (resolve c a gs \<sigma> \<rho> m es)
  have body: "list_all lp_cut_source_goal (snd (P!c))"
    using program resolve by (auto simp: lp_cut_source_program_def)
  have goals: "lpc_owned_goals E (lpc_barrier_ids es)
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)"
    by (rule lpc_owned_bound_body[OF body])
      (use resolve owned in \<open>auto simp: lpc_owned_goals_map\<close>)
  show ?thesis using resolve owned goals by simp
next
  case (meta m a gs es body)
  have fresh: "m\<notin>\<Union>(lp_cut_goal_scopes ` set gs)"
    using meta by (auto simp: lp_cut_fresh_def)
  have tail: "lpc_owned_goals E (m#lpc_barrier_ids es) gs"
    using meta owned by (simp add: lpc_owned_fresh_barrier[OF fresh])
  have goals: "lpc_owned_goals E (m#lpc_barrier_ids es) (body@gs)"
    by (rule lpc_owned_lower) (use meta tail in auto)
  show ?thesis using meta owned goals by simp
qed (use owned in \<open>auto simp: lpc_owned_goals_map\<close>)

lemma lpc_owned_admin_append:
  assumes nonempty: "ss\<noteq>[]" and owned: "lpc_owned_stack E ss"
    and separated: "E\<inter>set (lpc_barrier_ids es) = {}"
    and step: "lp_cut_admin (ss@es)=Some u"
  shows "\<exists>tt. lp_cut_admin ss=Some tt \<and> (u=tt@es \<or> u=tt)"
  using assms
proof (induct ss rule: lp_cut_admin.induct)
  case (5 g gs tail)
  show ?case
  proof (cases g)
    case (LPCCut m)
    have external: "m\<in>E \<Longrightarrow> LPCBarrier m\<notin>set es"
      using 5 by (auto simp: lpc_barrier_ids_member[symmetric])
    show ?thesis using 5 LPCCut external
      by (auto simp: lp_cut_prune_append lp_cut_prune_absent lpc_barrier_ids_member
        split: if_splits)
  qed (use 5 in auto)
qed auto

lemma lpc_owned_source_append:
  assumes nonempty: "ss\<noteq>[]" and owned: "lpc_owned_stack E ss"
    and separated: "E\<inter>set (lpc_barrier_ids es) = {}"
    and step: "(ss@es,u)\<in>lp_cut_mgu_source P"
  shows "\<exists>tt. (ss,tt)\<in>lp_cut_mgu_source P \<and> (u=tt@es \<or> u=tt)"
proof -
  obtain e tail where ss: "ss=e#tail" using nonempty by (cases ss) auto
  from step show ?thesis
  proof cases
    case admin
    then show ?thesis using lpc_owned_admin_append[OF nonempty owned separated]
      by (blast intro: lp_cut_mgu_source.admin)
  next
    case (case_call m f ts gs suffix)
    have shape: "ss=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#tail"
      and suffix: "suffix=tail@es" using case_call ss by auto
    have fresh: "lp_cut_fresh m ss" using case_call shape suffix
      by (auto simp: lp_cut_fresh_def)
    have src: "(ss,map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
      (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m#tail)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.case_call) (use fresh shape in simp)
    show ?thesis by (rule exI, rule conjI[OF src])
      (use case_call suffix in \<open>simp add: append_assoc\<close>)
  next
    case (resolve c a gs \<sigma> \<rho> m suffix)
    have shape: "ss=LPCClause (LPCAtom a#gs) c m#tail"
      and suffix: "suffix=tail@es" using resolve ss by auto
    have src: "(ss,LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
      map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#tail)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.resolve) (use resolve in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use resolve suffix in simp)
  next
    case (backtrack c a gs m)
    have shape: "ss=LPCClause (LPCAtom a#gs) c m#tail"
      and u: "u=tail@es" using backtrack ss by auto
    have src: "(ss,tail)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.backtrack) (use backtrack in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (simp add: u)
  next
    case (unify a b gs \<sigma> suffix)
    have shape: "ss=LPCGoals (LPCUnify a b#gs)#tail"
      and suffix: "suffix=tail@es" using unify ss by auto
    have src: "(ss,LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#tail)
        \<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.unify) (use unify in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use unify suffix in simp)
  next
    case (unify_fail a b gs)
    have shape: "ss=LPCGoals (LPCUnify a b#gs)#tail"
      and u: "u=tail@es" using unify_fail ss by auto
    have src: "(ss,tail)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.unify_fail) (use unify_fail in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (simp add: u)
  next
    case (meta m a gs suffix body)
    have shape: "ss=LPCGoals (LPCMeta a#gs)#tail"
      and suffix: "suffix=tail@es" using meta ss by auto
    have fresh: "lp_cut_fresh m ss" using meta shape suffix
      by (auto simp: lp_cut_fresh_def)
    have src: "(ss,LPCGoals (body@gs)#LPCBarrier m#tail)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.meta) (use meta fresh shape in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use meta suffix in simp)
  next
    case (meta_unlowerable a gs suffix)
    have shape: "ss=LPCGoals (LPCMeta a#gs)#tail"
      and suffix: "suffix=tail@es" using meta_unlowerable ss by auto
    have src: "(ss,ss)\<in>lp_cut_mgu_source P"
      unfolding shape by (rule lp_cut_mgu_source.meta_unlowerable) (use meta_unlowerable in auto)
    show ?thesis by (rule exI, rule conjI[OF src]) (use meta_unlowerable suffix shape in simp)
  qed
qed

theorem lpc_owned_append_SN:
  assumes program: "lp_cut_source_program P"
    and owned: "lpc_owned_stack E ss"
    and separated: "E\<inter>set (lpc_barrier_ids es) = {}"
    and first: "SN_on (lp_cut_mgu_source P) {ss}"
    and later: "SN_on (lp_cut_mgu_source P) {es}"
  shows "SN_on (lp_cut_mgu_source P) {ss@es}"
proof -
  have all: "SN_on (lp_cut_mgu_source P) {ss} \<and>
    (lpc_owned_stack E ss \<longrightarrow> SN_on (lp_cut_mgu_source P) {ss@es})"
  proof (rule SN_on_induct[OF first singletonI])
    fix ss
    assume ih: "\<And>tt. (ss,tt)\<in>lp_cut_mgu_source P \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {tt} \<and>
      (lpc_owned_stack E tt \<longrightarrow> SN_on (lp_cut_mgu_source P) {tt@es})"
    show "SN_on (lp_cut_mgu_source P) {ss} \<and>
      (lpc_owned_stack E ss \<longrightarrow> SN_on (lp_cut_mgu_source P) {ss@es})"
    proof (intro conjI impI)
      show "SN_on (lp_cut_mgu_source P) {ss}"
        by (rule step_reflects_SN_on) (use ih in blast)
    next
      assume own: "lpc_owned_stack E ss"
      show "SN_on (lp_cut_mgu_source P) {ss@es}"
      proof (cases "ss=[]")
        case True then show ?thesis using later by simp
      next
        case False
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix u assume st: "(ss@es,u)\<in>lp_cut_mgu_source P"
          obtain tt where src: "(ss,tt)\<in>lp_cut_mgu_source P"
            and shape: "u=tt@es \<or> u=tt"
            using lpc_owned_source_append[OF False own separated st] by blast
          have child_owned: "lpc_owned_stack E tt"
            by (rule lpc_owned_source_preserved[OF program own src])
          show "SN_on (lp_cut_mgu_source P) {u}"
            using ih[OF src] child_owned shape by blast
        qed
      qed
    qed
  qed
  show ?thesis using all owned by blast
qed

end
