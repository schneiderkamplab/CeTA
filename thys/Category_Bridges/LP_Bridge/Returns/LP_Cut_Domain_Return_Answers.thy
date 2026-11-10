theory LP_Cut_Domain_Return_Answers
  imports Category_LP_Cut_MGU_Bridge.LP_Cut_Domain_Precise_Checker Category_LP_Library.LP_Cut_Return_Nested_Triples_XML
begin

context cut_runtime_domain
begin

inductive precise_answer_transition ::
  "('f,string) lp_cut_program \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow>
   ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) option \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow> bool"
  for P where
  barrier: "precise_answer_transition P ((LPCBarrier m,\<eta>)#es) None es"
| success: "precise_answer_transition P ((LPCGoals [],\<eta>)#es) (Some \<eta>) es"
| truth: "precise_answer_transition P ((LPCGoals (LPCTrue#gs),\<eta>)#es) None
    ((LPCGoals gs,\<eta>)#es)"
| failure: "precise_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#es) None es"
| cut: "precise_answer_transition P ((LPCGoals (LPCCut m#gs),\<eta>)#es) None
    ((LPCGoals gs,\<eta>)#lpc_answer_prune m es)"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es) \<Longrightarrow>
    precise_answer_transition P ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),\<eta>)#es) None
     (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,\<eta>))
       (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,\<eta>)#es)"
| resolve: "c<length P \<Longrightarrow> mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<Longrightarrow>
    precise_answer_transition P ((LPCClause (LPCAtom a#gs) c m,\<eta>)#es) None
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs),
       \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      (\<forall>x. D (\<sigma> x)) \<and> (\<forall>x. D (\<rho> x)) \<and>
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    precise_answer_transition P ((LPCClause (LPCAtom a#gs) c m,\<eta>)#es) None es"
| unify: "mgu_unify a b gs \<sigma> \<Longrightarrow>
    precise_answer_transition P ((LPCGoals (LPCUnify a b#gs),\<eta>)#es) None
     ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs),
       \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
| unify_fail: "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      (\<forall>x. D (\<sigma> x)) \<and> lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    precise_answer_transition P ((LPCGoals (LPCUnify a b#gs),\<eta>)#es) None es"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#map fst es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow>
    precise_answer_transition P ((LPCGoals (LPCMeta a#gs),\<eta>)#es) None
     ((LPCGoals (body@gs),\<eta>)#(LPCBarrier m,\<eta>)#es)"
| meta_unlowerable: "\<not>(\<exists>m body. lp_cut_lower m a body) \<Longrightarrow>
    precise_answer_transition P ((LPCGoals (LPCMeta a#gs),\<eta>)#es) None
     ((LPCGoals (LPCMeta a#gs),\<eta>)#es)"

lemma precise_answer_transition_erases:
  assumes "precise_answer_transition P s event t"
  shows "(map fst s,map fst t)\<in>precise_source P"
  using assms
proof (induct rule: precise_answer_transition.induct)
  case (backtrack c a gs m eta es)
  show ?case by (simp only: list.map fst_conv; rule precise_source.backtrack[OF backtrack])
next
  case (unify_fail a b gs eta es)
  show ?case by (simp only: list.map fst_conv; rule precise_source.unify_fail[OF unify_fail])
qed (auto simp: lpc_answer_prune_erases o_def intro: precise_source.intros)

definition precise_answer_steps where
  "precise_answer_steps P = {(s,t). \<exists>event. precise_answer_transition P s event t}"

lemma precise_answer_event_is_success:
  "precise_answer_transition P s (Some \<eta>) t \<Longrightarrow> s=(LPCGoals [],\<eta>)#t"
  by (cases rule: precise_answer_transition.cases) auto

lemma precise_answer_failure_restores_saved:
  "precise_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#(e,\<nu>)#es) None ((e,\<nu>)#es)"
  by (rule precise_answer_transition.failure)

lemma precise_answer_failure_never_returns:
  "\<not> precise_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#es) (Some \<nu>) tt"
  using precise_answer_event_is_success by fastforce

lemma precise_answer_barrier_never_returns:
  "\<not> precise_answer_transition P ((LPCBarrier m,\<eta>)#es) (Some \<nu>) tt"
  using precise_answer_event_is_success by fastforce

lemma precise_answer_success_preserves_alternatives:
  "precise_answer_transition P ((LPCGoals [],\<eta>)#es) event tt
    \<longleftrightarrow> event=Some \<eta> \<and> tt=es"
  by (auto elim: precise_answer_transition.cases intro: precise_answer_transition.success)

lemma precise_answer_cut_keeps_caller:
  "lpc_answer_prune m ((LPCBarrier m,\<eta>)#caller) = (LPCBarrier m,\<eta>)#caller"
  by simp

lemma precise_answer_admin_lifts:
  assumes "lp_cut_admin (map fst ss) = Some t"
  shows "\<exists>event tt. precise_answer_transition P ss event tt \<and> map fst tt=t"
  using assms
proof (cases ss)
  case Nil then show ?thesis using assms by simp
next
  case (Cons frame es)
  obtain e \<eta> where frame: "frame=(e,\<eta>)" by (cases frame) auto
  show ?thesis
  proof (cases e)
    case (LPCGoals gs)
    show ?thesis
    proof (cases gs)
      case Nil
      then show ?thesis using assms Cons frame LPCGoals
        by (auto intro: precise_answer_transition.success)
    next
      case G: (Cons g tail)
      show ?thesis
      proof (cases g)
        case (LPCCut m)
        have step: "precise_answer_transition P ss None
          ((LPCGoals tail,\<eta>)#lpc_answer_prune m es)"
          using Cons frame LPCGoals G LPCCut by (simp add: precise_answer_transition.cut)
        show ?thesis using step assms Cons frame LPCGoals G LPCCut
          by (intro exI[of _ None] exI[of _ "(LPCGoals tail,\<eta>)#lpc_answer_prune m es"])
             (simp add: lpc_answer_prune_erases)
      next
        case LPCTrue
        have step: "precise_answer_transition P ss None ((LPCGoals tail,\<eta>)#es)"
          using Cons frame LPCGoals G LPCTrue by (simp add: precise_answer_transition.truth)
        show ?thesis using step assms Cons frame LPCGoals G LPCTrue
          by (intro exI[of _ None] exI[of _ "(LPCGoals tail,\<eta>)#es"]) simp
      qed (use assms Cons frame LPCGoals G in \<open>auto intro: precise_answer_transition.failure\<close>)
    qed
  next
    case LPCClause then show ?thesis using assms Cons frame by simp
  next
    case LPCBarrier then show ?thesis using assms Cons frame
      by (auto intro: precise_answer_transition.barrier)
  qed
qed

lemma precise_answer_source_lifts:
  assumes st: "(map fst ss,t)\<in>precise_source P"
  shows "\<exists>event tt. precise_answer_transition P ss event tt \<and> map fst tt=t"
proof -
  obtain e \<eta> es where ss: "ss=(e,\<eta>)#es"
    using st by (cases ss) (auto elim: precise_source.cases)
  from st show ?thesis
  proof cases
    case admin then show ?thesis by (rule precise_answer_admin_lifts)
  qed (use ss in \<open>force simp: map_map o_def intro: precise_answer_transition.intros\<close>)+
qed

theorem precise_answer_instrumentation_SN:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  shows "SN_on (precise_answer_steps P) {ss} \<longleftrightarrow> SN_on (precise_source P) {map fst ss}"
proof
  assume sn: "SN_on (precise_answer_steps P) {ss}"
  show "SN_on (precise_source P) {map fst ss}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix s assume ih: "\<And>t. (s,t)\<in>precise_answer_steps P \<Longrightarrow>
      SN_on (precise_source P) {map fst t}"
    show "SN_on (precise_source P) {map fst s}"
    proof (rule step_reflects_SN_on)
      fix u assume "(map fst s,u)\<in>precise_source P"
      then obtain event t where st: "precise_answer_transition P s event t" and u: "u=map fst t"
        using precise_answer_source_lifts by blast
      show "SN_on (precise_source P) {u}"
        using ih[of t] st by (simp add: u precise_answer_steps_def; blast)
    qed
  qed
next
  assume sn: "SN_on (precise_source P) {map fst ss}"
  have all: "\<forall>s :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list.
      qs=map fst s \<longrightarrow> SN_on (precise_answer_steps P) {s}"
    if sn: "SN_on (precise_source P) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs and s :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
    assume ih: "\<And>rs. (qs,rs)\<in>precise_source P \<Longrightarrow>
      \<forall>t :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
        ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list.
        rs=map fst t \<longrightarrow> SN_on (precise_answer_steps P) {t}"
      and qs: "qs=map fst s"
    show "SN_on (precise_answer_steps P) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume "(s,t)\<in>precise_answer_steps P"
      then have "(qs,map fst t)\<in>precise_source P"
        using precise_answer_transition_erases by (auto simp: precise_answer_steps_def qs)
      then show "SN_on (precise_answer_steps P) {t}" using ih by blast
    qed
  qed
  show "SN_on (precise_answer_steps P) {ss}" using all[OF sn] by blast
qed

end
end
