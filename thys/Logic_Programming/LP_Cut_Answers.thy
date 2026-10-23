theory LP_Cut_Answers
  imports LP_Cut_MGU_Stack LP_SEG_Answer_Contracts
begin

text \<open>Answer instrumentation for ordered resolution with scoped cuts.
Each saved alternative owns its environment. Successful resolution updates only
the active frame; backtracking restores the saved environment. A return event
is emitted only for an empty successful goal list, never for failure or a
barrier. Environments may contain infinite trees. This is infrastructure for
answer-aware Split, not a new accepting certificate rule.\<close>

fun lpc_answer_prune where
  "lpc_answer_prune m [] = []"
| "lpc_answer_prune m ((e,\<eta>)#es) =
    (case e of LPCBarrier n \<Rightarrow> if m=n then (e,\<eta>)#es else lpc_answer_prune m es
     | _ \<Rightarrow> lpc_answer_prune m es)"

lemma lpc_answer_prune_erases:
  "map fst (lpc_answer_prune m es) = lp_cut_prune m (map fst es)"
  by (induct es) (auto split: prod.splits lp_cut_entry.splits)

inductive lpc_answer_transition ::
  "('f,string) lp_cut_program \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow>
   ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) option \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow> bool"
  for P where
  barrier: "lpc_answer_transition P ((LPCBarrier m,\<eta>)#es) None es"
| success: "lpc_answer_transition P ((LPCGoals [],\<eta>)#es) (Some \<eta>) es"
| truth: "lpc_answer_transition P ((LPCGoals (LPCTrue#gs),\<eta>)#es) None
    ((LPCGoals gs,\<eta>)#es)"
| failure: "lpc_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#es) None es"
| cut: "lpc_answer_transition P ((LPCGoals (LPCCut m#gs),\<eta>)#es) None
    ((LPCGoals gs,\<eta>)#lpc_answer_prune m es)"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es) \<Longrightarrow>
    lpc_answer_transition P ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),\<eta>)#es) None
     (map (\<lambda>c. (LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m,\<eta>))
       (lp_cut_slice P (LPCUser f) (length ts)) @ (LPCBarrier m,\<eta>)#es)"
| resolve: "c<length P \<Longrightarrow> lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<Longrightarrow>
    lpc_answer_transition P ((LPCClause (LPCAtom a#gs) c m,\<eta>)#es) None
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs),
       \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    lpc_answer_transition P ((LPCClause (LPCAtom a#gs) c m,\<eta>)#es) None es"
| unify: "lpc_mgu_unify a b gs \<sigma> \<Longrightarrow>
    lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),\<eta>)#es) None
     ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs),
       \<lambda>x. lp_isubst (\<eta> x) \<sigma>)#es)"
| unify_fail: "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),\<eta>)#es) None es"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#map fst es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow>
    lpc_answer_transition P ((LPCGoals (LPCMeta a#gs),\<eta>)#es) None
     ((LPCGoals (body@gs),\<eta>)#(LPCBarrier m,\<eta>)#es)"
| meta_unlowerable: "\<not>(\<exists>m body. lp_cut_lower m a body) \<Longrightarrow>
    lpc_answer_transition P ((LPCGoals (LPCMeta a#gs),\<eta>)#es) None
     ((LPCGoals (LPCMeta a#gs),\<eta>)#es)"

lemma lpc_answer_transition_erases:
  assumes "lpc_answer_transition P s event t"
  shows "(map fst s,map fst t)\<in>lp_cut_mgu_source P"
  using assms
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: lpc_answer_prune_erases o_def intro: lp_cut_mgu_source.intros)

definition lpc_answer_steps where
  "lpc_answer_steps P = {(s,t). \<exists>event. lpc_answer_transition P s event t}"

lemma lpc_answer_event_is_success:
  "lpc_answer_transition P s (Some \<eta>) t \<Longrightarrow> s=(LPCGoals [],\<eta>)#t"
  by (cases rule: lpc_answer_transition.cases) auto

lemma lpc_answer_failure_restores_saved:
  "lpc_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#(e,\<nu>)#es) None ((e,\<nu>)#es)"
  by (rule lpc_answer_transition.failure)

lemma lpc_answer_failure_never_returns:
  "\<not> lpc_answer_transition P ((LPCGoals (LPCFail#gs),\<eta>)#es) (Some \<nu>) tt"
  using lpc_answer_event_is_success by fastforce

lemma lpc_answer_barrier_never_returns:
  "\<not> lpc_answer_transition P ((LPCBarrier m,\<eta>)#es) (Some \<nu>) tt"
  using lpc_answer_event_is_success by fastforce

lemma lpc_answer_success_preserves_alternatives:
  "lpc_answer_transition P ((LPCGoals [],\<eta>)#es) event tt
    \<longleftrightarrow> event=Some \<eta> \<and> tt=es"
  by (auto elim: lpc_answer_transition.cases intro: lpc_answer_transition.success)

lemma lpc_answer_cut_keeps_caller:
  "lpc_answer_prune m ((LPCBarrier m,\<eta>)#caller) = (LPCBarrier m,\<eta>)#caller"
  by simp

lemma lpc_answer_admin_lifts:
  assumes "lp_cut_admin (map fst ss) = Some t"
  shows "\<exists>event tt. lpc_answer_transition P ss event tt \<and> map fst tt=t"
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
        by (auto intro: lpc_answer_transition.success)
    next
      case G: (Cons g tail)
      show ?thesis
      proof (cases g)
        case (LPCCut m)
        have step: "lpc_answer_transition P ss None
          ((LPCGoals tail,\<eta>)#lpc_answer_prune m es)"
          using Cons frame LPCGoals G LPCCut by (simp add: lpc_answer_transition.cut)
        show ?thesis using step assms Cons frame LPCGoals G LPCCut
          by (intro exI[of _ None] exI[of _ "(LPCGoals tail,\<eta>)#lpc_answer_prune m es"])
             (simp add: lpc_answer_prune_erases)
      next
        case LPCTrue
        have step: "lpc_answer_transition P ss None ((LPCGoals tail,\<eta>)#es)"
          using Cons frame LPCGoals G LPCTrue by (simp add: lpc_answer_transition.truth)
        show ?thesis using step assms Cons frame LPCGoals G LPCTrue
          by (intro exI[of _ None] exI[of _ "(LPCGoals tail,\<eta>)#es"]) simp
      qed (use assms Cons frame LPCGoals G in \<open>auto intro: lpc_answer_transition.failure\<close>)
    qed
  next
    case LPCClause then show ?thesis using assms Cons frame by simp
  next
    case LPCBarrier then show ?thesis using assms Cons frame
      by (auto intro: lpc_answer_transition.barrier)
  qed
qed

lemma lpc_answer_source_lifts:
  assumes st: "(map fst ss,t)\<in>lp_cut_mgu_source P"
  shows "\<exists>event tt. lpc_answer_transition P ss event tt \<and> map fst tt=t"
proof -
  obtain e \<eta> es where ss: "ss=(e,\<eta>)#es"
    using st by (cases ss) (auto elim: lp_cut_mgu_source.cases)
  from st show ?thesis
  proof cases
    case admin then show ?thesis by (rule lpc_answer_admin_lifts)
  qed (use ss in \<open>force simp: map_map o_def intro: lpc_answer_transition.intros\<close>)+
qed

theorem lpc_answer_instrumentation_SN:
  fixes P :: "('f,string) lp_cut_program"
    and ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  shows "SN_on (lpc_answer_steps P) {ss} \<longleftrightarrow> SN_on (lp_cut_mgu_source P) {map fst ss}"
proof
  assume sn: "SN_on (lpc_answer_steps P) {ss}"
  show "SN_on (lp_cut_mgu_source P) {map fst ss}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix s assume ih: "\<And>t. (s,t)\<in>lpc_answer_steps P \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {map fst t}"
    show "SN_on (lp_cut_mgu_source P) {map fst s}"
    proof (rule step_reflects_SN_on)
      fix u assume "(map fst s,u)\<in>lp_cut_mgu_source P"
      then obtain event t where st: "lpc_answer_transition P s event t" and u: "u=map fst t"
        using lpc_answer_source_lifts by blast
      show "SN_on (lp_cut_mgu_source P) {u}"
        using ih[of t] st by (simp add: u lpc_answer_steps_def; blast)
    qed
  qed
next
  assume sn: "SN_on (lp_cut_mgu_source P) {map fst ss}"
  have all: "\<forall>s :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list.
      qs=map fst s \<longrightarrow> SN_on (lpc_answer_steps P) {s}"
    if sn: "SN_on (lp_cut_mgu_source P) {qs}" for qs
  proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
    fix qs and s :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
    assume ih: "\<And>rs. (qs,rs)\<in>lp_cut_mgu_source P \<Longrightarrow>
      \<forall>t :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
        ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list.
        rs=map fst t \<longrightarrow> SN_on (lpc_answer_steps P) {t}"
      and qs: "qs=map fst s"
    show "SN_on (lpc_answer_steps P) {s}"
    proof (rule step_reflects_SN_on)
      fix t assume "(s,t)\<in>lpc_answer_steps P"
      then have "(qs,map fst t)\<in>lp_cut_mgu_source P"
        using lpc_answer_transition_erases by (auto simp: lpc_answer_steps_def qs)
      then show "SN_on (lpc_answer_steps P) {t}" using ih by blast
    qed
  qed
  show "SN_on (lpc_answer_steps P) {ss}" using all[OF sn] by blast
qed

end
