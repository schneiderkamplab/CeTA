theory LP_Prolog_Answers
  imports LP_Cut_Return_Contracts LP_Prolog_Static
begin

text \<open>Atomic builtin operations extend the shared cut stack; they do not
replace it. Recognized builtin calls suppress ordinary clause dispatch, so a
guaranteed successful test does not gain a spurious failing alternative before
a cut. Each operation either succeeds with a substitution, fails into the
saved alternatives, or raises an uncaught error that clears the entire stack.
The operation relation U must be supplied by separately verified builtin
semantics. This interface alone neither proves that a builtin evaluation
finishes nor covers enumerating builtins with their own choice points.\<close>

datatype ('f,'w) lpp_builtin_result =
    LPPBuiltinSuccess "'w \<Rightarrow> ('f lp_cut_symbol,'w) lp_iterm"
  | LPPBuiltinFailure | LPPBuiltinError
  | LPPBuiltinProbe "('f lp_cut_symbol,'w) lp_iterm" bool


text \<open>An opaque first-answer probe invokes a single callable atom using
fresh commit and local cut scopes. Its failure alternative retains the original
environment. This extends the existing annotated cut stack; helper termination
and all later source steps remain obligations of the same graph.\<close>

definition lpp_probe_goals where
  "lpp_probe_goals a keep m gs = LPCAtom a # LPCCut m # (if keep then LPCTrue else LPCFail) # gs"

definition lpp_probe_else where
  "lpp_probe_else keep gs = (if keep then LPCFail else LPCTrue) # gs"


inductive_set lpp_atomic_source ::
  "('f,string) lp_cut_program \<Rightarrow> ('f \<times> nat) set \<Rightarrow>
   ('f \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm list \<Rightarrow>
      ('f,string) lpp_builtin_result \<Rightarrow> bool) \<Rightarrow>
   ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list rel"
  for P B U where
  base: "\<not>lpp_builtin_active B s \<Longrightarrow> (s,t)\<in>lp_cut_mgu_source P \<Longrightarrow>
    (s,t)\<in>lpp_atomic_source P B U"
| success: "U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)#es)
       \<in>lpp_atomic_source P B U"
| failure: "U f ts LPPBuiltinFailure \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,es)
       \<in>lpp_atomic_source P B U"
| error: "U f ts LPPBuiltinError \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,[])
       \<in>lpp_atomic_source P B U"

| probe: "U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
    lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
      LPCGoals (lpp_probe_goals a keep m gs)#LPCBarrier n#
      LPCGoals (lpp_probe_else keep gs)#LPCBarrier m#es) \<in>lpp_atomic_source P B U"

inductive lpp_answer_transition ::
  "('f,string) lp_cut_program \<Rightarrow> ('f \<times> nat) set \<Rightarrow>
   ('f \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm list \<Rightarrow>
      ('f,string) lpp_builtin_result \<Rightarrow> bool) \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow>
   ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) option \<Rightarrow>
   (('f lp_cut_symbol,string) lp_iterm lp_cut_entry \<times>
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list \<Rightarrow> bool"
  for P B U where
  base: "\<not>lpp_builtin_active B (map fst ss) \<Longrightarrow>
    lpc_answer_transition P ss event tt \<Longrightarrow>
    lpp_answer_transition P B U ss event tt"
| success: "U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
    lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es)
      None ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
        \<lambda>x. lp_isubst (eta x) sigma)#es)"
| failure: "U f ts LPPBuiltinFailure \<Longrightarrow>
    lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es)
      None es"
| error: "U f ts LPPBuiltinError \<Longrightarrow>
    lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es)
      None []"

| probe: "U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
    lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es) \<Longrightarrow>
    lp_cut_fresh n (LPCBarrier m#LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#map fst es) \<Longrightarrow>
    lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es)
      None ((LPCGoals (lpp_probe_goals a keep m gs),eta)#(LPCBarrier n,eta)#
        (LPCGoals (lpp_probe_else keep gs),eta)#(LPCBarrier m,eta)#es)"

lemma lpp_answer_transition_erases:
  "lpp_answer_transition P B U ss event tt \<Longrightarrow>
   (map fst ss,map fst tt)\<in>lpp_atomic_source P B U"
  by (erule lpp_answer_transition.cases)
    (auto intro: lpp_atomic_source.intros dest: lpc_answer_transition_erases)

lemma lpp_atomic_source_empty:
  "([],t)\<notin>lpp_atomic_source P B U"
  by (auto elim: lpp_atomic_source.cases simp: lp_cut_mgu_source_empty)

lemma lpp_answer_source_lifts:
  assumes st: "(map fst ss,t)\<in>lpp_atomic_source P B U"
  shows "\<exists>event tt. lpp_answer_transition P B U ss event tt \<and> map fst tt=t"
proof -
  obtain e eta es where ss: "ss=(e,eta)#es"
    using st by (cases ss) (auto simp: lpp_atomic_source_empty)
  from st show ?thesis
  proof (cases rule: lpp_atomic_source.cases)
    case base
    then obtain event tt where "lpc_answer_transition P ss event tt" "map fst tt=t"
      using lpc_answer_source_lifts by blast
    then show ?thesis using base by (auto intro: lpp_answer_transition.base)
  qed (use ss in \<open>force intro: lpp_answer_transition.intros\<close>)+
qed

lemma lpp_answer_event_is_success:
  "lpp_answer_transition P B U ss (Some eta) tt \<Longrightarrow> ss=(LPCGoals [],eta)#tt"
  by (erule lpp_answer_transition.cases)
    (auto dest: lpc_answer_event_is_success)

theorem lpp_answer_instrumentation_SN:
  assumes sn: "SN_on (lp_answer_steps (lpp_answer_transition P B U)) {ss}"
  shows "SN_on (lpp_atomic_source P B U) {map fst ss}"
proof (rule SN_on_induct[OF sn singletonI])
  fix s assume ih: "\<And>t. (s,t)\<in>lp_answer_steps (lpp_answer_transition P B U) \<Longrightarrow>
    SN_on (lpp_atomic_source P B U) {map fst t}"
  show "SN_on (lpp_atomic_source P B U) {map fst s}"
  proof (rule step_reflects_SN_on)
    fix u assume "(map fst s,u)\<in>lpp_atomic_source P B U"
    then obtain event t where step: "lpp_answer_transition P B U s event t" and u: "u=map fst t"
      using lpp_answer_source_lifts by blast
    show "SN_on (lpp_atomic_source P B U) {u}"
      using ih[of t] step by (simp add: u lp_answer_steps_def; blast)
  qed
qed

definition lpp_return_contract where
  "lpp_return_contract P B U ss R t ret =
    (SN_on (lpp_atomic_source P B U) {map fst ss} \<and>
     (\<forall>us tail eta. (ss,us)\<in>(lp_answer_steps (lpp_answer_transition P B U))\<^sup>* \<longrightarrow>
       lpp_answer_transition P B U us (Some eta) tail \<longrightarrow> (t,ret eta)\<in>R\<^sup>*))"

theorem lpp_return_graph_contract:
  assumes valid: "lp_answer_graph_valid (lpp_answer_transition P B U) R rep ret weight"
    and sn: "SN_on R {t}" and represented: "rep ss t"
  shows "lpp_return_contract P B U ss R t ret"
proof -
  have source: "SN_on (lpp_atomic_source P B U) {map fst ss}"
    using lp_answer_graph_SN[OF valid sn represented] lpp_answer_instrumentation_SN by blast
  have returns: "(t,ret eta)\<in>R\<^sup>*"
    if path: "(ss,us)\<in>(lp_answer_steps (lpp_answer_transition P B U))\<^sup>*"
      and event: "lpp_answer_transition P B U us (Some eta) tail" for us eta tail
  proof -
    obtain u where before: "(t,u)\<in>R\<^sup>*" and rep: "rep us u"
      using lp_answer_graph_path[OF valid path represented] by blast
    have returned: "(u,ret eta)\<in>R\<^sup>*"
      using valid rep event unfolding lp_answer_graph_valid_def by blast
    show ?thesis by (rule rtrancl_trans[OF before returned])
  qed
  show ?thesis using source returns unfolding lpp_return_contract_def by blast
qed

corollary lpp_atomic_uncaught_errors:
  "SN_on (lpp_atomic_source P B U) {s} \<Longrightarrow>
   SN_on (lp_prolog_stop_extension (lpp_atomic_source P B U) E) {s}"
  by (rule lp_prolog_stop_extension_SN) (auto simp: lpp_atomic_source_empty)

text \<open>These are explicit preservation obligations: a successful builtin
updates the active continuation and its return environment only. Failure
restores saved environments, and an uncaught error never resumes them.\<close>

lemma lpp_builtin_failure_restores_saved:
  "U f ts LPPBuiltinFailure \<Longrightarrow>
   lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#(e,nu)#es)
     None ((e,nu)#es)"
  by (rule lpp_answer_transition.failure)

lemma lpp_builtin_error_clears_saved:
  "U f ts LPPBuiltinError \<Longrightarrow>
   lpp_answer_transition P B U ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) None []"
  by (rule lpp_answer_transition.error)


text \<open>Exact single-outcome rules prevent accidental fall-through to
clause lookup. These facts are the local obligations for deterministic primitive
coverage; the premise must be proved from interpreted builtin semantics.\<close>

lemma lpp_builtin_success_only:
  assumes selected: "(f,length ts)\<in>B"
    and outcomes: "\<And>r. U f ts r \<longleftrightarrow> r=LPPBuiltinSuccess sigma"
  shows "lpp_answer_transition P B U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs),
        \<lambda>x. lp_isubst (eta x) sigma)#es"
  using selected outcomes
  by (auto simp: outcomes lpp_builtin_active_def elim: lpp_answer_transition.cases
    intro: lpp_answer_transition.success)

lemma lpp_builtin_failure_only:
  assumes selected: "(f,length ts)\<in>B"
    and outcomes: "\<And>r. U f ts r \<longleftrightarrow> r=LPPBuiltinFailure"
  shows "lpp_answer_transition P B U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) event tt
    \<longleftrightarrow> event=None \<and> tt=es"
  using selected outcomes
  by (auto simp: outcomes lpp_builtin_active_def elim: lpp_answer_transition.cases
    intro: lpp_answer_transition.failure)

lemma lpp_builtin_error_only:
  assumes selected: "(f,length ts)\<in>B"
    and outcomes: "\<And>r. U f ts r \<longleftrightarrow> r=LPPBuiltinError"
  shows "lpp_answer_transition P B U
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#es) event tt
    \<longleftrightarrow> event=None \<and> tt=[]"
  using selected outcomes
  by (auto simp: outcomes lpp_builtin_active_def elim: lpp_answer_transition.cases
    intro: lpp_answer_transition.error)

end
