theory LP_Cut_Source
  imports LP_Cut_Control LP_Infinite_Terms
begin

text \<open>Source-bound ordered resolution with scoped cuts. Built-in symbols
are tagged, so source predicates cannot alias controls. Runtime values include
rational trees. The relation below deliberately permits all successful unifiers;
it is a termination overapproximation, NOT a nontermination semantics. Clause
failure requires absence of a unifier, not failure of bounded search.\<close>

datatype 'f lp_cut_symbol = LPCUser 'f | LPCBang | LPCComma | LPCEquals
  | LPCTruth | LPCFailure | LPCCallSymbol

fun lp_cut_map where
  "lp_cut_map f (LPCAtom a) = LPCAtom (f a)"
| "lp_cut_map f (LPCCut m) = LPCCut m"
| "lp_cut_map f LPCTrue = LPCTrue"
| "lp_cut_map f LPCFail = LPCFail"
| "lp_cut_map f (LPCMeta a) = LPCMeta (f a)"
| "lp_cut_map f (LPCExpand a m) = LPCExpand (f a) m"
| "lp_cut_map f (LPCUnify a b) = LPCUnify (f a) (f b)"

fun lp_cut_bind where
  "lp_cut_bind m f (LPCCut n) = LPCCut m"
| "lp_cut_bind m f g = lp_cut_map f g"

fun lp_cut_goal_scopes where
  "lp_cut_goal_scopes (LPCCut m) = {m}"
| "lp_cut_goal_scopes (LPCExpand a m) = {m}"
| "lp_cut_goal_scopes g = {}"

fun lp_cut_entry_scopes where
  "lp_cut_entry_scopes (LPCGoals gs) = \<Union>(lp_cut_goal_scopes ` set gs)"
| "lp_cut_entry_scopes (LPCClause gs c m) = insert m (\<Union>(lp_cut_goal_scopes ` set gs))"
| "lp_cut_entry_scopes (LPCBarrier m) = {m}"

definition lp_cut_fresh where
  "lp_cut_fresh m es = (m \<notin> \<Union>(lp_cut_entry_scopes ` set es))"

definition lp_cut_slice where
  "lp_cut_slice P f n = filter (\<lambda>c. \<exists>ts. fst (P!c) = Fun f ts \<and> length ts=n) [0..<length P]"

type_synonym ('f,'v) lp_cut_program =
  "(('f lp_cut_symbol,'v) term \<times> ('f lp_cut_symbol,'v) term lp_cut_goal list) list"

text \<open>Decode a meta-called conjunction before executing it. A variable
leaf is an opaque meta-call even if an earlier conjunct subsequently binds it
to a cut. Decoding one conjunct at a time after substitution would change cut
scope. Infinite conjunction spines have no finite lowering derivation.\<close>

inductive lp_cut_lower ::
  "nat \<Rightarrow> ('f lp_cut_symbol,'w) lp_iterm \<Rightarrow>
    ('f lp_cut_symbol,'w) lp_iterm lp_cut_goal list \<Rightarrow> bool" for m where
  variable: "lp_cut_lower m (LPIVar x) [LPCMeta (LPIVar x)]"
| atom: "lp_cut_lower m (LPIFun (LPCUser f) ts) [LPCAtom (LPIFun (LPCUser f) ts)]"
| cut: "lp_cut_lower m (LPIFun LPCBang []) [LPCCut m]"
| conjunction: "lp_cut_lower m a as \<Longrightarrow> lp_cut_lower m b bs \<Longrightarrow>
    lp_cut_lower m (LPIFun LPCComma [a,b]) (as@bs)"
| unify: "lp_cut_lower m (LPIFun LPCEquals [a,b]) [LPCUnify a b]"
| true: "lp_cut_lower m (LPIFun LPCTruth []) [LPCTrue]"
| fail: "lp_cut_lower m (LPIFun LPCFailure []) [LPCFail]"
| call: "lp_cut_lower m (LPIFun LPCCallSymbol [a]) [LPCMeta a]"

lemma lp_cut_lower_deterministic:
  assumes "lp_cut_lower m a gs" "lp_cut_lower m a hs"
  shows "gs=hs"
  using assms
proof (induct arbitrary: hs rule: lp_cut_lower.induct)
  case (variable x)
  from variable.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case (atom f ts)
  from atom.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case cut
  from cut.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case (conjunction a as b bs)
  from conjunction.prems obtain xs ys where
    shape: "hs=xs@ys" and left: "lp_cut_lower m a xs" and right: "lp_cut_lower m b ys"
    by (cases rule: lp_cut_lower.cases) auto
  have "as=xs" using conjunction.hyps left by blast
  moreover have "bs=ys" using conjunction.hyps right by blast
  ultimately show ?case using shape by simp
next
  case (unify a b)
  from unify.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case true
  from true.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case fail
  from fail.prems show ?case by (cases rule: lp_cut_lower.cases) auto
next
  case (call a)
  from call.prems show ?case by (cases rule: lp_cut_lower.cases) auto
qed

lemma lp_cut_lower_variable_not_transparent:
  "lp_cut_lower m (LPIVar x) gs \<Longrightarrow> gs=[LPCMeta (LPIVar x)]"
  by (erule lp_cut_lower.cases) auto

inductive_set lp_cut_source ::
  "('f,'v) lp_cut_program \<Rightarrow>
   ('f lp_cut_symbol,'w) lp_iterm lp_cut_entry list rel"
  for P where
  admin: "lp_cut_admin s = Some t \<Longrightarrow> (s,t) \<in> lp_cut_source P"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
     map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
       (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m # es) \<in> lp_cut_source P"
| resolve: "c<length P \<Longrightarrow> lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho> \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es,
     LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) # es) \<in> lp_cut_source P"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::'w \<Rightarrow> ('f lp_cut_symbol,'w) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es, es) \<in> lp_cut_source P"
| unify: "lp_isubst a \<sigma> = lp_isubst b \<sigma> \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#es) \<in> lp_cut_source P"
| unify_fail: "\<not>(\<exists>\<sigma>::'w \<Rightarrow> ('f lp_cut_symbol,'w) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es, es) \<in> lp_cut_source P"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow>
    (LPCGoals (LPCMeta a#gs)#es,
     LPCGoals (body@gs)#LPCBarrier m#es) \<in> lp_cut_source P"
| meta_unlowerable:
    "\<not>(\<exists>m body. lp_cut_lower m a body) \<Longrightarrow>
     (LPCGoals (LPCMeta a#gs)#es, LPCGoals (LPCMeta a#gs)#es) \<in> lp_cut_source P"

text \<open>The self-loop for unavailable lowering is deliberately conservative:
cyclic conjunction expansion must not become an artificial terminating leaf.
Unsupported meta-calls cannot be certified by this YES relation.\<close>

lemma lp_cut_lower_variable_is_opaque:
  "lp_cut_lower m (LPIFun LPCComma [LPIFun LPCEquals [LPIVar x,LPIFun LPCBang []],LPIVar x])
    [LPCUnify (LPIVar x) (LPIFun LPCBang []),LPCMeta (LPIVar x)]"
  using lp_cut_lower.conjunction[OF lp_cut_lower.unify lp_cut_lower.variable] by simp

text \<open>All administrative rules are included without changing their scope.
Success returns to saved alternatives, because the property is universal
termination (exhausting answers), not merely finding one answer.\<close>

lemma lp_cut_source_admin:
  "{(s,t). lp_cut_admin s=Some t} \<subseteq> lp_cut_source P"
  by (auto intro: lp_cut_source.admin)

lemma lp_cut_success_backtracks:
  "(LPCGoals [] # es, es) \<in> lp_cut_source P"
  by (rule lp_cut_source.admin) simp

lemma lp_cut_source_scope:
  "(LPCGoals (LPCCut m#gs)#LPCBarrier m#es,
    LPCGoals gs#LPCBarrier m#es) \<in> lp_cut_source P"
  by (rule lp_cut_source.admin) simp

lemma lp_cut_slice_indices:
  "c \<in> set (lp_cut_slice P f n) \<Longrightarrow> c<length P"
  by (auto simp: lp_cut_slice_def)

lemma lp_cut_slice_ordered:
  "List.sorted (lp_cut_slice P f n) \<and> distinct (lp_cut_slice P f n)"
  using List.sorted_filter[of id "[0..<length P]"
    "\<lambda>c. \<exists>ts. fst (P!c) = Fun f ts \<and> length ts=n"]
  by (simp add: lp_cut_slice_def)

lemma lp_cut_eval_subst:
  "lp_ieval (t\<cdot>\<theta>) \<eta> = lp_ieval t (\<lambda>x. lp_ieval (\<theta> x) \<eta>)"
  by (induct t) (auto intro!: map_cong)

text \<open>A syntactic head match suffices for every represented call to
unify. Mere unifiability of the two symbolic terms does not suffice.\<close>

lemma lp_cut_head_match_possible:
  fixes \<eta> :: "'v \<Rightarrow> ('f,'w) lp_iterm"
  assumes "h\<cdot>\<theta> = a"
  shows "\<exists>\<sigma>::'w \<Rightarrow> ('f,'w) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
proof (intro exI[where x=LPIVar] exI[where x="\<lambda>x. lp_ieval (\<theta> x) \<eta>"])
  show "lp_isubst (lp_ieval a \<eta>) LPIVar = lp_ieval h (\<lambda>x. lp_ieval (\<theta> x) \<eta>)"
    using assms by (simp add: lp_cut_eval_subst[symmetric])
qed

lemma lp_cut_resolve_does_not_substitute_choices:
  assumes "c<length P" "lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>"
  shows "(LPCClause (LPCAtom a#gs) c m # es,
     LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) # es) \<in> lp_cut_source P"
  by (rule lp_cut_source.resolve[OF assms])

end
