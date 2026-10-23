theory LP_Cut_Most_General_Source
  imports LP_Cut_Negative_Guards
begin

text \<open>Precision layer only: this theory does not add an accepting checker.
The most-generality obligation covers the active continuation and fresh body
variables as well as the selected atom. Restricting only the equation's variables
would permit arbitrary instantiation of otherwise unconstrained body variables.
Saved alternatives are deliberately absent from the active substitution.\<close>

definition lpc_mgu_resolve ::
  "('f,string) lp_iterm \<Rightarrow> ('f,string) lp_iterm lp_cut_goal list \<Rightarrow>
   ('f,string) term \<Rightarrow> ('f,string) term lp_cut_goal list \<Rightarrow>
   (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow>
   (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool" where
  "lpc_mgu_resolve a gs h bs \<sigma> \<rho> =
    (lp_isubst a \<sigma> = lp_ieval h \<rho> \<and>
     (\<forall>\<tau> \<nu> :: string \<Rightarrow> ('f,string) lp_iterm. lp_isubst a \<tau> = lp_ieval h \<nu> \<longrightarrow>
       (\<exists>\<delta>.
         lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
           map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
           map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs)))"

definition lpc_mgu_unify ::
  "('f,string) lp_iterm \<Rightarrow> ('f,string) lp_iterm \<Rightarrow>
   ('f,string) lp_iterm lp_cut_goal list \<Rightarrow>
   (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool" where
  "lpc_mgu_unify a b gs \<sigma> =
    (lp_isubst a \<sigma> = lp_isubst b \<sigma> \<and>
     (\<forall>\<tau> :: string \<Rightarrow> ('f,string) lp_iterm. lp_isubst a \<tau> = lp_isubst b \<tau> \<longrightarrow>
       (\<exists>\<delta>.
         lp_isubst (lp_isubst a \<sigma>) \<delta> = lp_isubst a \<tau> \<and>
         map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t \<sigma>) \<delta>)) gs =
           map (lp_cut_map (\<lambda>t. lp_isubst t \<tau>)) gs)))"

lemma lpc_ieval_variables_eq:
  assumes "lp_ieval t \<rho> = lp_ieval t \<nu>" "x \<in> vars_term t"
  shows "\<rho> x = \<nu> x"
  using assms
proof (induct t)
  case (Var y) then show ?case by simp
next
  case (Fun f ts)
  from Fun.prems(2) obtain u where u: "u \<in> set ts" "x \<in> vars_term u" by auto
  have "lp_ieval u \<rho> = lp_ieval u \<nu>"
    using Fun.prems(1) u(1) by (auto simp: map_eq_conv)
  then show ?case using Fun.hyps u by blast
qed

lemma lpc_isubst_variable_reflect:
  "lp_isubst t \<delta> = LPIVar x \<Longrightarrow> \<exists>y. t = LPIVar y"
  by (cases t) auto

lemma lpc_mgu_body_factor:
  fixes a :: "('f,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    and comparison: "lp_isubst a \<tau> = lp_ieval h \<nu>"
  shows "\<exists>\<delta> :: string \<Rightarrow> ('f,string) lp_iterm.
    \<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
proof -
  from mgu comparison obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>)) bs =
     map (lp_cut_map (\<lambda>t. lp_ieval t \<nu>)) bs"
    unfolding lpc_mgu_resolve_def by blast
  show ?thesis
  proof (rule exI[of _ \<delta>], intro ballI)
    fix g t x assume body: "g \<in> set bs" and occurrence: "t \<in> set (lp_cut_terms g)"
      and variable: "x \<in> vars_term t"
    have eq: "lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t \<rho>) \<delta>) g =
      lp_cut_map (\<lambda>t. lp_ieval t \<nu>) g"
      using factor body by (simp add: map_eq_conv)
    have "lp_isubst (lp_ieval t \<rho>) \<delta> = lp_ieval t \<nu>"
      using eq occurrence by (cases g) auto
    then show "lp_isubst (\<rho> x) \<delta> = \<nu> x"
      using lpc_ieval_variables_eq[OF _ variable] by (simp add: lp_ieval_subst)
  qed
qed

text \<open>A freely variable comparison instance forces an MGU body variable
to remain a variable. A common factor also preserves separation of independent
variables. Neither property holds for an arbitrary successful unifier.\<close>

lemma lpc_mgu_body_variable_free:
  fixes a :: "('f,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    "lp_isubst a \<tau> = lp_ieval h \<nu>"
    "g \<in> set bs" "t \<in> set (lp_cut_terms g)" "x \<in> vars_term t"
    "\<nu> x = LPIVar y"
  shows "\<exists>z. \<rho> x = LPIVar z"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm"
    where "lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using lpc_mgu_body_factor[OF assms(1,2)] assms(3-5) by blast
  then have "lp_isubst (\<rho> x) \<delta> = LPIVar y" using assms(6) by simp
  then show ?thesis by (rule lpc_isubst_variable_reflect)
qed

lemma lpc_mgu_body_variables_separate:
  fixes a :: "('f,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    "lp_isubst a \<tau> = lp_ieval h \<nu>"
    "g \<in> set bs" "t \<in> set (lp_cut_terms g)" "x \<in> vars_term t"
    "g' \<in> set bs" "t' \<in> set (lp_cut_terms g')" "y \<in> vars_term t'"
    "\<nu> x \<noteq> \<nu> y"
  shows "\<rho> x \<noteq> \<rho> y"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using lpc_mgu_body_factor[OF assms(1,2)] by blast
  have x: "lp_isubst (\<rho> x) \<delta> = \<nu> x" using factor assms(3-5) by blast
  have y: "lp_isubst (\<rho> y) \<delta> = \<nu> y" using factor assms(6-8) by blast
  show ?thesis using x y assms(9) by auto
qed

lemma lpc_mgu_nullary_entry:
  "lpc_mgu_resolve (LPIFun f []) [] (Fun f []) bs LPIVar LPIVar"
  unfolding lpc_mgu_resolve_def
  apply (intro conjI)
   apply simp
  apply (intro allI impI)
  subgoal for \<tau> \<nu>
    by (rule exI[of _ \<nu>]) (simp add: lp_ieval_subst)
  done

lemma lpc_mgu_body_only_variable_free:
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
    and fresh: "x\<notin>vars_term h"
  shows "\<exists>y. \<rho> x = LPIVar y"
proof -
  let ?nu = "\<rho>(x := LPIVar x)"
  have head: "lp_ieval h ?nu = lp_ieval h \<rho>"
    by (rule lp_ieval_cong) (use fresh in auto)
  have comparison: "lp_isubst a \<sigma> = lp_ieval h ?nu"
    using mgu head by (simp add: lpc_mgu_resolve_def)
  show ?thesis
    by (rule lpc_mgu_body_variable_free[OF mgu comparison body]) simp
qed

lemma lpc_mgu_body_only_variables_separate:
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    and body: "g\<in>set bs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t"
      "g'\<in>set bs" "t'\<in>set (lp_cut_terms g')" "y\<in>vars_term t'"
    and fresh: "x\<notin>vars_term h" "y\<notin>vars_term h" "x\<noteq>y"
  shows "\<rho> x \<noteq> \<rho> y"
proof -
  let ?nu = "\<rho>(x := LPIVar x, y := LPIVar y)"
  have head: "lp_ieval h ?nu = lp_ieval h \<rho>"
    by (rule lp_ieval_cong) (use fresh in auto)
  have comparison: "lp_isubst a \<sigma> = lp_ieval h ?nu"
    using mgu head by (simp add: lpc_mgu_resolve_def)
  show ?thesis
    by (rule lpc_mgu_body_variables_separate[OF mgu comparison body]) (use fresh in simp)
qed

lemma lpc_mgu_nullary_body_is_renaming:
  fixes f :: 'f
  assumes mgu: "lpc_mgu_resolve (LPIFun f []) [] (Fun f []) bs \<sigma> \<rho>"
  defines "V \<equiv> \<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t"
  shows "\<exists>r. inj_on r V \<and> (\<forall>x\<in>V. \<rho> x = LPIVar (r x))"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = LPIVar x"
    using lpc_mgu_body_factor[OF mgu, of LPIVar LPIVar] by auto
  have eq: "\<And>x. x\<in>V \<Longrightarrow> lp_isubst (\<rho> x) \<delta> = LPIVar x"
    using factor by (auto simp: V_def)
  let ?r = "\<lambda>x. case \<rho> x of LPIVar y \<Rightarrow> y | LPIFun f ts \<Rightarrow> undefined"
  have variable: "\<And>x. x\<in>V \<Longrightarrow> \<rho> x = LPIVar (?r x)"
  proof -
    fix x assume "x\<in>V"
    then have "\<exists>y. \<rho> x = LPIVar y" by (rule lpc_isubst_variable_reflect[OF eq])
    then show "\<rho> x = LPIVar (?r x)" by auto
  qed
  have "inj_on ?r V"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>V" and y: "y\<in>V" and same: "?r x = ?r y"
    have same_rho: "\<rho> x = \<rho> y" using variable[OF x] variable[OF y] same by simp
    have same_eval: "lp_isubst (\<rho> x) \<delta> = lp_isubst (\<rho> y) \<delta>"
      by (rule arg_cong[OF same_rho])
    have "LPIVar x = (LPIVar y :: ('f,string) lp_iterm)"
      by (rule HOL.trans[OF eq[OF x, symmetric] HOL.trans[OF same_eval eq[OF y]]])
    then show "x=y" by (rule lp_iterm.inject(1)[THEN iffD1])
  qed
  then show ?thesis using variable by blast
qed

lemma lpc_mgu_rejects_instantiated_body_variable:
  "\<not>lpc_mgu_resolve (LPIFun f []) [] (Fun f [])
    [LPCAtom (Fun p [Var x])] \<sigma> (\<lambda>_. LPIFun c [])"
proof
  assume mgu: "lpc_mgu_resolve (LPIFun f []) [] (Fun f [])
    [LPCAtom (Fun p [Var x])] \<sigma> (\<lambda>_. LPIFun c [])"
  show False using lpc_mgu_nullary_body_is_renaming[OF mgu] by simp
qed

lemma lpc_mgu_rejects_collapsed_body_variables:
  "x\<noteq>y \<Longrightarrow> \<not>lpc_mgu_resolve (LPIFun f []) [] (Fun f [])
    [LPCAtom (Fun p [Var x,Var y])] \<sigma> (\<lambda>_. LPIVar z)"
proof
  assume xy: "x\<noteq>y"
  assume mgu: "lpc_mgu_resolve (LPIFun f []) [] (Fun f [])
    [LPCAtom (Fun p [Var x,Var y])] \<sigma> (\<lambda>_. LPIVar z)"
  obtain r where "inj_on r {x,y}" "r x=z" "r y=z"
    using lpc_mgu_nullary_body_is_renaming[OF mgu] by auto
  then show False using xy by (auto simp: inj_on_def)
qed

inductive_set lp_cut_mgu_source ::
  "('f,string) lp_cut_program \<Rightarrow>
   ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list rel"
  for P where
  admin: "lp_cut_admin s = Some t \<Longrightarrow> (s,t) \<in> lp_cut_mgu_source P"
| case_call: "lp_cut_fresh m (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es) \<Longrightarrow>
    (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
     map (\<lambda>c. LPCClause (LPCAtom (LPIFun (LPCUser f) ts)#gs) c m)
       (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m # es) \<in> lp_cut_mgu_source P"
| resolve: "c<length P \<Longrightarrow> lpc_mgu_resolve a gs (fst (P!c)) (snd (P!c)) \<sigma> \<rho> \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es,
     LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs) # es) \<in> lp_cut_mgu_source P"
| backtrack: "c<length P \<Longrightarrow> \<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>) \<Longrightarrow>
    (LPCClause (LPCAtom a#gs) c m # es, es) \<in> lp_cut_mgu_source P"
| unify: "lpc_mgu_unify a b gs \<sigma> \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es,
     LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs)#es) \<in> lp_cut_mgu_source P"
| unify_fail: "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>) \<Longrightarrow>
    (LPCGoals (LPCUnify a b#gs)#es, es) \<in> lp_cut_mgu_source P"
| meta: "lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#es) \<Longrightarrow>
    lp_cut_lower m a body \<Longrightarrow>
    (LPCGoals (LPCMeta a#gs)#es,
     LPCGoals (body@gs)#LPCBarrier m#es) \<in> lp_cut_mgu_source P"
| meta_unlowerable:
    "\<not>(\<exists>m body. lp_cut_lower m a body) \<Longrightarrow>
     (LPCGoals (LPCMeta a#gs)#es, LPCGoals (LPCMeta a#gs)#es) \<in> lp_cut_mgu_source P"

lemma lp_cut_mgu_source_subset:
  "lp_cut_mgu_source P \<subseteq> lp_cut_source P"
proof
  fix st assume "st \<in> lp_cut_mgu_source P"
  moreover obtain s t where "st = (s,t)" by (cases st) auto
  ultimately have "(s,t) \<in> lp_cut_mgu_source P" by simp
  then have "(s,t) \<in> lp_cut_source P"
    by (cases rule: lp_cut_mgu_source.cases)
      (auto simp: lpc_mgu_resolve_def lpc_mgu_unify_def intro: lp_cut_source.intros)
  then show "st \<in> lp_cut_source P"
    using \<open>st = (s,t)\<close> by simp
qed

theorem lp_cut_conservative_implies_mgu_SN:
  "SN_on (lp_cut_source P) S \<Longrightarrow> SN_on (lp_cut_mgu_source P) S"
  by (rule SN_on_subset1) (auto intro: lp_cut_mgu_source_subset[THEN subsetD])

text \<open>Before this relation can underpin additional certificates, source
standardization-apart, MGU coverage, and free-variable symbolic invariants must
be connected explicitly. The existing checker still proves the stronger
all-unifier theorem. This subset lemma alone does not justify any new YES/NO.\<close>

end
