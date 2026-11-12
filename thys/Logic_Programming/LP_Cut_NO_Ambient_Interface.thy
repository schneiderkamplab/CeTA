theory LP_Cut_NO_Ambient_Interface
 imports LP_Cut_NO_Return_Check LP_Cut_Finite_Interface_Renaming
begin

text \<open>Caller-only variables are carried as additional return coordinates.
A checked substitution fixes them when its finite domain is disjoint from
their variables. Renaming the private trace preserves this fact without
requiring caller variables to fit a fixed string-length namespace.\<close>

lemma lpc_mgu_substitution_outside:
 assumes "length V = length images" "x \<notin> set V"
 shows "lpc_mgu_substitution V images x = Var x"
proof -
 have "map_of (zip V images) x = None" using assms by simp
 then show ?thesis by (simp add: lpc_mgu_substitution_def)
qed

lemma lpc_conjugate_substitution_apply:
 assumes inverse: "\<And>x. p (p x) = x"
 shows "(t\<cdot>(Var \<circ> p))\<cdot>lpc_conjugate_substitution p s =
   (t\<cdot>s)\<cdot>(Var \<circ> p)"
 by (induct t) (auto simp: lpc_conjugate_substitution_def inverse o_def intro!: map_cong)

lemma lpc_conjugate_substitution_outside:
 assumes inverse: "\<And>x. p (p x) = x"
   and lengths: "length V = length images"
   and outside: "x \<notin> p ` set V"
 shows "lpc_conjugate_substitution p (lpc_mgu_substitution V images) x = Var x"
proof -
 have "p x \<notin> set V"
 proof
  assume "p x \<in> set V"
  then have "p (p x) \<in> p ` set V" by (rule imageI)
  then show False using outside by (simp add: inverse)
 qed
 then show ?thesis
   by (simp add: lpc_conjugate_substitution_def
     lpc_mgu_substitution_outside[OF lengths] inverse o_def)
qed

lemma lpc_substitution_fixes_ambient_terms:
 assumes fixed: "\<And>x. x\<in>\<Union>(vars_term ` set extra) \<Longrightarrow> substitution x = Var x"
 shows "map (\<lambda>t. t\<cdot>substitution) extra = extra"
proof -
 have same: "t\<cdot>substitution = t" if "\<forall>x\<in>vars_term t. substitution x = Var x" for t
   by (rule subst_apply_term_ident) (use that in \<open>auto simp: subst_domain_def\<close>)
 show ?thesis by (rule map_idI) (use same fixed in blast)
qed

lemma lpc_fresh_trace_substitutions:
 fixes A S C :: "string set"
   and substitutions :: "(string \<Rightarrow> ('f,string) term) list"
 assumes finite: "finite A" "finite S" "finite C"
   and separate: "A \<inter> C = {}"
   and support: "\<And>substitution x. substitution\<in>set substitutions \<Longrightarrow>
     x\<notin>S \<Longrightarrow> substitution x = Var x"
 shows "\<exists>p. (\<forall>x. p (p x) = x) \<and> (\<forall>x\<in>A. p x = x) \<and>
   p ` (S-A) \<inter> C = {} \<and>
   (\<forall>substitution\<in>set substitutions. \<forall>x\<in>C.
     lpc_conjugate_substitution p substitution x = Var x)"
proof -
 have finite_private: "finite (S-A)" using finite by simp
 have disjoint: "A \<inter> (S-A) = {}" by blast
 obtain p :: "string \<Rightarrow> string" where inverse: "\<forall>x. p (p x) = x"
   and bijective: "bij p"
   and fixed: "\<forall>x\<in>A. p x = x"
   and moved: "p ` (S-A) \<inter> (A \<union> (S-A) \<union> C) = {}"
   using lpc_fresh_private_involution[OF finite(1) finite_private finite(3) disjoint]
   by (elim exE conjE) assumption
 have outside: "p x \<notin> S" if caller: "x\<in>C" for x
 proof
   assume member: "p x\<in>S"
   show False
   proof (cases "p x\<in>A")
     case True
     have "p (p x) = p x" using fixed True by blast
     then have "x = p x" using inverse by simp
     have "x\<in>A" by (subst \<open>x = p x\<close>) (rule True)
     then show False using caller separate by blast
   next
     case False
     have "p (p x)\<in>p ` (S-A)" by (rule imageI) (use member False in simp)
     then have "x\<in>p ` (S-A)" using inverse by simp
     then show False using caller moved by blast
   qed
 qed
 have ambient: "lpc_conjugate_substitution p substitution x = Var x"
   if "substitution\<in>set substitutions" "x\<in>C" for substitution x
   using support[OF that(1) outside[OF that(2)]] inverse
   by (simp add: lpc_conjugate_substitution_def o_def)
 show ?thesis
 proof (rule exI[of _ p], intro conjI)
   show "\<forall>x. p (p x) = x" by (rule inverse)
   show "\<forall>x\<in>A. p x = x" by (rule fixed)
   show "p ` (S-A) \<inter> C = {}" using moved by blast
   show "\<forall>substitution\<in>set substitutions. \<forall>x\<in>C.
     lpc_conjugate_substitution p substitution x = Var x"
     by (intro ballI, rule ambient; assumption)
 qed
qed

lemma lpc_return_ambient_update:
 assumes result: "result = map (\<lambda>t. t\<cdot>substitution) payload"
   and fixed: "map (\<lambda>t. t\<cdot>substitution) extra = extra"
 shows "lpc_return_env (result@extra) LPIVar =
   (\<lambda>n. lp_isubst (lpc_return_env (payload@extra) LPIVar n)
     (\<lambda>x. lp_ieval (substitution x) LPIVar))"
proof (rule lpc_return_env_active)
 have all: "result@extra = map (\<lambda>t. t\<cdot>substitution) (payload@extra)"
   using result fixed by simp
 show "map (\<lambda>t. lp_ieval t LPIVar) (result@extra) =
   map (\<lambda>t. lp_isubst (lp_ieval t LPIVar) (\<lambda>x. lp_ieval (substitution x) LPIVar)) (payload@extra)"
   by (simp only: all map_map o_def lp_ieval_finite_subst lp_ieval_subst; simp)
qed

lemma lpc_global_return_resolve_ambient:
 fixes P :: "('f,string) lp_cut_program"
 assumes index: "c<length P"
   and mgu: "lpc_global_mgu [(a,fst (P!c)\<cdot>(Var \<circ> rename_clause_var))] substitution"
   and injective: "inj_on rename_clause_var B"
   and head_vars: "vars_term (fst (P!c)) \<subseteq> B"
   and body_vars: "\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> B"
   and fresh_a: "vars_term a \<inter> rename_clause_var ` B = {}"
   and fresh_goals: "\<forall>g\<in>set (gs @ map LPCAtom (payload@extra)). \<forall>t\<in>set (lp_cut_terms g).
     vars_term t \<inter> rename_clause_var ` B = {}"
   and fixed: "map (\<lambda>t. t\<cdot>substitution) extra = extra"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCClause (LPCAtom a#gs) c m,payload@extra)#saved))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_bind m (\<lambda>t. t\<cdot>(substitution \<circ> rename_clause_var))) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. t\<cdot>substitution)) gs),
       map (\<lambda>t. t\<cdot>substitution) payload @ extra)#saved)))"
proof -
 have actual: "lpc_mgu_resolve (lp_ieval a LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs @
     map (\<lambda>t. LPCAtom (lp_ieval t LPIVar)) (payload@extra))
   (fst (P!c)) (snd (P!c))
   (\<lambda>x. lp_ieval (substitution x) LPIVar)
   (\<lambda>x. lp_ieval (substitution (rename_clause_var x)) LPIVar)"
   using lpc_global_mgu_resolve_fresh_support[OF mgu[unfolded o_def] injective head_vars body_vars fresh_a fresh_goals]
   by (simp add: map_map o_def)
 note answers = lpc_return_ambient_update[OF refl fixed, of payload]
 note step = lpc_return_resolve_attach[OF index actual,
   of rest m "lpc_return_eval LPIVar saved"]
 show ?thesis using step
   by (simp add: lpc_return_eval_def answers map_map o_def
     lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

ML \<open>
val checked = [@{thm lpc_conjugate_substitution_apply},
 @{thm lpc_conjugate_substitution_outside}, @{thm lpc_substitution_fixes_ambient_terms},
 @{thm lpc_fresh_trace_substitutions}, @{thm lpc_return_ambient_update}, @{thm lpc_global_return_resolve_ambient}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ambient interface dependency" else ();
\<close>
end
