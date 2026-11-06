theory LP_Prolog_Partial_Integer_Selection
  imports LP_Prolog_Partial_Integer_Failure
begin

lemma lpp_partial_failed_alternatives:
  assumes failed: "\<And>d saved. d\<in>set earlier \<Longrightarrow>
    (LPCClause (LPCAtom source_call#pending) d mark#saved,saved)\<in>R\<^sup>+"
  shows "(map (\<lambda>d. LPCClause (LPCAtom source_call#pending) d mark) earlier @ es,es)\<in>R\<^sup>*"
  using failed
proof (induct earlier)
  case Nil show ?case by simp
next
  case (Cons d earlier)
  have head: "(LPCClause (LPCAtom source_call#pending) d mark#
      (map (\<lambda>d. LPCClause (LPCAtom source_call#pending) d mark) earlier @ es),
      map (\<lambda>d. LPCClause (LPCAtom source_call#pending) d mark) earlier @ es)\<in>R\<^sup>+"
    by (rule Cons.prems) simp
  have tail: "(map (\<lambda>d. LPCClause (LPCAtom source_call#pending) d mark) earlier @ es,es)\<in>R\<^sup>*"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using rtrancl_trans[OF trancl_into_rtrancl[OF head] tail] by simp
qed

text \<open>Earlier clauses are traversed through their checked failure traces.
Every trace must restore its original saved stack. The chosen clause retains
all later alternatives and the freshly allocated cut barrier.\<close>

lemma lpp_partial_selected_clause_steps:
  assumes selection: "lp_cut_slice P (LPCUser f) (length xs)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        eta)#pending) d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
  shows "\<exists>mark. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        eta)#pending)#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t
        (lpc_fresh_head_environment xs eta))) bs @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        eta)#pending) d mark) cs @ LPCBarrier mark#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?eta = "eta"
  let ?source_call = "lp_ieval (Fun (LPCUser f) (map Var xs)) ?eta"
  let ?s = "LPCGoals (LPCAtom ?source_call#pending)#es"
  obtain mark where fresh_mark: "lp_cut_fresh mark ?s" using lpc_uniform_fresh by blast
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?source_call#pending) d mark) cs @ LPCBarrier mark#es"
  let ?chosen = "LPCClause (LPCAtom ?source_call#pending) c mark#?saved"
  let ?alternatives = "map (\<lambda>d. LPCClause (LPCAtom ?source_call#pending) d mark) earlier @ ?chosen"
  have selected: "(?s,?alternatives)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.case_call[of mark f "map ?eta xs" pending es P] fresh_mark
    by (simp add: selection o_def)
  have defined: "lpp_defined P (f,length xs)"
    unfolding lpp_defined_def list_ex_iff
    by (rule bexI[of _ "P!c"]) (use nth_mem[OF index] clause in auto)
  have source_selected: "(?s,?alternatives)\<in>lpp_builtin_source P lpp_integer_source_builtin"
    using selected ordinary defined
    by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have skipped: "(?alternatives,?chosen)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    by (rule lpp_partial_failed_alternatives) (rule failed)
  have mgu: "lpc_mgu_resolve ?source_call pending (fst (P!c)) (snd (P!c))
      lpc_fresh_caller (lpc_fresh_head_environment xs eta)"
    using lpc_fresh_head_mgu[where eta=eta and f="LPCUser f" and xs=xs and gs=pending and bs=bs]
    by (simp add: clause)
  have resolution: "(?chosen,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t (lpc_fresh_head_environment xs eta))) bs @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#?saved)
      \<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of mark ?saved] by (simp add: clause)
  have source_resolution: "(?chosen,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t (lpc_fresh_head_environment xs eta))) bs @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#?saved)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using resolution by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have joined: "(?s,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t (lpc_fresh_head_environment xs eta))) bs @ map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using source_selected skipped source_resolution
    by (meson r_into_trancl trancl_rtrancl_trancl trancl_trans)
  show ?thesis using joined by blast
qed

ML \<open>
val checked = [@{thm lpp_partial_failed_alternatives}, @{thm lpp_partial_selected_clause_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial clause selection dependency" else ();
\<close>
end
