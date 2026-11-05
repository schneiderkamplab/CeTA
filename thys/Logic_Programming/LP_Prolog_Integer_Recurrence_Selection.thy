theory LP_Prolog_Integer_Recurrence_Selection
  imports LP_Prolog_Integer_Recurrence_Backtracking
begin

lemma lpp_recurrence_failed_alternatives:
  assumes failed: "\<And>d saved. d\<in>set earlier \<Longrightarrow>
    (LPCClause [LPCAtom source_call] d mark#saved,saved)\<in>R\<^sup>+"
  shows "(map (\<lambda>d. LPCClause [LPCAtom source_call] d mark) earlier @ es,es)\<in>R\<^sup>*"
  using failed
proof (induct earlier)
  case Nil show ?case by simp
next
  case (Cons d earlier)
  have head: "(LPCClause [LPCAtom source_call] d mark#
      (map (\<lambda>d. LPCClause [LPCAtom source_call] d mark) earlier @ es),
      map (\<lambda>d. LPCClause [LPCAtom source_call] d mark) earlier @ es)\<in>R\<^sup>+"
    by (rule Cons.prems) simp
  have tail: "(map (\<lambda>d. LPCClause [LPCAtom source_call] d mark) earlier @ es,es)\<in>R\<^sup>*"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case using rtrancl_trans[OF trancl_into_rtrancl[OF head] tail] by simp
qed

text \<open>Earlier clauses are traversed through their checked failure traces.
Every trace must restore its original saved stack. The chosen clause retains
all later alternatives and the freshly allocated cut barrier.\<close>

lemma lpp_recurrence_selected_clause_steps:
  assumes selection: "lp_cut_slice P (LPCUser f) (length xs)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))] d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
  shows "\<exists>mark. (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))]#es,
      LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t
        (lpp_recurrence_environment xs rho))) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))] d mark) cs @ LPCBarrier mark#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?eta = "lpp_recurrence_environment xs rho"
  let ?source_call = "lp_ieval (Fun (LPCUser f) (map Var xs)) ?eta"
  let ?s = "LPCGoals [LPCAtom ?source_call]#es"
  obtain mark where fresh_mark: "lp_cut_fresh mark ?s" using lpc_uniform_fresh by blast
  let ?saved = "map (\<lambda>d. LPCClause [LPCAtom ?source_call] d mark) cs @ LPCBarrier mark#es"
  let ?chosen = "LPCClause [LPCAtom ?source_call] c mark#?saved"
  let ?alternatives = "map (\<lambda>d. LPCClause [LPCAtom ?source_call] d mark) earlier @ ?chosen"
  have selected: "(?s,?alternatives)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.case_call[of mark f "map ?eta xs" "[]" es P] fresh_mark
    by (simp add: selection o_def)
  have defined: "lpp_defined P (f,length xs)"
    unfolding lpp_defined_def list_ex_iff
    by (rule bexI[of _ "P!c"]) (use nth_mem[OF index] clause in auto)
  have source_selected: "(?s,?alternatives)\<in>lpp_builtin_source P lpp_integer_source_builtin"
    using selected ordinary defined
    by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have skipped: "(?alternatives,?chosen)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    by (rule lpp_recurrence_failed_alternatives) (rule failed)
  have ground: "lp_seg_ground (?eta x)" if "x\<in>set xs" for x
    using that by (auto simp: lpp_recurrence_environment_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have fresh: "?eta x=LPIVar x" if "x\<notin>set xs" for x
    using that by (simp add: lpp_recurrence_environment_def)
  have mgu: "lpc_mgu_resolve ?source_call [] (fst (P!c)) (snd (P!c)) LPIVar ?eta"
    using lpc_ground_head_fresh_body_mgu[where f="LPCUser f" and bs=bs, OF ground fresh]
    by (simp add: clause)
  have resolution: "(?chosen,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?eta)) bs)#?saved)
      \<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of mark ?saved] by (simp add: clause)
  have source_resolution: "(?chosen,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?eta)) bs)#?saved)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using resolution by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have joined: "(?s,LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?eta)) bs)#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using source_selected skipped source_resolution
    by (meson r_into_trancl trancl_rtrancl_trancl trancl_trans)
  show ?thesis using joined by blast
qed

lemma lpp_recurrence_selected_source_iteration:
  assumes selection: "lp_cut_slice P (LPCUser f) (length xs)=earlier@c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),
      map lpp_recurrence_goal ops @ [LPCAtom tail])"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
    and failed: "\<And>d mark saved. d\<in>set earlier \<Longrightarrow>
      (LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))] d mark#saved,saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    and checked: "lpp_recurrence_check xs ops"
    and guards: "lpp_recurrence_guards ops rho"
  shows "\<exists>m. (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))]#es,
      LPCGoals [LPCAtom (lp_ieval tail
        (lpp_recurrence_environment (lpp_recurrence_known xs ops)
          (lpp_recurrence_values ops rho)))]#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
        (lpp_recurrence_environment xs rho))] d m) cs @ LPCBarrier m#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?eta = "lpp_recurrence_environment xs rho"
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var xs)) ?eta"
  let ?bs = "map lpp_recurrence_goal ops @ [LPCAtom tail]"
  have ground: "lp_seg_ground (?eta x)" if "x\<in>set xs" for x
    using that by (auto simp: lpp_recurrence_environment_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have fresh: "?eta x=LPIVar x" if "x\<notin>set xs" for x
    using that by (simp add: lpp_recurrence_environment_def)
  obtain m where prefix: "(LPCGoals [LPCAtom ?a]#es,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t ?eta)) ?bs)#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_recurrence_selected_clause_steps[OF selection index clause ordinary failed] by blast
  let ?saved = "map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es"
  have binding: "map (lp_cut_bind m h) ?bs = map (lp_cut_map h) ?bs" for h
    by (simp add: map_map lpp_recurrence_bind_goal o_def)
  note body = lpp_recurrence_body_source_steps[OF checked guards,
    where rest="[LPCAtom tail]" and es="?saved" and P=P]
  have joined: "(LPCGoals [LPCAtom ?a]#es,
      LPCGoals [LPCAtom (lp_ieval tail
        (lpp_recurrence_environment (lpp_recurrence_known xs ops)
          (lpp_recurrence_values ops rho)))]#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
  proof (rule trancl_rtrancl_trancl[OF prefix])
    show "(LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t ?eta)) ?bs)#?saved,
      LPCGoals [LPCAtom (lp_ieval tail
        (lpp_recurrence_environment (lpp_recurrence_known xs ops)
          (lpp_recurrence_values ops rho)))]#?saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
      using body by (simp only: binding list.map lp_cut_map.simps)
  qed
  show ?thesis using joined by blast
qed

ML \<open>
val checked = [@{thm lpp_recurrence_failed_alternatives},
  @{thm lpp_recurrence_selected_clause_steps},
  @{thm lpp_recurrence_selected_source_iteration}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic clause selection dependency" else ();
\<close>
end
