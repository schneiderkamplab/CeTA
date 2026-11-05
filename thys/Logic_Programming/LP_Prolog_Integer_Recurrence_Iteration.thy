theory LP_Prolog_Integer_Recurrence_Iteration
  imports LP_Prolog_Integer_Recurrence_Body
begin

text \<open>One complete source recurrence preserves all clause alternatives.
The case/resolution prefix supplies strict progress even when the arithmetic
body is empty. No termination residual is interpreted as a NO proof here.\<close>

lemma lpp_recurrence_bind_goal:
  "lp_cut_bind m h (lpp_recurrence_goal op) = lp_cut_map h (lpp_recurrence_goal op)"
  by (cases op) simp_all

lemma lpp_recurrence_source_iteration:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),
      map lpp_recurrence_goal ops @ [LPCAtom tail])"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
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
    using lpp_integer_recurrence_first_clause_steps[OF first index clause ground fresh ordinary] by blast
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

lemma lpp_recurrence_source_nontermination:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),
      map lpp_recurrence_goal ops @ [LPCAtom tail])"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
    and checked: "lpp_recurrence_check xs ops"
    and child: "\<not>SN_on S {rho}"
    and guards: "\<And>a b. (a,b)\<in>S \<Longrightarrow> lpp_recurrence_guards ops a"
    and tail_value: "\<And>a b. (a,b)\<in>S \<Longrightarrow>
      lp_ieval tail (lpp_recurrence_environment (lpp_recurrence_known xs ops)
        (lpp_recurrence_values ops a)) =
      lp_ieval (Fun (LPCUser f) (map Var xs)) (lpp_recurrence_environment xs b)"
  shows "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
    {LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs))
      (lpp_recurrence_environment xs rho))]#es}"
proof -
  let ?call = "\<lambda>a. lp_ieval (Fun (LPCUser f) (map Var xs)) (lpp_recurrence_environment xs a)"
  let ?rep = "\<lambda>a s. \<exists>saved. s=LPCGoals [LPCAtom (?call a)]#saved"
  have represented: "?rep rho (LPCGoals [LPCAtom (?call rho)]#es)" by blast
  have simulate: "\<exists>v. ?rep b v \<and>
      (u,v)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    if edge: "(a,b)\<in>S" and represented: "?rep a u" for a b u
  proof -
    obtain saved where state: "u=LPCGoals [LPCAtom (?call a)]#saved"
      using represented by blast
    have "\<exists>m. (u,LPCGoals [LPCAtom (?call b)]#
        (map (\<lambda>d. LPCClause [LPCAtom (?call a)] d m) cs @ LPCBarrier m#saved))
        \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
      using lpp_recurrence_source_iteration[OF first index clause ordinary checked guards[OF edge],
        where es=saved] tail_value[OF edge] state by simp
    then show ?thesis by blast
  qed
  show ?thesis by (rule lp_source_nontermination_simulation[
    where S=S and rep="?rep", OF child represented simulate])
qed

ML \<open>
val checked = [@{thm lpp_recurrence_source_iteration},
  @{thm lpp_recurrence_source_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted complete source recurrence dependency" else ();
\<close>
end
