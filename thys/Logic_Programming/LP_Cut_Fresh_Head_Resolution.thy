theory LP_Cut_Fresh_Head_Resolution
  imports LP_Cut_Ground_Recurrence
begin

text \<open>A variable head can match arbitrary runtime values, including rational
values and free output arguments. Separate injective namespaces for the caller
and fresh clause locals preserve most-generality on the entire active
continuation. This is a witness for the existing source resolution relation,
not a new operational rule. Saved alternatives are not substituted.\<close>

definition lpc_fresh_caller where
  "lpc_fresh_caller x = LPIVar (CHR ''0'' # x)"
definition lpc_fresh_local where
  "lpc_fresh_local x = LPIVar (CHR ''1'' # x)"

fun lpc_fresh_factor where
  "lpc_fresh_factor caller_values local_values [] = LPIVar []"
| "lpc_fresh_factor caller_values local_values (c#x) =
    (if c=CHR ''0'' then caller_values x else if c=CHR ''1'' then local_values x else LPIVar (c#x))"

definition lpc_fresh_head_environment where
  "lpc_fresh_head_environment xs eta x =
    (if x\<in>set xs then lp_isubst (eta x) lpc_fresh_caller else lpc_fresh_local x)"

lemma lpc_fresh_caller_factor:
  "lp_isubst (lp_isubst t lpc_fresh_caller) (lpc_fresh_factor caller_values local_values) = lp_isubst t caller_values"
  by (simp add: lpc_isubst_comp lpc_fresh_caller_def[abs_def])

lemma lpc_fresh_local_factor:
  "lp_isubst (lpc_fresh_local x) (lpc_fresh_factor caller_values local_values) = local_values x"
  by (simp add: lpc_fresh_local_def)

lemma lpc_fresh_local_assignment_preserves_caller:
  "lp_isubst (lp_isubst t lpc_fresh_caller)
    (LPIVar(CHR ''1'' # x := value)) = lp_isubst t lpc_fresh_caller"
  by (simp add: lpc_isubst_comp lpc_fresh_caller_def[abs_def])

lemma lpc_fresh_local_assignment:
  "lp_isubst (lpc_fresh_local y) (LPIVar(CHR ''1'' # x := value)) =
    (if y=x then value else lpc_fresh_local y)"
  by (simp add: lpc_fresh_local_def)

lemma lpc_fresh_head_mgu:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  shows "lpc_mgu_resolve (lp_ieval (Fun f (map Var xs)) eta) gs
    (Fun f (map Var xs)) bs lpc_fresh_caller (lpc_fresh_head_environment xs eta)"
proof -
  let ?a = "lp_ieval (Fun f (map Var xs)) eta"
  let ?rho = "lpc_fresh_head_environment xs eta"
  have equation: "lp_isubst ?a lpc_fresh_caller=lp_ieval (Fun f (map Var xs)) ?rho"
    by (auto simp: lpc_fresh_head_environment_def map_map o_def intro!: map_cong)
  have factor: "\<exists>delta. lp_isubst (lp_isubst ?a lpc_fresh_caller) delta=lp_isubst ?a caller_values \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t lpc_fresh_caller) delta)) gs =
        map (lp_cut_map (\<lambda>t. lp_isubst t caller_values)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) delta)) bs =
        map (lp_cut_map (\<lambda>t. lp_ieval t local_values)) bs"
    if comparison: "lp_isubst ?a caller_values=lp_ieval (Fun f (map Var xs)) local_values" for caller_values local_values :: "string \<Rightarrow> ('f,string) lp_iterm"
  proof -
    let ?delta = "lpc_fresh_factor caller_values local_values"
    have head: "lp_ieval (Fun f (map Var xs)) (\<lambda>x. lp_isubst (eta x) caller_values) =
        lp_ieval (Fun f (map Var xs)) local_values"
      using comparison by (simp only: lp_ieval_subst)
    have known: "lp_isubst (eta x) caller_values=local_values x" if "x\<in>set xs" for x
      using lpc_ieval_variables_eq[OF head, of x] that by simp
    have binding: "lp_isubst (?rho x) ?delta=local_values x" for x
      by (simp add: lpc_fresh_head_environment_def lpc_fresh_caller_factor lpc_fresh_local_factor known)
    have body: "lp_isubst (lp_ieval t ?rho) ?delta=lp_ieval t local_values" for t
      by (simp add: lp_ieval_subst binding)
    show ?thesis by (rule exI[of _ "?delta"])
      (simp add: lpc_fresh_caller_factor body)
  qed
  show ?thesis unfolding lpc_mgu_resolve_def using equation factor by blast
qed

lemma lpc_fresh_first_clause_progress:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
  shows "\<exists>m. (LPCGoals (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) eta)#gs)#es,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t (lpc_fresh_head_environment xs eta))) bs @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#
      (map (\<lambda>d. LPCClause (LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) eta)#gs) d m) cs @
        LPCBarrier m#es))\<in>(lp_cut_mgu_source P)\<^sup>+"
proof -
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var xs)) eta"
  let ?s = "LPCGoals (LPCAtom ?a#gs)#es"
  obtain m where fresh: "lp_cut_fresh m ?s" using lpc_uniform_fresh by blast
  let ?saved = "map (\<lambda>d. LPCClause (LPCAtom ?a#gs) d m) cs @ LPCBarrier m#es"
  let ?selected = "LPCClause (LPCAtom ?a#gs) c m#?saved"
  have selected: "(?s,?selected)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.case_call[of m f "map eta xs" gs es P] fresh
    by (simp add: first o_def)
  have mgu: "lpc_mgu_resolve ?a gs (fst (P!c)) (snd (P!c))
      lpc_fresh_caller (lpc_fresh_head_environment xs eta)"
    using lpc_fresh_head_mgu[where eta=eta and f="LPCUser f" and xs=xs and gs=gs and bs=bs]
    by (simp add: clause)
  have resolved: "(?selected,
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t (lpc_fresh_head_environment xs eta))) bs @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) gs)#?saved)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of m ?saved] by (simp add: clause)
  show ?thesis using selected resolved by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpc_fresh_local_assignment_preserves_caller}, @{thm lpc_fresh_head_mgu}, @{thm lpc_fresh_first_clause_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted fresh head resolution dependency" else ();
\<close>
end
