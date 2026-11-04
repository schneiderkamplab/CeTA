theory LP_Dependency_Triple_Data
  imports LP_Constructor_Source LP_Dependency_Triple_Chains
begin

text \<open>Constructor data erasure preserves actual successful prefixes of
  dependency triples. It does not turn arbitrary Pi-DP valuations into
  constructor valuations, or assert termination of the supporting program.\<close>

lemma lp_data_answer_step:
  assumes fixed: "lp_data_fixed_program data P"
    and step: "((gs,\<rho>),(hs,\<eta>)) \<in> lp_seg_answer_step P"
  shows "((map (lp_data_atom data) gs,\<lambda>x. map_lp_iterm data id (\<rho> x)),
    (map (lp_data_atom data) hs,\<lambda>x. map_lp_iterm data id (\<eta> x)))
    \<in> lp_seg_answer_step P"
proof -
  obtain c a tail \<sigma> \<nu> where c: "c<length P"
    and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    and gs: "gs=a#tail"
    and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
    and eta: "\<eta>=(\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    using step by (cases rule: lp_seg_answer_step.cases) blast
  have head: "lp_data_fixed_atom data (fst (P!c))"
    by (rule lp_data_fixed_head[OF fixed c])
  have body: "\<And>b. b\<in>set (snd (P!c)) \<Longrightarrow> lp_data_fixed_atom data b"
    using fixed c unfolding lp_data_fixed_program_def list_all_iff
    by (meson nth_mem)
  have match: "lp_iatom_subst (lp_data_atom data a)
      (\<lambda>x. map_lp_iterm data id (\<sigma> x)) =
    lp_atom_eval (fst (P!c)) (\<lambda>x. map_lp_iterm data id (\<nu> x))"
    using arg_cong[OF eq, of "lp_data_atom data"]
    by (simp add: lp_data_atom_subst lp_data_atom_eval[OF head])
  have mapped_body: "map (lp_data_atom data) (map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c))) =
    map (\<lambda>b. lp_atom_eval b (\<lambda>x. map_lp_iterm data id (\<nu> x))) (snd (P!c))"
    by (auto simp: map_map intro!: map_cong lp_data_atom_eval[OF body])
  show ?thesis
    using lp_seg_answer_step.resolve[OF c match,
      of "map (lp_data_atom data) tail" "\<lambda>x. map_lp_iterm data id (\<rho> x)"]
    by (simp add: gs hs eta map_append mapped_body mapped_body[unfolded map_map o_def] map_map o_def
      lp_data_atom_subst lp_data_map_subst)
qed

lemma lp_data_answer_steps:
  assumes fixed: "lp_data_fixed_program data P"
    and steps: "((gs,\<rho>),(hs,\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "((map (lp_data_atom data) gs,\<lambda>x. map_lp_iterm data id (\<rho> x)),
    (map (lp_data_atom data) hs,\<lambda>x. map_lp_iterm data id (\<eta> x)))
    \<in> (lp_seg_answer_step P)\<^sup>*"
  using steps
proof (induct rule: rtrancl_induct2)
  case refl then show ?case by simp
next
  case (step hs \<eta> ks \<tau>)
  show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3)
    lp_data_answer_step[OF fixed step.hyps(2)]])
qed

lemma lp_data_triple_call:
  assumes program: "lp_data_fixed_program data P"
    and triples: "\<And>h ps b. (h,ps,b)\<in>D \<Longrightarrow>
      lp_data_fixed_atom data h \<and> list_all (lp_data_fixed_atom data) ps \<and>
      lp_data_fixed_atom data b"
    and call: "(a,b)\<in>lp_triple_calls D P"
  shows "(lp_data_atom data a,lp_data_atom data b)\<in>lp_triple_calls D P"
proof -
  obtain h ps target \<sigma> \<rho> \<eta> where member: "(h,ps,target)\<in>D"
    and match: "lp_iatom_subst a \<sigma>=lp_atom_eval h \<rho>"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) ps,\<rho>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    and result: "b=lp_atom_eval target \<eta>"
    using call unfolding lp_triple_calls_def by blast
  have head: "lp_data_fixed_atom data h"
    and prefix: "list_all (lp_data_fixed_atom data) ps"
    and target: "lp_data_fixed_atom data target"
    using triples[OF member] by blast+
  have match': "lp_iatom_subst (lp_data_atom data a)
      (\<lambda>x. map_lp_iterm data id (\<sigma> x)) =
    lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    using arg_cong[OF match, of "lp_data_atom data"]
    by (simp add: lp_data_atom_subst lp_data_atom_eval[OF head])
  have mapped_prefix: "map (lp_data_atom data) (map (\<lambda>g. lp_atom_eval g \<rho>) ps) =
    map (\<lambda>g. lp_atom_eval g (\<lambda>x. map_lp_iterm data id (\<rho> x))) ps"
    using prefix unfolding list_all_iff
    by (auto simp: map_map intro!: map_cong lp_data_atom_eval)
  have success': "((map (\<lambda>g. lp_atom_eval g (\<lambda>x. map_lp_iterm data id (\<rho> x))) ps,
      \<lambda>x. map_lp_iterm data id (\<rho> x)),([],\<lambda>x. map_lp_iterm data id (\<eta> x)))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    using lp_data_answer_steps[OF program success] by (simp only: mapped_prefix list.map)
  have result': "lp_data_atom data b=lp_atom_eval target (\<lambda>x. map_lp_iterm data id (\<eta> x))"
    by (simp add: result lp_data_atom_eval[OF target])
  show ?thesis unfolding lp_triple_calls_def
    using member match' success' result' by blast
qed

end
