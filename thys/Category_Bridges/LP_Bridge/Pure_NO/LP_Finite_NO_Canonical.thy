theory LP_Finite_NO_Canonical
  imports LP_MGU_Canonical
begin

definition lp_finite_goals where
  "lp_finite_goals gs = map (logic_atom_map lp_finite_tree) gs"

lemma lp_exact_finite_step_canonical:
  assumes edge: "(s,t)\<in>lp_exact_finite_ld (logic_to_program P)"
    and finite: "\<And>u. D (logic_embed u)"
  shows "logic_step D P (lp_finite_goals s) (lp_finite_goals t)"
  using edge
proof (cases rule: lp_exact_finite_ld.cases)
  case (resolve c a sigma rho gs)
  have c: "c<length P" using resolve by (simp add: logic_to_program_def)
  obtain h bs where clause: "P!c=(h,bs)" by (cases "P!c") auto
  have member: "(h,bs)\<in>set P" using nth_mem[OF c] by (simp add: clause)
  have mgu: "logic_mgu D (logic_atom_map lp_finite_tree a)
    (map (logic_atom_map lp_finite_tree) gs) h bs
    (\<lambda>x. lp_finite_tree (sigma x)) (\<lambda>x. lp_finite_tree (rho x))"
    using lp_universal_mgu_canonical[where D=D, OF resolve(4) finite,
      where gs=gs and bs="snd (logic_to_program P!c)"]
    by (simp add: logic_to_program_def c clause logic_atom_map_def map_map o_def)
  have step: "logic_step D P
    (logic_atom_map lp_finite_tree a # map (logic_atom_map lp_finite_tree) gs)
    (map (logic_atom_map (logic_eval (\<lambda>x. lp_finite_tree (rho x)))) bs @
      map (logic_atom_map (logic_subst (\<lambda>x. lp_finite_tree (sigma x))))
        (map (logic_atom_map lp_finite_tree) gs))"
    by (rule logic_step.resolve[OF member mgu])
  have eval_r: "logic_eval (\<lambda>x. lp_finite_tree (rho x)) =
    (\<lambda>u. lp_finite_tree (to_term u\<cdot>rho))"
    by (rule ext; rule logic_finite_eval_substitution)
  show ?thesis using step
    by (simp add: resolve lp_finite_goals_def logic_to_program_def c clause
      logic_atom_map_def[abs_def] lp_atom_subst_def map_map o_def
      logic_subst_embed_eval lp_finite_tree_substitution logic_finite_eval_substitution eval_r)
qed

lemma lp_finite_witness_domain_no:
  assumes finite: "\<And>u. D (logic_embed u)"
    and bad: "\<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
    and len: "length ts=length modes"
    and ground: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> ground (ts!i)"
  shows "\<not>logic_terminates_in D P q modes"
proof -
  have bad': "\<not>SN_on (lp_exact_finite_ld (logic_to_program P)) {[(q,ts)]}"
    by (rule lp_finite_nontermination_has_mgu_execution[OF bad])
  obtain f where initial: "f 0=[(q,ts)]"
    and steps: "\<And>n. (f n,f (Suc n))\<in>lp_exact_finite_ld (logic_to_program P)"
    using bad' unfolding SN_on_def by blast
  let ?a = "(q,map from_term ts)"
  have query: "logic_query q modes ?a"
    using len ground
    by (auto simp: logic_query_def list_all_iff set_zip logic_ground_translation; blast)
  have init: "lp_finite_goals (f 0)=[logic_atom_map logic_embed ?a]"
    by (simp add: initial lp_finite_goals_def logic_atom_map_def map_map o_def)
  have run: "\<forall>n. logic_step D P (lp_finite_goals (f n)) (lp_finite_goals (f (Suc n)))"
    by (intro allI; rule lp_exact_finite_step_canonical[where D=D, OF steps finite])
  show ?thesis unfolding logic_terminates_in_def
    apply (simp only: not_not)
    apply (rule exI[of _ ?a])
    apply (rule exI[of _ "\<lambda>n. lp_finite_goals (f n)"])
    using query init run by simp
qed

lemma lp_finite_witness_canonical_no:
  assumes bad: "\<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
    and len: "length ts=length modes"
    and ground: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> ground (ts!i)"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
proof -
  have finite: "\<not>logic_terminates_in logic_finite P q modes"
    by (rule lp_finite_witness_domain_no[OF _ bad len ground]) (auto simp: logic_finite_def)
  have rational: "\<not>logic_terminates_in logic_rational P q modes"
    by (rule lp_finite_witness_domain_no[where D=logic_rational, OF logic_embed_rational bad len ground])
  have infinite: "\<not>logic_terminates_in (\<lambda>_. True) P q modes"
    by (rule lp_finite_witness_domain_no[OF _ bad len ground]) simp
  show ?thesis using finite rational infinite
    by (simp add: lp_finite_terminates_def lp_rational_terminates_def lp_infinite_terminates_def)
qed

end
