theory LP_Finite_NO_Canonical
  imports LP_MGU_Canonical
begin

abbreviation lp_ranked_runtime_atom where
  "lp_ranked_runtime_atom a \<equiv> logic_rank_runtime_atom (logic_from_atom lp_finite_tree a)"
definition lp_finite_goals ::
  "('f,string) lp_atom list \<Rightarrow> ('f \<times> nat,('f \<times> nat,string) logic_tree) logic_atom list" where
  "lp_finite_goals gs = map lp_ranked_runtime_atom gs"

lemma lp_finite_atom_substitution:
  "logic_atom_map (logic_subst (\<lambda>x. lp_finite_tree (sigma x))) (logic_from_atom lp_finite_tree a) =
    logic_from_atom lp_finite_tree (lp_atom_subst a sigma)"
  by (cases a) (simp add: lp_atom_subst_def map_map o_def lp_finite_tree_substitution)
lemma lp_ranked_atom_substitution:
  "lp_ranked_runtime_atom (lp_atom_subst a sigma) =
    logic_atom_map (logic_subst (logic_rank_tree \<circ> (\<lambda>x. lp_finite_tree (sigma x))))
      (lp_ranked_runtime_atom a)"
  by (simp add: lp_finite_atom_substitution[symmetric] logic_rank_runtime_atom_subst)
lemma lp_ranked_atom_embed:
  "lp_ranked_runtime_atom (logic_to_atom to_term a) = logic_atom_map logic_embed (logic_rank_atom a)"
  by (cases a) (simp add: logic_rank_atom_def logic_rank_runtime_atom_def map_map o_def logic_rank_embed)
lemma lp_ranked_atom_rename:
  "lp_ranked_runtime_atom (lp_atom_subst (logic_to_atom to_term a) (Var \<circ> r)) =
    logic_atom_map (logic_eval (LVar \<circ> r)) (logic_rank_atom a)"
  by (simp add: lp_ranked_atom_substitution lp_ranked_atom_embed logic_atom_map_comp o_def)

lemma lp_ranked_short_fresh:
  assumes short: "lp_short_atoms k gs"
  shows "logic_freshening (lp_prefix k)
    (concat (map logic_arguments (map lp_ranked_runtime_atom gs))) clause"
proof -
  have bound: "length x < k" if "t\<in>set (concat (map logic_arguments (map lp_ranked_runtime_atom gs)))"
      "x\<in>logic_variables t" for t x
    using short that
    by (auto simp: lp_short_atoms_def logic_rank_runtime_atom_def logic_rank_embed
      logic_rank_finite_variables split: prod.splits)
  let ?X = "\<Union>(logic_variables ` set (concat (map logic_arguments (map lp_ranked_runtime_atom gs))))"
  let ?Y = "\<Union>((logic_variables \<circ> logic_embed) ` set clause)"
  have low: "length x < k" if "x\<in>?X" for x using bound that by blast
  have disjoint: "lp_prefix k ` ?Y \<inter> ?X = {}"
  proof (rule equals0I)
    fix x assume x: "x\<in>lp_prefix k ` ?Y \<inter> ?X"
    then obtain y where xy: "x=lp_prefix k y" and mem: "x\<in>?X" by blast
    show False using low[OF mem] by (simp add: xy lp_prefix_def)
  qed
  have injective: "inj_on (lp_prefix k) ?Y" by (auto simp: inj_on_def lp_prefix_def)
  show ?thesis unfolding logic_freshening_def Let_def using disjoint injective by blast
qed

lemma lp_fresh_finite_step_canonical:
  assumes edge: "(s,t)\<in>lp_fresh_finite_ld (logic_to_program P)"
    and finite: "\<And>u. D (logic_embed u)"
  shows "logic_step snd (\<lambda>t. D (logic_unrank_tree t)) (logic_rank_program P)
    (lp_finite_goals s) (lp_finite_goals t)"
  using edge
proof (cases rule: lp_fresh_finite_ld.cases)
  case (resolve c k a gs mu)
  have c: "c<length P" using resolve by (simp add: logic_to_program_def)
  have short: "lp_short_atoms k (a#gs)" using resolve by auto
  have raw_mgu: "lp_normalized_mgu a (lp_atom_subst (fst (logic_to_program P!c)) (\<lambda>x. Var (lp_prefix k x))) mu"
    using resolve by auto
  obtain h bs where clause: "P!c=(h,bs)" by (cases "P!c") auto
  have member: "(logic_rank_atom h,map logic_rank_atom bs)\<in>set (logic_rank_program P)"
    using nth_mem[OF c] by (auto simp: logic_rank_program_def clause)
  have fresh: "logic_freshening (lp_prefix k)
      (concat (map logic_arguments (lp_ranked_runtime_atom a # map lp_ranked_runtime_atom gs)))
      (concat (map logic_arguments (logic_rank_atom h # map logic_rank_atom bs)))"
    using lp_ranked_short_fresh[OF short] by simp
  have mgu: "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
      (lp_ranked_runtime_atom a)
      (logic_atom_map (logic_eval (LVar \<circ> lp_prefix k)) (logic_rank_atom h))
      (logic_rank_tree \<circ> (\<lambda>x. lp_finite_tree (mu x)))"
    using lp_normalized_mgu_ranked[where D=D, OF raw_mgu finite]
    by (simp add: logic_to_program_def c clause lp_ranked_atom_rename[unfolded o_def] o_def)
  have step: "logic_step snd (\<lambda>t. D (logic_unrank_tree t)) (logic_rank_program P)
      (lp_ranked_runtime_atom a # map lp_ranked_runtime_atom gs)
      (map (logic_atom_map (logic_subst (logic_rank_tree \<circ> (\<lambda>x. lp_finite_tree (mu x)))))
        (map (logic_atom_map (logic_eval (LVar \<circ> lp_prefix k))) (map logic_rank_atom bs) @
          map lp_ranked_runtime_atom gs))"
    by (rule logic_step.resolve[OF member fresh mgu])
  show ?thesis using step
    by (simp add: resolve lp_finite_goals_def logic_to_program_def c clause map_map o_def
      lp_ranked_atom_substitution lp_ranked_atom_rename lp_ranked_atom_embed
      logic_atom_map_comp logic_subst_composition)
qed

lemma lp_finite_witness_domain_no:
  fixes P :: "('f,string) logic_clause list"
  assumes finite: "\<And>u. D (logic_embed u)"
    and bad: "\<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
    and len: "length ts=length modes"
    and ground: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> ground (ts!i)"
  shows "\<not>logic_terminates_in snd (\<lambda>t. D (logic_unrank_tree t))
    (logic_rank_program P) (q,length modes) modes"
proof -
  have bad': "\<not>SN_on (lp_fresh_finite_ld (logic_to_program P)) {[(q,ts)]}"
    by (rule lp_finite_nontermination_has_fresh_mgu_execution[OF bad])
  obtain f where initial: "f 0=[(q,ts)]"
    and steps: "\<And>n. (f n,f (Suc n))\<in>lp_fresh_finite_ld (logic_to_program P)"
    using bad' unfolding SN_on_def by blast
  let ?a = "logic_rank_atom (LAtom q (map from_term ts))"
  have query: "logic_query snd (q,length modes) modes ?a"
  proof (rule logic_rank_query)
    show "length (logic_arguments (LAtom q (map from_term ts))) = length modes" using len by simp
    show "logic_predicate (LAtom q (map from_term ts)) = q" by simp
    show "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t)
        (zip (logic_arguments (LAtom q (map from_term ts))) modes)"
      using len ground by (auto simp: list_all_iff set_zip logic_ground_translation)
  qed
  have init: "lp_finite_goals (f 0)=[logic_atom_map logic_embed ?a]"
    by (simp add: initial lp_finite_goals_def logic_rank_atom_def logic_rank_runtime_atom_def
      map_map o_def logic_rank_embed)
  have run: "\<forall>n. logic_step snd (\<lambda>t. D (logic_unrank_tree t)) (logic_rank_program P)
      (lp_finite_goals (f n)) (lp_finite_goals (f (Suc n)))"
    by (intro allI; rule lp_fresh_finite_step_canonical[where D=D, OF steps finite])
  show ?thesis unfolding logic_terminates_in_def
    apply (simp only: not_not)
    apply (rule exI[of _ ?a])
    apply (rule exI[of _ "\<lambda>n. lp_finite_goals (f n)"])
    using query init run by simp
qed

lemma logic_step_domain_cong:
  assumes same: "\<And>t. logic_tree_arity_correct A t \<Longrightarrow> D t = E t"
  shows "logic_step A D P s t \<longleftrightarrow> logic_step A E P s t"
proof -
  have eq: "(\<lambda>t. D t \<and> logic_tree_arity_correct A t) =
      (\<lambda>t. E t \<and> logic_tree_arity_correct A t)"
    using same by auto
  show ?thesis by (simp only: logic_step.simps eq)
qed
lemma logic_termination_domain_cong:
  assumes "\<And>t. logic_tree_arity_correct A t \<Longrightarrow> D t = E t"
  shows "logic_terminates_in A D P q modes \<longleftrightarrow> logic_terminates_in A E P q modes"
  unfolding logic_terminates_in_def by (simp add: logic_step_domain_cong[OF assms])

lemma lp_finite_witness_canonical_no:
  fixes P :: "('f,string) logic_clause list"
  assumes bad: "\<not>SN_on (lp_ld (logic_to_program P)) {[(q,ts)]}"
    and len: "length ts=length modes"
    and ground: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> ground (ts!i)"
  shows "\<not>lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    \<not>lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    \<not>lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
proof -
  have finite: "\<not>logic_terminates_in snd (\<lambda>t. logic_finite (logic_unrank_tree t))
      (logic_rank_program P) (q,length modes) modes"
    by (rule lp_finite_witness_domain_no[OF _ bad len ground]) (auto simp: logic_finite_def)
  have rational: "\<not>logic_terminates_in snd (\<lambda>t. logic_rational (logic_unrank_tree t))
      (logic_rank_program P) (q,length modes) modes"
    by (rule lp_finite_witness_domain_no[where D=logic_rational, OF logic_embed_rational bad len ground])
  have infinite: "\<not>logic_terminates_in snd (\<lambda>_. True) (logic_rank_program P) (q,length modes) modes"
    by (rule lp_finite_witness_domain_no[OF _ bad len ground]) simp
  have fin_eq: "logic_finite (logic_unrank_tree t) = logic_finite t"
    if "logic_tree_arity_correct snd t" for t
    using logic_rank_finite[of "logic_unrank_tree t"] logic_rank_unrank[OF that] by simp
  have rat_eq: "logic_rational (logic_unrank_tree t) = logic_rational t"
    if "logic_tree_arity_correct snd t" for t
    using logic_rank_rational[of "logic_unrank_tree t"] logic_rank_unrank[OF that] by simp
  show ?thesis using finite rational infinite
    by (simp add: lp_finite_terminates_def lp_rational_terminates_def lp_infinite_terminates_def
      logic_termination_domain_cong[OF fin_eq] logic_termination_domain_cong[OF rat_eq])
qed

end
