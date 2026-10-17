theory Relative_ADP_Block
  imports Relative_ADP_NT_Dev.Relative_ADP_Nontermination
begin

text \<open>
  One productive block consists of base steps followed by one main step.  Its
  two source positions are the origins of the main redex and of the continuation
  position after that main step.  This is the executable core of the two-path
  construction in the proof of Theorem 23.
\<close>

inductive relative_origin_block ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool"
  for R B D where
  strict:
    "(l, r) \<in> R \<Longrightarrow>
     origin_root_targets 1 D r A \<Longrightarrow>
     valid_vrf (plain_adp_term l, plain_adp_term r) phi \<Longrightarrow>
     p \<in> fun_poss s \<Longrightarrow>
     s |_ p = l \<cdot> sigma \<Longrightarrow>
     origin_edge l r p sigma A phi q' q \<Longrightarrow>
     relative_origin_block R B D s (replace_at s p (r \<cdot> sigma)) p q' q"
| weak:
    "(l, r) \<in> B \<Longrightarrow>
     origin_root_targets 2 D r A \<Longrightarrow>
     vars_term_ms r \<subseteq># vars_term_ms l \<Longrightarrow>
     p \<in> fun_poss s \<Longrightarrow>
     s |_ p = l \<cdot> sigma \<Longrightarrow>
     origin_edge l r p sigma A (covering_vrf l r) q1' q1 \<Longrightarrow>
     origin_edge l r p sigma A (covering_vrf l r) q2' q2 \<Longrightarrow>
     relative_origin_block R B D (replace_at s p (r \<cdot> sigma)) u q1 q2 q \<Longrightarrow>
     relative_origin_block R B D s u q1' q2' q"
| strict_prefix:
    "(l, r) \<in> R \<Longrightarrow>
     p \<in> fun_poss s \<Longrightarrow>
     s |_ p = l \<cdot> sigma \<Longrightarrow>
     (q1 <\<^sub>p p \<or> q1 \<bottom> p) \<Longrightarrow>
     (q2 <\<^sub>p p \<or> q2 \<bottom> p) \<Longrightarrow>
     relative_origin_block R B D (replace_at s p (r \<cdot> sigma)) u q1 q2 q \<Longrightarrow>
     relative_origin_block R B D s u q1 q2 q"

definition adp_productive_block_rel ::
  "('f, 'v) adp set \<Rightarrow> ('f, 'v) adp set \<Rightarrow>
    ('f adp_symbol, 'v) term rel" where
  "adp_productive_block_rel P Q =
    (adp_step (P \<union> Q))\<^sup>* O adp_step_case_rel P True"

lemma adp_step_case_mono_block:
  assumes subset: "P \<subseteq> P'" and step: "adp_step_case P b s t"
  shows "adp_step_case P' b s t"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  show ?thesis
    by (rule adp_step_case.adp_stepI[OF subset[THEN subsetD, OF adp_stepI(1)]
          adp_stepI(2-8)])
qed

lemma adp_step_mono_block:
  assumes "P \<subseteq> P'" shows "adp_step P \<subseteq> adp_step P'"
  using adp_step_case_mono_block[OF assms]
  unfolding adp_step_def adp_step_case_rel_def by blast

lemma relative_origin_block_lifts:
  assumes block: "relative_origin_block R B D s u q1 q2 q"
    and erased: "erase_adp_term sh = s"
    and marked1: "q1 \<in> sharp_positions sh"
    and marked2: "q2 \<in> sharp_positions sh"
  obtains uh where
    "erase_adp_term uh = u"
    "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    "q \<in> sharp_positions uh"
using block erased marked1 marked2
proof (induct arbitrary: sh thesis rule: relative_origin_block.induct)
  case (strict l r A phi p s sigma q' q)
  have erase_fun: "fun_poss s = fun_poss sh"
    using strict.prems(2) fun_poss_erase_adp_term[of sh] by simp
  have p_fun: "p \<in> fun_poss sh" using strict.hyps(4) unfolding erase_fun .
  have p_poss: "p \<in> poss sh" by (rule fun_poss_imp_poss[OF p_fun])
  have redex_sh: "erase_adp_term (sh |_ p) = l \<cdot> sigma"
    using erase_adp_term_subt_at[OF p_poss] strict.prems(2) strict.hyps(5) by simp
  obtain uh where erased_uh:
      "erase_adp_term uh = replace_at (erase_adp_term sh) p (r \<cdot> sigma)"
    and main_step: "adp_step_case (canonical_adps 1 D R) True sh uh"
    and marked_q: "q \<in> sharp_positions uh"
    by (rule canonical_strict_step_marks_target[
          OF strict.hyps(1-3) p_fun redex_sh strict.hyps(6)
            strict.prems(3) strict.prems(4)])
  have erased_target:
      "erase_adp_term uh = replace_at s p (r \<cdot> sigma)"
    using erased_uh strict.prems(2) by simp
  have productive: "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    unfolding adp_productive_block_rel_def
    by (rule relcompI[of sh])
       (rule rtrancl_refl, unfold adp_step_case_rel_def, use main_step in simp)
  show thesis by (rule strict.prems(1)[OF erased_target productive marked_q])
next
  case (weak l r A p s sigma q1' q1 q2' q2 u q)
  have erase_fun: "fun_poss s = fun_poss sh"
    using weak.prems(2) fun_poss_erase_adp_term[of sh] by simp
  have p_fun: "p \<in> fun_poss sh" using weak.hyps(4) unfolding erase_fun .
  have p_poss: "p \<in> poss sh" by (rule fun_poss_imp_poss[OF p_fun])
  have redex_sh: "erase_adp_term (sh |_ p) = l \<cdot> sigma"
    using erase_adp_term_subt_at[OF p_poss] weak.prems(2) weak.hyps(5) by simp
  obtain th where erased_th:
      "erase_adp_term th = replace_at (erase_adp_term sh) p (r \<cdot> sigma)"
    and base_case: "adp_step_case (canonical_adps 2 D B)
      (p \<in> sharp_positions sh) sh th"
    and marked_q1: "q1 \<in> sharp_positions th"
    and marked_q2: "q2 \<in> sharp_positions th"
    by (rule canonical_nonduplicating_step_marks_pair[
          OF weak.hyps(1-3) p_fun redex_sh weak.hyps(6-7) weak.prems(3-4)])
  have erased_middle:
      "erase_adp_term th = replace_at s p (r \<cdot> sigma)"
    using erased_th weak.prems(2) by simp
  have base_step: "(sh, th) \<in> adp_step (canonical_adps 2 D B)"
  proof (cases "p \<in> sharp_positions sh")
    case True
    then have "adp_step_case (canonical_adps 2 D B) True sh th"
      using base_case by simp
    then show ?thesis unfolding adp_step_def adp_step_case_rel_def by auto
  next
    case False
    then have "adp_step_case (canonical_adps 2 D B) False sh th"
      using base_case by simp
    then show ?thesis unfolding adp_step_def adp_step_case_rel_def by auto
  qed
  have base_step_union: "(sh, th) \<in> adp_step
      (canonical_adps 1 D R \<union> canonical_adps 2 D B)"
    by (rule subsetD[OF adp_step_mono_block[of "canonical_adps 2 D B"
          "canonical_adps 1 D R \<union> canonical_adps 2 D B"] base_step]) auto
  obtain uh where erased_uh: "erase_adp_term uh = u"
    and tail: "(th, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    and marked_q: "q \<in> sharp_positions uh"
    apply (rule weak.hyps(9)[where sh = th])
    subgoal for uh
      by (rule that)
    subgoal by (rule erased_middle)
    subgoal by (rule marked_q1)
    subgoal by (rule marked_q2)
    done
  from tail obtain vh where weak_tail:
      "(th, vh) \<in> (adp_step
        (canonical_adps 1 D R \<union> canonical_adps 2 D B))\<^sup>*"
    and main: "(vh, uh) \<in> adp_step_case_rel (canonical_adps 1 D R) True"
    unfolding adp_productive_block_rel_def by blast
  have weak_all: "(sh, vh) \<in> (adp_step
      (canonical_adps 1 D R \<union> canonical_adps 2 D B))\<^sup>*"
    by (rule rtrancl_trans[OF r_into_rtrancl[OF base_step_union] weak_tail])
  have productive: "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    unfolding adp_productive_block_rel_def
    by (rule relcompI[OF weak_all main])
  show thesis by (rule weak.prems(1)[OF erased_uh productive marked_q])
next
  case (strict_prefix l r p s sigma q1 q2 u q)
  have erase_fun: "fun_poss s = fun_poss sh"
    using strict_prefix.prems(2) fun_poss_erase_adp_term[of sh] by simp
  have p_fun: "p \<in> fun_poss sh"
    using strict_prefix.hyps(2) unfolding erase_fun .
  have p_poss: "p \<in> poss sh" by (rule fun_poss_imp_poss[OF p_fun])
  have redex_sh: "erase_adp_term (sh |_ p) = l \<cdot> sigma"
    using erase_adp_term_subt_at[OF p_poss] strict_prefix.prems(2)
      strict_prefix.hyps(3) by simp
  have targets: "origin_root_targets 1 D r {}" by simp
  have valid: "valid_vrf (plain_adp_term l, plain_adp_term r) (\<lambda>_. None)"
    by (rule empty_vrf_valid)
  obtain th where erased_th:
      "erase_adp_term th = replace_at (erase_adp_term sh) p (r \<cdot> sigma)"
    and main_case: "adp_step_case (canonical_adps 1 D R)
      (p \<in> sharp_positions sh) sh th"
    and realizes: "realizes_origin_relation
      (origin_edge l r p sigma {} (\<lambda>_. None)) sh th"
    by (rule canonical_strict_step_realizes_origin[
          OF strict_prefix.hyps(1) targets valid p_fun redex_sh])
  have edge1: "origin_edge l r p sigma {} (\<lambda>_. None) q1 q1"
    by (rule origin_edge.preserved[OF strict_prefix.hyps(4)])
  have edge2: "origin_edge l r p sigma {} (\<lambda>_. None) q2 q2"
    by (rule origin_edge.preserved[OF strict_prefix.hyps(5)])
  have marked_q1: "q1 \<in> sharp_positions th"
    by (rule realizes_origin_relationD[
          OF realizes edge1 strict_prefix.prems(3)])
  have marked_q2: "q2 \<in> sharp_positions th"
    by (rule realizes_origin_relationD[
          OF realizes edge2 strict_prefix.prems(4)])
  have erased_middle: "erase_adp_term th = replace_at s p (r \<cdot> sigma)"
    using erased_th strict_prefix.prems(2) by simp
  have main_step: "(sh, th) \<in> adp_step (canonical_adps 1 D R)"
  proof (cases "p \<in> sharp_positions sh")
    case True
    then have "adp_step_case (canonical_adps 1 D R) True sh th"
      using main_case by simp
    then show ?thesis unfolding adp_step_def adp_step_case_rel_def by auto
  next
    case False
    then have "adp_step_case (canonical_adps 1 D R) False sh th"
      using main_case by simp
    then show ?thesis unfolding adp_step_def adp_step_case_rel_def by auto
  qed
  have prefix_step: "(sh, th) \<in> adp_step
      (canonical_adps 1 D R \<union> canonical_adps 2 D B)"
    by (rule subsetD[OF adp_step_mono_block[of "canonical_adps 1 D R"
          "canonical_adps 1 D R \<union> canonical_adps 2 D B"] main_step]) auto
  obtain uh where erased_uh: "erase_adp_term uh = u"
    and tail: "(th, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    and marked_q: "q \<in> sharp_positions uh"
    apply (rule strict_prefix.hyps(7)[where sh = th])
    subgoal for uh by (rule that)
    subgoal by (rule erased_middle)
    subgoal by (rule marked_q1)
    subgoal by (rule marked_q2)
    done
  from tail obtain vh where weak_tail: "(th, vh) \<in> (adp_step
      (canonical_adps 1 D R \<union> canonical_adps 2 D B))\<^sup>*"
    and final: "(vh, uh) \<in> adp_step_case_rel
      (canonical_adps 1 D R) True"
    unfolding adp_productive_block_rel_def by blast
  have weak_all: "(sh, vh) \<in> (adp_step
      (canonical_adps 1 D R \<union> canonical_adps 2 D B))\<^sup>*"
    by (rule rtrancl_trans[OF r_into_rtrancl[OF prefix_step] weak_tail])
  have productive: "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    unfolding adp_productive_block_rel_def
    by (rule relcompI[OF weak_all final])
  show thesis
    by (rule strict_prefix.prems(1)[OF erased_uh productive marked_q])
qed

end
