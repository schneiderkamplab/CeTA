theory Relative_ADP_Trace
  imports Relative_ADP_Context_Dev.Relative_ADP_Context
begin

text \<open>
  A finite weak origin trace carries two selected positions through base-rule
  steps.  It is the finite fragment of Definition 39 needed immediately before
  a productive strict step.
\<close>

inductive weak_pair_origin_trace ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow>
    pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> bool"
  for R B D where
  refl:
    "weak_pair_origin_trace R B D s s q1 q2 q1 q2"
| step:
    "weak_pair_origin_trace R B D s t q1 q2 p1 p2 \<Longrightarrow>
     (l, r) \<in> B \<Longrightarrow>
     origin_root_targets 2 D r A \<Longrightarrow>
     vars_term_ms r \<subseteq># vars_term_ms l \<Longrightarrow>
     p \<in> fun_poss t \<Longrightarrow>
     t |_ p = l \<cdot> sigma \<Longrightarrow>
     origin_edge l r p sigma A (covering_vrf l r) p1 r1 \<Longrightarrow>
     origin_edge l r p sigma A (covering_vrf l r) p2 r2 \<Longrightarrow>
     weak_pair_origin_trace R B D s (replace_at t p (r \<cdot> sigma))
       q1 q2 r1 r2"
| strict_prefix:
    "weak_pair_origin_trace R B D s t q1 q2 p1 p2 \<Longrightarrow>
     (l, r) \<in> R \<Longrightarrow>
     p \<in> fun_poss t \<Longrightarrow>
     t |_ p = l \<cdot> sigma \<Longrightarrow>
     (p1 <\<^sub>p p \<or> p1 \<bottom> p) \<Longrightarrow>
     (p2 <\<^sub>p p \<or> p2 \<bottom> p) \<Longrightarrow>
     weak_pair_origin_trace R B D s (replace_at t p (r \<cdot> sigma))
       q1 q2 p1 p2"

lemma weak_pair_origin_trace_prepend_block:
  assumes trace: "weak_pair_origin_trace R B D s t q1 q2 p1 p2"
    and block: "relative_origin_block R B D t u p1 p2 q"
  shows "relative_origin_block R B D s u q1 q2 q"
  using trace block
proof (induct arbitrary: u q rule: weak_pair_origin_trace.induct)
  case (refl s q1 q2)
  then show ?case .
next
  case (step s t q1 q2 p1 p2 l r A p sigma r1 r2)
  have from_t: "relative_origin_block R B D t u p1 p2 q"
    by (rule relative_origin_block.weak[OF step.hyps(3-9) step.prems])
  show ?case by (rule step.hyps(2)[OF from_t])
next
  case (strict_prefix s t q1 q2 p1 p2 l r p sigma)
  have from_t: "relative_origin_block R B D t u p1 p2 q"
    by (rule relative_origin_block.strict_prefix[
          OF strict_prefix.hyps(3-7) strict_prefix.prems])
  show ?case by (rule strict_prefix.hyps(2)[OF from_t])
qed

lemma weak_pair_origin_trace_then_strict:
  assumes trace: "weak_pair_origin_trace R B D s t q1 q2 p q'"
    and rule: "(l, r) \<in> R"
    and targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and edge: "origin_edge l r p sigma A phi q' q"
  shows "relative_origin_block R B D s (replace_at t p (r \<cdot> sigma))
    q1 q2 q"
proof -
  have tail: "relative_origin_block R B D t (replace_at t p (r \<cdot> sigma))
      p q' q"
    by (rule relative_origin_block.strict[OF rule targets valid p_fun redex edge])
  show ?thesis by (rule weak_pair_origin_trace_prepend_block[OF trace tail])
qed

definition relative_root_origin_productive ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow> bool" where
  "relative_root_origin_productive R B D \<longleftrightarrow>
    (\<forall>s. s \<in> Tinf (relstep R B) \<longrightarrow>
      [] \<in> adp_defined_positions D s \<longrightarrow>
      (\<exists>t u p q' q l r A phi sigma.
        weak_pair_origin_trace R B D s t [] [] p q' \<and>
        (l, r) \<in> R \<and>
        origin_root_targets 1 D r A \<and>
        valid_vrf (plain_adp_term l, plain_adp_term r) phi \<and>
        p \<in> fun_poss t \<and>
        t |_ p = l \<cdot> sigma \<and>
        u = replace_at t p (r \<cdot> sigma) \<and>
        origin_edge l r p sigma A phi q' q \<and>
        q \<in> adp_defined_positions D u \<and>
        u |_ q \<in> Tinf (relstep R B)))"

lemma relative_root_origin_productive_block:
  assumes productive: "relative_root_origin_productive R B D"
    and minimal: "s \<in> Tinf (relstep R B)"
    and defined: "[] \<in> adp_defined_positions D s"
  obtains u q where
    "relative_origin_block R B D s u [] [] q"
    "q \<in> adp_defined_positions D u"
    "u |_ q \<in> Tinf (relstep R B)"
proof -
  have witness: "\<exists>t u p q' q l r A phi sigma.
        weak_pair_origin_trace R B D s t [] [] p q' \<and>
        (l, r) \<in> R \<and>
        origin_root_targets 1 D r A \<and>
        valid_vrf (plain_adp_term l, plain_adp_term r) phi \<and>
        p \<in> fun_poss t \<and>
        t |_ p = l \<cdot> sigma \<and>
        u = replace_at t p (r \<cdot> sigma) \<and>
        origin_edge l r p sigma A phi q' q \<and>
        q \<in> adp_defined_positions D u \<and>
        u |_ q \<in> Tinf (relstep R B)"
    using productive minimal defined
    unfolding relative_root_origin_productive_def by blast
  obtain t u p q' q l r A phi sigma where
    trace: "weak_pair_origin_trace R B D s t [] [] p q'"
    and rule: "(l, r) \<in> R"
    and targets: "origin_root_targets 1 D r A"
    and valid: "valid_vrf (plain_adp_term l, plain_adp_term r) phi"
    and p_fun: "p \<in> fun_poss t"
    and redex: "t |_ p = l \<cdot> sigma"
    and u: "u = replace_at t p (r \<cdot> sigma)"
    and edge: "origin_edge l r p sigma A phi q' q"
    and q_defined: "q \<in> adp_defined_positions D u"
    and q_minimal: "u |_ q \<in> Tinf (relstep R B)"
    using witness by blast
  have block: "relative_origin_block R B D s u [] [] q"
    unfolding u
    by (rule weak_pair_origin_trace_then_strict[
          OF trace rule targets valid p_fun redex edge])
  show thesis by (rule that[OF block q_defined q_minimal])
qed

end
