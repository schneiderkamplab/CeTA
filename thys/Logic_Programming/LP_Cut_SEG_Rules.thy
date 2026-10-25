theory LP_Cut_SEG_Rules
  imports LP_Cut_SEG_Interfaces
begin

hide_const (open) CPF_Proof_Parser.rstep


text \<open>Executable PPDP connection/Split rule construction. The checker
reconstructs these rules from checked interfaces and substitutions; serialized
TRS rules are not trusted as the result of extraction. Source-graph coverage
and groundness are separate checks.\<close>

definition lpc_seg_capture :: "('f,string) term \<Rightarrow> ('f,string) term list" where
  "lpc_seg_capture t = map Var (sorted_list_of_set (vars_term t))"

definition lpc_seg_connection_rules where
  "lpc_seg_connection_rules success inp outp child_in child_out mu u =
    (let lhs = inp\<cdot>mu; rhs = outp\<cdot>mu; captured = lpc_seg_capture lhs in
     if success then [(lhs,rhs)] else
       [(lhs,Fun u (child_in#captured)),(Fun u (child_out#captured),rhs)])"

definition lpc_seg_split_rules where
  "lpc_seg_split_rules inp outp first_in first_out second_in second_out delta u v =
    (let captured = lpc_seg_capture inp;
         extended = map Var (sorted_list_of_set (vars_term inp \<union> vars_term (first_out\<cdot>delta))) in
      [(inp,Fun u (first_in#captured)),
       (Fun u ((first_out\<cdot>delta)#captured),Fun v (second_in#extended)),
       (Fun v (second_out#extended),outp\<cdot>delta)])"

lemma lpc_seg_connection_enter:
  assumes rules: "set (lpc_seg_connection_rules False inp outp child_in child_out mu u) \<subseteq> R"
  shows "((inp\<cdot>mu)\<cdot>eta,(Fun u (child_in#lpc_seg_capture (inp\<cdot>mu)))\<cdot>eta)\<in>rstep R"
proof -
  have rule: "(inp\<cdot>mu,Fun u (child_in#lpc_seg_capture (inp\<cdot>mu)))\<in>R"
    using rules by (auto simp: lpc_seg_connection_rules_def Let_def)
  show ?thesis by (rule rstep_subst[OF rstep_rule[OF rule]])
qed

lemma lpc_seg_connection_return:
  assumes rules: "set (lpc_seg_connection_rules False inp outp child_in child_out mu u) \<subseteq> R"
  shows "((Fun u (child_out#lpc_seg_capture (inp\<cdot>mu)))\<cdot>eta,(outp\<cdot>mu)\<cdot>eta)\<in>rstep R"
proof -
  have rule: "(Fun u (child_out#lpc_seg_capture (inp\<cdot>mu)),outp\<cdot>mu)\<in>R"
    using rules by (auto simp: lpc_seg_connection_rules_def Let_def)
  show ?thesis by (rule rstep_subst[OF rstep_rule[OF rule]])
qed

lemma lpc_seg_connection_success:
  assumes rules: "set (lpc_seg_connection_rules True inp outp child_in child_out mu u) \<subseteq> R"
  shows "((inp\<cdot>mu)\<cdot>eta,(outp\<cdot>mu)\<cdot>eta)\<in>rstep R"
proof -
  have rule: "(inp\<cdot>mu,outp\<cdot>mu)\<in>R"
    using rules by (auto simp: lpc_seg_connection_rules_def Let_def)
  show ?thesis by (rule rstep_subst[OF rstep_rule[OF rule]])
qed

lemma lpc_seg_split_steps:
  assumes rules: "set (lpc_seg_split_rules inp outp first_in first_out second_in second_out delta u v) \<subseteq> R"
    and member: "(l,r)\<in>set (lpc_seg_split_rules inp outp first_in first_out second_in second_out delta u v)"
  shows "(l\<cdot>eta,r\<cdot>eta)\<in>rstep R"
  by (rule rstep_subst[OF rstep_rule]) (use rules member in blast)

text \<open>The source bridge uses constructor-valued inputs and returned
values. Every generated root step must discharge this normality condition when
the child is innermost/Q-restricted; full rewriting is not silently substituted.
Context lifting then uses ctxt_closed_qrstep.\<close>

lemma lpc_seg_restricted_root:
  assumes rule: "(l,r)\<in>R"
    and normal: "\<forall>u\<lhd>l\<cdot>eta. u\<in>NF_terms Q"
  shows "(l\<cdot>eta,r\<cdot>eta)\<in>qrstep False Q R"
  by (rule qrstep.subst[OF normal rule]) (simp add: NF_subst_def)

end
