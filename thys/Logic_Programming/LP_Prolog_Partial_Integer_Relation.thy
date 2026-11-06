theory LP_Prolog_Partial_Integer_Relation
  imports LP_Prolog_Partial_Integer_Row
begin

definition lpp_partial_call_relation where
  "lpp_partial_call_relation P interfaces recipes =
    {((f,ns),(g,ms)). \<exists>r. (f,r)\<in>set recipes \<and>
      lpp_partial_call_shape P f (length ns) r \<and>
      lpp_partial_inputs r=interfaces (f,length ns) \<and>
      lpp_partial_outputs r=interfaces (lpp_call_target r,length (lpp_call_outputs r)) \<and>
      lpp_arithmetic_call_holds r ns \<and>
      g=lpp_call_target r \<and> ms=lpp_arithmetic_call_outputs r ns}"

definition lpp_partial_call_represents where
  "lpp_partial_call_represents interfaces q s =
    (\<exists>actuals pending saved.
      lpp_partial_observations (interfaces (fst q,length (snd q))) (snd q) actuals \<and>
      s=LPCGoals (LPCAtom (LPIFun (LPCUser (fst q)) actuals)#pending)#saved)"

lemma lpp_partial_call_relation_source_step:
  assumes edge: "(a,b)\<in>lpp_partial_call_relation P interfaces recipes"
    and represented: "lpp_partial_call_represents interfaces a s"
  shows "\<exists>t. lpp_partial_call_represents interfaces b t \<and>
    (s,t)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  obtain f ns g ms where inputs: "a=(f,ns)" and outputs: "b=(g,ms)"
    by (cases a; cases b) blast
  obtain r where member: "(f,r)\<in>set recipes"
    and shape: "lpp_partial_call_shape P f (length ns) r"
    and input_interface: "lpp_partial_inputs r=interfaces (f,length ns)"
    and output_interface: "lpp_partial_outputs r=interfaces (lpp_call_target r,length (lpp_call_outputs r))"
    and holds: "lpp_arithmetic_call_holds r ns"
    and target: "g=lpp_call_target r" and output_values: "ms=lpp_arithmetic_call_outputs r ns"
    using edge by (auto simp: inputs outputs lpp_partial_call_relation_def)
  obtain actuals pending saved where observations: "lpp_partial_observations (lpp_partial_inputs r) ns actuals"
    and state: "s=LPCGoals (LPCAtom (LPIFun (LPCUser f) actuals)#pending)#saved"
    using represented by (auto simp: inputs lpp_partial_call_represents_def input_interface)
  show ?thesis using lpp_checked_partial_call_steps[OF shape holds observations, where pending=pending and es=saved]
    by (auto simp: state outputs target output_values lpp_partial_call_represents_def
      output_interface lpp_arithmetic_call_outputs_def)
qed

lemma lpp_partial_call_relation_source_no:
  assumes child: "\<not>SN_on (lpp_partial_call_relation P interfaces recipes) {q}"
    and represented: "lpp_partial_call_represents interfaces q s"
  shows "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin) {s}"
  by (rule lp_source_nontermination_simulation[where rep="lpp_partial_call_represents interfaces", OF child represented])
    (rule lpp_partial_call_relation_source_step; assumption)

ML \<open>
val checked = [@{thm lpp_partial_call_relation_source_step}, @{thm lpp_partial_call_relation_source_no}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial call relation dependency" else ();
\<close>
end
