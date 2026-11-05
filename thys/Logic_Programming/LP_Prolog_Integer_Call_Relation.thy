theory LP_Prolog_Integer_Call_Relation
  imports LP_Prolog_Integer_Call_Row
begin

definition lpp_integer_call_value where
  "lpp_integer_call_value q = LPIFun (LPCUser (fst q)) (map lpp_integer_value (snd q))"

definition lpp_arithmetic_call_relation where
  "lpp_arithmetic_call_relation P recipes =
    {((f,ns),(g,ms)). \<exists>r. (f,r)\<in>set recipes \<and>
      lpp_arithmetic_call_shape P f (length ns) r \<and>
      lpp_arithmetic_call_holds r ns \<and>
      g=lpp_call_target r \<and> ms=lpp_arithmetic_call_outputs r ns}"

lemma lpp_arithmetic_call_relation_source_step:
  assumes edge: "(a,b)\<in>lpp_arithmetic_call_relation P recipes"
  shows "\<exists>saved. (LPCGoals [LPCAtom (lpp_integer_call_value a)]#es,
      LPCGoals [LPCAtom (lpp_integer_call_value b)]#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  obtain f ns g ms where inputs: "a=(f,ns)" and outputs: "b=(g,ms)" by (cases a; cases b) blast
  obtain r where member: "(f,r)\<in>set recipes" and shape: "lpp_arithmetic_call_shape P f (length ns) r"
    and holds: "lpp_arithmetic_call_holds r ns"
    and target: "g=lpp_call_target r" and output_values: "ms=lpp_arithmetic_call_outputs r ns"
    using edge by (auto simp: inputs outputs lpp_arithmetic_call_relation_def)
  show ?thesis using lpp_checked_arithmetic_call_steps[OF shape holds, where es=es]
    by (simp add: inputs outputs target output_values lpp_integer_call_value_def)
qed

lemma lpp_arithmetic_call_relation_source_no:
  assumes child: "\<not>SN_on (lpp_arithmetic_call_relation P recipes) {q}"
  shows "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
    {LPCGoals [LPCAtom (lpp_integer_call_value q)]#es}"
proof -
  let ?rep = "\<lambda>q s. \<exists>saved. s=LPCGoals [LPCAtom (lpp_integer_call_value q)]#saved"
  have represented: "?rep q (LPCGoals [LPCAtom (lpp_integer_call_value q)]#es)" by blast
  have simulate: "\<exists>v. ?rep b v \<and>
      (u,v)\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    if edge: "(a,b)\<in>lpp_arithmetic_call_relation P recipes" and represented: "?rep a u" for a b u
  proof -
    obtain saved where state: "u=LPCGoals [LPCAtom (lpp_integer_call_value a)]#saved"
      using represented by blast
    show ?thesis using lpp_arithmetic_call_relation_source_step[OF edge, where es=saved] state by blast
  qed
  show ?thesis by (rule lp_source_nontermination_simulation[where rep="?rep", OF child represented simulate])
qed

ML \<open>
val checked = [@{thm lpp_arithmetic_call_relation_source_step},
  @{thm lpp_arithmetic_call_relation_source_no}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted arithmetic call relation dependency" else ();
\<close>
end
