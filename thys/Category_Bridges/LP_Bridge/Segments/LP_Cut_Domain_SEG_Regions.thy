theory LP_Cut_Domain_SEG_Regions
 imports LP_Cut_Domain_SEG_Reinterface
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_auxiliary_contract:
  assumes finite: "SN_on L {a}"
    and represented: "rep ss a"
    and local: "\<And>us b. rep us b \<Longrightarrow>
      precise_return_contract P us R t ret \<or>
      ((\<forall>event vs. precise_answer_transition P us event vs \<longrightarrow>
         (\<exists>c. (b,c)\<in>L\<^sup>+ \<and> rep vs c)) \<and>
       (\<forall>rho vs. precise_answer_transition P us (Some rho) vs \<longrightarrow> (t,ret rho)\<in>R\<^sup>*))"
  shows "precise_return_contract P ss R t ret"
proof -
  have all: "\<forall>us. rep us b \<longrightarrow> precise_return_contract P us R t ret"
    if sn: "SN_on L {b}" for b
  proof (rule SN_on_induct[OF SN_on_trancl[OF sn] singletonI], intro allI impI)
    fix b us
    assume ih: "\<And>c. (b,c)\<in>L\<^sup>+ \<Longrightarrow> \<forall>vs. rep vs c \<longrightarrow> precise_return_contract P vs R t ret"
      and rep: "rep us b"
    show "precise_return_contract P us R t ret"
    proof (cases "precise_return_contract P us R t ret")
      case True then show ?thesis .
    next
      case False
      have edges: "\<And>event vs. precise_answer_transition P us event vs \<Longrightarrow>
        \<exists>c. (b,c)\<in>L\<^sup>+ \<and> rep vs c"
        and answers: "\<And>rho vs. precise_answer_transition P us (Some rho) vs \<Longrightarrow> (t,ret rho)\<in>R\<^sup>*"
        using local[OF rep] False by blast+
      show ?thesis by (rule precise_seg_primitive_contract) (use ih edges answers in blast)+
    qed
  qed
  show ?thesis using all[OF finite] represented by blast
qed


end
end
