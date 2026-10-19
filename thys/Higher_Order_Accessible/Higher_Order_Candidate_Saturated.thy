theory Higher_Order_Candidate_Saturated
  imports Higher_Order_Candidate_Calls
begin

context ho_source_accessible_reducibility
begin

lemma source_candidate_retype:
  assumes ct: "source_candidate T t" and ty: "ho_typeof S V B t=Some A"
  shows "source_candidate A t"
proof -
  have "ho_typeof S V B t=Some T" by (rule source.candidate_typed[OF ct])
  then have "T=A" using ty by simp
  then show ?thesis using ct by simp
qed

theorem source_candidate_saturated:
  "ho_typeof S V B t=Some A \<Longrightarrow> ho_saturated_neutral R t \<Longrightarrow>
    (\<And>x. x\<in>set (ho_spine_arguments t) \<Longrightarrow> \<exists>T. source_candidate T x) \<Longrightarrow>
    (\<And>u. ho_step S V R B t u \<Longrightarrow> source_candidate A u) \<Longrightarrow>
    source_candidate A t"
proof (induction A arbitrary: t)
  case (HBase b)
  show ?case
  proof (rule source_candidate_base_intro[OF HBase.prems(1,4)])
    fix T v assume av: "(T,v)\<in>ho_accessible_arguments rank S V B t"
    have vt: "ho_typeof S V B v=Some T" and member: "v\<in>set (ho_spine_arguments t)"
      using av by (auto simp: ho_accessible_arguments_def split: option.splits ho_type.splits ho_term.splits)
    obtain U where cv: "source_candidate U v" using HBase.prems(3)[OF member] by blast
    show "source_candidate T v" by (rule source_candidate_retype[OF cv vt])
  qed
next
  case (HArrow A C)
  have sn: "source.strongly_normalizing t"
  proof (rule accp.accI)
    fix u assume "ho_step S V R B t u"
    then show "source.strongly_normalizing u" by (rule HArrow.prems(4)[THEN source.candidate_SN])
  qed
  have applied: "source_candidate C (HApp t x)" if cx: "source_candidate A x" for x
  proof -
    from source.candidate_SN[OF cx] cx show ?thesis
    proof (induction x rule: accp.induct)
      case (accI x)
      have ty: "ho_typeof S V B (HApp t x)=Some C"
        using HArrow.prems(1) source.candidate_typed[OF accI.prems] by simp
      have neu: "ho_saturated_neutral R (HApp t x)"
        by (rule saturated_neutral_application[OF HArrow.prems(2)])
      have args: "\<exists>T. source_candidate T y" if "y\<in>set (ho_spine_arguments (HApp t x))" for y
        using that HArrow.prems(3) accI.prems by auto
      have reducts: "source_candidate C u" if st: "ho_step S V R B (HApp t x) u" for u
      proof -
        from saturated_neutral_reduct[OF HArrow.prems(2) st] show ?thesis
        proof
          assume "\<exists>g. ho_step S V R B t g \<and> u=HApp g x"
          then obtain g where tg: "ho_step S V R B t g" and eq: "u=HApp g x" by blast
          show ?thesis unfolding eq
            by (rule source.candidate_application[OF HArrow.prems(4)[OF tg] accI.prems])
        next
          assume "\<exists>y. ho_step S V R B x y \<and> u=HApp t y"
          then obtain y where xy: "ho_step S V R B x y" and eq: "u=HApp t y" by blast
          have cy: "source_candidate A y" by (rule source_candidate_reduction[OF accI.prems xy])
          show ?thesis unfolding eq by (rule accI.IH[OF xy cy])
        qed
      qed
      show ?case by (rule HArrow.IH(2)[OF ty neu args reducts])
    qed
  qed
  show ?case using HArrow.prems(1) sn applied by simp
qed

end

end
