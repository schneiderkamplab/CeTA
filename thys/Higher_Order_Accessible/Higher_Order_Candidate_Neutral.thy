theory Higher_Order_Candidate_Neutral
  imports Higher_Order_Accessible_Candidates
begin

context ho_neutral_reducibility
begin

theorem candidate_neutral_computable:
  assumes closed: "\<And>b t u. I b t \<Longrightarrow> step t u \<Longrightarrow> I b u"
    and base_neutral: "\<And>b t. typed (HBase b) t \<Longrightarrow> neutral t \<Longrightarrow>
      (\<And>u. step t u \<Longrightarrow> I b u) \<Longrightarrow> I b t"
  shows
  "typed A t \<Longrightarrow> neutral t \<Longrightarrow>
    (\<And>u. step t u \<Longrightarrow> candidate_computable I A u) \<Longrightarrow> candidate_computable I A t"
proof (induction A arbitrary: t)
  case (HBase b)
  have sn: "strongly_normalizing t"
  proof (rule accp.accI)
    fix u assume "step t u"
    then show "strongly_normalizing u" by (rule HBase.prems(3)[THEN candidate_SN])
  qed
  have ib: "I b t" by (rule base_neutral[OF HBase.prems(1,2)])
      (use HBase.prems(3) in auto)
  show ?case using HBase.prems(1) sn ib by simp
next
  case (HArrow A B)
  have sn: "strongly_normalizing t"
  proof (rule accp.accI)
    fix u assume "step t u"
    then show "strongly_normalizing u" by (rule HArrow.prems(3)[THEN candidate_SN])
  qed
  have applied: "candidate_computable I B (application t x)" if cx: "candidate_computable I A x" for x
  proof -
    from candidate_SN[OF cx] cx show ?thesis
    proof (induction x rule: accp.induct)
      case (accI x)
      have ty: "typed B (application t x)"
        by (rule application_type[OF HArrow.prems(1) candidate_typed[OF accI.prems]])
      have neu: "neutral (application t x)" by (rule neutral_application[OF HArrow.prems(2)])
      have reducts: "candidate_computable I B u" if reduction: "step (application t x) u" for u
      proof -
        from neutral_reduct[OF HArrow.prems(2) reduction] show ?thesis
        proof
          assume "\<exists>g. step t g \<and> u=application g x"
          then obtain g where tg: "step t g" and u: "u=application g x" by auto
          show ?thesis unfolding u by (rule candidate_application[OF HArrow.prems(3)[OF tg] accI.prems])
        next
          assume "\<exists>y. step x y \<and> u=application t y"
          then obtain y where xy: "step x y" and u: "u=application t y" by auto
          have cy: "candidate_computable I A y" by (rule candidate_reduction[OF closed accI.prems xy])
          show ?thesis unfolding u by (rule accI.IH[OF xy cy])
        qed
      qed
      show ?case by (rule HArrow.IH(2)[OF ty neu reducts])
    qed
  qed
  show ?case using HArrow.prems(1) sn applied by simp
qed


end

end
