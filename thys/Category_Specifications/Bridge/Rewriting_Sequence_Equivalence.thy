theory Rewriting_Sequence_Equivalence
  imports Category_Specifications.Rewriting_Sequences_Spec TRS_Standard_Equivalence
begin

lemma finite_steps_relation:
  "finite_steps step s t \<longleftrightarrow> (s,t) \<in> {(u,v). step u v}^*"
proof
  assume "finite_steps step s t"
  then show "(s,t) \<in> {(u,v). step u v}^*"
    by (induct rule: finite_steps.induct) (auto intro: rtrancl_into_rtrancl)
next
  assume "(s,t) \<in> {(u,v). step u v}^*"
  then show "finite_steps step s t"
    by (induct rule: rtrancl_induct) (auto intro: finite_steps.zero finite_steps.append)
qed


lemma mapped_finite_relation:
  assumes simulation: "\<And>s t. (s,t) \<in> R \<Longrightarrow> (f s,f t) \<in> S"
    and path: "(s,t) \<in> R^*"
  shows "(f s,f t) \<in> S^*"
  using path by (induct rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl simulation)

lemma relative_direct_simulation:
  assumes sn: "SN_rel T U"
    and strict: "\<And>s t. (s,t) \<in> R \<Longrightarrow> (f s,f t) \<in> T"
    and weak: "\<And>s t. (s,t) \<in> S \<Longrightarrow> (f s,f t) \<in> U"
  shows "SN_rel R S"
proof -
  have weakpath: "\<And>s t. (s,t) \<in> S^* \<Longrightarrow> (f s,f t) \<in> U^*"
    by (rule mapped_finite_relation[OF weak])
  have block: "\<And>s t. (s,t) \<in> relto R S \<Longrightarrow> (f s,f t) \<in> relto T U"
    by (auto dest: strict weakpath)
  show ?thesis
  proof (unfold SN_rel_defs SN_defs, clarify)
    fix ts
    assume "\<forall>i. (ts i,ts (Suc i)) \<in> relto R S"
    then have "\<forall>i. ((f \<circ> ts) i,(f \<circ> ts) (Suc i)) \<in> relto T U"
      using block by simp
    then show False using sn unfolding SN_rel_defs SN_defs by blast
  qed
qed

locale step_translation =
  fixes encode :: "'a \<Rightarrow> 'b" and decode :: "'b \<Rightarrow> 'a"
    and step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and relation :: "'b rel"
  assumes decode_encode [simp]: "decode (encode t) = t"
    and encode_decode [simp]: "encode (decode u) = u"
    and step_iff: "step s t \<longleftrightarrow> (encode s, encode t) \<in> relation"
begin
lemma finite_steps_iff:
  "finite_steps step s t \<longleftrightarrow> (encode s, encode t) \<in> relation^*"
proof
  assume "finite_steps step s t"
  then show "(encode s, encode t) \<in> relation^*"
    by (induct rule: finite_steps.induct) (auto simp: step_iff intro: rtrancl_into_rtrancl)
next
  have "\<And>a b. (a,b) \<in> relation^* \<Longrightarrow> finite_steps step (decode a) (decode b)"
  proof -
    fix a b
    assume "(a,b) \<in> relation^*"
    then show "finite_steps step (decode a) (decode b)"
      by (induct rule: rtrancl_induct) (auto simp: step_iff intro: finite_steps.zero finite_steps.append)
  qed
  then show "(encode s, encode t) \<in> relation^* \<Longrightarrow> finite_steps step s t" by (metis decode_encode)
qed
lemma termination_iff:
  "no_infinite_steps step \<longleftrightarrow> SN relation"
proof -
  have chains: "(\<exists>ts. \<forall>i. step (ts i) (ts (Suc i))) \<longleftrightarrow>
    (\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> relation)"
  proof
    assume "\<exists>ts. \<forall>i. step (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. step (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> relation"
      by (intro exI[of _ "encode \<circ> ts"]) (simp add: step_iff)
  next
    assume "\<exists>ts. \<forall>i. (ts i, ts (Suc i)) \<in> relation"
    then obtain ts where "\<forall>i. (ts i, ts (Suc i)) \<in> relation" by blast
    then show "\<exists>ts. \<forall>i. step (ts i) (ts (Suc i))"
      by (intro exI[of _ "decode \<circ> ts"]) (simp add: step_iff)
  qed
  show ?thesis unfolding no_infinite_steps_def SN_defs using chains by blast
qed
end
end
