theory Sparse_Tiling_Simulation
  imports "Abstract-Rewriting.Abstract_Rewriting"
begin

text \<open>Local simulation infrastructure for sparse string tiling. This theory
  does not yet instantiate the shift algebra or provide a certificate checker.\<close>

definition sparse_word_step :: "('a list \<times> 'a list) set \<Rightarrow> ('a list \<times> 'a list) set" where
  "sparse_word_step R = {(s,t). \<exists>u v l r. (l,r) \<in> R \<and> s = u @ l @ v \<and> t = u @ r @ v}"

lemma sparse_word_stepI:
  "(l,r) \<in> R \<Longrightarrow> (u @ l @ v, u @ r @ v) \<in> sparse_word_step R"
  unfolding sparse_word_step_def by blast

lemma sparse_word_step_context:
  "(s,t) \<in> sparse_word_step R \<Longrightarrow>
    (u @ s @ v, u @ t @ v) \<in> sparse_word_step R"
proof -
  assume step: "(s,t) \<in> sparse_word_step R"
  then obtain a b l r where rule: "(l,r) \<in> R"
    and s: "s = a @ l @ b" and t: "t = a @ r @ b"
    unfolding sparse_word_step_def by blast
  have "((u @ a) @ l @ (b @ v), (u @ a) @ r @ (b @ v)) \<in> sparse_word_step R"
    by (rule sparse_word_stepI[OF rule])
  then show ?thesis by (simp add: s t append_assoc)
qed

lemma sparse_closed_chain:
  assumes start: "f 0 \<in> L"
    and steps: "chain R f"
    and closed: "\<And>x y. x \<in> L \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> y \<in> L"
  shows "f n \<in> L"
  by (induction n) (use start steps closed in auto)

lemma sparse_local_simulation_SN:
  assumes closed: "\<And>x y. x \<in> L \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> y \<in> L"
    and simulate: "\<And>x y. x \<in> L \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> (label x,label y) \<in> S"
    and target: "SN_on S (label ` L)"
  shows "SN_on R L"
proof (rule SN_onI)
  fix f
  assume start: "f 0 \<in> L" and steps: "chain R f"
  have inside: "\<And>n. f n \<in> L"
    by (rule sparse_closed_chain[OF start steps closed])
  have labelled: "chain S (\<lambda>n. label (f n))"
    using simulate inside steps by blast
  have initial: "label (f 0) \<in> label ` L" using start by blast
  have bad: "\<exists>g. g 0 \<in> label ` L \<and> chain S g"
    by (rule exI[of _ "\<lambda>n. label (f n)"]) (use initial labelled in blast)
  from target bad show False unfolding SN_on_def by blast
qed

end
