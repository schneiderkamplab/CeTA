theory ITS_Properties
  imports Category_Specifications.ITS_Spec
begin

lemma its_nontermination_iff:
  "\<not> its_terminates P \<longleftrightarrow>
    (\<exists>s. its_initial P (s 0) \<and> (\<forall>n. its_step P (s n) (s (Suc n))))"
  by (simp add: its_terminates_def)

lemma its_empty_rules:
  "its_rules P = {} \<Longrightarrow> its_terminates P"
  by (auto simp: its_terminates_def its_step_def)

lemma its_no_entry:
  "its_entries P = {} \<Longrightarrow> its_terminates P"
  by (auto simp: its_terminates_def its_initial_def)

lemma its_initial_self_loop:
  "its_initial P s \<Longrightarrow> its_step P s s \<Longrightarrow> \<not> its_terminates P"
  unfolding its_terminates_def by (intro notI; elim notE; rule exI[where x="\<lambda>n. s"]; simp)

text \<open>A self-loop at a non-entry location does not prevent termination
when the entries have no outgoing transitions.\<close>
lemma its_unreachable_loop:
  "its_terminates \<lparr>its_entries = {False},
    its_rules = {(True,True,\<lambda>a b z. b=a)}, its_allowed = \<lambda>l a. True\<rparr>"
  unfolding its_terminates_def its_initial_def its_step_def by auto

lemma its_nat_ranking:
  assumes decrease: "\<And>s t. its_step P s t \<Longrightarrow> rank t < (rank s :: nat)"
  shows "its_terminates P"
proof (unfold its_terminates_def, clarify)
  fix s assume initial: "its_initial P (s 0)"
    and chain: "\<forall>n. its_step P (s n) (s (Suc n))"
  have bound: "rank (s n) + n \<le> rank (s 0)" for n
  proof (induct n)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "rank (s (Suc n)) < rank (s n)" using decrease chain by blast
    then show ?case using Suc by arith
  qed
  show False using bound[of "Suc (rank (s 0))"] by simp
qed

definition integer_countdown :: "(unit,unit) integer_system" where
  "integer_countdown = \<lparr>its_entries={()}, its_rules={((),(),\<lambda>a b z. a ()>0 \<and> b ()=a ()-1)},
    its_allowed=\<lambda>l a. True\<rparr>"
lemma integer_countdown_terminates: "its_terminates integer_countdown"
proof (rule its_nat_ranking[where rank="\<lambda>s. nat (snd s ())"])
  fix s t assume "its_step integer_countdown s t"
  then show "nat (snd t ()) < nat (snd s ())"
    by (auto simp: its_step_def integer_countdown_def)
qed

text \<open>A local value is chosen separately at every transition. It is not
an extra initial-state restriction or a persistent store component.\<close>
lemma integer_local_choice:
  "its_step \<lparr>its_entries={()}, its_rules={((),(),\<lambda>a b z. b ()=z ())},
    its_allowed=\<lambda>l a. True\<rparr> ((),a) ((),b)"
  unfolding its_step_def by (auto intro!: exI[of _ b])

text \<open>Both updates read the old store: this swaps two values rather than
performing two sequential assignments.\<close>
lemma integer_simultaneous_swap:
  "its_step \<lparr>its_entries={()},
    its_rules={((),(),\<lambda>a b z. b True=a False \<and> b False=a True)},
    its_allowed=\<lambda>l a. True\<rparr> ((),a) ((),\<lambda>x. a (\<not>x))"
  by (simp add: its_step_def)

end
