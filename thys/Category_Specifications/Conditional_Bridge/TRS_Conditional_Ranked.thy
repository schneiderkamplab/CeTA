theory TRS_Conditional_Ranked
  imports TRS_Conditional_Embedding
begin
text \<open>Ranked inference in IsaFoR's native representation. The Boolean tag
is False for a single rewrite and True for reachability. Signature restrictions
apply to every premise and substitution, not just to the outer endpoints.\<close>
type_synonym ('f,'v) native_conditional_goal = "bool \<times> ('f,'v) term \<times> ('f,'v) term"
fun to_conditional_goal where
  "to_conditional_goal (CRewrite s t) = (False,to_term s,to_term t)"
| "to_conditional_goal (CReach s t) = (True,to_term s,to_term t)"
definition from_conditional_goal where
  "from_conditional_goal g = (case g of (b,s,t) \<Rightarrow>
    if b then CReach (from_term s) (from_term t) else CRewrite (from_term s) (from_term t))"
lemma conditional_goal_roundtrip [simp]:
  "from_conditional_goal (to_conditional_goal g) = g"
  "to_conditional_goal (from_conditional_goal h) = h"
  by (cases g; simp add: from_conditional_goal_def)
     (cases h; auto simp: from_conditional_goal_def split: prod.splits)
lemma conditional_goal_inj [simp]: "to_conditional_goal g = to_conditional_goal h \<longleftrightarrow> g=h"
  by (metis conditional_goal_roundtrip(1))
definition from_conditional_rules where
  "from_conditional_rules R = (\<lambda>((l,r),cs).
    ((from_term l,from_term r),map (\<lambda>(s,t). (from_term s,from_term t)) cs)) ` R"
lemma conditional_rules_roundtrip [simp]:
  "from_conditional_rules (to_conditional_rules R) = R"
  "to_conditional_rules (from_conditional_rules S) = S"
  by (auto simp: from_conditional_rules_def to_conditional_rules_def image_image
      split_def o_def map_idI)

inductive native_conditional_inference ::
  "('f \<times> nat) set \<Rightarrow> ('f,'v) ctrs \<Rightarrow>
    ('f,'v) native_conditional_goal \<Rightarrow> ('f,'v) native_conditional_goal list \<Rightarrow> bool"
  for F R where
  reflexive: "funas_term s \<subseteq> F \<Longrightarrow> native_conditional_inference F R (True,s,s) []"
| transitive: "funas_term s \<subseteq> F \<Longrightarrow> funas_term u \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow>
    native_conditional_inference F R (True,s,t) [(False,s,u),(True,u,t)]"
| apply_rule: "((l,r),cs) \<in> R \<Longrightarrow> funas_ctxt C \<subseteq> F \<Longrightarrow>
    (\<forall>x. funas_term (sigma x) \<subseteq> F) \<Longrightarrow>
    funas_term (C\<langle>l \<cdot> sigma\<rangle>) \<subseteq> F \<Longrightarrow>
    funas_term (C\<langle>r \<cdot> sigma\<rangle>) \<subseteq> F \<Longrightarrow>
    (\<forall>(s,t)\<in>set cs. funas_term (s \<cdot> sigma) \<subseteq> F \<and> funas_term (t \<cdot> sigma) \<subseteq> F) \<Longrightarrow>
    native_conditional_inference F R (False,C\<langle>l \<cdot> sigma\<rangle>,C\<langle>r \<cdot> sigma\<rangle>)
      (map (\<lambda>(s,t). (True,s \<cdot> sigma,t \<cdot> sigma)) cs)"

inductive native_conditional_success for F R where
  conclude: "native_conditional_inference F R g gs \<Longrightarrow>
    list_all (native_conditional_success F R) gs \<Longrightarrow> native_conditional_success F R g"

lemma conditional_inference_translation:
  assumes "conditional_inference A R g gs"
  shows "native_conditional_inference (to_signature A) (to_conditional_rules R)
    (to_conditional_goal g) (map to_conditional_goal gs)"
  using assms
proof cases
  case (reflexive s)
  then show ?thesis by (simp add: native_conditional_inference.reflexive)
next
  case (transitive s u t)
  then show ?thesis by (simp add: native_conditional_inference.transitive)
next
  case (rule l r cs C sigma)
  have mem: "((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs) \<in> to_conditional_rules R"
    unfolding to_conditional_rules_def
    using imageI[of "((l,r),cs)" R "\<lambda>((l,r),cs). ((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)"] rule by simp
  note inf = native_conditional_inference.apply_rule[OF mem, of "to_context C" "to_signature A" "to_substitution sigma"]
  show ?thesis using inf rule
    by (simp add: correct_substitution_iff map_map split_def o_def)
qed

lemma conditional_inference_reflection:
  assumes "native_conditional_inference (to_signature A) S g gs"
  shows "conditional_inference A (from_conditional_rules S)
    (from_conditional_goal g) (map from_conditional_goal gs)"
  using assms
proof cases
  case (reflexive s)
  then show ?thesis by (simp add: from_conditional_goal_def conditional_inference.reflexive)
next
  case (transitive s u t)
  then show ?thesis by (simp add: from_conditional_goal_def conditional_inference.transitive)
next
  case (apply_rule l r cs C sigma)
  have mem: "((from_term l,from_term r),map (\<lambda>(s,t). (from_term s,from_term t)) cs) \<in> from_conditional_rules S"
    unfolding from_conditional_rules_def
    using imageI[of "((l,r),cs)" S "\<lambda>((l,r),cs). ((from_term l,from_term r),map (\<lambda>(s,t). (from_term s,from_term t)) cs)"] apply_rule by simp
  have sub: "correct_substitution A (from_substitution sigma)"
    using apply_rule by (simp add: correct_substitution_iff)
  have subst_back: "standard_subst (from_substitution sigma) (from_term t) = from_term (t \<cdot> sigma)" for t
    by (rule to_term_inj[THEN iffD1]) simp
  have ctxt_back: "standard_plug (from_context C) (from_term t) = from_term (C\<langle>t\<rangle>)" for t
    by (rule to_term_inj[THEN iffD1]) simp
  note inf = conditional_inference.rule[OF mem, of A "from_context C" "from_substitution sigma"]
  show ?thesis using inf apply_rule sub
    by (simp add: from_conditional_goal_def subst_back ctxt_back map_map split_def o_def)
qed

lemma conditional_inference_iff:
  "conditional_inference A R g gs \<longleftrightarrow>
    native_conditional_inference (to_signature A) (to_conditional_rules R)
      (to_conditional_goal g) (map to_conditional_goal gs)"
  using conditional_inference_translation[of A R g gs]
    conditional_inference_reflection[of A "to_conditional_rules R" "to_conditional_goal g" "map to_conditional_goal gs"]
  by (auto simp: map_map o_def)

lemma conditional_success_translation:
  "conditional_success A R g \<Longrightarrow>
    native_conditional_success (to_signature A) (to_conditional_rules R) (to_conditional_goal g)"
proof (induct rule: conditional_success.induct)
  case ("derive" g gs)
  have inf: "native_conditional_inference (to_signature A) (to_conditional_rules R)
      (to_conditional_goal g) (map to_conditional_goal gs)"
    by (rule conditional_inference_translation[OF "derive.hyps"(1)])
  have pre: "list_all (native_conditional_success (to_signature A) (to_conditional_rules R)) (map to_conditional_goal gs)"
    using "derive" by (simp add: list_all_iff)
  show ?case by (rule native_conditional_success.conclude[OF inf pre])
qed
lemma conditional_success_reflection:
  "native_conditional_success (to_signature A) S g \<Longrightarrow>
    conditional_success A (from_conditional_rules S) (from_conditional_goal g)"
proof (induct rule: native_conditional_success.induct)
  case (conclude g gs)
  have inf: "conditional_inference A (from_conditional_rules S)
      (from_conditional_goal g) (map from_conditional_goal gs)"
    by (rule conditional_inference_reflection[OF conclude.hyps(1)])
  have pre: "list_all (conditional_success A (from_conditional_rules S)) (map from_conditional_goal gs)"
    using conclude by (simp add: list_all_iff)
  show ?case by (rule conditional_success.derive[OF inf pre])
qed
lemma conditional_success_iff:
  "conditional_success A R g \<longleftrightarrow>
    native_conditional_success (to_signature A) (to_conditional_rules R) (to_conditional_goal g)"
  using conditional_success_translation conditional_success_reflection[of A "to_conditional_rules R" "to_conditional_goal g"] by auto

definition ranked_cstep where
  "ranked_cstep F R = {(s,t). native_conditional_success F R (False,s,t)}"
definition ranked_conditional_evaluation where
  "ranked_conditional_evaluation F R = {(g,h). \<exists>gs i.
    native_conditional_inference F R g gs \<and> i < length gs \<and>
    (\<forall>j<i. native_conditional_success F R (gs!j)) \<and> h=gs!i}"
lemma conditional_step_iff_ranked:
  "conditional_step A R s t \<longleftrightarrow>
    (to_term s,to_term t) \<in> ranked_cstep (to_signature A) (to_conditional_rules R)"
  by (simp add: conditional_step_def conditional_success_iff ranked_cstep_def)
lemma conditional_evaluation_iff_ranked:
  "conditional_evaluation_step A R g h \<longleftrightarrow>
    (to_conditional_goal g,to_conditional_goal h) \<in>
      ranked_conditional_evaluation (to_signature A) (to_conditional_rules R)"
proof
  assume "conditional_evaluation_step A R g h"
  then obtain gs i where inf: "conditional_inference A R g gs" and idx: "i<length gs"
    and pre: "\<forall>j<i. conditional_success A R (gs!j)" and h: "h=gs!i"
    by (auto simp: conditional_evaluation_step_def)
  show "(to_conditional_goal g,to_conditional_goal h) \<in> ranked_conditional_evaluation (to_signature A) (to_conditional_rules R)"
    unfolding ranked_conditional_evaluation_def
    by (intro CollectI case_prodI exI[of _ "map to_conditional_goal gs"] exI[of _ i])
      (use conditional_inference_translation[OF inf] idx pre h in \<open>auto simp: conditional_success_iff\<close>)
next
  assume "(to_conditional_goal g,to_conditional_goal h) \<in> ranked_conditional_evaluation (to_signature A) (to_conditional_rules R)"
  then obtain gs i where inf: "native_conditional_inference (to_signature A) (to_conditional_rules R) (to_conditional_goal g) gs"
    and idx: "i<length gs" and pre: "\<forall>j<i. native_conditional_success (to_signature A) (to_conditional_rules R) (gs!j)"
    and h: "to_conditional_goal h=gs!i" by (auto simp: ranked_conditional_evaluation_def)
  have pre': "conditional_success A R (from_conditional_goal (gs!j))" if "j<i" for j
    using conditional_success_reflection[of A "to_conditional_rules R" "gs!j"] pre that by auto
  have h': "h=from_conditional_goal (gs!i)" using h by (metis conditional_goal_roundtrip(1))
  show "conditional_evaluation_step A R g h"
    unfolding conditional_evaluation_step_def
    by (intro exI[of _ "map from_conditional_goal gs"] exI[of _ i])
      (use conditional_inference_reflection[OF inf] pre' idx h' in \<open>auto\<close>)
qed

lemma no_infinite_SN_bijection:
  assumes step: "\<And>x y. P x y \<longleftrightarrow> (f x,f y) \<in> S"
    and inverse: "\<And>y. f (g y) = y"
  shows "no_infinite_steps P \<longleftrightarrow> SN S"
proof -
  have chains: "(\<exists>ts. \<forall>i. P (ts i) (ts (Suc i))) \<longleftrightarrow>
      (\<exists>ts. \<forall>i. (ts i,ts (Suc i)) \<in> S)"
  proof
    assume "\<exists>ts. \<forall>i. P (ts i) (ts (Suc i))"
    then obtain ts where "\<forall>i. P (ts i) (ts (Suc i))" by blast
    then show "\<exists>ts. \<forall>i. (ts i,ts (Suc i)) \<in> S"
      by (intro exI[of _ "f \<circ> ts"]) (simp add: step)
  next
    assume "\<exists>ts. \<forall>i. (ts i,ts (Suc i)) \<in> S"
    then obtain ts where "\<forall>i. (ts i,ts (Suc i)) \<in> S" by blast
    then show "\<exists>ts. \<forall>i. P (ts i) (ts (Suc i))"
      by (intro exI[of _ "g \<circ> ts"]) (simp add: step inverse)
  qed
  show ?thesis unfolding no_infinite_steps_def SN_defs using chains by blast
qed
lemma trs_conditional_terminates_iff_ranked:
  "trs_conditional_terminates A R \<longleftrightarrow> SN (ranked_cstep (to_signature A) (to_conditional_rules R))"
  unfolding trs_conditional_terminates_def
  by (rule no_infinite_SN_bijection[where P="conditional_step A R" and S="ranked_cstep (to_signature A) (to_conditional_rules R)" and f=to_term and g=from_term])
    (simp_all add: conditional_step_iff_ranked)
lemma trs_conditional_operationally_terminates_iff_ranked:
  "trs_conditional_operationally_terminates A R \<longleftrightarrow>
    SN (ranked_conditional_evaluation (to_signature A) (to_conditional_rules R))"
  unfolding trs_conditional_operationally_terminates_def
  by (rule no_infinite_SN_bijection[where P="conditional_evaluation_step A R" and S="ranked_conditional_evaluation (to_signature A) (to_conditional_rules R)" and f=to_conditional_goal and g=from_conditional_goal])
    (simp_all add: conditional_evaluation_iff_ranked)
end
