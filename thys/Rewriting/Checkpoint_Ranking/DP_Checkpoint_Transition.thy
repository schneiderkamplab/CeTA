theory DP_Checkpoint_Transition
 imports DP_Checkpoint_Inference
begin

text \<open>A transition receipt names an original pair and one antecedent
alternative. Its conclusion must be an actual annotation at the original target
interface. Checking receipts does not by itself establish coverage.\<close>
definition check_checkpoint_transition where
 "check_checkpoint_transition checker pair_list table receipt =
 (case receipt of (i,antecedents,derivation,after) \<Rightarrow>
  i<length pair_list \<and>
  (case pair_list!i of (Fun f ss,Fun g ts) \<Rightarrow>
    (g,length ts,after)\<in>set table \<and>
    check_checkpoint_clause_derivation checker antecedents ss derivation after ts
  | _ \<Rightarrow> False))"

lemma checkpoint_annotation_from_clause:
 assumes member: "(f,length ts,clause)\<in>set table"
 and holds: "checkpoint_clause_holds C L N Z S R old clause ts"
 shows "checkpoint_annotation_holds C L N Z S R table old (Fun f ts)"
 unfolding checkpoint_annotation_holds_def
 apply (simp only: term.case list_ex_iff)
 apply (rule bexI[of _ "(f,length ts,clause)"])
 using assms by auto

lemma checked_checkpoint_transition:
 assumes sound: "\<And>known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S R old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma claim"
 and checked: "check_checkpoint_transition checker pair_list table (i,antecedents,derivation,after)"
 and holds: "checkpoint_clause_holds C L N Z S R old antecedents
 (args (fst (pair_list!i)\<cdot>sigma))"
 shows "checkpoint_annotation_holds C L N Z S R table old (snd (pair_list!i)\<cdot>sigma)"
proof -
 obtain l r where raw_pair: "pair_list!i=(l,r)" by (cases "pair_list!i") auto
 obtain f ss where left: "l=Fun f ss" using checked
 by (cases l; cases r) (auto simp: check_checkpoint_transition_def raw_pair)
 obtain g ts where right: "r=Fun g ts" using checked
 by (cases r) (auto simp: check_checkpoint_transition_def raw_pair left)
 have pair: "pair_list!i=(Fun f ss,Fun g ts)" using raw_pair left right by simp
 have member: "(g,length ts,after)\<in>set table"
 and derivation: "check_checkpoint_clause_derivation checker antecedents ss derivation after ts"
 using checked by (auto simp: check_checkpoint_transition_def pair)
 have initial: "checkpoint_clause_holds C L N Z S R old antecedents (map (\<lambda>t. t\<cdot>sigma) ss)"
 using holds by (simp add: pair)
 have final: "checkpoint_clause_holds C L N Z S R old after (map (\<lambda>t. t\<cdot>sigma) ts)"
 by (rule checked_checkpoint_clause_derivation[OF sound derivation initial])
 have target_member: "(g,length (map (\<lambda>t. t\<cdot>sigma) ts),after)\<in>set table"
 using member by simp
 show ?thesis using checkpoint_annotation_from_clause[OF target_member final] by (simp add: pair)
qed

definition checkpoint_has_transition where
 "checkpoint_has_transition receipts i antecedents =
 list_ex (\<lambda>(j,b,d,a). i=j \<and> antecedents=b) receipts"

definition check_checkpoint_transition_coverage where
 "check_checkpoint_transition_coverage K coord_map pair_list table receipts =
 list_all (\<lambda>i. case fst (pair_list!i) of Var x \<Rightarrow> False | Fun f ss \<Rightarrow>
   (if f\<in>K then coord_map f<length ss \<and>
     checkpoint_has_transition receipts i [CP_Exact (coord_map f)]
    else list_all (\<lambda>(g,n,clause). g=f \<and> n=length ss \<longrightarrow>
     checkpoint_has_transition receipts i clause) table)) [0..<length pair_list]"


lemma checkpoint_has_transitionD:
 assumes "checkpoint_has_transition receipts i antecedents"
 obtains derivation after where "(i,antecedents,derivation,after)\<in>set receipts"
 using assms by (auto simp: checkpoint_has_transition_def list_ex_iff)

lemma checkpoint_coverage_at:
 assumes covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list"
 shows "case fst (pair_list!i) of Var x \<Rightarrow> False | Fun f ss \<Rightarrow>
 (if f\<in>K then coord_map f<length ss \<and> checkpoint_has_transition receipts i [CP_Exact (coord_map f)]
 else list_all (\<lambda>(g,n,clause). g=f \<and> n=length ss \<longrightarrow> checkpoint_has_transition receipts i clause) table)"
proof -
 have all: "\<forall>j\<in>set [0..<length pair_list].
 (case fst (pair_list!j) of Var x \<Rightarrow> False | Fun f ss \<Rightarrow>
 (if f\<in>K then coord_map f<length ss \<and> checkpoint_has_transition receipts j [CP_Exact (coord_map f)]
 else list_all (\<lambda>(g,n,clause). g=f \<and> n=length ss \<longrightarrow> checkpoint_has_transition receipts j clause) table))"
 using covered by (simp only: check_checkpoint_transition_coverage_def list_all_iff)
 have member: "i\<in>set [0..<length pair_list]" using index by simp
 show ?thesis by (rule bspec[OF all member])
qed

lemma checkpoint_entry_coverage:
 assumes covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list" and left: "fst (pair_list!i)=Fun f ss" and marked: "f\<in>K"
 shows "coord_map f<length ss" "checkpoint_has_transition receipts i [CP_Exact (coord_map f)]"
 using checkpoint_coverage_at[OF covered index] left marked by auto

lemma checkpoint_internal_coverage:
 assumes covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list" and left: "fst (pair_list!i)=Fun f ss" and unmarked: "f\<notin>K"
 and member: "(f,length ss,clause)\<in>set table"
 shows "checkpoint_has_transition receipts i clause"
 using checkpoint_coverage_at[OF covered index] left unmarked member by (auto simp: list_all_iff)

lemma checked_checkpoint_transition_for_clause:
 assumes sound: "\<And>known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S R old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma claim"
 and checked: "list_all (check_checkpoint_transition checker pair_list table) receipts"
 and covered: "checkpoint_has_transition receipts i antecedents"
 and holds: "checkpoint_clause_holds C L N Z S R old antecedents (args (fst (pair_list!i)\<cdot>sigma))"
 shows "checkpoint_annotation_holds C L N Z S R table old (snd (pair_list!i)\<cdot>sigma)"
proof -
 obtain derivation after where member: "(i,antecedents,derivation,after)\<in>set receipts"
 by (rule checkpoint_has_transitionD[OF covered])
 have step: "check_checkpoint_transition checker pair_list table (i,antecedents,derivation,after)"
 using member checked by (simp add: list_all_iff)
 show ?thesis by (rule checked_checkpoint_transition[OF sound step holds])
qed

lemma checked_checkpoint_entry_transition:
 assumes sound: "\<And>old known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S R old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma claim"
 and checked: "list_all (check_checkpoint_transition checker pair_list table) receipts"
 and covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list" and left: "fst (pair_list!i)=Fun f ss" and marked: "f\<in>K"
 shows "checkpoint_annotation_holds C L N Z S R table
 (checkpoint_forest N Z S (checkpoint_skeleton C ((ss!(coord_map f))\<cdot>sigma))) (snd (pair_list!i)\<cdot>sigma)"
proof -
 have bound: "coord_map f<length ss"
 and present: "checkpoint_has_transition receipts i [CP_Exact (coord_map f)]"
 using checkpoint_entry_coverage[OF covered index left marked] by auto
 have initial: "checkpoint_clause_holds C L N Z S R
 (checkpoint_forest N Z S (checkpoint_skeleton C ((ss!(coord_map f))\<cdot>sigma)))
 [CP_Exact (coord_map f)] (args (fst (pair_list!i)\<cdot>sigma))"
 by (simp add: checkpoint_clause_holds_def checkpoint_atom_bounded_def left bound)
 show ?thesis by (rule checked_checkpoint_transition_for_clause[OF _ checked present initial]) (use sound in blast)
qed

lemma checked_checkpoint_internal_transition:
 assumes sound: "\<And>known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S R old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma claim"
 and checked: "list_all (check_checkpoint_transition checker pair_list table) receipts"
 and covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list" and left: "fst (pair_list!i)=Fun f ss" and unmarked: "f\<notin>K"
 and holds: "checkpoint_annotation_holds C L N Z S R table old (fst (pair_list!i)\<cdot>sigma)"
 shows "checkpoint_annotation_holds C L N Z S R table old (snd (pair_list!i)\<cdot>sigma)"
proof -
 obtain clause where member: "(f,length ss,clause)\<in>set table"
 and initial: "checkpoint_clause_holds C L N Z S R old clause (args (fst (pair_list!i)\<cdot>sigma))"
 using holds by (auto simp: checkpoint_annotation_holds_def left list_ex_iff)
 have present: "checkpoint_has_transition receipts i clause"
 by (rule checkpoint_internal_coverage[OF covered index left unmarked member])
 show ?thesis by (rule checked_checkpoint_transition_for_clause[OF sound checked present initial])
qed

ML \<open>
val thms = @{thms checkpoint_annotation_from_clause checked_checkpoint_transition checkpoint_has_transitionD checkpoint_entry_coverage checkpoint_internal_coverage checked_checkpoint_transition_for_clause checked_checkpoint_entry_transition checked_checkpoint_internal_transition};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted pair transition checker" else ();
\<close>
end
