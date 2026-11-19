theory DP_Checkpoint_Arguments
 imports DP_Checkpoint_Ground
begin

fun checkpoint_raw_children where
 "checkpoint_raw_children Z S (Fun f []) = (if f=Z then Some [] else None)"
| "checkpoint_raw_children Z S (Fun f [x,xs]) =
   (if f=S then map_option (Cons x) (checkpoint_raw_children Z S xs) else None)"
| "checkpoint_raw_children Z S _ = None"

definition checkpoint_list_cons where
 "checkpoint_list_cons N Z S x xs = Fun N [Fun S [x,Fun S [xs,Fun Z []]]]"

fun checkpoint_encoded_list where
 "checkpoint_encoded_list N Z S [] = Fun N [Fun Z []]"
| "checkpoint_encoded_list N Z S (x#xs) = checkpoint_list_cons N Z S x (checkpoint_encoded_list N Z S xs)"

definition checkpoint_argument_outputs where
 "checkpoint_argument_outputs N Z S t =
   {checkpoint_encoded_list N Z S xs |xs. checkpoint_raw_children Z S t=Some xs}"

lemma checkpoint_argument_outputs_nil[simp]:
 "checkpoint_argument_outputs N Z S (Fun Z []) = {Fun N [Fun Z []]}"
 by (auto simp: checkpoint_argument_outputs_def)

lemma checkpoint_argument_outputs_cons:
 "checkpoint_argument_outputs N Z S (Fun S [x,xs]) =
   checkpoint_list_cons N Z S x ` checkpoint_argument_outputs N Z S xs"
 by (cases "checkpoint_raw_children Z S xs") (auto simp: checkpoint_argument_outputs_def)

definition checkpoint_argument_algebra where
 "checkpoint_argument_algebra N Z S ain aout resume f shapes values =
   (if f=ain then (if length shapes=1 then checkpoint_argument_outputs N Z S (shapes!0) else UNIV)
    else if f=aout then (if length shapes=2 then {shapes!1} else UNIV)
    else if f=resume then (if length shapes=3 then
      checkpoint_list_cons N Z S (shapes!1) ` checkpoint_first_set values else UNIV)
    else UNIV)"

lemma checkpoint_argument_algebra_mono:
 "checkpoint_algebra_mono (checkpoint_argument_algebra N Z S ain aout resume)"
 unfolding checkpoint_algebra_mono_def checkpoint_argument_algebra_def
 using checkpoint_first_set_mono by (auto split: if_splits)

definition checkpoint_argument_rules :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f,nat) rule list" where
 "checkpoint_argument_rules N Z S ain aout resume = [
   (Fun ain [Fun Z []], Fun aout [Fun Z [],Fun N [Fun Z []]]),
   (Fun ain [Fun S [Var 0,Var 1]],Fun resume [Fun ain [Var 1],Var 0,Var 1]),
   (Fun resume [Fun aout [Var 1,Var 2],Var 0,Var 1],
    Fun aout [Fun S [Var 0,Var 1],checkpoint_list_cons N Z S (Var 0) (Var 2)])]"

lemma checkpoint_argument_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [N,Z,S,ain,aout,resume]"
 and constructors: "{N,Z,S}\<subseteq>C"
 and rule: "(l,r)\<in>set (checkpoint_argument_rules N Z S ain aout resume)"
 shows "checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (r\<cdot>sigma)
  \<subseteq> checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (l\<cdot>sigma)"
 using rule distinct constructors
 by (auto simp: checkpoint_argument_rules_def checkpoint_argument_algebra_def
   checkpoint_argument_outputs_cons checkpoint_list_cons_def split: if_splits)

lemma checkpoint_argument_unrestricted_lhs:
 "f\<notin>{ain,aout,resume} \<Longrightarrow>
   checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (Fun f ts)=UNIV"
 by (simp add: checkpoint_argument_algebra_def)

definition check_checkpoint_argument_summary where
 "check_checkpoint_argument_summary C N Z S ain aout resume rules witnesses =
  (distinct [N,Z,S,ain,aout,resume] \<and> {N,Z,S}\<subseteq>C \<and>
   list_all (checkpoint_skeleton_safe_rule C) rules \<and>
   list_all2 (check_checkpoint_schema_rule {ain,aout,resume}
      (checkpoint_argument_rules N Z S ain aout resume)) rules witnesses)"

lemma checked_checkpoint_argument_success:
 fixes rules :: "('f,'v) rule list"
 assumes checked: "check_checkpoint_argument_summary C N Z S ain aout resume rules witnesses"
 and success: "(Fun ain [input],Fun aout [copied,output])\<in>(rstep (set rules))\<^sup>*"
 shows "\<exists>xs. checkpoint_raw_children Z S (checkpoint_skeleton C input)=Some xs \<and>
   checkpoint_skeleton C output=checkpoint_encoded_list N Z S xs"
proof -
 have safe: "checkpoint_skeleton_safe C (set rules)"
 and distinct: "distinct [N,Z,S,ain,aout,resume]"
 and constructors: "{N,Z,S}\<subseteq>C"
 and table: "list_all2 (check_checkpoint_schema_rule {ain,aout,resume}
      (checkpoint_argument_rules N Z S ain aout resume)) rules witnesses"
  using checked by (auto simp: check_checkpoint_argument_summary_def checkpoint_skeleton_safe_list)
 have included: "checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (Fun aout [copied,output])
   \<subseteq> checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (Fun ain [input])"
 proof (rule checkpoint_interpret_rsteps[OF safe checkpoint_argument_algebra_mono _ success])
  fix l r :: "('f,'v) term"
  fix sigma :: "'v \<Rightarrow> ('f,'v) term"
  assume member: "(l,r)\<in>set rules"
  show "checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (r\<cdot>sigma)
   \<subseteq> checkpoint_interpret C (checkpoint_argument_algebra N Z S ain aout resume) (l\<cdot>sigma)"
   by (rule checkpoint_schema_table_sound[OF _ _ table member])
    (rule checkpoint_argument_rules_sound[OF distinct constructors], assumption,
     rule checkpoint_argument_unrestricted_lhs, assumption)
 qed
 show ?thesis using included distinct
  by (auto simp: checkpoint_argument_algebra_def checkpoint_argument_outputs_def)
qed

ML \<open>
val checked = @{thms checkpoint_argument_outputs_cons checkpoint_argument_algebra_mono
 checkpoint_argument_rules_sound checked_checkpoint_argument_success};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted argument extraction summary" else ();
\<close>
end
