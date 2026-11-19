theory DP_Checkpoint_Ground
 imports DP_Checkpoint_Schema
begin

fun checkpoint_ground_tree and checkpoint_ground_spine where
 "checkpoint_ground_tree N Z S (Fun f [xs]) = (f=N \<and> checkpoint_ground_spine N Z S xs)"
| "checkpoint_ground_tree N Z S _ = False"
| "checkpoint_ground_spine N Z S (Fun f []) = (f=Z)"
| "checkpoint_ground_spine N Z S (Fun f [x,xs]) =
    (f=S \<and> checkpoint_ground_tree N Z S x \<and> checkpoint_ground_spine N Z S xs)"
| "checkpoint_ground_spine N Z S _ = False"

fun checkpoint_first_set where
 "checkpoint_first_set [] = UNIV"
| "checkpoint_first_set (x#xs) = x"

lemma checkpoint_first_set_mono:
 "list_all2 (\<subseteq>) xs ys \<Longrightarrow> checkpoint_first_set xs \<subseteq> checkpoint_first_set ys"
 by (cases xs; cases ys) auto

definition checkpoint_ground_algebra where
 "checkpoint_ground_algebra N Z S gin sin resume head tail f shapes values =
   (if f=gin then (if length shapes=1 then
     (if checkpoint_ground_tree N Z S (shapes!0) then UNIV else {}) else UNIV)
    else if f=sin then (if length shapes=1 then
     (if checkpoint_ground_spine N Z S (shapes!0) then UNIV else {}) else UNIV)
    else if f=resume \<or> f=tail then checkpoint_first_set values
    else if f=head then (if length shapes=3 then
      checkpoint_first_set values \<inter> (if checkpoint_ground_spine N Z S (shapes!2) then UNIV else {})
      else UNIV)
    else (UNIV::unit set))"

lemma checkpoint_ground_algebra_mono:
 "checkpoint_algebra_mono (checkpoint_ground_algebra N Z S gin sin resume head tail)"
 unfolding checkpoint_algebra_mono_def checkpoint_ground_algebra_def
 using checkpoint_first_set_mono by (auto split: if_splits)

text \<open>The six rules are a generic sequential tree/spine recognizer schema.
Symbol names are parameters. Actual support rules must be checked as schema
instances or shown to have an unrestricted left-hand-side interpretation.\<close>

definition checkpoint_ground_rules :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f,nat) rule list" where
 "checkpoint_ground_rules N Z S gin gout sin sout resume head tail = [
   (Fun gin [Fun N [Var 0]], Fun resume [Fun sin [Var 0],Var 0]),
   (Fun resume [Fun sout [Var 0],Var 0], Fun gout [Fun N [Var 0]]),
   (Fun sin [Fun Z []], Fun sout [Fun Z []]),
   (Fun sin [Fun S [Var 0,Var 1]], Fun head [Fun gin [Var 0],Var 0,Var 1]),
   (Fun head [Fun gout [Var 0],Var 0,Var 1], Fun tail [Fun sin [Var 1],Var 0,Var 1]),
   (Fun tail [Fun sout [Var 1],Var 0,Var 1], Fun sout [Fun S [Var 0,Var 1]])]"

lemma checkpoint_ground_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [N,Z,S,gin,gout,sin,sout,resume,head,tail]"
 and constructors: "{N,Z,S}\<subseteq>C"
 and rule: "(l,r)\<in>set (checkpoint_ground_rules N Z S gin gout sin sout resume head tail)"
 shows "checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (r\<cdot>sigma)
   \<subseteq> checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (l\<cdot>sigma)"
 using rule distinct constructors
 by (auto simp: checkpoint_ground_rules_def checkpoint_ground_algebra_def split: if_splits)

lemma checkpoint_ground_unrestricted_lhs:
 assumes "f\<notin>{gin,sin,resume,head,tail}"
 shows "checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (Fun f ts)=UNIV"
 using assms by (simp add: checkpoint_ground_algebra_def)

lemma checkpoint_ground_success:
 fixes R :: "('f,'v) trs"
 assumes safe: "checkpoint_skeleton_safe C R"
 and distinct: "distinct [N,Z,S,gin,gout,sin,sout,resume,head,tail]"
 and rules: "\<And>l r sigma. (l,r)\<in>R \<Longrightarrow>
   checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (r\<cdot>sigma)
   \<subseteq> checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (l\<cdot>(sigma::'v \<Rightarrow> ('f,'v) term))"
 and success: "(Fun gin [input],Fun gout outputs)\<in>(rstep R)\<^sup>*"
 shows "checkpoint_ground_tree N Z S (checkpoint_skeleton C input)"
proof -
 have included: "checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (Fun gout outputs)
   \<subseteq> checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (Fun gin [input])"
  by (rule checkpoint_interpret_rsteps[OF safe checkpoint_ground_algebra_mono rules success])
 show ?thesis using included distinct by (auto simp: checkpoint_ground_algebra_def split: if_splits)
qed

definition check_checkpoint_ground_summary where
 "check_checkpoint_ground_summary C N Z S gin gout sin sout resume head tail rules witnesses =
  (distinct [N,Z,S,gin,gout,sin,sout,resume,head,tail] \<and> {N,Z,S}\<subseteq>C \<and>
   list_all (checkpoint_skeleton_safe_rule C) rules \<and>
   list_all2 (check_checkpoint_schema_rule {gin,sin,resume,head,tail}
     (checkpoint_ground_rules N Z S gin gout sin sout resume head tail)) rules witnesses)"

lemma checked_checkpoint_ground_success:
 fixes rules :: "('f,'v) rule list"
 assumes checked: "check_checkpoint_ground_summary C N Z S gin gout sin sout resume head tail rules witnesses"
 and success: "(Fun gin [input],Fun gout outputs)\<in>(rstep (set rules))\<^sup>*"
 shows "checkpoint_ground_tree N Z S (checkpoint_skeleton C input)"
proof -
 have safe: "checkpoint_skeleton_safe C (set rules)"
  and distinct: "distinct [N,Z,S,gin,gout,sin,sout,resume,head,tail]"
  and constructors: "{N,Z,S}\<subseteq>C"
  and table: "list_all2 (check_checkpoint_schema_rule {gin,sin,resume,head,tail}
   (checkpoint_ground_rules N Z S gin gout sin sout resume head tail)) rules witnesses"
  using checked by (auto simp: check_checkpoint_ground_summary_def checkpoint_skeleton_safe_list)
 show ?thesis
 proof (rule checkpoint_ground_success[OF safe distinct _ success])
  fix l r :: "('f,'v) term"
  fix sigma :: "'v \<Rightarrow> ('f,'v) term"
  assume member: "(l,r)\<in>set rules"
  show "checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (r\<cdot>sigma)
   \<subseteq> checkpoint_interpret C (checkpoint_ground_algebra N Z S gin sin resume head tail) (l\<cdot>sigma)"
   by (rule checkpoint_schema_table_sound[OF _ _ table member])
      (rule checkpoint_ground_rules_sound[OF distinct constructors], assumption,
       rule checkpoint_ground_unrestricted_lhs, assumption)
 qed
qed

lemma checkpoint_ground_shape_closed:
 "(checkpoint_ground_tree N Z S t \<longrightarrow> vars_term t={} \<and> funs_term t\<subseteq>{N,Z,S}) \<and>
  (checkpoint_ground_spine N Z S t \<longrightarrow> vars_term t={} \<and> funs_term t\<subseteq>{N,Z,S})"
proof (induct t)
 case (Var x) show ?case by simp
next
 case (Fun f ts)
 show ?case
 proof (cases ts)
  case Nil then show ?thesis by simp
 next
  case (Cons a rest)
  show ?thesis
  proof (cases rest)
   case Nil then show ?thesis using Fun Cons by auto
  next
   case (Cons b more)
   then show ?thesis using Fun \<open>ts=a#rest\<close> by (cases more) auto
  qed
 qed
qed

lemma checked_checkpoint_ground_leaf_free:
 assumes checked: "check_checkpoint_ground_summary C N Z S gin gout sin sout resume head tail rules witnesses"
 and success: "(Fun gin [input],Fun gout outputs)\<in>(rstep (set rules))\<^sup>*"
 and leaf: "L\<notin>{N,Z,S}"
 shows "vars_term (checkpoint_skeleton C input)={}"
   "L\<notin>funs_term (checkpoint_skeleton C input)"
 using checkpoint_ground_shape_closed[of N Z S "checkpoint_skeleton C input"]
   checked_checkpoint_ground_success[OF checked success] leaf by auto

lemma checked_checkpoint_ground_constructor_value:
 assumes checked: "check_checkpoint_ground_summary C N Z S gin gout sin sout resume head tail rules witnesses"
 and success: "(Fun gin [input],Fun gout outputs)\<in>(rstep (set rules))\<^sup>*"
 shows "vars_term input={} \<and> funs_term input\<subseteq>{N,Z,S}"
proof -
 have shape: "checkpoint_ground_tree N Z S (checkpoint_skeleton C input)"
  by (rule checked_checkpoint_ground_success[OF checked success])
 have closed: "vars_term (checkpoint_skeleton C input)={}"
  and symbols: "funs_term (checkpoint_skeleton C input)\<subseteq>{N,Z,S}"
  using checkpoint_ground_shape_closed[of N Z S "checkpoint_skeleton C input"] shape by auto
 show ?thesis using checkpoint_closed_skeleton_exact[OF closed] symbols by auto
qed

ML \<open>
val checked = @{thms checkpoint_ground_algebra_mono checkpoint_ground_rules_sound
 checkpoint_ground_unrestricted_lhs checkpoint_ground_success checked_checkpoint_ground_success
 checkpoint_ground_shape_closed checked_checkpoint_ground_leaf_free checked_checkpoint_ground_constructor_value};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted residual ground summary" else ();
\<close>
end
