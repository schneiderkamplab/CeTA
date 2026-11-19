theory DP_Checkpoint_List_Domain
 imports DP_Checkpoint_Arguments
begin

fun checkpoint_list_domain where
 "checkpoint_list_domain N Z S (Fun f [Fun z []]) = (f=N \<and> z=Z)"
| "checkpoint_list_domain N Z S (Fun f [Fun g [x,Fun h [xs,Fun z []]]]) =
  (f=N \<and> g=S \<and> h=S \<and> z=Z \<and> checkpoint_list_domain N Z S xs)"
| "checkpoint_list_domain N Z S _ = False"

lemma checkpoint_list_domain_encoding:
 "checkpoint_list_domain N Z S (checkpoint_encoded_list N Z S xs)"
 by (induct xs) (auto simp: checkpoint_list_cons_def)

lemma checkpoint_list_domain_decode:
 "checkpoint_list_domain N Z S t \<Longrightarrow> \<exists>xs. t=checkpoint_encoded_list N Z S xs"
proof (induct N Z S t rule: checkpoint_list_domain.induct)
 case (1 N Z S f z)
 then show ?case by (auto intro: exI[of _ "[]"])
next
 case (2 N Z S f g x h xs z)
 then obtain ys where "xs=checkpoint_encoded_list N Z S ys" by auto
 with 2 show ?case by (auto simp: checkpoint_list_cons_def intro: exI[of _ "x#ys"])
qed auto

definition checkpoint_list_domain_algebra where
 "checkpoint_list_domain_algebra N Z S lin head tail f shapes values =
 (if f=lin then (if length shapes=2 then (if checkpoint_list_domain N Z S (shapes!0) then UNIV else {}) else UNIV)
 else if f=head then (if length shapes=4 then (if checkpoint_list_domain N Z S (shapes!2) then UNIV else {}) else UNIV)
 else if f=tail then checkpoint_first_set values else UNIV)"

lemma checkpoint_list_domain_algebra_mono:
 "checkpoint_algebra_mono (checkpoint_list_domain_algebra N Z S lin head tail)"
 unfolding checkpoint_algebra_mono_def checkpoint_list_domain_algebra_def
 using checkpoint_first_set_mono by (auto split: if_splits)

definition checkpoint_list_rules :: "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f,nat) rule list" where
 "checkpoint_list_rules N Z S lin lout head tail ein eout = [
 (Fun lin [Fun N [Fun Z []],Var 0],Fun lout [Fun N [Fun Z []],Fun N [Fun Z []],Var 0]),
 (Fun lin [checkpoint_list_cons N Z S (Var 0) (Var 1),Var 2],Fun head [Fun ein [Var 0,Var 2],Var 0,Var 1,Var 2]),
 (Fun head [Fun eout [Var 0,Var 1,Var 2],Var 0,Var 3,Var 2],Fun tail [Fun lin [Var 3,Var 2],Var 0,Var 3,Var 1,Var 2]),
 (Fun tail [Fun lout [Var 0,Var 1,Var 2],Var 3,Var 0,Var 4,Var 2],Fun lout [checkpoint_list_cons N Z S (Var 3) (Var 0),checkpoint_list_cons N Z S (Var 4) (Var 1),Var 2])]"

lemma checkpoint_list_domain_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes "distinct [N,Z,S,lin,lout,head,tail,ein,eout]" "{N,Z,S}\<subseteq>C"
 and "(l,r)\<in>set (checkpoint_list_rules N Z S lin lout head tail ein eout)"
 shows "checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (l\<cdot>sigma)"
 using assms by (auto simp: checkpoint_list_rules_def checkpoint_list_domain_algebra_def checkpoint_list_cons_def split: if_splits)

definition check_checkpoint_list_domain where
 "check_checkpoint_list_domain C N Z S lin lout head tail ein eout support witnesses =
 (distinct [N,Z,S,lin,lout,head,tail,ein,eout] \<and> {N,Z,S}\<subseteq>C \<and>
 list_all (checkpoint_skeleton_safe_rule C) support \<and>
 list_all2 (check_checkpoint_schema_rule {lin,head,tail}
   (checkpoint_list_rules N Z S lin lout head tail ein eout)) support witnesses)"

lemma checkpoint_list_domain_unrestricted:
 "f\<notin>{lin,head,tail} \<Longrightarrow>
 checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (Fun f ts)=UNIV"
 by (simp add: checkpoint_list_domain_algebra_def)

lemma checked_checkpoint_list_domain:
 fixes support :: "('f,'v) rule list"
 assumes checked: "check_checkpoint_list_domain C N Z S lin lout head tail ein eout support witnesses"
 and success: "(Fun lin [input,param],Fun lout outputs)\<in>(rstep (set support))\<^sup>*"
 shows "\<exists>xs. checkpoint_skeleton C input=checkpoint_encoded_list N Z S xs"
proof -
 have safe: "checkpoint_skeleton_safe C (set support)"
 and distinct: "distinct [N,Z,S,lin,lout,head,tail,ein,eout]"
 and constructors: "{N,Z,S}\<subseteq>C"
 and table: "list_all2 (check_checkpoint_schema_rule {lin,head,tail}
   (checkpoint_list_rules N Z S lin lout head tail ein eout)) support witnesses"
  using checked by (auto simp: check_checkpoint_list_domain_def checkpoint_skeleton_safe_list)
 have mono: "\<And>l r (sigma::'v \<Rightarrow> ('f,'v) term). (l,r)\<in>set support \<Longrightarrow>
 checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (l\<cdot>sigma)"
  by (rule checkpoint_schema_table_sound[OF _ _ table])
   (rule checkpoint_list_domain_rules_sound[OF distinct constructors], assumption,
    rule checkpoint_list_domain_unrestricted, assumption, assumption)
 have included: "checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (Fun lout outputs)
 \<subseteq> checkpoint_interpret C (checkpoint_list_domain_algebra N Z S lin head tail) (Fun lin [input,param])"
  by (rule checkpoint_interpret_rsteps[OF safe checkpoint_list_domain_algebra_mono mono success])
 have "checkpoint_list_domain N Z S (checkpoint_skeleton C input)"
  using included distinct by (auto simp: checkpoint_list_domain_algebra_def split: if_splits)
 then show ?thesis by (rule checkpoint_list_domain_decode)
qed

ML \<open>
val thms = @{thms checkpoint_list_domain_encoding checkpoint_list_domain_decode checkpoint_list_domain_algebra_mono checkpoint_list_domain_rules_sound checked_checkpoint_list_domain};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted list domain" else ();
\<close>
end
