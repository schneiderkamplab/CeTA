theory DP_Checkpoint_Effect_Composition
 imports DP_Checkpoint_Leaf_Summary DP_Checkpoint_List_Domain DP_Checkpoint_List_Effect DP_Checkpoint_Rank_View
begin

text \<open>Both the element helper and the enclosing list traversal share one
interpretation. Every producer of either output interface is checked.\<close>

definition checkpoint_composed_algebra where
 "checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail f shapes child_sets =
 (if f=lin then (if length shapes=2 then E (shapes!1) (shapes!0) else UNIV)
 else if f=lout then (if length shapes=3 then {shapes!1} else UNIV)
 else if f=lhead then (if length shapes=4 then
  {checkpoint_list_cons N Z S x y |x y. x\<in>checkpoint_first_set child_sets \<and> y\<in>E (shapes!3) (shapes!2)} else UNIV)
 else if f=ltail then (if length shapes=5 then
  checkpoint_list_cons N Z S (shapes!3) ` checkpoint_first_set child_sets else UNIV)
 else checkpoint_effect_algebra E N S ein eout spine_in sout resume head tail f shapes child_sets)"

lemma checkpoint_composed_algebra_mono:
 fixes E :: "('f,unit) term \<Rightarrow> ('f,unit) term \<Rightarrow> ('f,unit) term set"
 and ein :: 'f
 shows "checkpoint_algebra_mono (checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail)"
 unfolding checkpoint_algebra_mono_def
proof (intro allI impI)
 fix f :: 'f
 fix shapes :: "('f,unit) term list"
 fix xs ys :: "('f,unit) term set list"
 assume related: "list_all2 (\<subseteq>) xs ys"
 have first: "checkpoint_first_set xs\<subseteq>checkpoint_first_set ys"
  by (rule checkpoint_first_set_mono[OF related])
 have core: "checkpoint_effect_algebra E N S ein eout spine_in sout resume head tail f shapes xs
  \<subseteq>checkpoint_effect_algebra E N S ein eout spine_in sout resume head tail f shapes ys"
  by (rule checkpoint_effect_algebra_mono[unfolded checkpoint_algebra_mono_def, rule_format]; rule related)
 show "checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail f shapes xs
  \<subseteq>checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail f shapes ys"
  using first core by (auto simp: checkpoint_composed_algebra_def split: if_splits)
qed

lemma checkpoint_effect_local_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 and A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> ('f,unit) term set list \<Rightarrow> ('f,unit) term set"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and leaf: "\<And>p. Fun L []\<in>E p (Fun L [])"
 and nil: "\<And>p. Fun Z []\<in>E p (Fun Z [])"
 and node: "\<And>p x y. y\<in>E p x \<Longrightarrow> Fun N [y]\<in>E p (Fun N [x])"
 and cons: "\<And>p x y xs ys. y\<in>E p x \<Longrightarrow> ys\<in>E p xs \<Longrightarrow> Fun S [y,ys]\<in>E p (Fun S [x,xs])"
 and agrees: "\<And>f. f\<in>{ein,eout,spine_in,sout,resume,head,tail} \<Longrightarrow>
 A f=checkpoint_effect_algebra E N S ein eout spine_in sout resume head tail f"
 and rule: "(l,r)\<in>set (checkpoint_effect_rules L N Z S ein eout spine_in sout resume head tail)"
 shows "checkpoint_interpret C A (r\<cdot>sigma)\<subseteq>checkpoint_interpret C A (l\<cdot>sigma)"
 using rule distinct constructors leaf nil node cons
 by (auto simp: checkpoint_effect_rules_def agrees checkpoint_effect_algebra_def split: if_splits)

lemma checkpoint_composed_helper_agrees:
 assumes "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail]"
 and "f\<in>{ein,eout,spine_in,sout,resume,head,tail}"
 shows "checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail f =
 checkpoint_effect_algebra E N S ein eout spine_in sout resume head tail f"
 using assms by (auto simp: checkpoint_composed_algebra_def fun_eq_iff)

lemma checkpoint_composed_list_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail]"
 and constructors: "{N,Z,S}\<subseteq>C"
 and nil: "\<And>p. Fun N [Fun Z []]\<in>E p (Fun N [Fun Z []])"
 and cons: "\<And>p x y xs ys. y\<in>E p x \<Longrightarrow> ys\<in>E p xs \<Longrightarrow>
 checkpoint_list_cons N Z S y ys\<in>E p (checkpoint_list_cons N Z S x xs)"
 and rule: "(l,r)\<in>set (checkpoint_list_rules N Z S lin lout lhead ltail ein eout)"
 shows "checkpoint_interpret C (checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (r\<cdot>sigma)
 \<subseteq>checkpoint_interpret C (checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (l\<cdot>sigma)"
 using rule distinct constructors nil cons
 by (auto simp: checkpoint_list_rules_def checkpoint_composed_algebra_def checkpoint_effect_algebra_def checkpoint_list_cons_def split: if_splits)

lemma checkpoint_leaf_outputs_list_nil:
 "N\<noteq>L \<Longrightarrow> Z\<noteq>L \<Longrightarrow> Fun N [Fun Z []]\<in>checkpoint_leaf_outputs L p (Fun N [Fun Z []])"
 by (rule checkpoint_leaf_outputs_constructor; simp; rule checkpoint_leaf_outputs_constructor; simp)

lemma checkpoint_leaf_outputs_list_cons:
 assumes "N\<noteq>L" "Z\<noteq>L" "S\<noteq>L"
 and "y\<in>checkpoint_leaf_outputs L p x" "ys\<in>checkpoint_leaf_outputs L p xs"
 shows "checkpoint_list_cons N Z S y ys\<in>checkpoint_leaf_outputs L p (checkpoint_list_cons N Z S x xs)"
 unfolding checkpoint_list_cons_def
 by (rule checkpoint_leaf_outputs_constructor; use assms in simp;
   rule checkpoint_leaf_outputs_constructor; use assms in simp;
   rule checkpoint_leaf_outputs_constructor; use assms in simp;
   rule checkpoint_leaf_outputs_constructor; use assms in simp)

ML \<open>
val thms = @{thms checkpoint_composed_algebra_mono checkpoint_effect_local_sound checkpoint_composed_helper_agrees
 checkpoint_composed_list_rules_sound checkpoint_leaf_outputs_list_nil checkpoint_leaf_outputs_list_cons};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted summary composition" else ();
\<close>
end
