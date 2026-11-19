theory DP_Checkpoint_Effect_Schema
 imports DP_Checkpoint_Ground
begin

text \<open>A sequential structural traversal: successful child results are
composed in their original order. E is the allowed output set, indexed by the
preserved parameter and input skeleton. The algebra tracks actual output slots.\<close>

definition checkpoint_effect_algebra where
 "checkpoint_effect_algebra E N S ein eout sin sout resume head tail f shapes values =
 (if f=ein \<or> f=sin then (if length shapes=2 then E (shapes!1) (shapes!0) else UNIV)
 else if f=eout \<or> f=sout then (if length shapes=3 then {shapes!1} else UNIV)
 else if f=resume then (if length shapes=3 then (\<lambda>x. Fun N [x]) ` checkpoint_first_set values else UNIV)
 else if f=head then (if length shapes=4 then
   {Fun S [x,y] |x y. x\<in>checkpoint_first_set values \<and> y\<in>E (shapes!3) (shapes!2)} else UNIV)
 else if f=tail then (if length shapes=5 then
   (\<lambda>y. Fun S [shapes!3,y]) ` checkpoint_first_set values else UNIV)
 else UNIV)"

lemma checkpoint_effect_algebra_mono:
 "checkpoint_algebra_mono (checkpoint_effect_algebra E N S ein eout sin sout resume head tail)"
 unfolding checkpoint_algebra_mono_def checkpoint_effect_algebra_def
 using checkpoint_first_set_mono by (auto split: if_splits; blast)

definition checkpoint_effect_rules ::
 "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f,nat) rule list" where
 "checkpoint_effect_rules L N Z S ein eout sin sout resume head tail = [
 (Fun ein [Fun L [],Var 0],Fun eout [Fun L [],Fun L [],Var 0]),
 (Fun ein [Fun N [Var 0],Var 1],Fun resume [Fun sin [Var 0,Var 1],Var 0,Var 1]),
 (Fun resume [Fun sout [Var 0,Var 1,Var 2],Var 0,Var 2],Fun eout [Fun N [Var 0],Fun N [Var 1],Var 2]),
 (Fun sin [Fun Z [],Var 0],Fun sout [Fun Z [],Fun Z [],Var 0]),
 (Fun sin [Fun S [Var 0,Var 1],Var 2],Fun head [Fun ein [Var 0,Var 2],Var 0,Var 1,Var 2]),
 (Fun head [Fun eout [Var 0,Var 1,Var 2],Var 0,Var 3,Var 2],Fun tail [Fun sin [Var 3,Var 2],Var 0,Var 3,Var 1,Var 2]),
 (Fun tail [Fun sout [Var 0,Var 1,Var 2],Var 3,Var 0,Var 4,Var 2],Fun sout [Fun S [Var 3,Var 0],Fun S [Var 4,Var 1],Var 2])]"

lemma checkpoint_effect_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,sin,sout,resume,head,tail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and leaf: "\<And>p. Fun L []\<in>E p (Fun L [])"
 and nil: "\<And>p. Fun Z []\<in>E p (Fun Z [])"
 and node: "\<And>p x y. y\<in>E p x \<Longrightarrow> Fun N [y]\<in>E p (Fun N [x])"
 and cons: "\<And>p x y xs ys. y\<in>E p x \<Longrightarrow> ys\<in>E p xs \<Longrightarrow> Fun S [y,ys]\<in>E p (Fun S [x,xs])"
 and rule: "(l,r)\<in>set (checkpoint_effect_rules L N Z S ein eout sin sout resume head tail)"
 shows "checkpoint_interpret C (checkpoint_effect_algebra E N S ein eout sin sout resume head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_effect_algebra E N S ein eout sin sout resume head tail) (l\<cdot>sigma)"
 using rule distinct constructors leaf nil node cons
 by (auto simp: checkpoint_effect_rules_def checkpoint_effect_algebra_def split: if_splits)

lemma checkpoint_effect_unrestricted_lhs:
 "f\<notin>{ein,eout,sin,sout,resume,head,tail} \<Longrightarrow>
 checkpoint_interpret C (checkpoint_effect_algebra E N S ein eout sin sout resume head tail) (Fun f ts)=UNIV"
 by (simp add: checkpoint_effect_algebra_def)

lemma checkpoint_effect_success:
 fixes rules :: "('f,'v) rule list"
 assumes safe: "checkpoint_skeleton_safe C (set rules)"
 and distinct: "distinct [ein,eout,sin,sout,resume,head,tail]"
 and rules: "\<And>l r (sigma::'v \<Rightarrow> ('f,'v) term). (l,r)\<in>set rules \<Longrightarrow>
 checkpoint_interpret C (checkpoint_effect_algebra E N S ein eout sin sout resume head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_effect_algebra E N S ein eout sin sout resume head tail) (l\<cdot>sigma)"
 and success: "(Fun ein [input,param],Fun eout [copied,result,returned_param])\<in>(rstep (set rules))\<^sup>*"
 shows "checkpoint_skeleton C result\<in>E (checkpoint_skeleton C param) (checkpoint_skeleton C input)"
 using checkpoint_interpret_rsteps[OF safe checkpoint_effect_algebra_mono rules success] distinct
 by (auto simp: checkpoint_effect_algebra_def)

ML \<open>
val thms = @{thms checkpoint_effect_algebra_mono checkpoint_effect_rules_sound
 checkpoint_effect_unrestricted_lhs checkpoint_effect_success};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted effect schemas" else ();
\<close>
end
