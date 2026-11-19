theory DP_Checkpoint_Route
 imports DP_Checkpoint_Transport
begin

fun checkpoint_route_next where
 "checkpoint_route_next U i value (l,Fun f ss) (Fun g ts,r) =
  (if f\<in>U \<and> f=g \<and> length ss=length ts \<and> i<length ss \<and> ss!i=value
   then Some (ts!i) else None)"
| "checkpoint_route_next U i value before after = None"

fun check_checkpoint_route where
 "check_checkpoint_route U pairs [] coordinates source target = False"
| "check_checkpoint_route U pairs [p] coordinates source target =
   (p<length pairs \<and> coordinates=[] \<and> source=target)"
| "check_checkpoint_route U pairs (p#q#path) [] source target = False"
| "check_checkpoint_route U pairs (p#q#path) (i#coordinates) source target =
   (p<length pairs \<and> q<length pairs \<and>
    (case checkpoint_route_next U i source (pairs!p) (pairs!q) of None \<Rightarrow> False
     | Some next \<Rightarrow> check_checkpoint_route U pairs (q#path) coordinates next target))"

definition checkpoint_route_connections where
 "checkpoint_route_connections R pairs path sigma =
 (\<forall>j. Suc j < length path \<longrightarrow>
  (snd (pairs!(path!j))\<cdot>sigma j,fst (pairs!(path!Suc j))\<cdot>sigma (Suc j))\<in>(rstep R)\<^sup>*)"

lemma checkpoint_route_next_sound:
 fixes sigma tau :: "'w \<Rightarrow> ('f,'v) term"
 assumes control: "check_checkpoint_control U K h pairs support"
 and safe: "checkpoint_skeleton_safe C (set support)"
 and checked: "checkpoint_route_next U i source before after=Some target"
 and connection: "(snd before\<cdot>sigma,fst after\<cdot>tau)\<in>(rstep (set support))\<^sup>*"
 shows "checkpoint_skeleton C (source\<cdot>sigma)=checkpoint_skeleton C (target\<cdot>tau)"
proof -
 obtain bl br where b: "before=(bl,br)" by (cases before) auto
 obtain al ar where a: "after=(al,ar)" by (cases after) auto
 obtain f ss ts where rhs: "br=Fun f ss" and lhs: "al=Fun f ts"
 and root: "f\<in>U" and len: "length ss=length ts" and index: "i<length ss"
 and source: "ss!i=source" and target: "ts!i=target"
  using checked unfolding b a by (cases br; cases al; auto split: if_splits)
 have arguments: "list_all2 (\<lambda>s t. (s,t)\<in>(rstep (set support))\<^sup>*)
  (map (\<lambda>t. t\<cdot>sigma) ss) (map (\<lambda>t. t\<cdot>tau) ts)"
  by (rule checked_checkpoint_argument_transport[OF control root])
   (use connection in \<open>simp add: b a rhs lhs\<close>)
 have step: "(source\<cdot>sigma,target\<cdot>tau)\<in>(rstep (set support))\<^sup>*"
  using arguments len index source target by (auto simp: list_all2_conv_all_nth)
 show ?thesis by (rule checkpoint_skeleton_rsteps[OF safe step])
qed

lemma checked_checkpoint_route_sound:
 fixes sigma :: "nat \<Rightarrow> 'v \<Rightarrow> ('f,'v) term"
 assumes control: "check_checkpoint_control U K h pairs support"
 and safe: "checkpoint_skeleton_safe C (set support)"
 and checked: "check_checkpoint_route U pairs path coordinates source target"
 and connections: "checkpoint_route_connections (set support) pairs path sigma"
 shows "checkpoint_skeleton C (source\<cdot>sigma 0)=
  checkpoint_skeleton C (target\<cdot>sigma (length path-1))"
 using checked connections
proof (induct path arbitrary: coordinates source sigma)
 case Nil then show ?case by simp
next
 case (Cons p rest)
 note IH = Cons.hyps
 show ?case
 proof (cases rest)
  case Nil then show ?thesis using Cons.prems by simp
 next
  case (Cons q path')
  obtain i coordinates' where coordinates: "coordinates=i#coordinates'"
   using \<open>check_checkpoint_route U pairs (p#rest) coordinates source target\<close>
   by (cases coordinates) (auto simp: Cons)
  obtain value_next where value_next: "checkpoint_route_next U i source (pairs!p) (pairs!q)=Some value_next"
  and remaining: "check_checkpoint_route U pairs (q#path') coordinates' value_next target"
   using \<open>check_checkpoint_route U pairs (p#rest) coordinates source target\<close>
   by (auto simp: Cons coordinates split: option.splits)
  have edge: "(snd (pairs!p)\<cdot>sigma 0,fst (pairs!q)\<cdot>sigma 1)\<in>(rstep (set support))\<^sup>*"
   using \<open>checkpoint_route_connections (set support) pairs (p#rest) sigma\<close>[unfolded checkpoint_route_connections_def, rule_format, of 0]
   by (simp add: Cons)
  have first: "checkpoint_skeleton C (source\<cdot>sigma 0)=checkpoint_skeleton C (value_next\<cdot>sigma 1)"
   by (rule checkpoint_route_next_sound[OF control safe value_next edge])
  have rest_connections: "checkpoint_route_connections (set support) pairs (q#path') (\<lambda>j. sigma (Suc j))"
   using \<open>checkpoint_route_connections (set support) pairs (p#rest) sigma\<close>
   unfolding checkpoint_route_connections_def Cons by auto
  have last: "checkpoint_skeleton C (value_next\<cdot>sigma 1)=checkpoint_skeleton C (target\<cdot>sigma (length (p#rest)-1))"
   using IH[of coordinates' value_next "\<lambda>j. sigma (Suc j)"] remaining rest_connections
   by (simp add: Cons)
  show ?thesis using first last by simp
 qed
qed

lemma checked_checkpoint_route_property:
 fixes sigma :: "nat \<Rightarrow> 'v \<Rightarrow> ('f,'v) term"
 assumes control: "check_checkpoint_control U K h pairs support"
 and safe: "checkpoint_skeleton_safe C (set support)"
 and checked: "check_checkpoint_route U pairs path coordinates source target"
 and connections: "checkpoint_route_connections (set support) pairs path sigma"
 and property: "P (checkpoint_skeleton C (source\<cdot>sigma 0))"
 shows "P (checkpoint_skeleton C (target\<cdot>sigma (length path-1)))"
 using checked_checkpoint_route_sound[OF control safe checked connections] property by simp

ML \<open>
val thms = @{thms checkpoint_route_next_sound checked_checkpoint_route_sound checked_checkpoint_route_property};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted coordinate route" else ();
\<close>
end
