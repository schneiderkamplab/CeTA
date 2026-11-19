theory DP_Checkpoint_Acquisition
 imports DP_Checkpoint_Transport
begin

fun checkpoint_call_shape where
 "checkpoint_call_shape f n (Fun g xs) = (f=g \<and> length xs=n)"
| "checkpoint_call_shape f n (Var x) = False"

fun check_checkpoint_acquisition where
 "check_checkpoint_acquisition U i gin n gout m (l,Fun f ss) (Fun g ts,r) =
  (f\<in>U \<and> f=g \<and> length ss=length ts \<and> i<length ss \<and>
   checkpoint_call_shape gin n (ss!i) \<and> checkpoint_call_shape gout m (ts!i))"
| "check_checkpoint_acquisition U i gin n gout m before after = False"

text \<open>This check binds a successful-prefix observation to an actual
support derivation between original pair instances. It cannot establish that
such a connection exists or discharge a summary's domain conditions.\<close>
lemma checked_checkpoint_acquisition:
 fixes support :: "('f,'v) rule list"
 and sigma tau :: "'w \<Rightarrow> ('f,'v) term"
 assumes control: "check_checkpoint_control U K h pairs support"
 and checked: "check_checkpoint_acquisition U i gin n gout m before after"
 and connection: "(snd before\<cdot>sigma,fst after\<cdot>tau)\<in>(rstep (set support))\<^sup>*"
 shows "\<exists>xs ys. args (snd before)!i=Fun gin xs \<and> args (fst after)!i=Fun gout ys \<and>
 length xs=n \<and> length ys=m \<and>
 (Fun gin (map (\<lambda>t. t\<cdot>sigma) xs),Fun gout (map (\<lambda>t. t\<cdot>tau) ys))\<in>(rstep (set support))\<^sup>*"
proof -
 obtain bl br where b: "before=(bl,br)" by (cases before) auto
 obtain al ar where a: "after=(al,ar)" by (cases after) auto
 obtain l f ss ts r where before: "before=(l,Fun f ss)" and after: "after=(Fun f ts,r)"
 and root: "f\<in>U" and lengths: "length ss=length ts" and index: "i<length ss"
 and input: "checkpoint_call_shape gin n (ss!i)" and outgoing: "checkpoint_call_shape gout m (ts!i)"
  using checked unfolding b a by (cases br; cases al; auto)
 obtain xs where xs: "ss!i=Fun gin xs" and n: "length xs=n"
  using input by (cases "ss!i") auto
 obtain ys where ys: "ts!i=Fun gout ys" and m: "length ys=m"
  using outgoing by (cases "ts!i") auto
 have arguments: "list_all2 (\<lambda>s t. (s,t)\<in>(rstep (set support))\<^sup>*)
  (map (\<lambda>t. t\<cdot>sigma) ss) (map (\<lambda>t. t\<cdot>tau) ts)"
  by (rule checked_checkpoint_argument_transport[OF control root]) (use connection in \<open>simp add: before after\<close>)
 have success: "(Fun gin (map (\<lambda>t. t\<cdot>sigma) xs),Fun gout (map (\<lambda>t. t\<cdot>tau) ys))\<in>(rstep (set support))\<^sup>*"
  using arguments index lengths xs ys by (auto simp: list_all2_conv_all_nth)
 show ?thesis by (rule exI[of _ xs], rule exI[of _ ys]) (use xs ys n m success in \<open>simp add: before after\<close>)
qed

lemma checked_checkpoint_acquisition_step:
 fixes support :: "('f,'v) rule list"
 and sigma tau :: "'w \<Rightarrow> ('f,'v) term"
 assumes control: "check_checkpoint_control U K h pairs support"
 and checked: "check_checkpoint_acquisition U i gin n gout m before after"
 and connection: "(snd before\<cdot>sigma,fst after\<cdot>tau)\<in>(rstep (set support))\<^sup>*"
 shows "((args (snd before)!i)\<cdot>sigma,(args (fst after)!i)\<cdot>tau)\<in>(rstep (set support))\<^sup>*"
 using checked_checkpoint_acquisition[OF control checked connection] by auto

ML \<open>
val thms = @{thms checked_checkpoint_acquisition checked_checkpoint_acquisition_step};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted successful-prefix acquisition" else ();
\<close>
end
