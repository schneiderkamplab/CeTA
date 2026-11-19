theory DP_Checkpoint_Inference
 imports DP_Checkpoint_Derivation
begin

text \<open>Codes identify shared inference rules, not input pair numbers.
Return-interface membership is a separate checked-summary dependency. Witness
indices refer only to the current alternative's already established facts.\<close>
definition check_checkpoint_inference where
 "check_checkpoint_inference N Z S arg_interfaces ground_interfaces list_interfaces known witness dst_claim =
 (case witness of (tag,fs,ts,refs) \<Rightarrow>
  list_all (\<lambda>i. i<length known) refs \<and>
  (if (tag::nat)=0 then fs=[] \<and> ts=[] \<and> refs=[] \<and> check_checkpoint_fact_copy known dst_claim
   else if tag=1 then fs=[] \<and> length ts=2 \<and> length refs=1 \<and>
    check_checkpoint_fact_split N Z S (ts!0) (ts!1) (known!(refs!0)) dst_claim
   else if tag=2 then fs=[] \<and> length ts=2 \<and> length refs=1 \<and>
    check_checkpoint_fact_prefix (ts!0) (ts!1) (known!(refs!0)) dst_claim
   else if tag=3 then length fs=1 \<and> length ts=1 \<and> length refs=1 \<and>
    check_checkpoint_fact_arguments_start N (fs!0) (ts!0) (known!(refs!0)) dst_claim
   else if tag=4 then length fs=1 \<and> length ts=1 \<and> refs=[] \<and>
    check_checkpoint_fact_ground_start (fs!0) (ts!0) dst_claim
   else if tag=5 then length fs=1 \<and> length ts=3 \<and> length refs=2 \<and>
    check_checkpoint_fact_list_start (fs!0) (ts!0) (ts!1) (ts!2) (known!(refs!0)) (known!(refs!1)) dst_claim
   else if tag=6 then length fs=2 \<and> length ts=2 \<and> length refs=1 \<and>
    (fs!0,fs!1)\<in>set arg_interfaces \<and>
    check_checkpoint_fact_arguments_return (fs!0) (fs!1) (ts!0) (ts!1) (known!(refs!0)) dst_claim
   else if tag=7 then length fs=2 \<and> length ts=2 \<and> length refs=1 \<and>
    (fs!0,fs!1)\<in>set ground_interfaces \<and>
    check_checkpoint_fact_ground_return (fs!0) (fs!1) (ts!0) (ts!1) (known!(refs!0)) dst_claim
   else if tag=8 then length fs=2 \<and> length ts=4 \<and> length refs=1 \<and>
    (fs!0,fs!1)\<in>set list_interfaces \<and>
    check_checkpoint_fact_list_return (fs!0) (fs!1) (ts!0) (ts!1) (ts!2) (ts!3) (known!(refs!0)) dst_claim
   else False))"

lemma checked_checkpoint_inference:
 assumes constructors: "{N,Z,S}\<subseteq>C"
 and arguments: "\<And>f g copied result src dst. (f,g)\<in>set arg_interfaces \<Longrightarrow>
 check_checkpoint_fact_arguments_return f g copied result src dst \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma src \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma dst"
 and ground: "\<And>f g copied param src dst. (f,g)\<in>set ground_interfaces \<Longrightarrow>
 check_checkpoint_fact_ground_return f g copied param src dst \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma src \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma dst"
 and lists: "\<And>f g copied result param h src dst. (f,g)\<in>set list_interfaces \<Longrightarrow>
 check_checkpoint_fact_list_return f g copied result param h src dst \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma src \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma dst"
 and checked: "check_checkpoint_inference N Z S arg_interfaces ground_interfaces list_interfaces known witness dst_claim"
 and known: "list_all (checkpoint_fact_holds C L N Z S R old sigma) known"
 shows "checkpoint_fact_holds C L N Z S R old sigma dst_claim"
proof -
 obtain tag fs ts refs where witness: "witness=(tag,fs,ts,refs)" by (cases witness) auto
 have bounds: "list_all (\<lambda>i. i<length known) refs"
  using checked by (simp add: check_checkpoint_inference_def witness)
 have previous: "\<And>j. j<length refs \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma (known!(refs!j))"
  using bounds known by (simp add: list_all_length)
 have previous0: "0<length refs \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))"
 by (rule previous)
 have previous1: "1<length refs \<Longrightarrow> checkpoint_fact_holds C L N Z S R old sigma (known!(refs!1))"
 by (rule previous)
 have node: "N\<in>C" using constructors by auto
 consider (c0) "tag=0" | (c1) "tag=1" | (c2) "tag=2" | (c3) "tag=3" | (c4) "tag=4" | (c5) "tag=5" | (c6) "tag=6" | (c7) "tag=7" | (c8) "tag=8" | (other) "tag\<notin>{0,1,2,3,4,5,6,7,8}" by auto
 then show ?thesis
 proof cases
  case c0
  have selected: "check_checkpoint_fact_copy known dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c0)
  show ?thesis by (rule checked_checkpoint_fact_copy[OF selected known])
 next
  case c1
  have selected: "check_checkpoint_fact_split N Z S (ts!0) (ts!1) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c1)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c1)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  show ?thesis by (rule checked_checkpoint_fact_split[OF constructors selected current])
 next
  case c2
  have selected: "check_checkpoint_fact_prefix (ts!0) (ts!1) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c2)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c2)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  show ?thesis by (rule checked_checkpoint_fact_prefix[OF selected current])
 next
  case c3
  have selected: "check_checkpoint_fact_arguments_start N (fs!0) (ts!0) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c3)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c3)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  show ?thesis by (rule checked_checkpoint_fact_arguments_start[OF node selected current])
 next
  case c4
  have selected: "check_checkpoint_fact_ground_start (fs!0) (ts!0) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c4)
  show ?thesis by (rule checked_checkpoint_fact_ground_start[OF selected])
 next
  case c5
  have selected: "check_checkpoint_fact_list_start (fs!0) (ts!0) (ts!1) (ts!2) (known!(refs!0)) (known!(refs!1)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c5)
  have width: "length refs=2" using checked by (simp add: check_checkpoint_inference_def witness c5)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  have current1: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!1))" by (rule previous) (simp add: width)
  show ?thesis by (rule checked_checkpoint_fact_list_start[OF selected current current1])
 next
  case c6
  have selected: "check_checkpoint_fact_arguments_return (fs!0) (fs!1) (ts!0) (ts!1) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c6)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c6)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  have interface: "(fs!0,fs!1)\<in>set arg_interfaces" using checked by (simp add: check_checkpoint_inference_def witness c6)
  show ?thesis by (rule arguments[OF interface selected current])
 next
  case c7
  have selected: "check_checkpoint_fact_ground_return (fs!0) (fs!1) (ts!0) (ts!1) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c7)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c7)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  have interface: "(fs!0,fs!1)\<in>set ground_interfaces" using checked by (simp add: check_checkpoint_inference_def witness c7)
  show ?thesis by (rule ground[OF interface selected current])
 next
  case c8
  have selected: "check_checkpoint_fact_list_return (fs!0) (fs!1) (ts!0) (ts!1) (ts!2) (ts!3) (known!(refs!0)) dst_claim" using checked by (simp add: check_checkpoint_inference_def witness c8)
  have width: "length refs=1" using checked by (simp add: check_checkpoint_inference_def witness c8)
  have current: "checkpoint_fact_holds C L N Z S R old sigma (known!(refs!0))" by (rule previous) (simp add: width)
  have interface: "(fs!0,fs!1)\<in>set list_interfaces" using checked by (simp add: check_checkpoint_inference_def witness c8)
  show ?thesis by (rule lists[OF interface selected current])
 next
  case other
  show ?thesis using checked other by (auto simp: check_checkpoint_inference_def witness)
 qed
qed

ML \<open>
val thms = @{thms checked_checkpoint_inference};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted inference checker" else ();
\<close>
end
