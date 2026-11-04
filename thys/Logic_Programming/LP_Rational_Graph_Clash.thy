theory LP_Rational_Graph_Clash
  imports LP_Rational_Graph_Match
begin

fun lp_rational_observe where
  "lp_rational_observe G i t [] = (if i<length G then Some (t,i) else None)"
| "lp_rational_observe G i t (k#ks) =
    (if i<length G then case (t,G!i) of
      (Fun f ts,LPRBranch g js) \<Rightarrow>
        if f=g \<and> length ts=length js \<and> k<length ts
        then lp_rational_observe G (js!k) (ts!k) ks else None
      | _ \<Rightarrow> None
    else None)"

lemma lp_rational_observe_sound:
  assumes observed: "lp_rational_observe G i t observation_path=Some (u,j)"
    and matched: "lp_ieval t eta=lp_rational_graph_value G rho i"
  shows "lp_ieval u eta=lp_rational_graph_value G rho j"
  using assms
proof (induction observation_path arbitrary: t i)
  case Nil then show ?case by (auto split: if_splits)
next
  case (Cons k ks)
  obtain f ts js where shape: "t=Fun f ts" and branch: "G!i=LPRBranch f js"
    and index: "i<length G" "k<length ts" and lengths: "length ts=length js"
    and tail: "lp_rational_observe G (js!k) (ts!k) ks=Some (u,j)"
    using Cons.prems(1) by (cases t; cases "G!i") (auto split: if_splits)
  have evaluated_value: "lp_rational_graph_value G rho i=LPIFun f (map (lp_rational_graph_value G rho) js)"
    by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model index(1) branch])
  have lists: "map (\<lambda>t. lp_ieval t eta) ts=map (lp_rational_graph_value G rho) js"
    using Cons.prems(2) by (simp add: shape evaluated_value)
  have child: "lp_ieval (ts!k) eta=lp_rational_graph_value G rho (js!k)"
    using arg_cong[OF lists, of "\<lambda>xs. xs!k"] index(2) lengths by simp
  show ?case by (rule Cons.IH[OF tail child])
qed

datatype lp_rational_clash = LPRConstructorClash "nat list"
  | LPRRepeatedVariableClash "nat list" "nat list"

fun lp_rational_head_clash where
  "lp_rational_head_clash fuel G i h (LPRConstructorClash observation_path) =
    (case lp_rational_observe G i h observation_path of
      Some (Fun f ts,j) \<Rightarrow> j<length G \<and> (case G!j of
        LPRBranch g js \<Rightarrow> f\<noteq>g \<or> length ts\<noteq>length js | _ \<Rightarrow> False)
      | _ \<Rightarrow> False)"
| "lp_rational_head_clash fuel G i h (LPRRepeatedVariableClash left right) =
    (case (lp_rational_observe G i h left,lp_rational_observe G i h right) of
      (Some (Var x,j),Some (Var y,k)) \<Rightarrow> x=y \<and> lp_rational_distinct fuel G j k
      | _ \<Rightarrow> False)"

lemma lp_rational_head_clash_sound:
  assumes checked: "lp_rational_head_clash fuel G i h evidence"
  shows "lp_ieval h eta\<noteq>lp_rational_graph_value G rho i"
proof
  assume matched: "lp_ieval h eta=lp_rational_graph_value G rho i"
  show False
  proof (cases evidence)
    case (LPRConstructorClash observation_path)
    obtain sub j where observed: "lp_rational_observe G i h observation_path=Some (sub,j)"
      using checked LPRConstructorClash by (cases "lp_rational_observe G i h observation_path") auto
    obtain f ts where sub: "sub=Fun f ts"
      using checked observed LPRConstructorClash by (cases sub) auto
    obtain g js where branch: "G!j=LPRBranch g js"
      using checked observed sub LPRConstructorClash by (cases "G!j") auto
    have obs: "lp_rational_observe G i h observation_path=Some (Fun f ts,j)"
      using observed sub by simp
    have index: "j<length G" and different: "f\<noteq>g \<or> length ts\<noteq>length js"
      using checked obs branch LPRConstructorClash by simp_all
    have equal: "lp_ieval (Fun f ts) eta=lp_rational_graph_value G rho j"
      by (rule lp_rational_observe_sound[OF obs matched])
    have evaluated_value: "lp_rational_graph_value G rho j=LPIFun g (map (lp_rational_graph_value G rho) js)"
      by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model index branch])
    show False using equal different by (simp add: evaluated_value; metis length_map)
  next
    case (LPRRepeatedVariableClash left right)
    obtain u j where lo: "lp_rational_observe G i h left=Some (u,j)"
      using checked LPRRepeatedVariableClash
      by (cases "lp_rational_observe G i h left") auto
    obtain x where ux: "u=Var x"
      using checked lo LPRRepeatedVariableClash by (cases u) auto
    obtain v k where ro: "lp_rational_observe G i h right=Some (v,k)"
      using checked lo ux LPRRepeatedVariableClash
      by (cases "lp_rational_observe G i h right") auto
    have vx: "v=Var x" and different: "lp_rational_distinct fuel G j k"
      using checked lo ro ux LPRRepeatedVariableClash by (cases v; auto)+
    have left: "lp_rational_observe G i h left=Some (Var x,j)"
      and right: "lp_rational_observe G i h right=Some (Var x,k)"
      using lo ro ux vx by simp_all
    have a: "eta x=lp_rational_graph_value G rho j"
      using lp_rational_observe_sound[OF left matched] by simp
    have b: "eta x=lp_rational_graph_value G rho k"
      using lp_rational_observe_sound[OF right matched] by simp
    show False using a b lp_rational_distinct_sound[OF different, of rho] by simp
  qed
qed

lemma lp_rational_head_clash_no_unifier:
  fixes rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lp_rational_graph_closed G" "i<length G"
    "lp_rational_head_clash fuel G i h evidence"
  shows "\<not>(\<exists>(sigma :: string \<Rightarrow> ('f,string) lp_iterm) eta. lp_isubst (lp_rational_graph_value G rho i) sigma=lp_ieval h eta)"
  using lp_rational_closed_value_subst[OF assms(1,2)] lp_rational_head_clash_sound[OF assms(3)] by metis

ML \<open>
val checked = [@{thm lp_rational_head_clash_no_unifier}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational clash dependency" else ();
\<close>
end
