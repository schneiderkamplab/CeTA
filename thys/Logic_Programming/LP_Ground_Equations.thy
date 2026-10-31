theory LP_Ground_Equations
  imports LP_Answer_Groundness
begin

text \<open>Equations retain sharing between an abstracted term and separately
carried fields. They propagate finite groundness justified by term structure
or previous observations; a cyclic equation does not supply finite groundness.
Runtime values use the existing infinitary terms.\<close>

fun lp_ground_equation_step where
  "lp_ground_equation_step [] G = G"
| "lp_ground_equation_step ((a,b)#equations) G =
    lp_ground_equation_step equations
      (G \<union> (if vars_term a \<subseteq> G then vars_term b else {}) \<union>
        (if vars_term b \<subseteq> G then vars_term a else {}))"

fun lp_ground_equation_closure where
  "lp_ground_equation_closure 0 equations G = G"
| "lp_ground_equation_closure (Suc fuel) equations G =
    lp_ground_equation_closure fuel equations (lp_ground_equation_step equations G)"

lemma lp_ground_equation_step_sound:
  assumes equations: "\<forall>(a,b)\<in>set equations. lp_ieval a eta=lp_ieval b eta"
    and known: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "\<forall>x\<in>lp_ground_equation_step equations G. lp_seg_ground (eta x)"
  using equations known
proof (induction equations arbitrary: G)
  case Nil
  then show ?case by simp
next
  case (Cons equation equations)
  obtain a b where pair: "equation=(a,b)" by (cases equation) auto
  have equal: "lp_ieval a eta=lp_ieval b eta" using Cons.prems by (auto simp: pair)
  have left: "vars_term a \<subseteq> G \<Longrightarrow> \<forall>x\<in>vars_term b. lp_seg_ground (eta x)"
    using equal Cons.prems(2) by (metis lp_seg_ground_eval subsetD)
  have right: "vars_term b \<subseteq> G \<Longrightarrow> \<forall>x\<in>vars_term a. lp_seg_ground (eta x)"
    using equal Cons.prems(2) by (metis lp_seg_ground_eval subsetD)
  have known: "\<forall>x\<in>G \<union> (if vars_term a \<subseteq> G then vars_term b else {}) \<union>
      (if vars_term b \<subseteq> G then vars_term a else {}). lp_seg_ground (eta x)"
    using Cons.prems(2) left right by auto
  have rest: "\<forall>(a,b)\<in>set equations. lp_ieval a eta=lp_ieval b eta"
    using Cons.prems by auto
  show ?case using Cons.IH[OF rest known] by (simp add: pair)
qed

lemma lp_ground_equation_closure_sound:
  assumes equations: "\<forall>(a,b)\<in>set equations. lp_ieval a eta=lp_ieval b eta"
    and known: "\<forall>x\<in>G. lp_seg_ground (eta x)"
  shows "\<forall>x\<in>lp_ground_equation_closure fuel equations G. lp_seg_ground (eta x)"
  using known
proof (induction fuel arbitrary: G)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  have step: "\<forall>x\<in>lp_ground_equation_step equations G. lp_seg_ground (eta x)"
    by (rule lp_ground_equation_step_sound[OF equations Suc.prems])
  show ?case using Suc.IH[OF step] by simp
qed

lemma lp_ground_equation_preserved:
  "lp_ieval a eta=lp_ieval b eta \<Longrightarrow>
    lp_ieval a (\<lambda>x. lp_isubst (eta x) sigma)=lp_ieval b (\<lambda>x. lp_isubst (eta x) sigma)"
  by (simp add: lp_ieval_subst[symmetric])

lemma lp_ground_equation_shared_field:
  "''field'' \<in> lp_ground_equation_closure 1
    [(Var ''whole'',Fun ''cell'' [Var ''field'',Fun ''nil'' []])] {''whole''}"
  by simp

lemma lp_ground_equation_cycle_does_not_seed_groundness:
  "lp_ground_equation_closure fuel [(Var ''x'',Fun ''f'' [Var ''x''])] {} = {}"
  by (induction fuel) simp_all

ML \<open>
val checked = [@{thm lp_ground_equation_closure_sound}, @{thm lp_ground_equation_preserved}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm lp_ground_check_model}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted ground-equation dependency" else ();
\<close>
end
