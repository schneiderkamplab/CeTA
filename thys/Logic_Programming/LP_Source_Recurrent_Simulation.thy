theory LP_Source_Recurrent_Simulation
  imports LP_Source_Barrier_Pumping LP_Cut_Ground_Recurrence
begin

text \<open>A nontermination child needs an underapproximate simulation into
actual source execution. The representation includes the complete source state,
so saved alternatives and pending continuations cannot be silently discarded.
Every abstract step must make nonempty source progress. This shared contract
uses the existing LP-with-cut state and transition relation.\<close>

lemma lp_source_recurrent_simulation:
  fixes R :: "'s rel" and S :: "'a rel"
  assumes entry: "a\<in>X" and represented: "rep a s"
    and recurrent: "\<And>x. x\<in>X \<Longrightarrow> \<exists>y\<in>X. (x,y)\<in>S"
    and simulate: "\<And>x y u. x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>
      (x,y)\<in>S \<Longrightarrow> rep x u \<Longrightarrow>
      \<exists>v. rep y v \<and> (u,v)\<in>R\<^sup>+"
  shows "\<not> SN_on R {s}"
proof -
  let ?Y = "{u. \<exists>x\<in>X. rep x u}"
  have start: "s\<in>?Y" using entry represented by blast
  have successors: "\<forall>u\<in>?Y. \<exists>v\<in>?Y. (u,v)\<in>R\<^sup>+"
  proof (intro ballI)
    fix u assume "u\<in>?Y"
    then obtain x where x: "x\<in>X" "rep x u" by blast
    obtain y where y: "y\<in>X" "(x,y)\<in>S"
      using recurrent[OF x(1)] by blast
    obtain v where v: "rep y v" "(u,v)\<in>R\<^sup>+"
      using simulate[OF x(1) y x(2)] by blast
    show "\<exists>v\<in>?Y. (u,v)\<in>R\<^sup>+" using y v by blast
  qed
  show ?thesis using lower_set_imp_not_SN_on[OF start successors] SN_on_trancl by blast
qed

lemma lp_source_progress_simulation_SN:
  assumes source_sn: "SN_on R {s}" and represented: "rep a s"
    and simulate: "\<And>x y u. (x,y)\<in>S \<Longrightarrow> rep x u \<Longrightarrow>
      \<exists>v. rep y v \<and> (u,v)\<in>R\<^sup>+"
  shows "SN_on S {a}"
proof -
  have progress_sn: "SN_on (R\<^sup>+) {s}" using source_sn SN_on_trancl by blast
  have all: "\<forall>a. rep a s \<longrightarrow> SN_on S {a}"
  proof (rule SN_on_induct[OF progress_sn singletonI], intro allI impI)
    fix u a
    assume ih: "\<And>v. (u,v)\<in>R\<^sup>+ \<Longrightarrow> \<forall>a. rep a v \<longrightarrow> SN_on S {a}"
      and rep: "rep a u"
    show "SN_on S {a}"
    proof (rule step_reflects_SN_on)
      fix b assume edge: "(a,b)\<in>S"
      obtain v where v: "rep b v" "(u,v)\<in>R\<^sup>+"
        using simulate[OF edge rep] by blast
      show "SN_on S {b}" using ih[OF v(2)] v(1) by blast
    qed
  qed
  show ?thesis using all represented by blast
qed

corollary lp_source_nontermination_simulation:
  assumes child: "\<not> SN_on S {a}" and represented: "rep a s"
    and simulate: "\<And>x y u. (x,y)\<in>S \<Longrightarrow> rep x u \<Longrightarrow>
      \<exists>v. rep y v \<and> (u,v)\<in>R\<^sup>+"
  shows "\<not> SN_on R {s}"
proof
  assume sn: "SN_on R {s}"
  have "SN_on S {a}" by (rule lp_source_progress_simulation_SN[where R=R and S=S and rep=rep, OF sn represented simulate])
  then show False using child by blast
qed

text \<open>Reflexive simulation would be unsound: the abstract self-loop
below can stutter forever while the source has no step.\<close>
lemma lp_source_stuttering_is_not_progress:
  "SN ({} :: unit rel) \<and> ((),())\<in>({} :: unit rel)\<^sup>* \<and>
    ((),())\<notin>({} :: unit rel)\<^sup>+"
  by simp

ML \<open>
val checked = [@{thm lp_source_recurrent_simulation},
  @{thm lp_source_nontermination_simulation},
  @{thm lp_source_stuttering_is_not_progress}];
val _ = List.app (fn th => if Thm_Deps.has_skip_proof [th]
  then error "Unproved source recurrent simulation" else ()) checked;
val _ = writeln "SOURCE_RECURRENT_SIMULATION_VERIFIED";
\<close>
end
