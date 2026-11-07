theory LP_Prolog_Stable_Control_Composition
 imports LP_Prolog_Stable_Constrained_Valuation
begin

text \<open>Eliminating a control location preserves termination only when
there are no transitions between eliminated states. Every incoming/outgoing
pair must be represented in the retained relation. This statement concerns
existing transition relations and introduces no additional source semantics.\<close>

definition lpp_control_composition where
  "lpp_control_composition R A = {(x,z). x\<in>A \<and> z\<in>A \<and>
    ((x,z)\<in>R \<or> (\<exists>y. y\<notin>A \<and> (x,y)\<in>R \<and> (y,z)\<in>R))}"

lemma lpp_control_composition_SN:
  assumes child: "SN S"
    and coverage: "lpp_control_composition R A \<subseteq> S"
    and no_loop: "\<And>x y. x\<notin>A \<Longrightarrow> y\<notin>A \<Longrightarrow> (x,y)\<notin>R"
  shows "SN R"
proof -
  have retained: "x\<in>A \<longrightarrow> SN_on R {x}" for x
  proof (rule SN_on_induct[OF child UNIV_I], intro impI)
    fix x assume ih: "\<And>z. (x,z)\<in>S \<Longrightarrow> z\<in>A \<longrightarrow> SN_on R {z}"
      and keep: "x\<in>A"
    show "SN_on R {x}"
    proof (rule step_reflects_SN_on)
      fix y assume edge: "(x,y)\<in>R"
      show "SN_on R {y}"
      proof (cases "y\<in>A")
        case True
        have "(x,y)\<in>S" using coverage keep True edge
          by (auto simp: lpp_control_composition_def)
        then show ?thesis using ih True by blast
      next
        case False
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix z assume edge_next: "(y,z)\<in>R"
          have kept: "z\<in>A" using no_loop False edge_next by blast
          have "(x,z)\<in>S" using coverage keep kept False edge edge_next
            by (auto simp: lpp_control_composition_def)
          then show "SN_on R {z}" using ih kept by blast
        qed
      qed
    qed
  qed
  have all_states: "SN_on R {x}" for x
  proof (cases "x\<in>A")
    case True then show ?thesis using retained by blast
  next
    case False
    show ?thesis by (rule step_reflects_SN_on)
      (use no_loop False retained in blast)
  qed
  show ?thesis using all_states unfolding SN_on_def by blast
qed

ML \<open>
val checked = [@{thm lpp_control_composition_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control composition dependency" else ();
\<close>
end
