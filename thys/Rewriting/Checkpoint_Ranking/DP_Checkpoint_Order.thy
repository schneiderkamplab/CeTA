theory DP_Checkpoint_Order
 imports DP_Checkpoint_Skeleton "Abstract-Rewriting.Abstract_Rewriting"
begin

definition checkpoint_internal where
 "checkpoint_internal R K = {(s,t)\<in>R. s\<notin>K}"

definition checkpoint_returns where
 "checkpoint_returns R K = {(s,t). s\<in>K \<and> t\<in>K \<and>
    (s,t)\<in>R O (checkpoint_internal R K)\<^sup>*}"

text \<open>A first return consists of one step out of a checkpoint followed
by zero or more steps whose sources are not checkpoints. It retains all choices
and exits. Termination of the internal relation covers arbitrary starting states.\<close>

lemma checkpoint_internal_boundary_SN:
 assumes internal: "SN (checkpoint_internal R K)"
 and boundary: "\<And>z. z\<in>K \<Longrightarrow> (x,z)\<in>(checkpoint_internal R K)\<^sup>* \<Longrightarrow> SN_on R {z}"
 shows "SN_on R {x}"
proof -
 have general: "(\<forall>z\<in>K. (y,z)\<in>(checkpoint_internal R K)\<^sup>* \<longrightarrow> SN_on R {z}) \<longrightarrow> SN_on R {y}" for y
 proof (induct y rule: SN_induct[OF internal])
  case (1 y)
  show ?case
  proof
   assume bound: "\<forall>z\<in>K. (y,z)\<in>(checkpoint_internal R K)\<^sup>* \<longrightarrow> SN_on R {z}"
   show "SN_on R {y}"
   proof (cases "y\<in>K")
    case True then show ?thesis using bound by auto
   next
    case False
    show ?thesis
    proof (rule step_reflects_SN_on)
     fix z assume yz: "(y,z)\<in>R"
     have edge: "(y,z)\<in>checkpoint_internal R K"
      using yz False unfolding checkpoint_internal_def by simp
     have bound_z: "\<forall>w\<in>K. (z,w)\<in>(checkpoint_internal R K)\<^sup>* \<longrightarrow> SN_on R {w}"
      using bound edge by (meson r_into_rtrancl rtrancl_trans)
     show "SN_on R {z}" using 1[OF edge] bound_z by blast
    qed
   qed
  qed
 qed
 show ?thesis using general[of x] boundary by blast
qed

lemma checkpoint_termination:
 assumes internal: "SN (checkpoint_internal R K)"
 and returns: "SN (checkpoint_returns R K)"
 shows "SN R"
proof -
 have checkpoints: "x\<in>K \<longrightarrow> SN_on R {x}" for x
 proof (induct x rule: SN_induct[OF returns])
  case (1 x)
  show ?case
  proof
   assume x: "x\<in>K"
   show "SN_on R {x}"
   proof (rule step_reflects_SN_on)
    fix y assume xy: "(x,y)\<in>R"
    show "SN_on R {y}"
    proof (rule checkpoint_internal_boundary_SN[OF internal])
     fix z assume z: "z\<in>K"
      and yz: "(y,z)\<in>(checkpoint_internal R K)\<^sup>*"
     have ret: "(x,z)\<in>checkpoint_returns R K"
      using x z xy yz unfolding checkpoint_returns_def by auto
     show "SN_on R {z}" using 1[OF ret] z by blast
    qed
   qed
  qed
 qed
 show ?thesis
  by (rule SN_I, rule checkpoint_internal_boundary_SN[OF internal]) (use checkpoints in blast)
qed

lemma checkpoint_rank_SN:
 assumes order: "wf W"
 and descent: "\<And>s t. (s,t)\<in>R \<Longrightarrow> (rank t,rank s)\<in>W"
 shows "SN R"
proof -
 have "R\<inverse> \<subseteq> inv_image W rank" using descent by (auto simp: inv_image_def)
 then have "wf (R\<inverse>)" by (rule wf_subset[OF wf_inv_image[OF order]])
 then show ?thesis by (simp add: SN_iff_wf)
qed

lemma checkpoint_ranking:
 assumes order: "wf W"
 and control: "\<And>s t. (s,t)\<in>R \<Longrightarrow> s\<notin>K \<Longrightarrow> height t < (height s::nat)"
 and descent: "\<And>s t. (s,t)\<in>checkpoint_returns R K \<Longrightarrow> (rank t,rank s)\<in>W"
 shows "SN R"
proof (rule checkpoint_termination)
 show "SN (checkpoint_internal R K)"
  by (rule checkpoint_rank_SN[OF wf_less_than, where rank=height])
     (use control in \<open>auto simp: checkpoint_internal_def\<close>)
 show "SN (checkpoint_returns R K)" by (rule checkpoint_rank_SN[OF order descent])
qed

ML \<open>
val checked = @{thms checkpoint_internal_boundary_SN checkpoint_termination checkpoint_rank_SN checkpoint_ranking};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checkpoint termination proof" else ();
\<close>
end
