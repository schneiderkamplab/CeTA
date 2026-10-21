theory LP_Source_Loop
  imports LP_Infinite_Resolution LP_Leftmost_Resolution
begin

lemma lp_serial_not_SN:
  assumes member: "x\<in>X" and serial: "\<And>s. s\<in>X \<Longrightarrow> \<exists>t\<in>X. (s,t)\<in>R"
  shows "\<not>SN_on R {x}"
proof
  assume sn: "SN_on R {x}"
  have outside: "x\<notin>X"
  proof (rule SN_on_induct[OF sn singletonI])
    fix s assume ih: "\<And>t. (s,t)\<in>R \<Longrightarrow> t\<notin>X"
    show "s\<notin>X" using serial[of s] ih by blast
  qed
  show False using member outside by contradiction
qed

text \<open>A selected recursive call which is an instance of its clause head
  admits an infinite leftmost derivation. Subsequent body goals accumulate on
  the right and are never selected. This proves source nontermination, not
  nontermination of a transformed TRS.\<close>

theorem lp_head_instance_loop:
  fixes P :: "('f,'v) lp_clause list" and \<rho> \<tau> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and body: "snd (P!c)=b#bs"
    and inst: "b=lp_atom_subst (fst (P!c)) \<tau>"
  shows "\<not>SN_on (lp_ld P) {[lp_atom_subst (fst (P!c)) \<rho>]}"
proof -
  let ?h = "fst (P!c)"
  let ?X = "{gs :: ('f,'v) lp_atom list. \<exists>\<sigma> tail. gs=lp_atom_subst ?h \<sigma>#tail}"
  show ?thesis
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[lp_atom_subst ?h \<rho>]\<in>?X" by blast
  next
    fix gs assume "gs\<in>?X"
    then obtain \<sigma> tail where gs: "gs=lp_atom_subst ?h \<sigma>#tail" by blast
    let ?next = "map (\<lambda>a. lp_atom_subst a \<sigma>) (snd (P!c)) @ tail"
    have step: "(gs,?next)\<in>lp_ld P"
      using lp_ld.resolve[OF c, of "lp_atom_subst ?h \<sigma>" Var \<sigma> tail]
      by (simp add: gs)
    have member: "?next\<in>?X" by (auto simp: body inst)
    show "\<exists>t\<in>?X. (gs,t)\<in>lp_ld P" using step member by blast
  qed
qed

lemma lp_atom_eval_finite_subst:
  "lp_atom_eval (lp_atom_subst a \<tau>) \<rho> =
    lp_atom_eval a (\<lambda>x. lp_ieval (\<tau> x) \<rho>)"
proof -
  have eval: "\<And>t. lp_ieval (t\<cdot>\<tau>) \<rho> = lp_ieval t (\<lambda>x. lp_ieval (\<tau> x) \<rho>)"
  proof -
    fix t show "lp_ieval (t\<cdot>\<tau>) \<rho> = lp_ieval t (\<lambda>x. lp_ieval (\<tau> x) \<rho>)"
      by (induct t) (auto intro!: map_cong)
  qed
  show ?thesis by (simp add: lp_atom_eval_def lp_atom_subst_def map_map o_def eval)
qed

theorem lp_infinite_head_instance_loop:
  fixes P :: "('f,'v) lp_clause list" and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm"
    and \<tau> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and body: "snd (P!c)=b#bs"
    and inst: "b=lp_atom_subst (fst (P!c)) \<tau>"
  shows "\<not>SN_on (lp_ild P) {[lp_atom_eval (fst (P!c)) \<rho>]}"
proof -
  let ?h = "fst (P!c)"
  let ?X = "{gs :: ('f,'w) lp_iatom list. \<exists>\<sigma> tail. gs=lp_atom_eval ?h \<sigma>#tail}"
  show ?thesis
  proof (rule lp_serial_not_SN[where X="?X"])
    show "[lp_atom_eval ?h \<rho>]\<in>?X" by blast
  next
    fix gs assume "gs\<in>?X"
    then obtain \<sigma> tail where gs: "gs=lp_atom_eval ?h \<sigma>#tail" by blast
    let ?next = "map (\<lambda>a. lp_atom_eval a \<sigma>) (snd (P!c)) @ tail"
    have step: "(gs,?next)\<in>lp_ild P"
      using lp_ild.resolve[OF c, of "lp_atom_eval ?h \<sigma>" LPIVar \<sigma> tail]
      by (simp add: gs)
    have member: "?next\<in>?X"
      by (auto simp: body inst lp_atom_eval_finite_subst)
    show "\<exists>t\<in>?X. (gs,t)\<in>lp_ild P" using step member by blast
  qed
qed

end
