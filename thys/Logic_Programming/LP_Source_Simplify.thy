theory LP_Source_Simplify
  imports LP_PiDP_Rule_Graph LP_Infinite_Resolution
begin

definition lp_dead_call where
  "lp_dead_call P a = (\<not> list_ex (\<lambda>c.
    lp_shapes_compatible (lp_tag id a) (lp_tag id (fst c))) P)"

definition lp_live_clauses where
  "lp_live_clauses P = filter (\<lambda>c. snd c = [] \<or>
    \<not> lp_dead_call P (hd (snd c))) P"

lemma lp_atom_common_shape:
  assumes "lp_atom_eval a \<rho> = lp_atom_eval b \<tau>"
  shows "lp_shapes_compatible (lp_tag id a) (lp_tag id b)"
proof -
  have eq: "lp_ieval (lp_tag id a) \<rho> = lp_ieval (lp_tag id b) \<tau>"
    using assms by (simp add: lp_tag_def lp_atom_eval_def split: prod.splits)
  have first: "lp_shape (lp_tag id a) (lp_ieval (lp_tag id a) \<rho>)"
    by (rule lp_shape_eval)
  have second: "lp_shape (lp_tag id b) (lp_ieval (lp_tag id a) \<rho>)"
    unfolding eq by (rule lp_shape_eval)
  show ?thesis by (rule lp_shape_compatible[OF first second])
qed

lemma lp_dead_call_stuck:
  fixes P :: "('f,'v) lp_clause list" and a :: "('f,'v) lp_atom"
    and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm"
  assumes dead: "lp_dead_call P a"
  shows "(lp_atom_eval a \<rho>#gs,t) \<notin> lp_ild P"
proof
  assume step: "(lp_atom_eval a \<rho>#gs,t) \<in> lp_ild P"
  obtain c and \<sigma> :: "'w\<Rightarrow>('f,'w) lp_iterm"
    and \<tau> :: "'v\<Rightarrow>('f,'w) lp_iterm" where c: "c<length P"
    and eq: "lp_iatom_subst (lp_atom_eval a \<rho>) \<sigma> = lp_atom_eval (fst (P!c)) \<tau>"
    using step by (cases rule: lp_ild.cases) auto
  have compat: "lp_shapes_compatible (lp_tag id a) (lp_tag id (fst (P!c)))"
    by (rule lp_atom_common_shape) (use eq in simp)
  show False using dead compat c unfolding lp_dead_call_def
    by (auto simp: list_ex_iff)
qed

lemma lp_live_step:
  assumes step: "(s,t)\<in>lp_ild P" and successor: "(t,u)\<in>lp_ild P"
  shows "(s,t)\<in>lp_ild (lp_live_clauses P)"
  using step successor
proof (cases rule: lp_ild.cases)
  case (resolve c a \<sigma> \<rho> gs)
  have live: "snd (P!c)=[] \<or> \<not>lp_dead_call P (hd (snd (P!c)))"
  proof (rule ccontr)
    assume bad: "\<not>(snd (P!c)=[] \<or> \<not>lp_dead_call P (hd (snd (P!c))))"
    obtain b bs where body: "snd (P!c)=b#bs"
      using bad by (cases "snd (P!c)") auto
    have dead: "lp_dead_call P b" using bad body by simp
    show False using lp_dead_call_stuck[OF dead] successor resolve body by auto
  qed
  have member: "P!c\<in>set (lp_live_clauses P)"
    using live resolve unfolding lp_live_clauses_def by auto
  obtain d where d: "d<length (lp_live_clauses P)"
    and same: "lp_live_clauses P!d=P!c" using member by (auto simp: in_set_conv_nth)
  have eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (lp_live_clauses P!d)) \<rho>"
    using resolve same by auto
  have edge: "(a#gs,map (\<lambda>b. lp_atom_eval b \<rho>) (snd (lp_live_clauses P!d)) @
    map (\<lambda>b. lp_iatom_subst b \<sigma>) gs)\<in>lp_ild (lp_live_clauses P)"
    by (rule lp_ild.resolve[OF d eq])
  show ?thesis using edge by (simp add: same resolve(1,2))
qed

theorem lp_live_clauses_sound:
  assumes sn: "SN_on (lp_ild (lp_live_clauses P)) X"
  shows "SN_on (lp_ild P) X"
proof (rule ccontr)
  assume "\<not>SN_on (lp_ild P) X"
  then obtain f where start: "f 0\<in>X"
    and steps: "\<And>i. (f i,f (Suc i))\<in>lp_ild P"
    unfolding SN_on_def by blast
  have live: "\<And>i. (f i,f (Suc i))\<in>lp_ild (lp_live_clauses P)"
    by (rule lp_live_step[OF steps steps])
  show False using sn start live unfolding SN_on_def by blast
qed

end
