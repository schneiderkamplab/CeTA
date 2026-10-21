theory LP_SEG_Expansion
  imports LP_SEG_Finite_Measure
begin

lemma lp_seg_expansion_step:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes fresh: "lp_short_goals k gs"
    and bounded: "\<forall>x\<in>set G. length x<k"
    and finite: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and ready: "\<And>c. c<length P \<Longrightarrow> \<exists>result. lp_source_branch fuel k gs (P!c)=Some result"
    and step: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs,hs)\<in>lp_ild P"
  obtains c child \<eta> where "c<length P"
    "lp_source_branch fuel k gs (P!c)=Some (Some child)"
    "map (\<lambda>a. lp_atom_eval a \<eta>) child=hs"
    "\<forall>x\<in>set G. \<eta> x=\<rho> x"
proof -
  obtain a rest where gs: "gs=a#rest"
    using step by (cases gs) (auto elim: lp_ild.cases)
  obtain c \<tau> \<nu> where c: "c<length P"
    and eq: "lp_iatom_subst (lp_atom_eval a \<rho>) \<tau> = lp_atom_eval (fst (P!c)) \<nu>"
    and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<tau>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
    using lp_ild_cons_cases[of "lp_atom_eval a \<rho>"
      "map (\<lambda>b. lp_atom_eval b \<rho>) rest" hs P] step
    unfolding gs list.map by blast
  let ?old = "\<lambda>x. lp_isubst (\<rho> x) \<tau>"
  let ?env = "\<lambda>x. if length x<k then ?old x else \<nu> (drop k x)"
  have old: "map (\<lambda>b. lp_atom_eval b ?env) gs = map (\<lambda>b. lp_atom_eval b ?old) gs"
    by (rule lp_old_goals_eval[OF fresh])
  have head: "lp_atom_eval a ?env = lp_atom_eval (lp_rename_atom k (fst (P!c))) ?env"
    using old eq lp_fresh_atom_eval[of k "fst (P!c)" ?old \<nu>]
    by (auto simp only: gs list.map list.inject lp_atom_eval_subst)
  have equations: "lp_equations [(lp_tag id a,lp_tag id (lp_rename_atom k (fst (P!c))))] ?env"
    using arg_cong[OF head, of "lp_itag id"] by (simp add: lp_equations_def lp_itag_eval)
  obtain result where check: "lp_source_branch fuel k gs (P!c)=Some result"
    using ready[OF c] by blast
  have normalized: "lp_normalize_goals fuel
    [(lp_tag id a,lp_tag id (lp_rename_atom k (fst (P!c))))]
    (map (lp_rename_atom k) (snd (P!c)) @ rest) = Some result"
    using check by (simp only: lp_source_branch_def gs list.case)
  obtain child where result: "result=Some child"
    and projected: "map (\<lambda>b. lp_atom_eval b ?env) child =
      map (\<lambda>b. lp_atom_eval b ?env) (map (lp_rename_atom k) (snd (P!c)) @ rest)"
    using lp_normalize_goals_sound[OF normalized equations] by blast
  have target: "map (\<lambda>b. lp_atom_eval b ?env) child = hs"
    using projected old lp_fresh_atom_eval[of k _ ?old \<nu>] by (auto simp: gs hs o_def)
  have unchanged: "\<forall>x\<in>set G. ?env x=\<rho> x"
    using bounded finite by (simp add: lp_seg_ground_subst)
  show thesis by (rule that[OF c _ target unchanged]) (simp add: check result)
qed

text \<open>A trailing symbolic marker records the input measure while the
  normalization algorithm propagates equations through the entire state. It is
  never executed as an LP call and needs no reserved source predicate.\<close>

theorem lp_seg_measured_expansion:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes fresh: "lp_short_goals k (gs@[(anchor,map Var G)])"
    and bounded: "\<forall>x\<in>set G. length x<k"
    and finite: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and ready: "\<And>c. c<length P \<Longrightarrow> \<exists>result.
      lp_source_branch fuel k (gs@[(anchor,map Var G)]) (P!c)=Some result"
    and step: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs,hs)\<in>lp_ild P"
  obtains c child inputs \<eta> where "c<length P"
    "lp_source_branch fuel k (gs@[(anchor,map Var G)]) (P!c)=Some (Some (child@[(anchor,inputs)]))"
    "map (\<lambda>a. lp_atom_eval a \<eta>) child=hs"
    "map (\<lambda>t. lp_ieval t \<eta>) inputs=map \<rho> G"
    "\<forall>x\<in>\<Union>(vars_term ` set inputs). lp_seg_ground (\<eta> x)"
proof -
  obtain a rest where gs: "gs=a#rest" using step by (cases gs) (auto elim: lp_ild.cases)
  obtain c \<tau> \<nu> where c: "c<length P"
    and eq: "lp_iatom_subst (lp_atom_eval a \<rho>) \<tau> = lp_atom_eval (fst (P!c)) \<nu>"
    and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<tau>) (map (\<lambda>b. lp_atom_eval b \<rho>) rest)"
    using lp_ild_cons_cases[of "lp_atom_eval a \<rho>"
      "map (\<lambda>b. lp_atom_eval b \<rho>) rest" hs P] step
    unfolding gs list.map by blast
  have fixed: "map (\<lambda>x. lp_isubst (\<rho> x) \<tau>) G=map \<rho> G"
    using finite by (auto intro!: map_cong simp: lp_seg_ground_subst)
  have augmented: "(map (\<lambda>a. lp_atom_eval a \<rho>) (gs@[(anchor,map Var G)]),
    hs@[(anchor,map \<rho> G)])\<in>lp_ild P"
    using lp_ild.resolve[OF c eq, of "map (\<lambda>b. lp_atom_eval b \<rho>) rest @ [(anchor,map \<rho> G)]"]
    by (simp add: gs hs lp_atom_eval_def lp_iatom_subst_def o_def fixed)
  obtain ci flat \<eta> where ci: "ci<length P"
    and branch: "lp_source_branch fuel k (gs@[(anchor,map Var G)]) (P!ci)=Some (Some flat)"
    and projected: "map (\<lambda>a. lp_atom_eval a \<eta>) flat=hs@[(anchor,map \<rho> G)]"
    by (rule lp_seg_expansion_step[OF fresh bounded finite ready augmented]) blast
  have nonempty: "flat\<noteq>[]" using projected by auto
  obtain child last_atom where flat: "flat=child@[last_atom]"
    using nonempty by (metis append_butlast_last_id)
  obtain p inputs where last_atom: "last_atom=(p,inputs)" by (cases last_atom) auto
  have child: "map (\<lambda>a. lp_atom_eval a \<eta>) child=hs"
    and pred: "p=anchor"
    and inputs: "map (\<lambda>t. lp_ieval t \<eta>) inputs=map \<rho> G"
    using projected by (simp_all add: flat last_atom lp_atom_eval_def)
  have ground: "\<forall>x\<in>\<Union>(vars_term ` set inputs). lp_seg_ground (\<eta> x)"
    using arg_cong[OF inputs, of "list_all lp_seg_ground"] finite
    by (auto simp: list_all_iff lp_seg_ground_eval)
  show thesis by (rule that[OF ci _ child inputs ground])
    (use branch in \<open>simp add: flat last_atom pred\<close>)
qed

end
