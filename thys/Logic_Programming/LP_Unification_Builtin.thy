theory LP_Unification_Builtin
  imports LP_Infinite_Resolution LP_Leftmost_Resolution
begin

text \<open>The fresh reflexive fact implements an explicit unification goal.
  Both sides use the same substitution on the remaining goals. This is not
  syntactic equality testing and does not introduce an occurs check.\<close>

lemma lp_unification_fact:
  "((q,[s,t])#gs,hs)\<in>lp_ld [((q,[Var x,Var x]),[])] \<longleftrightarrow>
    (\<exists>\<sigma>. s\<cdot>\<sigma>=t\<cdot>\<sigma> \<and> hs=map (\<lambda>a. lp_atom_subst a \<sigma>) gs)"
proof
  assume "((q,[s,t])#gs,hs)\<in>lp_ld [((q,[Var x,Var x]),[])]"
  then show "\<exists>\<sigma>. s\<cdot>\<sigma>=t\<cdot>\<sigma> \<and> hs=map (\<lambda>a. lp_atom_subst a \<sigma>) gs"
    by cases (force simp: lp_atom_subst_def)
next
  assume "\<exists>\<sigma>. s\<cdot>\<sigma>=t\<cdot>\<sigma> \<and> hs=map (\<lambda>a. lp_atom_subst a \<sigma>) gs"
  then obtain \<sigma> where eq: "s\<cdot>\<sigma>=t\<cdot>\<sigma>" and hs: "hs=map (\<lambda>a. lp_atom_subst a \<sigma>) gs" by blast
  show "((q,[s,t])#gs,hs)\<in>lp_ld [((q,[Var x,Var x]),[])]"
    using lp_ld.resolve[of 0 "[((q,[Var x,Var x]),[])]" "(q,[s,t])" \<sigma> "\<lambda>_. s\<cdot>\<sigma>" gs]
    by (simp add: lp_atom_subst_def eq hs)
qed

lemma lp_infinite_unification_fact:
  "((q,[s,t])#gs,hs)\<in>lp_ild [((q,[Var x,Var x]),[])] \<longleftrightarrow>
    (\<exists>\<sigma>. lp_isubst s \<sigma>=lp_isubst t \<sigma> \<and> hs=map (\<lambda>a. lp_iatom_subst a \<sigma>) gs)"
proof
  assume "((q,[s,t])#gs,hs)\<in>lp_ild [((q,[Var x,Var x]),[])]"
  then show "\<exists>\<sigma>. lp_isubst s \<sigma>=lp_isubst t \<sigma> \<and> hs=map (\<lambda>a. lp_iatom_subst a \<sigma>) gs"
    by cases (force simp: lp_iatom_subst_def lp_atom_eval_def)
next
  assume "\<exists>\<sigma>. lp_isubst s \<sigma>=lp_isubst t \<sigma> \<and> hs=map (\<lambda>a. lp_iatom_subst a \<sigma>) gs"
  then obtain \<sigma> where eq: "lp_isubst s \<sigma>=lp_isubst t \<sigma>" and hs: "hs=map (\<lambda>a. lp_iatom_subst a \<sigma>) gs" by blast
  show "((q,[s,t])#gs,hs)\<in>lp_ild [((q,[Var x,Var x]),[])]"
    using lp_ild.resolve[of 0 "[((q,[Var x,Var x]),[])]" "(q,[s,t])" \<sigma> "\<lambda>_. lp_isubst s \<sigma>" gs]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def eq hs)
qed

end
