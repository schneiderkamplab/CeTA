(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Finite_Semantic_Labeling
  imports CSR_Checker_Extensions.CSR_Semantic_Labeling
    CSR_Checker_Extensions.CSR_Hybrid_Recursive_Subterm
begin

fun csr_semantic_sharp_bridge :: "('f,'l) lab \<Rightarrow> ('f,'l) lab"
where
  "csr_semantic_sharp_bridge (Labelings.Lab (Sharp f) l) =
    Sharp (Labelings.Lab f l)"
| "csr_semantic_sharp_bridge (Sharp (Labelings.Lab f l)) =
    Labelings.Lab (Sharp f) l"
| "csr_semantic_sharp_bridge f = f"

lemma csr_semantic_sharp_bridge_involution [simp]:
  "csr_semantic_sharp_bridge (csr_semantic_sharp_bridge f) = f"
proof (cases f)
  case (Lab f l)
  then show ?thesis by (cases f, auto)
next
  case (Sharp f)
  then show ?thesis by (cases f, auto)
qed auto

lemma csr_semantic_sharp_bridge_inj:
  "inj csr_semantic_sharp_bridge"
  unfolding inj_on_def
  by (metis csr_semantic_sharp_bridge_involution)

lemma csr_semantic_sharp_bridge_commute_initial [simp]:
  "csr_semantic_sharp_bridge
      (csr_lab_sharp (Labelings.Lab (UnLab f) l)) =
    Sharp (csr_semantic_sharp_bridge (Labelings.Lab (UnLab f) l))"
  by simp

lemma csr_semantic_sharp_bridge_label_SharpD:
  assumes "csr_semantic_sharp_bridge (label g n x) = Sharp f"
  obtains h where "g = Sharp h"
  using assms by (cases x; cases g; auto)

lemma label_arity_irrelevant:
  "label g n x = label g m x"
  by (cases x, auto)

lemma csr_csdp_step_cond_lift_term:
  assumes image: "map_funs_term U s' = s"
    and marked: "\<And>f us. s = Fun (shp f) us \<Longrightarrow>
      \<exists>f' us'. s' = Fun (shp' f') us' \<and> U f' = f"
    and cond: "csdp_step_cond shp \<mu> p s"
  shows "csdp_step_cond shp' (map_mu U \<mu>) p s'"
  unfolding csdp_step_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume eqposs: "p = p1 @ j # p2 \<and> p \<in> poss s'"
  then have eq: "p = p1 @ j # p2" and pposs': "p \<in> poss s'"
    by auto
  have pposs: "p \<in> poss s"
    using pposs' image by (metis poss_map_funs_term_csr)
  from cond[unfolded csdp_step_cond_def, rule_format,
      OF conjI[OF eq pposs]]
  obtain g us where sub: "s |_ p1 = Fun g us"
    and active: "case p1 of
        [] \<Rightarrow> \<exists>f. g = shp f \<and> j \<in> \<mu> (f,length us)
      | _ \<Rightarrow> j \<in> \<mu> (g,length us)" by blast
  show "\<exists>g' us'. s' |_ p1 = Fun g' us' \<and>
      (case p1 of [] \<Rightarrow> \<exists>f'. g' = shp' f' \<and>
          j \<in> map_mu U \<mu> (f',length us')
        | _ \<Rightarrow> j \<in> map_mu U \<mu> (g',length us'))"
  proof (cases p1)
    case Nil
    from active[simplified Nil] obtain f where g: "g = shp f"
      and j: "j \<in> \<mu> (f,length us)" by auto
    have s: "s = Fun (shp f) us" using sub g unfolding Nil by simp
    from marked[OF s] obtain f' us' where s': "s' = Fun (shp' f') us'"
      and Uf: "U f' = f" by auto
    from arg_cong[OF image, of args] s s'
    have args: "map (map_funs_term U) us' = us" by simp
    from arg_cong[OF args, of length]
    have len: "length us' = length us" by simp
    show ?thesis unfolding Nil s'
      apply (rule exI[where x="shp' f'"])
      apply (rule exI[where x=us'])
      apply (rule conjI)
       apply simp
      apply (simp only: list.case)
      apply (rule exI[where x=f'])
      using j Uf len by (simp add: map_mu_def)
  next
    case (Cons k ks)
    have p1poss': "p1 \<in> poss s'"
      using pposs' eq poss_append_poss by blast
    have mapped_sub: "map_funs_term U (s' |_ p1) = Fun g us"
      using image sub
        subt_at_map_funs_term_csr[of p1 s' U, OF p1poss'] by simp
    then obtain g' us' where sub': "s' |_ p1 = Fun g' us'"
      and Ug: "U g' = g" and len: "length us' = length us"
      by (cases "s' |_ p1", auto)
    have j: "j \<in> \<mu> (g,length us)"
      using active unfolding Cons by simp
    show ?thesis unfolding Cons
      apply (rule exI[where x=g'])
      apply (rule exI[where x=us'])
      apply (rule conjI)
       using sub' apply (simp only: Cons)
      apply (simp only: list.case)
      using j Ug len by (simp add: map_mu_def)
  qed
qed

theorem csr_finite_dpp_nonminimal_imp_finite_min_csr_dpp:
  fixes P R :: "('f::{showl,compare_order},'v) trs"
  assumes fin: "finite_dpp (False,False,P,{}, {},{},R)"
  shows "finite_min_csr_dpp shp \<mu> P R"
proof -
  have target: "SN_rel (rrstep P) (rstep R)"
    using fin unfolding finite_dpp_iff_SN_rel CS_rrstep_conv by simp
  let ?M = "csr_min_pair_step shp \<mu> P R"
  let ?S = "csdp_step shp \<mu> R"
  have strict: "\<And>s t. (s,t) \<in> ?M \<Longrightarrow>
      (s,t) \<in> (rrstep P \<union> rstep R)\<^sup>* O rrstep P O
        (rrstep P \<union> rstep R)\<^sup>*"
    unfolding csr_min_pair_step_def by auto
  have weak: "\<And>s t. (s,t) \<in> ?S \<Longrightarrow>
      (s,t) \<in> (rrstep P \<union> rstep R)\<^sup>*"
  proof -
    fix s t
    assume "(s,t) \<in> ?S"
    then obtain p lr \<sigma> where
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
      unfolding csdp_step_def csdp_step_p_def by blast
    then have "(s,t) \<in> rstep R" by (rule rstep_r_p_s_imp_rstep)
    then show "(s,t) \<in> (rrstep P \<union> rstep R)\<^sup>*" by auto
  qed
  from SN_rel_map[where R="?M" and Rw="?S" and R'="rrstep P"
      and Rw'="rstep R" and f=id, OF target strict weak]
  show ?thesis unfolding finite_min_csr_dpp_def by simp
qed

locale csr_csr_sl_interpr_same = sl_interpr_same C c I cge lge L LC LD LS
  for C :: "'c set"
  and c :: 'c
  and I :: "('f::{showl,compare_order},'c)inter"
  and cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and L :: "('f,'c,'l)label"
  and LC :: "('f,'l,'f)lcompose"
  and LD :: "('f,'f,'l)ldecompose"
  and LS :: "('f,'l)labels"

context csr_csr_sl_interpr_same
begin

lemma csr_csdp_step_cond_LAB:
  assumes sharp: "\<And>f n l. shp' (LC f n l) = LC (shp f) n l"
    and cond: "csdp_step_cond shp \<mu> p s"
  shows "csdp_step_cond shp' (map_mu UNLAB \<mu>) p (LAB s)"
proof (rule csdp_step_cond_lift_term[where U=UNLAB and s=s
      and shp=shp])
  show "map_funs_term UNLAB (LAB s) = s" by (rule UNLAB_lab)
next
  fix f us
  assume s: "s = Fun (shp f) us"
  let ?clts = "map (eval_lab I L LC default_ass) us"
  show "\<exists>f' us'. LAB s = Fun (shp' f') us' \<and> UNLAB f' = f"
    apply (rule exI[where x="LC f (length us)
        (L (shp f) (map fst ?clts))"])
    apply (rule exI[where x="map snd ?clts"])
    using s sharp[of f "length us"
        "L (shp f) (map fst ?clts)"] LD_LC
    by (simp add: Let_def)
next
  show "csdp_step_cond shp \<mu> p s" by (rule cond)
qed

end

definition csr_finite_lab_mu ::
  "(('f,label_type) lab) muL \<Rightarrow> nat \<Rightarrow>
   (('f,label_type) lab) muL"
where
  "csr_finite_lab_mu \<mu> c = concat (map (\<lambda>((f,n),is).
     map (\<lambda>cs. ((Lab f cs,n),is))
       (enum_vectors_nat [0..<Suc c] n)) \<mu>)"

lemma csr_map_of_lab_vectors:
  assumes mem: "cs \<in> set css"
  shows "map_of (map (\<lambda>xs. ((Lab f xs,n),vals)) css)
    (Lab f cs,n) = Some vals"
  using mem
proof (induct css)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases "cs = x", auto)
qed

lemma csr_map_add_none:
  assumes "n k = None"
  shows "(m ++ n) k = m k"
  using assms by (cases "m k", auto simp: map_add_None map_add_Some_iff)

lemma csr_map_of_finite_lab_mu:
  assumes cs: "cs \<in> set (enum_vectors_nat [0..<Suc c] n)"
  shows "map_of (csr_finite_lab_mu \<mu> c) (Lab f cs,n) =
    map_of \<mu> (f,n)"
  using assms
proof (induct \<mu>)
  case Nil
  then show ?case by (simp add: csr_finite_lab_mu_def)
next
  case (Cons a rest)
  obtain fn vals where a: "a = (fn,vals)" by (cases a)
  obtain g m where fn: "fn = (g,m)" by (cases fn)
  show ?case
  proof (cases "f = g \<and> n = m")
    case True
    have hit: "map_of (map (\<lambda>xs. ((Lab g xs,m),vals))
        (enum_vectors_nat [0..<Suc c] m)) (Lab g cs,m) = Some vals"
      apply (rule csr_map_of_lab_vectors)
      using True cs by simp
    with True show ?thesis
      unfolding csr_finite_lab_mu_def a fn
      by (simp add: map_of_append)
  next
    case False
    have absent: "(Lab f cs,n) \<notin>
      set (map fst (map (\<lambda>xs. ((Lab g xs,m),vals))
        (enum_vectors_nat [0..<Suc c] m)))"
      using False by auto
    have miss: "map_of (map (\<lambda>xs. ((Lab g xs,m),vals))
        (enum_vectors_nat [0..<Suc c] m)) (Lab f cs,n) = None"
      unfolding map_of_eq_None_iff
      using absent by auto
    have expand: "csr_finite_lab_mu (a # rest) c =
        map (\<lambda>xs. ((Lab g xs,m),vals))
          (enum_vectors_nat [0..<Suc c] m) @
        csr_finite_lab_mu rest c"
      unfolding csr_finite_lab_mu_def a fn by simp
    have lhs: "map_of (csr_finite_lab_mu (a # rest) c)
        (Lab f cs,n) = map_of (csr_finite_lab_mu rest c) (Lab f cs,n)"
      unfolding expand map_of_append
      apply (rule csr_map_add_none)
      apply (rule miss)
      done
    have rhs: "map_of (a # rest) (f,n) = map_of rest (f,n)"
      unfolding a fn using False by auto
    show ?thesis using lhs rhs Cons.hyps cs by simp
  qed
qed

lemma csr_mu_of_finite_lab_mu:
  assumes cs: "set cs \<subseteq> set [0..<Suc c]" "length cs = n"
  shows "mu_of (csr_finite_lab_mu \<mu> c) (Lab f cs,n) =
    mu_of \<mu> (f,n)"
  using csr_map_of_finite_lab_mu[of cs c n \<mu> f]
    assms unfolding mu_of_def enum_vectors_nat by simp

lemma csr_csdp_step_cond_lift_term_on:
  assumes image: "map_funs_term U s' = s"
    and marked: "\<And>f us. s = Fun (shp f) us \<Longrightarrow>
      \<exists>f' us'. s' = Fun (shp' f') us' \<and> U f' = f"
    and root_active: "\<And>f' us'. s' = Fun (shp' f') us' \<Longrightarrow>
      \<mu>' (f',length us') = \<mu> (U f',length us')"
    and inner_active: "\<And>q g' us'. q \<in> poss s' \<Longrightarrow> q \<noteq> [] \<Longrightarrow>
      s' |_ q = Fun g' us' \<Longrightarrow>
      \<mu>' (g',length us') = \<mu> (U g',length us')"
    and cond: "csdp_step_cond shp \<mu> p s"
  shows "csdp_step_cond shp' \<mu>' p s'"
  unfolding csdp_step_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume eqposs: "p = p1 @ j # p2 \<and> p \<in> poss s'"
  then have eq: "p = p1 @ j # p2" and pposs': "p \<in> poss s'"
    by auto
  have pposs: "p \<in> poss s"
    using pposs' image by (metis poss_map_funs_term_csr)
  from cond[unfolded csdp_step_cond_def, rule_format,
      OF conjI[OF eq pposs]]
  obtain g us where sub: "s |_ p1 = Fun g us"
    and active: "case p1 of
        [] \<Rightarrow> \<exists>f. g = shp f \<and> j \<in> \<mu> (f,length us)
      | _ \<Rightarrow> j \<in> \<mu> (g,length us)" by blast
  show "\<exists>g' us'. s' |_ p1 = Fun g' us' \<and>
      (case p1 of [] \<Rightarrow> \<exists>f'. g' = shp' f' \<and>
          j \<in> \<mu>' (f',length us')
        | _ \<Rightarrow> j \<in> \<mu>' (g',length us'))"
  proof (cases p1)
    case Nil
    from active[simplified Nil] obtain f where g: "g = shp f"
      and j: "j \<in> \<mu> (f,length us)" by auto
    have s: "s = Fun (shp f) us" using sub g unfolding Nil by simp
    from marked[OF s] obtain f' us' where s': "s' = Fun (shp' f') us'"
      and Uf: "U f' = f" by auto
    from arg_cong[OF image, of args] s s'
    have args: "map (map_funs_term U) us' = us" by simp
    from arg_cong[OF args, of length]
    have len: "length us' = length us" by simp
    have act: "\<mu>' (f',length us') = \<mu> (f,length us)"
      using root_active[OF s'] Uf len by simp
    show ?thesis unfolding Nil s'
      using j act by auto
  next
    case (Cons k ks)
    have p1poss': "p1 \<in> poss s'"
      using pposs' eq poss_append_poss by blast
    have mapped_sub: "map_funs_term U (s' |_ p1) = Fun g us"
      using image sub
        subt_at_map_funs_term_csr[of p1 s' U, OF p1poss'] by simp
    then obtain g' us' where sub': "s' |_ p1 = Fun g' us'"
      and Ug: "U g' = g" and len: "length us' = length us"
      by (cases "s' |_ p1", auto)
    have j: "j \<in> \<mu> (g,length us)"
      using active unfolding Cons by simp
    have act: "\<mu>' (g',length us') = \<mu> (g,length us)"
      using inner_active[OF p1poss' _ sub'] Ug len Cons by simp
    show ?thesis unfolding Cons
      apply (rule exI[where x=g'])
      apply (rule exI[where x=us'])
      apply (rule conjI)
       using sub' Cons apply simp
      using j act apply simp
      done
  qed
qed

locale csr_finite_csr_sl = csr_sl_interpr_same C c I cge lge L LC LD LS
  for C :: "nat set"
  and c :: nat
  and I :: "(('f::{showl,compare_order},label_type) lab,nat) inter"
  and cge :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  and lge :: "('f,label_type) lab \<Rightarrow> nat \<Rightarrow>
    (label_type + ('f,label_type) lab list) \<Rightarrow>
    (label_type + ('f,label_type) lab list) \<Rightarrow> bool"
  and L :: "(('f,label_type) lab,nat,
    label_type + ('f,label_type) lab list) label"
  and LC :: "(('f,label_type) lab,
    label_type + ('f,label_type) lab list,('f,label_type) lab) lcompose"
  and LD :: "(('f,label_type) lab,('f,label_type) lab,
    label_type + ('f,label_type) lab list) ldecompose"
  and LS :: "(('f,label_type) lab,
    label_type + ('f,label_type) lab list) labels"
  + assumes lform: "\<And>f cs. L f cs = Inl cs"
    and lcform: "\<And>f n cs. LC f n (Inl cs) = Labelings.Lab f cs"

context csr_finite_csr_sl
begin

lemma csr_LAB_subt_finite_label:
  assumes wf: "wf_ass \<alpha>"
    and p: "p \<in> poss t"
    and sub: "Lab \<alpha> t |_ p = Fun g us"
  shows "\<exists>f cs. g = Labelings.Lab f cs \<and>
    set cs \<subseteq> C \<and> length cs = length us"
  using p sub
proof (induct p arbitrary: t g us)
  case Nil
  then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  let ?es = "map (eval_lab I L LC \<alpha>) ts"
  let ?cs = "map fst ?es"
  let ?lus = "map snd ?es"
  have bound: "set ?cs \<subseteq> C"
    using wf_term[OF wf] by auto
  have root: "Lab \<alpha> (Fun f ts) = Fun g us"
    using Nil.prems(2) unfolding t by (simp add: Let_def)
  from root have g: "g = Labelings.Lab f ?cs"
    by (simp add: Let_def lform lcform o_def)
  from arg_cong[OF root, of args] have us: "us = ?lus"
    by (simp add: Let_def o_def)
  show ?case
  proof (intro exI[of _ f] exI[of _ ?cs])
    show "g = Labelings.Lab f ?cs \<and>
        set ?cs \<subseteq> C \<and> length ?cs = length us"
      using g bound us by simp
  qed
next
  case (Cons i p)
  then obtain f ts where t: "t = Fun f ts" and i: "i < length ts"
    and pp: "p \<in> poss (ts ! i)" by (cases t, auto)
  have sub': "Lab \<alpha> (ts ! i) |_ p = Fun g us"
    using Cons.prems(2) t i by (simp add: Let_def)
  show ?case by (rule Cons.hyps[OF pp sub'])
qed

lemma csr_csdp_step_cond_LAB_finite:
  assumes carrier: "C = set [0..<Suc c]"
    and cond: "csdp_step_cond Sharp (mu_of \<mu>) p s"
  shows "csdp_step_cond csr_lab_sharp
    (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
proof (rule csr_csdp_step_cond_lift_term_on[
    where U=UNLAB and s=s and shp=Sharp])
  show "map_funs_term UNLAB (LAB s) = s" by (rule UNLAB_lab)
next
  fix f us
  assume s: "s = Fun (Sharp f) us"
  let ?es = "map (eval_lab I L LC default_ass) us"
  let ?cs = "map fst ?es"
  let ?lus = "map snd ?es"
  show "\<exists>f' us'. LAB s = Fun (csr_lab_sharp f') us' \<and>
      UNLAB f' = f"
    apply (rule exI[of _ "Labelings.Lab f ?cs"])
    apply (rule exI[of _ ?lus])
    using s LD_LC[of f "length us" "Inl ?cs"]
    by (simp add: Let_def lform lcform o_def)
next
  fix f' us'
  assume root: "LAB s = Fun (csr_lab_sharp f') us'"
  from csr_LAB_subt_finite_label[OF wf_default_ass, of "[]" s
      "csr_lab_sharp f'" us'] root
  obtain g cs where sym: "csr_lab_sharp f' = Labelings.Lab g cs"
    and cs: "set cs \<subseteq> C" and len: "length cs = length us'"
    by auto
  from sym obtain h where f': "f' = Labelings.Lab h cs"
    by (cases f', auto)
  show "mu_of (csr_finite_lab_mu \<mu> c) (f', length us') =
      mu_of \<mu> (UNLAB f', length us')"
    unfolding f' using csr_mu_of_finite_lab_mu[of cs c "length us'" \<mu> h]
      cs len carrier LD_LC[of h "length us'" "Inl cs"]
      by (simp add: lcform)
next
  fix q g' us'
  assume q: "q \<in> poss (LAB s)" "q \<noteq> []"
    and sub: "LAB s |_ q = Fun g' us'"
  from csr_LAB_subt_finite_label[OF wf_default_ass, of q s g' us']
    q(1) sub
  obtain f cs where g': "g' = Labelings.Lab f cs"
    and cs: "set cs \<subseteq> C" and len: "length cs = length us'"
    by auto
  show "mu_of (csr_finite_lab_mu \<mu> c) (g', length us') =
      mu_of \<mu> (UNLAB g', length us')"
    unfolding g' using csr_mu_of_finite_lab_mu[of cs c "length us'" \<mu> f]
      cs len carrier LD_LC[of f "length us'" "Inl cs"]
      by (simp add: lcform)
next
  show "csdp_step_cond Sharp (mu_of \<mu>) p s" by (rule cond)
qed

lemma csr_model_csdp_step_LAB_finite:
  assumes carrier: "C = set [0..<Suc c]"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and step: "(s,t) \<in> csdp_step Sharp (mu_of \<mu>) R"
  shows "(LAB s,LAB t) \<in> csdp_step csr_lab_sharp
    (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
proof -
  from step obtain p lr \<sigma> where raw:
      "(s,t) \<in> rstep_r_p_s R lr p \<sigma>"
    and cond: "csdp_step_cond Sharp (mu_of \<mu>) p s"
    unfolding csdp_step_def csdp_step_p_def by blast
  obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
  from model_rstep_r_p_s_LAB[OF eq model raw[unfolded lr]]
  obtain lr' \<delta> where raw':
      "(LAB s,LAB t) \<in> rstep_r_p_s (Lab_trs R) lr' p \<delta>" by blast
  have cond': "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
    by (rule csr_csdp_step_cond_LAB_finite[OF carrier cond])
  show ?thesis unfolding csdp_step_def csdp_step_p_def
    using raw' cond' by blast
qed

lemma csr_csdp_step_cond_UNLAB_finite:
  assumes carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and cond: "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
  shows "csdp_step_cond Sharp (mu_of \<mu>) p s"
  unfolding csdp_step_cond_def
proof (intro allI impI)
  fix p1 j p2
  assume eqposs: "p = p1 @ j # p2 \<and> p \<in> poss s"
  then have eq: "p = p1 @ j # p2" and pposs: "p \<in> poss s"
    by auto
  have lposs: "p \<in> poss (LAB s)" using pposs by simp
  from cond[unfolded csdp_step_cond_def, rule_format,
      OF conjI[OF eq lposs]]
  obtain g us where sub: "LAB s |_ p1 = Fun g us"
    and active: "case p1 of
        [] \<Rightarrow> \<exists>f'. g = csr_lab_sharp f' \<and>
          j \<in> mu_of (csr_finite_lab_mu \<mu> c) (f',length us)
      | _ \<Rightarrow> j \<in> mu_of (csr_finite_lab_mu \<mu> c)
          (g,length us)" by blast
  have p1poss: "p1 \<in> poss s"
    using pposs eq poss_append_poss by blast
  have lp1poss: "p1 \<in> poss (LAB s)" using p1poss by simp
  have mapped_sub: "s |_ p1 = Fun (UNLAB g)
      (map (map_funs_term UNLAB) us)"
  proof -
    have mapped: "map_funs_term UNLAB (LAB s |_ p1) =
        Fun (UNLAB g) (map (map_funs_term UNLAB) us)"
      using arg_cong[OF sub, of "map_funs_term UNLAB"] by simp
    have image: "map_funs_term UNLAB (LAB s) = s" by (rule UNLAB_lab)
    show ?thesis
      using subt_at_map_funs_term_csr[OF lp1poss, of UNLAB]
        mapped image by simp
  qed
  show "\<exists>g0 us0. s |_ p1 = Fun g0 us0 \<and>
      (case p1 of [] \<Rightarrow> \<exists>f. g0 = Sharp f \<and>
          j \<in> mu_of \<mu> (f,length us0)
        | _ \<Rightarrow> j \<in> mu_of \<mu> (g0,length us0))"
  proof (cases p1)
    case Nil
    from active[simplified Nil] obtain f' where
      g: "g = csr_lab_sharp f'" and
      j: "j \<in> mu_of (csr_finite_lab_mu \<mu> c) (f',length us)"
      by auto
    from csr_LAB_subt_finite_label[OF wf_default_ass, of "[]" s g us]
      sub[unfolded Nil]
    obtain h cs where sym: "g = Labelings.Lab h cs"
      and cs: "set cs \<subseteq> C" and len: "length cs = length us"
      by auto
    from sym g obtain f cs0 where f': "f' = Labelings.Lab f cs0"
      and cs0: "cs0 = cs" by (cases f', auto)
    have act: "mu_of (csr_finite_lab_mu \<mu> c) (f',length us) =
        mu_of \<mu> (UNLAB f',length us)"
      unfolding f' using csr_mu_of_finite_lab_mu[of cs0 c "length us" \<mu> f]
        cs len cs0 carrier LD_LC[of f "length us" "Inl cs0"]
        by (simp add: lcform)
    have comm: "UNLAB (csr_lab_sharp f') = Sharp (UNLAB f')"
      using unlab[of "csr_lab_sharp f'"] unlab[of f']
        unlab_csr_lab_sharp[of f'] by simp
    have root0: "s = Fun (Sharp (UNLAB f'))
        (map (map_funs_term UNLAB) us)"
      using mapped_sub unfolding Nil g comm by simp
    show ?thesis unfolding Nil
      apply (rule exI[of _ "Sharp (UNLAB f')"])
      apply (rule exI[of _ "map (map_funs_term UNLAB) us"])
      apply (rule conjI)
       using root0 apply simp
      apply (simp only: list.case)
      apply (rule exI[of _ "UNLAB f'"])
      using j act by simp
  next
    case (Cons k ks)
    have j: "j \<in> mu_of (csr_finite_lab_mu \<mu> c) (g,length us)"
      using active unfolding Cons by simp
    from csr_LAB_subt_finite_label[OF wf_default_ass, of p1 s g us]
      _ sub
    obtain f cs where g: "g = Labelings.Lab f cs"
      and cs: "set cs \<subseteq> C" and len: "length cs = length us"
      using p1poss by auto
    have act: "mu_of (csr_finite_lab_mu \<mu> c) (g,length us) =
        mu_of \<mu> (UNLAB g,length us)"
      unfolding g using csr_mu_of_finite_lab_mu[of cs c "length us" \<mu> f]
        cs len carrier LD_LC[of f "length us" "Inl cs"]
        by (simp add: lcform)
    show ?thesis unfolding Cons
      apply (rule exI[of _ "UNLAB g"])
      apply (rule exI[of _ "map (map_funs_term UNLAB) us"])
      using mapped_sub[unfolded Cons] j act by simp
  qed
qed

lemma csr_csr_inj_step_finite:
  assumes carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and step: "(LAB s,u) \<in> csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
  shows "\<exists>t. (s,t) \<in> csdp_step Sharp (mu_of \<mu>) R \<and>
    u = LAB t"
proof -
  from step obtain p lr \<sigma> where raw:
      "(LAB s,u) \<in> rstep_r_p_s (Lab_trs R) lr p \<sigma>"
    and cond: "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
    unfolding csdp_step_def csdp_step_p_def by blast
  have injL: "\<And>f. inj (L f)"
    unfolding inj_on_def using lform by auto
  have target_qr: "(LAB s,u) \<in> qrstep False (Lab_lhss {}) (Lab_trs R)"
    using rstep_r_p_s_imp_rstep[OF raw]
    unfolding qrstep_rstep_conv by simp
  have wwf: "wwf_qtrs {} R" using wfR unfolding wwf_qtrs_empty .
  have triv: "False \<Longrightarrow> {} \<noteq> {} \<Longrightarrow> wwf_qtrs {} R" by simp
  have snwwf: "\<not> SN_on (qrstep False {} R) {s} \<Longrightarrow>
      wwf_qtrs {} R" using wwf by simp
  from inj_step[OF injL target_qr triv snwwf model eq wf_default_ass]
  obtain t where source_qr: "(s,t) \<in> qrstep False {} R"
    and u: "u = LAB t"
    by auto
  have mapped_raw: "(s,map_funs_term UNLAB u) \<in>
      rstep_r_p_s (map_funs_trs UNLAB (Lab_trs R))
        (map_funs_rule UNLAB lr) p (map_funs_subst UNLAB \<sigma>)"
    using rstep_r_p_s_map_funs_term[OF raw, of UNLAB]
      UNLAB_lab[of default_ass s] by simp
  have mapped_rule: "map_funs_rule UNLAB lr \<in>
      map_funs_trs UNLAB (Lab_trs R)"
    using mapped_raw unfolding rstep_r_p_s_def' by auto
  have source_rule: "map_funs_rule UNLAB lr \<in> R"
    using map_funs_trs_UNLAB_Lab_trs[of R] mapped_rule by auto
  have source_raw: "(s,t) \<in> rstep_r_p_s R
      (map_funs_rule UNLAB lr) p (map_funs_subst UNLAB \<sigma>)"
    using mapped_raw source_rule u
    unfolding rstep_r_p_s_def' by (simp add: UNLAB_lab)
  have source_cond: "csdp_step_cond Sharp (mu_of \<mu>) p s"
    by (rule csr_csdp_step_cond_UNLAB_finite[OF carrier unlab cond])
  show ?thesis
    apply (rule exI[of _ t])
    apply (rule conjI)
     unfolding csdp_step_def csdp_step_p_def
     using source_raw source_cond apply blast
    apply (rule u)
    done
qed

lemma csr_SN_on_canonical_lift:
  assumes reflect: "\<And>s u. (F s,u) \<in> B \<Longrightarrow>
      \<exists>t. (s,t) \<in> A \<and> u = F t"
    and sn: "SN_on A {s}"
  shows "SN_on B {F s}"
proof (rule SN_on_induct_acc_style[
    where R=A and P="\<lambda>x. SN_on B {F x}", OF sn])
  fix x
  assume snx: "SN_on A {x}"
    and IH: "\<And>y. (x,y) \<in> A \<Longrightarrow> SN_on B {F y}"
  show "SN_on B {F x}"
  proof (rule SN_onI)
    fix f
    assume start: "f 0 \<in> {F x}" and steps: "chain B f"
    have raw0: "(f 0,f (Suc 0)) \<in> B"
      using steps unfolding chain_def by simp
    have step0: "(F x,f (Suc 0)) \<in> B"
      using start raw0 by simp
    from reflect[OF step0]
    obtain y where xy: "(x,y) \<in> A" and f1: "f (Suc 0) = F y"
      by auto
    let ?tail = "\<lambda>n. f (Suc n)"
    have tail0: "?tail 0 \<in> {F y}" using f1 by simp
    have tail_chain: "chain B ?tail"
      using steps unfolding chain_def by simp
    from not_SN_onI[OF tail0 tail_chain]
    have "\<not> SN_on B {F y}" .
    with IH[OF xy] show False by contradiction
  qed
qed

lemma csr_SN_on_csdp_step_LAB_finite:
  assumes carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and sn: "SN_on (csdp_step Sharp (mu_of \<mu>) R) {s}"
  shows "SN_on (csdp_step csr_lab_sharp
    (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)) {LAB s}"
proof (rule csr_SN_on_canonical_lift[OF _ sn])
  fix x u
  assume "(LAB x,u) \<in> csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
  then show "\<exists>t. (x,t) \<in> csdp_step Sharp (mu_of \<mu>) R \<and>
      u = LAB t"
    by (rule csr_csr_inj_step_finite[OF carrier unlab wfR eq model])
qed

theorem csr_finite_min_csr_dpp_semantic_labeling_finite:
  assumes fin: "finite_min_csr_dpp csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs P) (Lab_trs R)"
    and carrier: "C = set [0..<Suc c]"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>) P R"
proof (rule finite_min_csr_dpp_map[where F=LAB, OF fin])
  fix s t
  assume "(s,t) \<in> rrstep P"
  then show "(LAB s,LAB t) \<in> rrstep (Lab_trs P)"
    by (rule rrstep_LAB)
next
  fix s t
  assume "(s,t) \<in> csdp_step Sharp (mu_of \<mu>) R"
  then show "(LAB s,LAB t) \<in> csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
    by (rule csr_model_csdp_step_LAB_finite[OF carrier eq model])
next
  fix t
  assume sn: "SN_on (csdp_step Sharp (mu_of \<mu>) R) {t}"
  show "SN_on (csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)) {LAB t}"
    by (rule csr_SN_on_csdp_step_LAB_finite[
      OF carrier unlab wfR eq model sn])
qed

end

definition csr_bridge_semantic_mu ::
  "(('f,'l) lab) muL \<Rightarrow> (('f,'l) lab) muL"
where
  "csr_bridge_semantic_mu \<mu> = map (\<lambda>((f,n),is).
    ((csr_semantic_sharp_bridge f,n),is)) \<mu>"

lemma csr_map_of_map_inj:
  assumes inj: "inj h"
  shows "map_of (map (\<lambda>(k,v). (h k,v)) xs) (h k) = map_of xs k"
  using inj
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain k0 v where a: "a = (k0,v)" by (cases a)
  show ?case
  proof (cases "k = k0")
    case True
    then show ?thesis unfolding a by simp
  next
    case False
    from Cons.prems False have "h k \<noteq> h k0"
      unfolding inj_on_def by auto
    with Cons.hyps Cons.prems False show ?thesis unfolding a by simp
  qed
qed

lemma csr_mu_of_bridge_semantic_mu [simp]:
  "mu_of (csr_bridge_semantic_mu \<mu>)
      (csr_semantic_sharp_bridge f,n) = mu_of \<mu> (f,n)"
proof -
  have key_inj: "inj (\<lambda>(f,n). (csr_semantic_sharp_bridge f,n))"
    using csr_semantic_sharp_bridge_inj unfolding inj_on_def by auto
  have lookup:
    "map_of (csr_bridge_semantic_mu \<mu>)
        (csr_semantic_sharp_bridge f,n) = map_of \<mu> (f,n)"
    using csr_map_of_map_inj[OF key_inj, of \<mu> "(f,n)"]
    unfolding csr_bridge_semantic_mu_def
    by (simp add: split_def)
  show ?thesis
    unfolding mu_of_def
    apply (simp only: Let_def split_beta fst_conv snd_conv)
    apply (subst lookup)
    by (rule refl)
qed

lemma csr_map_funs_term_semantic_bridge_involution [simp]:
  "map_funs_term csr_semantic_sharp_bridge
      (map_funs_term csr_semantic_sharp_bridge t) = t"
  unfolding map_funs_term_comp o_def
  by (simp add: map_funs_term_ident[unfolded id_def])

lemma csr_map_funs_rule_semantic_bridge_involution [simp]:
  "map_funs_rule csr_semantic_sharp_bridge
      (map_funs_rule csr_semantic_sharp_bridge r) = r"
  by (cases r, simp)

lemma csr_map_funs_trs_semantic_bridge_involution [simp]:
  "map_funs_trs csr_semantic_sharp_bridge
      (map_funs_trs csr_semantic_sharp_bridge R) = R"
proof
  show "map_funs_trs csr_semantic_sharp_bridge
      (map_funs_trs csr_semantic_sharp_bridge R) \<subseteq> R"
    by (auto simp: map_funs_trs.simps)
next
  show "R \<subseteq> map_funs_trs csr_semantic_sharp_bridge
      (map_funs_trs csr_semantic_sharp_bridge R)"
  proof
    fix r
    assume r: "r \<in> R"
    have inner: "map_funs_rule csr_semantic_sharp_bridge r \<in>
        map_funs_trs csr_semantic_sharp_bridge R"
      using r unfolding map_funs_trs.simps by blast
    have outer: "map_funs_rule csr_semantic_sharp_bridge
        (map_funs_rule csr_semantic_sharp_bridge r) \<in>
      map_funs_trs csr_semantic_sharp_bridge
        (map_funs_trs csr_semantic_sharp_bridge R)"
      using inner unfolding map_funs_trs.simps by blast
    then show "r \<in> map_funs_trs csr_semantic_sharp_bridge
        (map_funs_trs csr_semantic_sharp_bridge R)" by simp
  qed
qed

lemma csr_lab_sharp_inj:
  "inj csr_lab_sharp"
proof (rule injI)
  fix x y
  assume "csr_lab_sharp x = csr_lab_sharp y"
  then show "x = y"
    by (cases x; cases y; auto)
qed

definition csr_unlab_sharp_root ::
  "(('f,'l) lab,'v) term \<Rightarrow> bool"
where
  "csr_unlab_sharp_root t \<longleftrightarrow>
    (\<exists>f ts. t = Fun (Sharp (UnLab f)) ts)"

lemma csr_unlab_sharp_root_subst:
  assumes "csr_unlab_sharp_root t"
  shows "csr_unlab_sharp_root (t \<cdot> \<sigma>)"
  using assms unfolding csr_unlab_sharp_root_def
  by auto

context csr_finite_csr_sl
begin

lemma csr_LAB_unlab_sharp_root:
  assumes root: "csr_unlab_sharp_root s"
  shows "\<exists>f cs us.
    LAB s = Fun (csr_lab_sharp (Labelings.Lab (UnLab f) cs)) us \<and>
    map_funs_term csr_semantic_sharp_bridge (LAB s) =
      Fun (Sharp (Labelings.Lab (UnLab f) cs))
        (map (map_funs_term csr_semantic_sharp_bridge) us)"
proof -
  from root obtain f ts where s: "s = Fun (Sharp (UnLab f)) ts"
    unfolding csr_unlab_sharp_root_def by blast
  let ?es = "map (eval_lab I L LC default_ass) ts"
  let ?cs = "map fst ?es"
  let ?us = "map snd ?es"
  show ?thesis
    apply (intro exI[of _ f] exI[of _ ?cs] exI[of _ ?us])
    using s LD_LC[of "Sharp (UnLab f)" "length ts" "Inl ?cs"]
    by (simp add: Let_def lform lcform o_def)
qed

lemma csr_bridge_LAB_step_forward:
  assumes root: "csr_unlab_sharp_root s"
    and step: "(LAB s,LAB t) \<in> csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
  shows "(map_funs_term csr_semantic_sharp_bridge (LAB s),
      map_funs_term csr_semantic_sharp_bridge (LAB t)) \<in>
    csdp_step Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
      (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
proof -
  from step obtain p lr \<sigma> where raw:
      "(LAB s,LAB t) \<in> rstep_r_p_s (Lab_trs R) lr p \<sigma>"
    and cond: "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
    unfolding csdp_step_def csdp_step_p_def by blast
  from csr_LAB_unlab_sharp_root[OF root]
  obtain f cs us where source:
      "LAB s = Fun (csr_lab_sharp (Labelings.Lab (UnLab f) cs)) us"
    and target:
      "map_funs_term csr_semantic_sharp_bridge (LAB s) =
        Fun (Sharp (Labelings.Lab (UnLab f) cs))
          (map (map_funs_term csr_semantic_sharp_bridge) us)"
    by blast
  have mapped_cond: "csdp_step_cond Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))) p
      (map_funs_term csr_semantic_sharp_bridge (LAB s))"
  proof (rule csr_csdp_step_cond_lift_term_on[
      where U=csr_semantic_sharp_bridge and s="LAB s"
        and shp=csr_lab_sharp])
    show "map_funs_term csr_semantic_sharp_bridge
        (map_funs_term csr_semantic_sharp_bridge (LAB s)) = LAB s"
      by simp
  next
    fix g vs
    assume eq: "LAB s = Fun (csr_lab_sharp g) vs"
    have marked_eq: "csr_lab_sharp g =
        csr_lab_sharp (Labelings.Lab (UnLab f) cs)"
      using source eq by auto
    have g: "g = Labelings.Lab (UnLab f) cs"
      by (rule injD[OF csr_lab_sharp_inj marked_eq])
    have vs: "vs = us" using source eq marked_eq by auto
    show "\<exists>g' vs'.
      map_funs_term csr_semantic_sharp_bridge (LAB s) =
        Fun (Sharp g') vs' \<and> csr_semantic_sharp_bridge g' = g"
      apply (intro exI[of _ g] exI[of _
        "map (map_funs_term csr_semantic_sharp_bridge) us"] conjI)
       using target g apply simp
      using g by simp
  next
    fix g vs
    assume "map_funs_term csr_semantic_sharp_bridge (LAB s) =
      Fun (Sharp g) vs"
    show "mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))
        (g,length vs) =
      mu_of (csr_finite_lab_mu \<mu> c)
        (csr_semantic_sharp_bridge g,length vs)"
      using csr_mu_of_bridge_semantic_mu[of
        "csr_finite_lab_mu \<mu> c"
        "csr_semantic_sharp_bridge g" "length vs"] by simp
  next
    fix q g vs
    assume "q \<in> poss (map_funs_term csr_semantic_sharp_bridge (LAB s))"
      "q \<noteq> []"
      "map_funs_term csr_semantic_sharp_bridge (LAB s) |_ q = Fun g vs"
    show "mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))
        (g,length vs) =
      mu_of (csr_finite_lab_mu \<mu> c)
        (csr_semantic_sharp_bridge g,length vs)"
      using csr_mu_of_bridge_semantic_mu[of
        "csr_finite_lab_mu \<mu> c"
        "csr_semantic_sharp_bridge g" "length vs"] by simp
  next
    show "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)" by (rule cond)
  qed
  have mapped_raw:
    "(map_funs_term csr_semantic_sharp_bridge (LAB s),
      map_funs_term csr_semantic_sharp_bridge (LAB t)) \<in>
      rstep_r_p_s
        (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))
        (map_funs_rule csr_semantic_sharp_bridge lr) p
        (map_funs_subst csr_semantic_sharp_bridge \<sigma>)"
    by (rule rstep_r_p_s_map_funs_term[OF raw])
  show ?thesis unfolding csdp_step_def csdp_step_p_def
    using mapped_raw mapped_cond by blast
qed

lemma csr_bridge_LAB_step_reflect:
  assumes root: "csr_unlab_sharp_root s"
    and step:
      "(map_funs_term csr_semantic_sharp_bridge (LAB s),u) \<in>
        csdp_step Sharp
          (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
  shows "\<exists>v. (LAB s,v) \<in> csdp_step csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R) \<and>
    u = map_funs_term csr_semantic_sharp_bridge v"
proof -
  from step obtain p lr \<sigma> where raw:
      "(map_funs_term csr_semantic_sharp_bridge (LAB s),u) \<in>
        rstep_r_p_s
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))
          lr p \<sigma>"
    and cond: "csdp_step_cond Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))) p
      (map_funs_term csr_semantic_sharp_bridge (LAB s))"
    unfolding csdp_step_def csdp_step_p_def by blast
  from csr_LAB_unlab_sharp_root[OF root]
  obtain f cs us where source:
      "LAB s = Fun (csr_lab_sharp (Labelings.Lab (UnLab f) cs)) us"
    and target:
      "map_funs_term csr_semantic_sharp_bridge (LAB s) =
        Fun (Sharp (Labelings.Lab (UnLab f) cs))
          (map (map_funs_term csr_semantic_sharp_bridge) us)"
    by blast
  have source_cond: "csdp_step_cond csr_lab_sharp
      (mu_of (csr_finite_lab_mu \<mu> c)) p (LAB s)"
  proof (rule csr_csdp_step_cond_lift_term_on[
      where U=csr_semantic_sharp_bridge
        and s="map_funs_term csr_semantic_sharp_bridge (LAB s)"
        and shp=Sharp])
    show "map_funs_term csr_semantic_sharp_bridge (LAB s) =
      map_funs_term csr_semantic_sharp_bridge (LAB s)" by simp
  next
    fix g vs
    assume eq: "map_funs_term csr_semantic_sharp_bridge (LAB s) =
      Fun (Sharp g) vs"
    have g: "g = Labelings.Lab (UnLab f) cs" and
      vs: "vs = map (map_funs_term csr_semantic_sharp_bridge) us"
      using target eq by auto
    show "\<exists>g' vs'. LAB s = Fun (csr_lab_sharp g') vs' \<and>
      csr_semantic_sharp_bridge g' = g"
      apply (intro exI[of _ g] exI[of _ us] conjI)
       using source g apply simp
      using g by simp
  next
    fix g vs
    assume "LAB s = Fun (csr_lab_sharp g) vs"
    show "mu_of (csr_finite_lab_mu \<mu> c) (g,length vs) =
      mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))
        (csr_semantic_sharp_bridge g,length vs)"
      using csr_mu_of_bridge_semantic_mu[of
        "csr_finite_lab_mu \<mu> c" g "length vs"] by simp
  next
    fix q g vs
    assume "q \<in> poss (LAB s)" "q \<noteq> []"
      "LAB s |_ q = Fun g vs"
    show "mu_of (csr_finite_lab_mu \<mu> c) (g,length vs) =
      mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))
        (csr_semantic_sharp_bridge g,length vs)"
      using csr_mu_of_bridge_semantic_mu[of
        "csr_finite_lab_mu \<mu> c" g "length vs"] by simp
  next
    show "csdp_step_cond Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))) p
      (map_funs_term csr_semantic_sharp_bridge (LAB s))" by (rule cond)
  qed
  have mapped_raw:
    "(LAB s,map_funs_term csr_semantic_sharp_bridge u) \<in>
      rstep_r_p_s (Lab_trs R)
        (map_funs_rule csr_semantic_sharp_bridge lr) p
        (map_funs_subst csr_semantic_sharp_bridge \<sigma>)"
    using rstep_r_p_s_map_funs_term[OF raw,
      of csr_semantic_sharp_bridge] by simp
  have source_step:
    "(LAB s,map_funs_term csr_semantic_sharp_bridge u) \<in>
      csdp_step csr_lab_sharp
        (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
    unfolding csdp_step_def csdp_step_p_def
    using mapped_raw source_cond by blast
  show ?thesis
    apply (intro exI[of _
      "map_funs_term csr_semantic_sharp_bridge u"] conjI)
     apply (rule source_step)
    by simp
qed

end

lemma csr_rrstep_map_semantic_bridge:
  assumes step: "(s,t) \<in> rrstep R"
  shows "(map_funs_term csr_semantic_sharp_bridge s,
      map_funs_term csr_semantic_sharp_bridge t) \<in>
    rrstep (map_funs_trs csr_semantic_sharp_bridge R)"
proof -
  from step obtain l r \<sigma> where lr: "(l,r) \<in> R"
    and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    unfolding rrstep_def' by auto
  show ?thesis
  proof (rule rrstepI[
      where l="map_funs_term csr_semantic_sharp_bridge l"
        and r="map_funs_term csr_semantic_sharp_bridge r"
        and \<sigma>="map_funs_subst csr_semantic_sharp_bridge \<sigma>"])
    show "(map_funs_term csr_semantic_sharp_bridge l,
        map_funs_term csr_semantic_sharp_bridge r) \<in>
      map_funs_trs csr_semantic_sharp_bridge R"
    proof -
      have "map_funs_rule csr_semantic_sharp_bridge (l,r) \<in>
          map_funs_trs csr_semantic_sharp_bridge R"
        using lr unfolding map_funs_trs.simps by (rule imageI)
      then show ?thesis by simp
    qed
    show "map_funs_term csr_semantic_sharp_bridge s =
      map_funs_term csr_semantic_sharp_bridge l \<cdot>
        map_funs_subst csr_semantic_sharp_bridge \<sigma>"
      using s by simp
    show "map_funs_term csr_semantic_sharp_bridge t =
      map_funs_term csr_semantic_sharp_bridge r \<cdot>
        map_funs_subst csr_semantic_sharp_bridge \<sigma>"
      using t by simp
  qed
qed

lemma csr_unlab_sharp_root_step_preserved:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and root: "csr_unlab_sharp_root s"
    and step: "(s,t) \<in> csdp_step Sharp \<mu> R"
  shows "csr_unlab_sharp_root t"
proof -
  from root obtain f ts where s: "s = Fun (Sharp (UnLab f)) ts"
    unfolding csr_unlab_sharp_root_def by blast
  from csstep_Fun_undefined_root_preserved[
    OF wf fresh[of "UnLab f" "length ts"] step[unfolded s]]
  obtain us where t: "t = Fun (Sharp (UnLab f)) us" by blast
  show ?thesis unfolding csr_unlab_sharp_root_def t by blast
qed

lemma csr_SN_on_canonical_lift_invariant:
  assumes inv: "Inv s"
    and reflect: "\<And>x u. Inv x \<Longrightarrow> (F x,u) \<in> B \<Longrightarrow>
      \<exists>y. (x,y) \<in> A \<and> Inv y \<and> u = F y"
    and sn: "SN_on A {s}"
  shows "SN_on B {F s}"
proof -
  have guarded: "Inv x \<longrightarrow> SN_on B {F x}" if "SN_on A {x}" for x
  proof (rule SN_on_induct_acc_style[
      where R=A and P="\<lambda>x. Inv x \<longrightarrow> SN_on B {F x}", OF that])
    fix x
    assume snx: "SN_on A {x}"
      and IH: "\<And>y. (x,y) \<in> A \<Longrightarrow>
        Inv y \<longrightarrow> SN_on B {F y}"
    show "Inv x \<longrightarrow> SN_on B {F x}"
    proof
      assume invx: "Inv x"
      show "SN_on B {F x}"
      proof (rule SN_onI)
        fix f
        assume start: "f 0 \<in> {F x}" and steps: "chain B f"
        have f0: "f 0 = F x" using start by simp
        have raw_first: "(f 0,f (Suc 0)) \<in> B"
          using steps unfolding chain_def by blast
        have first: "(F x,f (Suc 0)) \<in> B"
          using raw_first f0 by simp
        from reflect[OF invx first]
        obtain y where xy: "(x,y) \<in> A" and iy: "Inv y"
          and f1: "f (Suc 0) = F y" by auto
        let ?tail = "\<lambda>n. f (Suc n)"
        have tail0: "?tail 0 \<in> {F y}" using f1 by simp
        have tail_chain: "chain B ?tail"
          using steps unfolding chain_def by simp
        have "\<not> SN_on B {F y}"
          by (rule not_SN_onI[OF tail0 tail_chain])
        moreover have "SN_on B {F y}"
          using IH[OF xy] iy by blast
        ultimately show False by contradiction
      qed
    qed
  qed
  show ?thesis using guarded[OF sn] inv by blast
qed

context csr_finite_csr_sl
begin

lemma csr_semantic_bridged_step_forward:
  assumes carrier: "C = set [0..<Suc c]"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and root: "csr_unlab_sharp_root s"
    and step: "(s,t) \<in> csdp_step Sharp (mu_of \<mu>) R"
  shows "(map_funs_term csr_semantic_sharp_bridge (LAB s),
      map_funs_term csr_semantic_sharp_bridge (LAB t)) \<in>
    csdp_step Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
      (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
proof -
  from csr_model_csdp_step_LAB_finite[OF carrier eq model step]
  show ?thesis by (rule csr_bridge_LAB_step_forward[OF root])
qed

lemma csr_semantic_bridged_step_reflect:
  assumes carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and root: "csr_unlab_sharp_root s"
    and step:
      "(map_funs_term csr_semantic_sharp_bridge (LAB s),u) \<in>
        csdp_step Sharp
          (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
  shows "\<exists>t. (s,t) \<in> csdp_step Sharp (mu_of \<mu>) R \<and>
    u = map_funs_term csr_semantic_sharp_bridge (LAB t)"
proof -
  from csr_bridge_LAB_step_reflect[OF root step]
  obtain v where labeled:
      "(LAB s,v) \<in> csdp_step csr_lab_sharp
        (mu_of (csr_finite_lab_mu \<mu> c)) (Lab_trs R)"
    and u: "u = map_funs_term csr_semantic_sharp_bridge v" by blast
  from csr_csr_inj_step_finite[
    OF carrier unlab wfR eq model labeled]
  obtain t where source: "(s,t) \<in> csdp_step Sharp (mu_of \<mu>) R"
    and v: "v = LAB t" by blast
  show ?thesis using source u v by blast
qed

lemma csr_semantic_bridged_steps_forward:
  assumes carrier: "C = set [0..<Suc c]"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and wfR: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and root: "csr_unlab_sharp_root s"
    and steps: "(s,t) \<in> (csdp_step Sharp (mu_of \<mu>) R)\<^sup>*"
  shows "(map_funs_term csr_semantic_sharp_bridge (LAB s),
      map_funs_term csr_semantic_sharp_bridge (LAB t)) \<in>
      (csdp_step Sharp
        (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
        (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R)))\<^sup>* \<and>
    csr_unlab_sharp_root t"
  using steps root
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  from step.hyps(3)[OF step.prems]
  have mapped_prefix:
      "(map_funs_term csr_semantic_sharp_bridge (LAB s),
        map_funs_term csr_semantic_sharp_bridge (LAB y)) \<in>
        (csdp_step Sharp
          (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R)))\<^sup>*"
    and root_y: "csr_unlab_sharp_root y" by auto
  have mapped_step:
      "(map_funs_term csr_semantic_sharp_bridge (LAB y),
        map_funs_term csr_semantic_sharp_bridge (LAB z)) \<in>
        csdp_step Sharp
          (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
    by (rule csr_semantic_bridged_step_forward[
      OF carrier eq model root_y step.hyps(2)])
  have root_z: "csr_unlab_sharp_root z"
    by (rule csr_unlab_sharp_root_step_preserved[
      OF wfR fresh root_y step.hyps(2)])
  show ?case using mapped_prefix mapped_step root_z by auto
qed

lemma csr_semantic_bridged_SN:
  assumes carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
    and root: "csr_unlab_sharp_root s"
    and sn: "SN_on (csdp_step Sharp (mu_of \<mu>) R) {s}"
  shows "SN_on (csdp_step Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
      (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R)))
    {map_funs_term csr_semantic_sharp_bridge (LAB s)}"
proof (rule csr_SN_on_canonical_lift_invariant[
    where Inv=csr_unlab_sharp_root
      and A="csdp_step Sharp (mu_of \<mu>) R"
      and F="\<lambda>x. map_funs_term csr_semantic_sharp_bridge (LAB x)",
    OF root _ sn])
  fix x u
  assume root_x: "csr_unlab_sharp_root x"
    and target_step:
      "(map_funs_term csr_semantic_sharp_bridge (LAB x),u) \<in>
        csdp_step Sharp
          (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
          (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
  from csr_semantic_bridged_step_reflect[
    OF carrier unlab wfR eq model root_x target_step]
  obtain y where source_step:
      "(x,y) \<in> csdp_step Sharp (mu_of \<mu>) R"
    and u: "u = map_funs_term csr_semantic_sharp_bridge (LAB y)"
    by blast
  have root_y: "csr_unlab_sharp_root y"
    by (rule csr_unlab_sharp_root_step_preserved[
      OF wfR fresh root_x source_step])
  show "\<exists>y. (x,y) \<in> csdp_step Sharp (mu_of \<mu>) R \<and>
    csr_unlab_sharp_root y \<and>
    u = map_funs_term csr_semantic_sharp_bridge (LAB y)"
    using source_step root_y u by blast
qed

theorem csr_finite_min_csr_dpp_semantic_labeling_bridged:
  assumes fin: "finite_min_csr_dpp Sharp
      (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c)))
      (map_funs_trs csr_semantic_sharp_bridge (Lab_trs P))
      (map_funs_trs csr_semantic_sharp_bridge (Lab_trs R))"
    and shape: "\<And>s t. (s,t) \<in> P \<Longrightarrow>
      csr_unlab_sharp_root s \<and> csr_unlab_sharp_root t"
    and carrier: "C = set [0..<Suc c]"
    and unlab: "\<And>f. UNLAB f = unlab f"
    and wfR: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
    and eq: "cge = (=)"
    and model: "qmodel I L LC C cge R"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>) P R"
proof (rule ccontr)
  let ?S = "csdp_step Sharp (mu_of \<mu>) R"
  let ?P' = "map_funs_trs csr_semantic_sharp_bridge (Lab_trs P)"
  let ?R' = "map_funs_trs csr_semantic_sharp_bridge (Lab_trs R)"
  let ?S' = "csdp_step Sharp
    (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))) ?R'"
  let ?M' = "csr_min_pair_step Sharp
    (mu_of (csr_bridge_semantic_mu (csr_finite_lab_mu \<mu> c))) ?P' ?R'"
  let ?F = "\<lambda>x. map_funs_term csr_semantic_sharp_bridge (LAB x)"
  assume not_fin: "\<not> finite_min_csr_dpp Sharp (mu_of \<mu>) P R"
  from not_finite_min_csr_dpp_obtain_chain[OF not_fin]
  obtain s t \<sigma> where pair: "\<And>i. (s i,t i) \<in> P"
    and source_SN: "\<And>i. SN_on ?S {t i \<cdot> \<sigma> i}"
    and source_steps: "\<And>i. (t i \<cdot> \<sigma> i,
      s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> ?S\<^sup>*" by blast
  have roots: "\<And>i. csr_unlab_sharp_root (s i) \<and>
      csr_unlab_sharp_root (t i)"
    by (rule shape[OF pair])
  have target_pair: "\<And>i. (?F (s i \<cdot> \<sigma> i),
      ?F (t i \<cdot> \<sigma> i)) \<in> ?M'"
  proof -
    fix i
    have source_rr: "(s i \<cdot> \<sigma> i,t i \<cdot> \<sigma> i) \<in> rrstep P"
      by (rule rrstepI[OF pair[of i]], simp_all)
    from rrstep_LAB[OF source_rr]
    have labeled_rr: "(LAB (s i \<cdot> \<sigma> i),
      LAB (t i \<cdot> \<sigma> i)) \<in> rrstep (Lab_trs P)" .
    from csr_rrstep_map_semantic_bridge[OF labeled_rr]
    have bridged_rr: "(?F (s i \<cdot> \<sigma> i),
      ?F (t i \<cdot> \<sigma> i)) \<in> rrstep ?P'" .
    have root_t: "csr_unlab_sharp_root (t i \<cdot> \<sigma> i)"
      by (rule csr_unlab_sharp_root_subst[OF conjunct2[OF roots[of i]]])
    have target_sn: "SN_on ?S' {?F (t i \<cdot> \<sigma> i)}"
      by (rule csr_semantic_bridged_SN[
        OF carrier unlab wfR fresh eq model root_t source_SN[of i]])
    show "(?F (s i \<cdot> \<sigma> i),?F (t i \<cdot> \<sigma> i)) \<in> ?M'"
      using bridged_rr target_sn unfolding csr_min_pair_step_def by auto
  qed
  have target_steps: "\<And>i. (?F (t i \<cdot> \<sigma> i),
      ?F (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> ?S'\<^sup>*"
  proof -
    fix i
    have root_t: "csr_unlab_sharp_root (t i \<cdot> \<sigma> i)"
      by (rule csr_unlab_sharp_root_subst[OF conjunct2[OF roots[of i]]])
    from csr_semantic_bridged_steps_forward[
      OF carrier eq model wfR fresh root_t source_steps[of i]]
    show "(?F (t i \<cdot> \<sigma> i),
      ?F (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> ?S'\<^sup>*" by simp
  qed
  let ?chain = "\<lambda>i. ?F (s i \<cdot> \<sigma> i)"
  have chain: "\<And>i. (?chain i,?chain (Suc i)) \<in>
      ?S'\<^sup>* O ?M' O ?S'\<^sup>*"
    using target_pair target_steps by auto
  have chain': "chain (?S'\<^sup>* O ?M' O ?S'\<^sup>*) ?chain"
    unfolding chain_def by (rule allI, rule chain)
  have not_sn: "\<not> SN (?S'\<^sup>* O ?M' O ?S'\<^sup>*)"
    by (rule not_SN_onI[of ?chain], simp, rule chain')
  have not_target: "\<not> SN_rel ?M' ?S'"
    unfolding SN_rel_on_def using not_sn .
  from fin have "SN_rel ?M' ?S'"
    unfolding finite_min_csr_dpp_def .
  with not_target show False by contradiction
qed

end

fun csr_unlab_sharp_root_check ::
  "(('f,'l) lab,'v) term \<Rightarrow> bool"
where
  "csr_unlab_sharp_root_check (Fun (Sharp (UnLab f)) ts) = True"
| "csr_unlab_sharp_root_check t = False"

lemma csr_unlab_sharp_root_check_sound:
  assumes "csr_unlab_sharp_root_check t"
  shows "csr_unlab_sharp_root t"
proof (cases t)
  case (Var x)
  then show ?thesis using assms by simp
next
  case (Fun f ts)
  show ?thesis
  proof (cases f)
    case (Sharp g)
    then show ?thesis
      using assms Fun unfolding csr_unlab_sharp_root_def
      by (cases g; auto)
  qed (use assms Fun in auto)
qed

definition csr_unlab_sharp_pairs_check ::
  "(('f,'l) lab,'v) rules \<Rightarrow> bool"
where
  "csr_unlab_sharp_pairs_check P = list_all
    (\<lambda>(s,t). csr_unlab_sharp_root_check s \<and>
      csr_unlab_sharp_root_check t) P"

lemma csr_unlab_sharp_pairs_check_sound:
  assumes "csr_unlab_sharp_pairs_check P"
    and "(s,t) \<in> set P"
  shows "csr_unlab_sharp_root s \<and> csr_unlab_sharp_root t"
  using assms unfolding csr_unlab_sharp_pairs_check_def
  by (auto simp: list_all_iff split: prod.splits
    intro: csr_unlab_sharp_root_check_sound)

lemma semlab_finitelab_proc_exact:
  assumes J: "dpp_spec J"
    and proc: "semlab_fin_proc J (Finitelab sli) lP lQ lR
      (dpp_ops.mk J False False P [] [] [] R) = return dpp'"
  shows "lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (set P)
        \<subseteq> set (dpp_ops.pairs J dpp')"
    and "set (dpp_ops.rules J dpp') =
      lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (set R)"
    and "qmodel (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (=) (set R)"
proof -
  interpret dpp_spec J by fact
  have splitP: "model_splitter label_decomp lP {} = (lP, [], [])"
    by (induct lP, auto simp: model_splitter_def Let_def)
  obtain lRs lRw where splitR:
      "model_splitter label_decomp lR (set R) = (lRs, lRw, [])"
    unfolding model_splitter_def
    by (cases "List.partition
        (\<lambda>(r,ur). ur \<in> set R)
        (map (\<lambda>r. (r,map_funs_rule
          (\<lambda>lf. fst (label_decomp lf)) r)) lR)", auto)
  have raw: "sem_lab_proc label_decomp J succeed
      (check_sl_Q' (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        [0..<Suc (get_largest_element sli)])
      (check_sl_lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl)
        [0..<Suc (get_largest_element sli)] (=) label)
      (check_sl_lab' (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        [0..<Suc (get_largest_element sli)])
      (check_sl_model_lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl)
        [0..<Suc (get_largest_element sli)] (=) label)
      lP lQ lR (dpp_ops.mk J False False P [] [] [] R) = return dpp'"
    using proc
    by (auto simp: semlab_fin_proc.simps sem_lab_fin_proc_def
      slm_gen_to_sl_gen_def sli_to_slm_def slm_to_sl_def Let_def)
  note raw = raw[unfolded sem_lab_proc_def Let_def]
  note raw_ok = arg_cong[OF raw, of isOK, simplified]
  have out:
      "dpp' = dpp_ops.mk J False False lP [] lQ lRs lRw"
    using raw
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have p_more: "isOK (check_sl_lab_trs
      (sl_inter_to_inter sli) (\<lambda>_. Inl)
      [0..<Suc (get_largest_element sli)] (=) label (set lP)
        (dpp_ops.P J (dpp_ops.mk J False False P [] [] [] R)))"
    using raw_ok
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have rs_more: "isOK (check_sl_model_lab_trs
      (sl_inter_to_inter sli) (\<lambda>_. Inl)
      [0..<Suc (get_largest_element sli)] (=) label (set lRs)
        (dpp_ops.R J (dpp_ops.mk J False False P [] [] [] R)))"
    using raw_ok
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have rw_more: "isOK (check_sl_model_lab_trs
      (sl_inter_to_inter sli) (\<lambda>_. Inl)
      [0..<Suc (get_largest_element sli)] (=) label (set lRw)
        (dpp_ops.Rw J (dpp_ops.mk J False False P [] [] [] R)))"
    using raw_ok
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have rs_less: "isOK (check_sl_lab'
      (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      [0..<Suc (get_largest_element sli)] lRs
        (dpp_ops.R J (dpp_ops.mk J False False P [] [] [] R)))"
    using raw_ok
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have rw_less: "isOK (check_sl_lab'
      (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      [0..<Suc (get_largest_element sli)] lRw
        (dpp_ops.Rw J (dpp_ops.mk J False False P [] [] [] R)))"
    using raw_ok
    by (auto simp: mk_sound check_return_def splitP splitR upt_Suc)
  have p_sup: "lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (set P) \<subseteq> set lP"
    using check_sl_lab_trs_sound[OF p_more] by simp
  have rs_sub: "set lRs \<subseteq>
      lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) {}"
    using check_sl_lab'[OF rs_less] by simp
  then have rs_empty: "set lRs = {}" by simp
  have r_facts: "lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (set R) \<subseteq> set lRw \<and>
      qmodel (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (=) (set R)"
    using check_sl_model_lab_trs_sound[OF rw_more] rs_empty by simp
  have r_sub: "set lRw \<subseteq>
      lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (set R)"
    using check_sl_lab'[OF rw_less] by simp
  have out_dpp: "dpp_ops.dpp J dpp' =
      (False,False,set lP,{},set lQ,set lRs,set lRw)"
    using mk_sound[of False False lP "[]" lQ lRs lRw]
    unfolding out by simp
  have out_pairs: "set (dpp_ops.pairs J dpp') = set lP"
    using pairs_sound[of dpp'] dpp_sound[of dpp'] out_dpp by auto
  have out_rules: "set (dpp_ops.rules J dpp') = set lRs \<union> set lRw"
    using rules_sound[of dpp'] dpp_sound[of dpp'] out_dpp by auto
  show "lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (set P)
        \<subseteq> set (dpp_ops.pairs J dpp')"
    unfolding out_pairs by (rule p_sup)
  have rw_eq: "set lRw =
      lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (set R)"
  proof (rule subset_antisym)
    show "set lRw \<subseteq> lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl)
        label (set [0..<Suc (get_largest_element sli)]) (set R)"
      by (rule r_sub)
    show "lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (set R) \<subseteq> set lRw"
      by (rule conjunct1[OF r_facts])
  qed
  show "set (dpp_ops.rules J dpp') =
      lab_trs (sl_inter_to_inter sli) (\<lambda>_. Inl) label
        (set [0..<Suc (get_largest_element sli)]) (set R)"
    unfolding out_rules rs_empty Un_empty_left by (rule rw_eq)
  show "qmodel (sl_inter_to_inter sli) (\<lambda>_. Inl) label
      (set [0..<Suc (get_largest_element sli)]) (=) (set R)"
    by (rule conjunct2[OF r_facts])
qed

definition csr_bridge_semantic_rules ::
  "(('f,'l) lab,'v) rules \<Rightarrow> (('f,'l) lab,'v) rules"
where
  "csr_bridge_semantic_rules R =
    map (map_funs_rule csr_semantic_sharp_bridge) R"

lemma set_csr_bridge_semantic_rules [simp]:
  "set (csr_bridge_semantic_rules R) =
    map_funs_trs csr_semantic_sharp_bridge (set R)"
  unfolding csr_bridge_semantic_rules_def map_funs_trs.simps by auto

lemma vars_term_lab_raw [simp]:
  "vars_term (lab I L LC \<alpha> t) = vars_term t"
  by (induct t, auto simp: Let_def)

lemma wf_trs_csr_bridge_lab_trs:
  assumes "wf_trs R"
  shows "wf_trs (map_funs_trs csr_semantic_sharp_bridge
    (lab_trs I L label C R))"
proof (unfold wf_trs_def, intro allI impI)
  fix l r
  assume lr: "(l,r) \<in> map_funs_trs csr_semantic_sharp_bridge
    (lab_trs I L label C R)"
  then obtain lr' where lab: "lr' \<in> lab_trs I L label C R"
    and mapped: "(l,r) = map_funs_rule csr_semantic_sharp_bridge lr'"
    unfolding map_funs_trs.simps by blast
  obtain l' r' where lr': "lr' = (l',r')" by (cases lr', auto)
  from mapped have l: "l = map_funs_term csr_semantic_sharp_bridge l'"
    and r: "r = map_funs_term csr_semantic_sharp_bridge r'"
    unfolding lr' by auto
  from lab obtain lr0 where lr0: "lr0 \<in> R"
    and lablr: "(l',r') \<in> lab_rule I L label C lr0"
    unfolding lr' by blast
  obtain l0 r0 where lr0': "lr0 = (l0,r0)" by (cases lr0, auto)
  have lr0mem: "(l0,r0) \<in> R" using lr0 unfolding lr0' .
  have lablr': "(l',r') \<in>
      {(lab I L label \<alpha> l0,lab I L label \<alpha> r0) |\<alpha>.
        wf_assign C \<alpha>}"
    using lablr unfolding lr0' lab_rule_def by simp
  from lablr' obtain \<alpha> where ass: "wf_assign C \<alpha>"
    and pair: "(l',r') =
      (lab I L label \<alpha> l0,lab I L label \<alpha> r0)"
    by blast
  from pair have l': "l' = lab I L label \<alpha> l0"
    and r': "r' = lab I L label \<alpha> r0" by auto
  from assms lr0mem obtain f ts where l0: "l0 = Fun f ts"
    and vars: "vars_term r0 \<subseteq> vars_term l0"
    unfolding wf_trs_def by blast
  show "(\<exists>f ts. l = Fun f ts) \<and> vars_term r \<subseteq> vars_term l"
  proof
    show "\<exists>f ts. l = Fun f ts"
      unfolding l l' l0 by (simp add: Let_def split: prod.splits)
    show "vars_term r \<subseteq> vars_term l"
      using vars unfolding l r l' r' by simp
  qed
qed

lemma fresh_sharp_csr_bridge_lab_trs:
  assumes wf: "wf_trs R"
    and fresh: "\<And>f n. \<not> defined R (Sharp f,n)"
  shows "\<not> defined
    (map_funs_trs csr_semantic_sharp_bridge
      (lab_trs I L label C R)) (Sharp f,n)"
proof
  assume def: "defined
    (map_funs_trs csr_semantic_sharp_bridge
      (lab_trs I L label C R)) (Sharp f,n)"
  from def obtain ml mr where mapped_rule:
      "(ml,mr) \<in> map_funs_trs csr_semantic_sharp_bridge
        (lab_trs I L label C R)"
    and mapped_root: "root ml = Some (Sharp f,n)"
    unfolding defined_def by blast
  from mapped_rule obtain lr where lr: "lr \<in> lab_trs I L label C R"
    and mapped_pair:
      "(ml,mr) = map_funs_rule csr_semantic_sharp_bridge lr"
    unfolding map_funs_trs.simps by blast
  have root: "root (map_funs_term csr_semantic_sharp_bridge (fst lr)) =
      Some (Sharp f,n)"
    using mapped_root mapped_pair by simp
  obtain l r where lrp: "lr = (l,r)" by (cases lr, auto)
  from lr obtain lr0 where lr0: "lr0 \<in> R"
    and lablr: "(l,r) \<in> lab_rule I L label C lr0"
    unfolding lrp by blast
  obtain l0 r0 where lr0p: "lr0 = (l0,r0)" by (cases lr0, auto)
  have lablr': "(l,r) \<in>
      {(lab I L label \<alpha> l0,lab I L label \<alpha> r0) |\<alpha>.
        wf_assign C \<alpha>}"
    using lablr unfolding lr0p lab_rule_def by simp
  from lablr' obtain \<alpha> where
    ass: "wf_assign C \<alpha>"
    and pair: "(l,r) =
      (lab I L label \<alpha> l0,lab I L label \<alpha> r0)" by blast
  from pair have l: "l = lab I L label \<alpha> l0" by auto
  have lr0mem: "(l0,r0) \<in> R" using lr0 unfolding lr0p .
  from wf lr0mem obtain g ts where l0: "l0 = Fun g ts"
    unfolding wf_trs_def by (cases l0, auto)
  have root_lab:
      "root (map_funs_term csr_semantic_sharp_bridge
        (lab I L label \<alpha> (Fun g ts))) = Some (Sharp f,n)"
    using root unfolding lrp l l0 by simp
  from root_lab have root_info:
      "csr_semantic_sharp_bridge
        (label g n
          (L g (map ((fst \<circ>\<circ>\<circ> eval_lab I L) label \<alpha>) ts))) =
        Sharp f \<and> length ts = n"
    by (simp add: Let_def; metis label_arity_irrelevant)
  have arity: "length ts = n"
    by (rule conjunct2[OF root_info])
  have bridge_root:
      "csr_semantic_sharp_bridge
        (label g n
          (L g (map ((fst \<circ>\<circ>\<circ> eval_lab I L) label \<alpha>) ts))) =
        Sharp f"
    by (rule conjunct1[OF root_info])
  from csr_semantic_sharp_bridge_label_SharpD[OF bridge_root]
  obtain h where g: "g = Sharp h" .
  have "root l0 = Some (Sharp h,length ts)" unfolding l0 g by simp
  with lr0mem fresh[of h "length ts"] show False
    unfolding defined_def by auto
qed

fun csr_finite_total_label_decomp ::
  "('f,'l) lab \<Rightarrow> ('f,'l) lab \<times> ('l + ('f,'l) lab list)"
where
  "csr_finite_total_label_decomp (Labelings.Lab f l) = (f,Inl l)"
| "csr_finite_total_label_decomp (FunLab f ls) = (f,Inr ls)"
| "csr_finite_total_label_decomp (UnLab f) = (UnLab f,Inr [])"
| "csr_finite_total_label_decomp (Sharp f) = (Sharp f,Inr [])"

lemma fst_csr_finite_total_label_decomp [simp]:
  "fst (csr_finite_total_label_decomp f) = unlab f"
  by (cases f, auto)

lemma csr_finite_total_label_decomp_label [simp]:
  "csr_finite_total_label_decomp (label f n l) = (f,l)"
  by (cases l, auto)

lemma csr_finite_csr_sl_sli:
  "csr_finite_csr_sl
    (set [0..<Suc (get_largest_element sli)])
    (get_largest_element sli) (sl_inter_to_inter sli) (=)
    (\<lambda>_ _. (=)) (\<lambda>_. Inl) label
    csr_finite_total_label_decomp
    (\<lambda>_ _ _. True)"
proof unfold_locales
  show "wf_inter (sl_inter_to_inter sli)
      (set [0..<Suc (get_largest_element sli)])"
    using wf_sl_inter[of sli] unfolding sl_helper .
qed (auto simp: wf_label_def cge_wm lge_wm
  lge_to_lgr_rel_def lge_to_lgr_def)

fun csr_frozen_sct_graph_projection where
  "csr_frozen_sct_graph_projection ((l,r),(stri,nstri)) =
    (case stri @ nstri of
      [(i,j)] => (case (root l, root r) of
        (Some lf, Some rf) =>
          if i = 0 | j = 0 then None
          else Some ([(lf,i - 1),(rf,j - 1)],
            (if stri = [] then [] else [(l,r)]))
      | _ => None)
    | _ => None)"

fun csr_frozen_sct_projection where
  "csr_frozen_sct_projection [] = Some ([],[])"
| "csr_frozen_sct_projection (G # Gs) =
    (case (csr_frozen_sct_graph_projection G,
        csr_frozen_sct_projection Gs) of
      (Some (p,Pr), Some (ps,Prs)) => Some (p @ ps, Pr @ Prs)
    | _ => None)"

fun csr_frozen_sct_unsharp_candidate ::
  "((('f,'l) lab,'v) rules) => (('f,'l) lab) option"
where
  "csr_frozen_sct_unsharp_candidate ((Fun (Sharp f) ts,r) # P) =
    Some (FunLab f [])"
| "csr_frozen_sct_unsharp_candidate P = None"

definition csr_frozen_sct_fresh where
  "csr_frozen_sct_fresh U R =
    list_all (%(f,n). f ~= U) (funas_trs_list R)"

lemma csr_frozen_sct_fresh_sound:
  assumes "csr_frozen_sct_fresh U R"
  shows "!!n. ~ defined (set R) (U,n)"
proof
  fix n
  assume def: "defined (set R) (U,n)"
  from defined_funas_trs[OF def]
  have "(U,n) : set (funas_trs_list R)" by simp
  with assms show False
    unfolding csr_frozen_sct_fresh_def by (auto simp: list_all_iff)
qed

definition csr_frozen_sct_graph_tail where
  "csr_frozen_sct_graph_tail J mu dpp =
    check_csr_dep_graph_proc J mu dpp
      [(None :: unit option, dpp_ops.pairs J dpp)]"

definition csr_frozen_sct_subterm_proc ::
  "('dpp, (('f::{showl, compare_order}, label_type) lab), string) dpp_ops =>
   (('f, label_type) lab) muL =>
   ((((('f, label_type) lab), string) rule *
      ((nat * nat) list * (nat * nat) list)) list) =>
   'dpp => showsl check"
where
  "csr_frozen_sct_subterm_proc J mu Gs dpp =
    (case csr_frozen_sct_projection Gs of
      None => error (showsl_lit
        (STR ''size-change graphs do not encode a frozen projection''))
    | Some (p,Pr) =>
      (case csr_frozen_sct_unsharp_candidate (dpp_ops.pairs J dpp) of
        None => error (showsl_lit
          (STR ''frozen projection has no sharp source root''))
      | Some U => do {
          check (csr_frozen_sct_fresh U (dpp_ops.rules J dpp))
            (showsl_lit (STR ''derived frozen projection symbol is not fresh''));
          dpp' <- csr_frozen_recursive_subterm_proc J U mu
            (Projection p) [] Pr dpp;
          csr_frozen_sct_graph_tail J mu dpp';
          succeed
        }))"

lemma csr_frozen_sct_unsharp_candidate_sound:
  assumes "csr_frozen_sct_unsharp_candidate P = Some U"
  shows "~ is_sharp_lab U"
proof (cases P)
  case Nil
  with assms show ?thesis by simp
next
  case (Cons a P')
  obtain l r where a: "a = (l,r)" by (cases a)
  show ?thesis
  proof (cases l)
    case (Var x)
    with assms Cons a show ?thesis by simp
  next
    case (Fun g ts)
    with assms Cons a show ?thesis
      by (cases g; auto simp: is_sharp_lab.simps)
  qed
qed

lemma csr_frozen_sct_subterm_proc_sound:
  assumes J: "dpp_spec J" and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "!!f n. ~ defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (csr_frozen_sct_subterm_proc J mu Gs dpp)"
  shows "finite_min_csr_dpp Sharp (mu_of mu)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  obtain p Pr where proj: "csr_frozen_sct_projection Gs = Some (p,Pr)"
    using ok unfolding csr_frozen_sct_subterm_proc_def
    by (cases "csr_frozen_sct_projection Gs"; auto split: prod.splits)
  obtain U where cand: "csr_frozen_sct_unsharp_candidate
      (dpp_ops.pairs J dpp) = Some U"
    using ok proj unfolding csr_frozen_sct_subterm_proc_def
    by (cases "csr_frozen_sct_unsharp_candidate (dpp_ops.pairs J dpp)"; auto)
  from ok proj cand have fresh_U:
      "csr_frozen_sct_fresh U (dpp_ops.rules J dpp)"
    and proc_ok: "isOK (csr_frozen_recursive_subterm_proc J U mu
      (Projection p) [] Pr dpp)"
    unfolding csr_frozen_sct_subterm_proc_def by auto
  from proc_ok obtain dpp' where proc:
      "csr_frozen_recursive_subterm_proc J U mu
        (Projection p) [] Pr dpp = return dpp'"
    by (cases "csr_frozen_recursive_subterm_proc J U mu
      (Projection p) [] Pr dpp"; auto)
  from ok proj cand proc fresh_U have graph:
      "isOK (csr_frozen_sct_graph_tail J mu dpp')"
    unfolding csr_frozen_sct_subterm_proc_def
    by (simp add: fresh_U proc)
  have dpp'_eq: "dpp' = dpp_spec.delete_pairs J dpp Pr"
    using proc unfolding csr_frozen_recursive_subterm_proc_def
    by (cases "afs_of (csr_projection_collapsing_afs (Projection p))"; auto)
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp'_eq by (rule plain_csr_dpp_delete_pairs[OF J plain])
  interpret dpp_spec J by fact
  have graph': "isOK (check_csr_dep_graph_proc J mu dpp'
      [(None :: unit option,pairs dpp')])"
    using graph unfolding csr_frozen_sct_graph_tail_def .
  have no_components: "\<And>prf C.
      (Some prf,C) \<in> set [(None :: unit option,pairs dpp')] \<Longrightarrow>
      finite_min_csr_dpp Sharp (mu_of mu)
        (set (pairs dpp') \<inter> set C) (set (rules dpp'))"
    by simp
  have fin': "finite_min_csr_dpp Sharp (mu_of mu)
      (set (pairs dpp')) (set (rules dpp'))"
    by (rule check_csr_dep_graph_proc_min_sound[
      OF J plain' graph' no_components])
  show ?thesis by (rule csr_frozen_recursive_subterm_proc_sound[
      OF J plain wf fresh csr_frozen_sct_fresh_sound[OF fresh_U]
        csr_frozen_sct_unsharp_candidate_sound[OF cand] proc fin'])
qed

definition csr_hybrid_sct_subterm_proc ::
  "('dpp, (('f::{showl, compare_order}, label_type) lab), string) dpp_ops =>
   (('f, label_type) lab) muL =>
   ((((('f, label_type) lab), string) rule *
      ((nat * nat) list * (nat * nat) list)) list) =>
   'dpp => showsl check"
where
  "csr_hybrid_sct_subterm_proc J mu Gs dpp =
    (case csr_frozen_sct_projection Gs of
      None => error (showsl_lit
        (STR ''size-change graphs do not encode a hybrid projection''))
    | Some (p,Pr) =>
      (case csr_frozen_sct_unsharp_candidate (dpp_ops.pairs J dpp) of
        None => error (showsl_lit
          (STR ''hybrid projection has no sharp source root''))
      | Some U => do {
          check (csr_frozen_sct_fresh U (dpp_ops.rules J dpp))
            (showsl_lit (STR ''derived hybrid projection symbol is not fresh''));
          dpp' <- csr_hybrid_recursive_subterm_proc J U mu
            (Projection p) [] Pr dpp;
          csr_frozen_sct_graph_tail J mu dpp';
          succeed
        }))"

lemma csr_hybrid_sct_subterm_proc_sound:
  assumes J: "dpp_spec J" and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "!!f n. ~ defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (csr_hybrid_sct_subterm_proc J mu Gs dpp)"
  shows "finite_min_csr_dpp Sharp (mu_of mu)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  obtain p Pr where proj: "csr_frozen_sct_projection Gs = Some (p,Pr)"
    using ok unfolding csr_hybrid_sct_subterm_proc_def
    by (cases "csr_frozen_sct_projection Gs"; auto split: prod.splits)
  obtain U where cand: "csr_frozen_sct_unsharp_candidate
      (dpp_ops.pairs J dpp) = Some U"
    using ok proj unfolding csr_hybrid_sct_subterm_proc_def
    by (cases "csr_frozen_sct_unsharp_candidate (dpp_ops.pairs J dpp)"; auto)
  from ok proj cand have fresh_U:
      "csr_frozen_sct_fresh U (dpp_ops.rules J dpp)"
    and proc_ok: "isOK (csr_hybrid_recursive_subterm_proc J U mu
      (Projection p) [] Pr dpp)"
    unfolding csr_hybrid_sct_subterm_proc_def by auto
  from proc_ok obtain dpp' where proc:
      "csr_hybrid_recursive_subterm_proc J U mu
        (Projection p) [] Pr dpp = return dpp'"
    by (cases "csr_hybrid_recursive_subterm_proc J U mu
      (Projection p) [] Pr dpp"; auto)
  from ok proj cand proc fresh_U have graph:
      "isOK (csr_frozen_sct_graph_tail J mu dpp')"
    unfolding csr_hybrid_sct_subterm_proc_def
    by (simp add: fresh_U proc)
  have dpp'_eq: "dpp' = dpp_spec.delete_pairs J dpp Pr"
    using proc unfolding csr_hybrid_recursive_subterm_proc_def
    by (cases "afs_of (csr_projection_collapsing_afs (Projection p))"; auto)
  have plain': "plain_csr_dpp J dpp'"
    unfolding dpp'_eq by (rule plain_csr_dpp_delete_pairs[OF J plain])
  interpret dpp_spec J by fact
  have graph': "isOK (check_csr_dep_graph_proc J mu dpp'
      [(None :: unit option,pairs dpp')])"
    using graph unfolding csr_frozen_sct_graph_tail_def .
  have no_components: "\<And>prf C.
      (Some prf,C) \<in> set [(None :: unit option,pairs dpp')] \<Longrightarrow>
      finite_min_csr_dpp Sharp (mu_of mu)
        (set (pairs dpp') \<inter> set C) (set (rules dpp'))"
    by simp
  have fin': "finite_min_csr_dpp Sharp (mu_of mu)
      (set (pairs dpp')) (set (rules dpp'))"
    by (rule check_csr_dep_graph_proc_min_sound[
      OF J plain' graph' no_components])
  show ?thesis by (rule csr_hybrid_recursive_subterm_proc_sound[
      OF J plain wf fresh csr_frozen_sct_fresh_sound[OF fresh_U]
        csr_frozen_sct_unsharp_candidate_sound[OF cand] proc fin'])
qed

fun csr_bridge_semantic_component_proof ::
  "('f, 'l, 'v) dp_termination_proof \<Rightarrow>
   ('f, 'l, 'v) dp_termination_proof"
where
  "csr_bridge_semantic_component_proof (Size_Change_Subterm_Proc Gs) =
    Size_Change_Subterm_Proc
      (map (\<lambda>(st,es). (map_funs_rule csr_semantic_sharp_bridge st,es)) Gs)"
| "csr_bridge_semantic_component_proof prf = prf"

fun csr_semantic_component_shape ::
  "('f, 'l, 'v) dp_termination_proof \<Rightarrow> bool"
where
  "csr_semantic_component_shape (Size_Change_Subterm_Proc _) = True"
| "csr_semantic_component_shape P_is_Empty = True"
| "csr_semantic_component_shape (Redpair_Proc _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Subterm_Criterion_Proc _ _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Gen_Subterm_Criterion_Proc _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Dep_Graph_Proc edpts) =
    list_all (\<lambda>(po,_). po = None) edpts"
| "csr_semantic_component_shape (Redpair_UR_Proc _ _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Mono_Redpair_Proc _ _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Mono_URM_Redpair_Proc _ _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape (Mono_Redpair_UR_Proc _ _ _ _ prf) =
    csr_semantic_component_shape prf"
| "csr_semantic_component_shape _ = False"

fun csr_bridge_semantic_tail ::
  "('f, 'l, 'v) dp_termination_proof \<Rightarrow>
   ('f, 'l, 'v) dp_termination_proof"
where
  "csr_bridge_semantic_tail (Dep_Graph_Proc edpts) =
    Dep_Graph_Proc (map (\<lambda>(po,C).
      (map_option csr_bridge_semantic_component_proof po,
       csr_bridge_semantic_rules C)) edpts)"
| "csr_bridge_semantic_tail prf = prf"

fun csr_semantic_tail_shape ::
  "('f, 'l, 'v) dp_termination_proof \<Rightarrow> bool"
where
  "csr_semantic_tail_shape (Dep_Graph_Proc edpts) =
    list_all (\<lambda>(po,_). case po of None \<Rightarrow> True
      | Some prf \<Rightarrow> csr_semantic_component_shape prf) edpts"
| "csr_semantic_tail_shape _ = False"

fun check_csr_finite_semantic_component ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops =>
   ('dpp, ('f, label_type) lab, string) dpp_ops =>
   (('f, label_type) lab) muL => bool => showsl => 'dpp =>
   ('f, label_type, string) dp_termination_proof => showsl check"
and check_csr_finite_semantic_components ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops =>
   ('dpp, ('f, label_type) lab, string) dpp_ops =>
   (('f, label_type) lab) muL => bool => showsl => 'dpp =>
   (('f, label_type, string) dp_termination_proof option *
    ('f, label_type, string) trsLL) list => showsl check"
where
  "check_csr_finite_semantic_component I J mu a i dpp
      (Size_Change_Subterm_Proc Gs) =
    (if isOK (csr_frozen_sct_subterm_proc J mu Gs dpp)
     then debug i (STR ''frozen recursive semantic CSR subterm'') succeed
     else if isOK (csr_hybrid_sct_subterm_proc J mu Gs dpp)
     then debug i (STR ''hybrid recursive semantic CSR subterm'') succeed
     else check_csr_dp_component_core I J mu a i dpp
       (Size_Change_Subterm_Proc Gs))"
| "check_csr_finite_semantic_component I J mu a i dpp prf =
    check_csr_dp_component_core I J mu a i dpp prf"
| "check_csr_finite_semantic_components I J mu a i dpp [] = succeed"
| "check_csr_finite_semantic_components I J mu a i dpp
      ((None,P) # rest) =
    check_csr_finite_semantic_components I J mu a (add_index i 1) dpp rest"
| "check_csr_finite_semantic_components I J mu a i dpp
      ((Some prf,P) # rest) = do {
    check_csr_finite_semantic_component I J mu a (add_index i 1)
      (dpp_ops.intersect_pairs J dpp P) prf;
    check_csr_finite_semantic_components I J mu a (add_index i 1) dpp rest
  }"

definition check_csr_finite_semantic_tail where
  "check_csr_finite_semantic_tail I J mu a i dpp prf =
    (case prf of Dep_Graph_Proc edpts => do {
      _ <- check_csr_dep_graph_proc J mu dpp edpts;
      check_csr_finite_semantic_components I J mu a i dpp edpts
    } | _ => check_csr_finite_semantic_component I J mu a i dpp prf)"

fun check_csr_dp_termination_proof_finite_semantic ::
  "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
   (('f, label_type) lab) muL \<Rightarrow> bool \<Rightarrow>
   showsl \<Rightarrow> 'dpp \<Rightarrow>
   ('f, label_type, string) csr_dp_termination_proof \<Rightarrow> showsl check"
where
  "check_csr_dp_termination_proof_finite_semantic I J \<mu> a i dpp
      (CSR_DP_Ordinary_Proof
        (Semlab_Proc (Finitelab sli) lP lQ lR subprf)) =
    debug i (STR ''exact minimal CSR finite semantic labeling'') (do {
      let base = dpp_ops.mk J False False (dpp_ops.pairs J dpp)
        [] [] [] (dpp_ops.rules J dpp);
      check (csr_unlab_sharp_pairs_check (dpp_ops.pairs J dpp))
        (showsl_lit (STR ''exact CSR semantic labeling requires original marked pairs''));
      dpp' \<leftarrow> semlab_fin_proc J (Finitelab sli) lP lQ lR base
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error when applying exact CSR semantic labeling\<newline>'') \<circ> s);
      check (csr_semantic_tail_shape subprf)
        (showsl_lit (STR ''unsupported proof below exact CSR semantic labeling''));
      let bdpp = dpp_ops.mk J False False
        (csr_bridge_semantic_rules (dpp_ops.pairs J dpp')) [] [] []
        (csr_bridge_semantic_rules (dpp_ops.rules J dpp'));
      check_csr_finite_semantic_tail I J
        (csr_bridge_semantic_mu
          (csr_finite_lab_mu \<mu> (get_largest_element sli))) a
        (add_index i 1) bdpp (csr_bridge_semantic_tail subprf)
        <+? (\<lambda>s. i \<circ> showsl_lit
          (STR '': error below exact CSR semantic labeling\<newline>'') \<circ> s)
    })"
| "check_csr_dp_termination_proof_finite_semantic I J \<mu> a i dpp prf =
    check_csr_dp_termination_proof_min I J \<mu> a i dpp prf"

lemma check_csr_finite_semantic_component_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "!!f n. ~ defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_csr_finite_semantic_component
      I J mu False i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of mu)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof (cases "EX Gs. prf = Size_Change_Subterm_Proc Gs")
  case True
  then obtain Gs where prf_eq: "prf = Size_Change_Subterm_Proc Gs" by blast
  show ?thesis
  proof (cases "isOK (csr_frozen_sct_subterm_proc J mu Gs dpp)")
    case True
    show ?thesis by (rule csr_frozen_sct_subterm_proc_sound[
      OF J plain wf fresh True])
  next
    case False
    show ?thesis
    proof (cases "isOK (csr_hybrid_sct_subterm_proc J mu Gs dpp)")
      case True
      show ?thesis by (rule csr_hybrid_sct_subterm_proc_sound[
        OF J plain wf fresh True])
    next
      case False_hybrid: False
      from ok prf_eq False False_hybrid have core:
        "isOK (check_csr_dp_component_core I J mu False i dpp prf)" by simp
      show ?thesis by (rule check_csr_dp_component_core_sound[
        OF I J plain wf fresh core])
    qed
  qed
next
  case False
  from ok False have core: "isOK (check_csr_dp_component_core
      I J mu False i dpp prf)"
    by (cases "prf") auto
  show ?thesis by (rule check_csr_dp_component_core_sound[
    OF I J plain wf fresh core])
qed

lemma check_csr_finite_semantic_components_member:
  assumes ok: "isOK (check_csr_finite_semantic_components
      I J mu a i dpp edpts)"
    and mem: "(Some prf,C) : set edpts"
  shows "EX j. isOK (check_csr_finite_semantic_component I J mu a j
    (dpp_ops.intersect_pairs J dpp C) prf)"
  using ok mem
proof (induct edpts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain po P where x: "x = (po,P)" by (cases x)
  show ?case
  proof (cases po)
    case None
    with Cons x show ?thesis by (auto intro: Cons.hyps)
  next
    case (Some p)
    show ?thesis
    proof (cases "(Some prf,C) = x")
      case True
      with Cons x Some show ?thesis by auto
    next
      case False
      with Cons x Some show ?thesis by (auto intro: Cons.hyps)
    qed
  qed
qed

lemma check_csr_finite_semantic_tail_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "!!f n. ~ defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_csr_finite_semantic_tail
      I J mu False i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of mu)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof (cases "EX edpts. prf = Dep_Graph_Proc edpts")
  case True
  then obtain edpts where prf_eq: "prf = Dep_Graph_Proc edpts" by blast
  from ok prf_eq have graph: "isOK (check_csr_dep_graph_proc J mu dpp edpts)"
    and components: "isOK (check_csr_finite_semantic_components
      I J mu False i dpp edpts)"
    unfolding check_csr_finite_semantic_tail_def by auto
  show ?thesis
  proof (rule check_csr_dep_graph_proc_min_sound[OF J plain graph])
    fix p C
    assume mem: "(Some p,C) : set edpts"
    from check_csr_finite_semantic_components_member[OF components mem]
    obtain j where checked: "isOK (check_csr_finite_semantic_component
      I J mu False j (dpp_ops.intersect_pairs J dpp C) p)" by blast
    have plain': "plain_csr_dpp J (dpp_ops.intersect_pairs J dpp C)"
      by (rule plain_csr_dpp_intersect_pairs[OF J plain])
    interpret dpp_spec J by fact
    have sem: "dpp_ops.dpp J (intersect_pairs dpp C) =
      (NFS dpp, M dpp, set (P dpp) Int set C,
       set (Pw dpp) Int set C, set (Q dpp), set (R dpp), set (Rw dpp))"
      by (rule intersect_pairs_sound)
    have sem': "dpp_ops.dpp J (intersect_pairs dpp C) =
      (NFS (intersect_pairs dpp C), M (intersect_pairs dpp C),
       set (P (intersect_pairs dpp C)), set (Pw (intersect_pairs dpp C)),
       set (Q (intersect_pairs dpp C)), set (R (intersect_pairs dpp C)),
       set (Rw (intersect_pairs dpp C)))" by (rule dpp_sound)
    have rules': "set (rules (intersect_pairs dpp C)) = set (rules dpp)"
      using sem sem' rules_sound[of dpp] rules_sound[of "intersect_pairs dpp C"]
      by auto
    have pairs': "set (pairs (intersect_pairs dpp C)) =
      set (pairs dpp) Int set C"
      using sem sem' pairs_sound[of dpp] pairs_sound[of "intersect_pairs dpp C"]
      by auto
    have wf': "wf_trs (set (rules (intersect_pairs dpp C)))"
      using wf by (simp only: rules')
    have fresh': "\<And>f n. \<not> defined
        (set (rules (intersect_pairs dpp C))) (Sharp f,n)"
    proof -
      fix f n
      show "\<not> defined
          (set (rules (intersect_pairs dpp C))) (Sharp f,n)"
        by (subst rules', rule fresh)
    qed
    show "finite_min_csr_dpp Sharp (mu_of mu)
      (set (pairs dpp) Int set C) (set (rules dpp))"
      unfolding pairs'[symmetric] rules'[symmetric]
      by (rule check_csr_finite_semantic_component_sound[
        OF I J plain' wf' fresh' checked])
  qed
next
  case False
  from ok False have component: "isOK (check_csr_finite_semantic_component
      I J mu False i dpp prf)"
    unfolding check_csr_finite_semantic_tail_def by (cases "prf"; auto)
  show ?thesis by (rule check_csr_finite_semantic_component_sound[
    OF I J plain wf fresh component])
qed

lemma check_csr_dp_termination_proof_finite_semantic_exact_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_csr_dp_termination_proof_finite_semantic
      I J \<mu> False i dpp
        (CSR_DP_Ordinary_Proof
          (Semlab_Proc (Finitelab sli) lP lQ lR subprf)))"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  let ?base = "dpp_ops.mk J False False (dpp_ops.pairs J dpp)
    [] [] [] (dpp_ops.rules J dpp)"
  from ok obtain dpp' where
    shape: "csr_unlab_sharp_pairs_check (dpp_ops.pairs J dpp)"
    and proc: "semlab_fin_proc J (Finitelab sli) lP lQ lR ?base =
      return dpp'"
    and tail_shape: "csr_semantic_tail_shape subprf"
    and tail: "isOK (check_csr_finite_semantic_tail I J
      (csr_bridge_semantic_mu
        (csr_finite_lab_mu \<mu> (get_largest_element sli))) False
      (add_index i 1)
      (dpp_ops.mk J False False
        (csr_bridge_semantic_rules (dpp_ops.pairs J dpp')) [] [] []
        (csr_bridge_semantic_rules (dpp_ops.rules J dpp')))
      (csr_bridge_semantic_tail subprf))"
    by auto
  note exact = semlab_finitelab_proc_exact[OF J proc]
  let ?C = "set [0..<Suc (get_largest_element sli)]"
  let ?LI = "sl_inter_to_inter sli"
  let ?LP = "lab_trs ?LI (\<lambda>_. Inl) label ?C
    (set (dpp_ops.pairs J dpp))"
  let ?LR = "lab_trs ?LI (\<lambda>_. Inl) label ?C
    (set (dpp_ops.rules J dpp))"
  let ?bdpp = "dpp_ops.mk J False False
    (csr_bridge_semantic_rules (dpp_ops.pairs J dpp')) [] [] []
    (csr_bridge_semantic_rules (dpp_ops.rules J dpp'))"
  interpret dpp_spec J by fact
  note bdpp_sem = mk_sound[of False False
    "csr_bridge_semantic_rules (dpp_ops.pairs J dpp')" "[]" "[]" "[]"
    "csr_bridge_semantic_rules (dpp_ops.rules J dpp')"]
  have bdpp_sem': "dpp_ops.dpp J ?bdpp =
      (NFS ?bdpp,M ?bdpp,set (P ?bdpp),set (Pw ?bdpp),set (Q ?bdpp),
        set (R ?bdpp),set (Rw ?bdpp))"
    by (rule dpp_sound)
  have plain_b: "plain_csr_dpp J ?bdpp"
  proof -
    have pw_set: "set (Pw ?bdpp) = {}"
      using bdpp_sem bdpp_sem' by auto
    have q_set: "set (Q ?bdpp) = {}"
      using bdpp_sem bdpp_sem' by auto
    have r_set: "set (R ?bdpp) = {}"
      using bdpp_sem bdpp_sem' by auto
    have pw_nil: "Pw ?bdpp = []"
      using pw_set by (cases "Pw ?bdpp", auto)
    have q_nil: "Q ?bdpp = []"
      using q_set by (cases "Q ?bdpp", auto)
    have r_nil: "R ?bdpp = []"
      using r_set by (cases "R ?bdpp", auto)
    have empties: "Pw ?bdpp = [] \<and> Q ?bdpp = [] \<and> R ?bdpp = []"
      using pw_nil q_nil r_nil by blast
    show ?thesis using bdpp_sem bdpp_sem' empties
      unfolding plain_csr_dpp_def by auto
  qed
  have bdpp_pairs: "set (dpp_ops.pairs J ?bdpp) =
      set (csr_bridge_semantic_rules (dpp_ops.pairs J dpp'))"
    using pairs_sound[of ?bdpp] bdpp_sem bdpp_sem' by auto
  have bdpp_rules: "set (dpp_ops.rules J ?bdpp) =
      set (csr_bridge_semantic_rules (dpp_ops.rules J dpp'))"
    using rules_sound[of ?bdpp] bdpp_sem bdpp_sem' by auto
  have mapped_lp_sup:
      "map_funs_trs csr_semantic_sharp_bridge ?LP \<subseteq>
        map_funs_trs csr_semantic_sharp_bridge
          (set (dpp_ops.pairs J dpp'))"
    unfolding map_funs_trs.simps
    by (rule image_mono[OF exact(1)])
  have bdpp_pairs_sup: "map_funs_trs csr_semantic_sharp_bridge ?LP
      \<subseteq> set (dpp_ops.pairs J ?bdpp)"
    using bdpp_pairs mapped_lp_sup by simp
  have bdpp_rules_exact: "set (dpp_ops.rules J ?bdpp) =
      map_funs_trs csr_semantic_sharp_bridge ?LR"
    using bdpp_rules exact(2) by simp
  have wf_b: "wf_trs (set (dpp_ops.rules J ?bdpp))"
    using wf_trs_csr_bridge_lab_trs[OF wf,
      of ?LI "\<lambda>_. Inl" ?C]
    unfolding bdpp_rules_exact .
  have fresh_b: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J ?bdpp)) (Sharp f,n)"
    using fresh_sharp_csr_bridge_lab_trs[OF wf fresh,
      of ?LI "\<lambda>_. Inl" ?C]
    unfolding bdpp_rules_exact .
  from check_csr_finite_semantic_tail_sound[
      OF I J plain_b wf_b fresh_b tail]
  have fin_b_sup: "finite_min_csr_dpp Sharp
      (mu_of (csr_bridge_semantic_mu
        (csr_finite_lab_mu \<mu> (get_largest_element sli))))
      (set (dpp_ops.pairs J ?bdpp))
      (map_funs_trs csr_semantic_sharp_bridge ?LR)"
    using bdpp_rules_exact by simp
  have fin_b: "finite_min_csr_dpp Sharp
      (mu_of (csr_bridge_semantic_mu
        (csr_finite_lab_mu \<mu> (get_largest_element sli))))
      (map_funs_trs csr_semantic_sharp_bridge ?LP)
      (map_funs_trs csr_semantic_sharp_bridge ?LR)"
    by (rule finite_min_csr_dpp_mono_pairs[OF bdpp_pairs_sup fin_b_sup])
  interpret sem: csr_finite_csr_sl ?C "get_largest_element sli"
    ?LI "(=)" "\<lambda>_ _. (=)" "\<lambda>_. Inl" label
    csr_finite_total_label_decomp
    "\<lambda>_ _ _. True"
    by (rule csr_finite_csr_sl_sli)
  show ?thesis
  proof (rule sem.csr_finite_min_csr_dpp_semantic_labeling_bridged[
      OF fin_b])
    fix s t
    assume mem: "(s,t) \<in> set (dpp_ops.pairs J dpp)"
    show "csr_unlab_sharp_root s \<and> csr_unlab_sharp_root t"
      by (rule csr_unlab_sharp_pairs_check_sound[OF shape mem])
  next
    show "?C = set [0..<Suc (get_largest_element sli)]" by simp
  next
    fix f
    show "fst (csr_finite_total_label_decomp f) = unlab f" by simp
  next
    show "wf_trs (set (dpp_ops.rules J dpp))" by (rule wf)
  next
    fix f n
    show "\<not> defined (set (dpp_ops.rules J dpp)) (Sharp f,n)"
      by (rule fresh)
  next
    show "(=) = (=)" by simp
  next
    show "qmodel ?LI (\<lambda>_. Inl) label ?C (=)
      (set (dpp_ops.rules J dpp))" by (rule exact(3))
  qed
qed

lemma check_csr_dp_termination_proof_finite_semantic_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and plain: "plain_csr_dpp J dpp"
    and wf: "wf_trs (set (dpp_ops.rules J dpp))"
    and fresh: "\<And>f n. \<not> defined
      (set (dpp_ops.rules J dpp)) (Sharp f,n)"
    and ok: "isOK (check_csr_dp_termination_proof_finite_semantic
      I J \<mu> False i dpp prf)"
  shows "finite_min_csr_dpp Sharp (mu_of \<mu>)
    (set (dpp_ops.pairs J dpp)) (set (dpp_ops.rules J dpp))"
proof -
  have old_sound: ?thesis if old:
      "isOK (check_csr_dp_termination_proof_min I J \<mu> False i dpp p)"
    for p
    by (rule check_csr_dp_termination_proof_min_sound[
      OF I J plain wf fresh old])
  show ?thesis
  proof (cases "prf")
  case (CSR_DP_Ordinary_Proof x)
  show ?thesis
  proof (cases "x")
    case (Semlab_Proc sl lP lQ lR subprf)
    show ?thesis
    proof (cases "sl")
      case (Finitelab sli)
      show ?thesis
      proof (rule check_csr_dp_termination_proof_finite_semantic_exact_sound[
          OF I J plain wf fresh])
        show "isOK (check_csr_dp_termination_proof_finite_semantic I J \<mu>
          False i dpp (CSR_DP_Ordinary_Proof
            (Semlab_Proc (Finitelab sli) lP lQ lR subprf)))"
          using ok unfolding CSR_DP_Ordinary_Proof Semlab_Proc Finitelab .
      qed
    next
      case (Rootlab x)
      have old: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
        i dpp prf)" using ok
        unfolding CSR_DP_Ordinary_Proof Semlab_Proc Rootlab by simp
      show ?thesis by (rule check_csr_dp_termination_proof_min_sound[
        OF I J plain wf fresh old])
    next
      case (QuasiFinitelab x y)
      have old: "isOK (check_csr_dp_termination_proof_min I J \<mu> False
        i dpp prf)" using ok
        unfolding CSR_DP_Ordinary_Proof Semlab_Proc QuasiFinitelab by simp
      show ?thesis by (rule check_csr_dp_termination_proof_min_sound[
        OF I J plain wf fresh old])
    qed
  qed ((rule old_sound[where p="CSR_DP_Ordinary_Proof x"],
    insert ok, simp add: CSR_DP_Ordinary_Proof)+)
  qed ((rule old_sound[where p="prf"], insert ok, simp)+)
qed

end
