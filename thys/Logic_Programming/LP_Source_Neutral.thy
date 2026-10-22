theory LP_Source_Neutral
  imports LP_Source_Unify LP_Source_Tree
begin

text \<open>Position-only derivation neutrality (Payet and Mesnard, TOPLAS
  2006, Definition 3.27). A binary transition must be justified separately:
  selecting a later body atom does not discharge the preceding calls.
  These lemmas establish the environment-independence side condition; they
  are not yet an executable source nontermination checker.\<close>

definition lp_dn_positions where
  "lp_dn_positions hs bs I J =
    (\<forall>i\<in>I. i<length hs \<and>
      (\<exists>x. hs!i=Var x \<and>
        (\<forall>k<length hs. k\<noteq>i \<longrightarrow> x\<notin>vars_term (hs!k)) \<and>
        (\<forall>k<length bs. k\<notin>J \<longrightarrow> x\<notin>vars_term (bs!k))))"

lemma lp_dn_head_variable:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I"
  obtains x where "i<length hs" "hs!i=Var x"
    "\<And>k. k<length hs \<Longrightarrow> k\<noteq>i \<Longrightarrow> x\<notin>vars_term (hs!k)"
    "\<And>k. k<length bs \<Longrightarrow> k\<notin>J \<Longrightarrow> x\<notin>vars_term (bs!k)"
proof -
  have one: "i<length hs \<and>
      (\<exists>x. hs!i=Var x \<and>
        (\<forall>k<length hs. k\<noteq>i \<longrightarrow> x\<notin>vars_term (hs!k)) \<and>
        (\<forall>k<length bs. k\<notin>J \<longrightarrow> x\<notin>vars_term (bs!k)))"
    using dn i unfolding lp_dn_positions_def by (rule bspec)
  then obtain x where x: "i<length hs" "hs!i=Var x"
    "\<forall>k<length hs. k\<noteq>i \<longrightarrow> x\<notin>vars_term (hs!k)"
    "\<forall>k<length bs. k\<notin>J \<longrightarrow> x\<notin>vars_term (bs!k)" by auto
  show thesis by (rule that[OF x(1,2)]) (use x(3,4) in auto)
qed

lemma lp_dn_update_head:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I"
    and var: "hs!i=Var x" and k: "k<length hs" "k\<noteq>i"
  shows "lp_ieval (hs!k) (\<rho>(x:=v)) = lp_ieval (hs!k) \<rho>"
proof (rule lp_ieval_cong)
  fix y assume y: "y\<in>vars_term (hs!k)"
  have "x\<notin>vars_term (hs!k)"
    using dn i var k unfolding lp_dn_positions_def by auto
  then show "(\<rho>(x:=v)) y=\<rho> y" using y by auto
qed

lemma lp_dn_update_retained_body:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I"
    and var: "hs!i=Var x" and k: "k<length bs" "k\<notin>J"
  shows "lp_ieval (bs!k) (\<rho>(x:=v)) = lp_ieval (bs!k) \<rho>"
proof (rule lp_ieval_cong)
  fix y assume y: "y\<in>vars_term (bs!k)"
  have "x\<notin>vars_term (bs!k)"
    using dn i var k unfolding lp_dn_positions_def by auto
  then show "(\<rho>(x:=v)) y=\<rho> y" using y by auto
qed

text \<open>The replacement value is an arbitrary runtime tree: the lemmas
  do not assume groundness, finiteness, or an occurs check.\<close>

definition lp_dn_env where
  "lp_dn_env hs I vals \<rho> x =
    (if \<exists>i\<in>I. hs!i=Var x
     then vals!(SOME i. i\<in>I \<and> hs!i=Var x) else \<rho> x)"

lemma lp_dn_env_outside:
  assumes "\<And>i. i\<in>I \<Longrightarrow> hs!i\<noteq>Var x"
  shows "lp_dn_env hs I vals \<rho> x=\<rho> x"
  using assms unfolding lp_dn_env_def by auto

lemma lp_dn_env_selected:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I" and var: "hs!i=Var x"
  shows "lp_dn_env hs I vals \<rho> x=vals!i"
proof -
  have unique: "\<And>j. j\<in>I \<and> hs!j=Var x \<Longrightarrow> j=i"
  proof -
    fix j assume j: "j\<in>I \<and> hs!j=Var x"
    have bound: "j<length hs" using dn j unfolding lp_dn_positions_def by auto
    have apart: "j\<noteq>i \<Longrightarrow> x\<notin>vars_term (hs!j)"
      using dn i var bound unfolding lp_dn_positions_def by auto
    show "j=i" using apart j by auto
  qed
  have selected: "(SOME j. j\<in>I \<and> hs!j=Var x)=i"
    by (rule some_equality[where a=i]) (rule conjI[OF i var], rule unique)
  have exists: "\<exists>j\<in>I. hs!j=Var x" by (rule bexI[where x=i]) (rule var, rule i)
  show ?thesis unfolding lp_dn_env_def using exists selected by simp
qed

lemma lp_dn_env_retained:
  assumes dn: "lp_dn_positions hs bs I J" and k: "k<length bs" "k\<notin>J"
  shows "lp_ieval (bs!k) (lp_dn_env hs I vals \<rho>)=lp_ieval (bs!k) \<rho>"
proof (rule lp_ieval_cong)
  fix x assume x: "x\<in>vars_term (bs!k)"
  show "lp_dn_env hs I vals \<rho> x=\<rho> x"
  proof (rule lp_dn_env_outside)
    fix i assume i: "i\<in>I"
    show "hs!i\<noteq>Var x" using dn i k x unfolding lp_dn_positions_def by auto
  qed
qed

lemma lp_dn_env_head:
  assumes dn: "lp_dn_positions hs bs I J" and k: "k<length hs"
  shows "lp_ieval (hs!k) (lp_dn_env hs I vals \<rho>) =
    (if k\<in>I then vals!k else lp_ieval (hs!k) \<rho>)"
proof (cases "k\<in>I")
  case True
  obtain x where var: "hs!k=Var x" using dn True unfolding lp_dn_positions_def by auto
  show ?thesis using lp_dn_env_selected[OF dn True var, of vals \<rho>] by (simp add: var True)
next
  case False
  have eq: "lp_ieval (hs!k) (lp_dn_env hs I vals \<rho>)=lp_ieval (hs!k) \<rho>"
  proof (rule lp_ieval_cong)
    fix x assume x: "x\<in>vars_term (hs!k)"
    show "lp_dn_env hs I vals \<rho> x=\<rho> x"
    proof (rule lp_dn_env_outside)
      fix i assume i: "i\<in>I"
      have neq: "k\<noteq>i" using False i by auto
      show "hs!i\<noteq>Var x" using dn i k neq x unfolding lp_dn_positions_def by auto
    qed
  qed
  show ?thesis using eq False by simp
qed

definition lp_dn_agrees where
  "lp_dn_agrees I bs us = (length us=length bs \<and>
    (\<forall>k<length bs. k\<notin>I \<longrightarrow> us!k=lp_ieval (bs!k) LPIVar))"

lemma lp_dn_step:
  fixes P :: "('f,'v) lp_clause list"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs" "length us=length hs"
    and dn: "lp_dn_positions hs bs I I"
    and matched: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_isubst (us!k) \<sigma> = lp_ieval (hs!k) LPIVar"
  obtains vs tail' where
    "((q,us)#tail,(q,vs)#tail')\<in>lp_ild P" "lp_dn_agrees I bs vs"
proof -
  let ?vals = "map (\<lambda>t. lp_isubst t \<sigma>) us"
  let ?env = "lp_dn_env hs I ?vals LPIVar"
  have eq: "?vals=map (\<lambda>t. lp_ieval t ?env) hs"
  proof (rule nth_equalityI)
    show "length ?vals=length (map (\<lambda>t. lp_ieval t ?env) hs)" using len by simp
    fix k assume k: "k<length ?vals"
    have kh: "k<length hs" using k len by simp
    show "?vals!k=map (\<lambda>t. lp_ieval t ?env) hs!k"
      using lp_dn_env_head[OF dn kh, of ?vals LPIVar] matched[OF kh] k kh
      by (auto simp: nth_map)
  qed
  have match: "lp_iatom_subst (q,us) \<sigma>=lp_atom_eval (fst (P!c)) ?env"
    using eq by (simp add: head lp_iatom_subst_def lp_atom_eval_def)
  let ?vs = "map (\<lambda>t. lp_ieval t ?env) bs"
  let ?tail = "map (\<lambda>a. lp_atom_eval a ?env) rest @
    map (\<lambda>a. lp_iatom_subst a \<sigma>) tail"
  have step: "((q,us)#tail,(q,?vs)#?tail)\<in>lp_ild P"
    using lp_ild.resolve[OF c match, of tail] by (simp add: body lp_atom_eval_def)
  have agrees: "lp_dn_agrees I bs ?vs"
    unfolding lp_dn_agrees_def
    using lp_dn_env_retained[OF dn, of _ ?vals LPIVar] by auto
  show thesis by (rule that[OF step agrees])
qed

theorem lp_dn_binary_loop:
  fixes P :: "('f,'v) lp_clause list" and \<tau> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs"
    and dn: "lp_dn_positions hs bs I I"
    and repeat: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> bs!k\<cdot>\<tau>=hs!k"
    and entry: "lp_dn_agrees I bs us"
  shows "\<not>SN_on (lp_ild P) {(q,us)#tail}"
proof (rule lp_serial_not_SN[where X="{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_dn_agrees I bs us}"])
  show "(q,us)#tail\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_dn_agrees I bs us}"
    using entry by auto
next
  fix gs assume member: "gs\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_dn_agrees I bs us}"
  then obtain us tail where gs: "gs=(q,us)#tail" and agrees: "lp_dn_agrees I bs us" by auto
  let ?sigma = "\<lambda>x. lp_ieval (\<tau> x) LPIVar"
  have length: "length us=length hs" using agrees len unfolding lp_dn_agrees_def by simp
  have match: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_isubst (us!k) ?sigma=lp_ieval (hs!k) LPIVar"
  proof -
    fix k assume k: "k<length hs" "k\<notin>I"
    have us: "us!k=lp_ieval (bs!k) LPIVar" using agrees k len unfolding lp_dn_agrees_def by auto
    show "lp_isubst (us!k) ?sigma=lp_ieval (hs!k) LPIVar"
      using arg_cong[OF repeat[OF k], of "\<lambda>t. lp_ieval t LPIVar"]
      by (simp add: us lp_ieval_subst lp_ieval_finite_subst)
  qed
  obtain vs tail' where step: "((q,us)#tail,(q,vs)#tail')\<in>lp_ild P"
    and closed: "lp_dn_agrees I bs vs"
    by (rule lp_dn_step[OF c head body len length dn match]) auto
  show "\<exists>t\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_dn_agrees I bs us}. (gs,t)\<in>lp_ild P"
    using step closed unfolding gs by auto
qed

theorem lp_dn_finite_entry:
  fixes P :: "('f,'v) lp_clause list" and \<tau> \<sigma> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs" "length es=length hs"
    and dn: "lp_dn_positions hs bs I I"
    and repeat: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> bs!k\<cdot>\<tau>=hs!k"
    and enter: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> es!k\<cdot>\<sigma>=hs!k"
  shows "\<not>SN_on (lp_ild P) {lp_atom_eval (q,es) LPIVar#tail}"
proof -
  let ?us = "map (\<lambda>t. lp_ieval t LPIVar) es"
  let ?sigma = "\<lambda>x. lp_ieval (\<sigma> x) LPIVar"
  have length: "length ?us=length hs" using len by simp
  have match: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_isubst (?us!k) ?sigma=lp_ieval (hs!k) LPIVar"
  proof -
    fix k assume k: "k<length hs" "k\<notin>I"
    show "lp_isubst (?us!k) ?sigma=lp_ieval (hs!k) LPIVar"
      using arg_cong[OF enter[OF k], of "\<lambda>t. lp_ieval t LPIVar"] k len
      by (simp add: lp_ieval_subst lp_ieval_finite_subst)
  qed
  obtain vs tail' where step: "((q,?us)#tail,(q,vs)#tail')\<in>lp_ild P"
    and closed: "lp_dn_agrees I bs vs"
    by (rule lp_dn_step[OF c head body len(1) length dn match]) auto
  have bad: "\<not>SN_on (lp_ild P) {(q,vs)#tail'}"
    by (rule lp_dn_binary_loop[OF c head body len(1) dn repeat closed])
  show ?thesis using bad lp_SN_reachable[OF _ r_into_rtrancl[OF step]]
    by (auto simp: lp_atom_eval_def)
qed

definition lp_dn_positions_list where
  "lp_dn_positions_list hs bs Is Js = list_all (\<lambda>i. i<length hs \<and>
    (case hs!i of Var x \<Rightarrow>
      list_all (\<lambda>k. k=i \<or> x\<notin>vars_term (hs!k)) [0..<length hs] \<and>
      list_all (\<lambda>k. k\<in>set Js \<or> x\<notin>vars_term (bs!k)) [0..<length bs]
    | _ \<Rightarrow> False)) Is"

lemma lp_dn_positions_list_sound:
  assumes checked: "lp_dn_positions_list hs bs Is Js"
  shows "lp_dn_positions hs bs (set Is) (set Js)"
  unfolding lp_dn_positions_def
proof (intro ballI)
  fix i assume i: "i\<in>set Is"
  have one: "i<length hs \<and> (case hs!i of Var x \<Rightarrow>
      list_all (\<lambda>k. k=i \<or> x\<notin>vars_term (hs!k)) [0..<length hs] \<and>
      list_all (\<lambda>k. k\<in>set Js \<or> x\<notin>vars_term (bs!k)) [0..<length bs]
    | _ \<Rightarrow> False)"
    using checked i unfolding lp_dn_positions_list_def list_all_iff by (rule bspec)
  show "i<length hs \<and> (\<exists>x. hs!i=Var x \<and>
    (\<forall>k<length hs. k\<noteq>i \<longrightarrow> x\<notin>vars_term (hs!k)) \<and>
    (\<forall>k<length bs. k\<notin>set Js \<longrightarrow> x\<notin>vars_term (bs!k)))"
    using one by (cases "hs!i") (auto simp: list_all_iff)
qed

definition lp_dn_terminal where
  "lp_dn_terminal P e c Is sb rb = (c<length P \<and>
    (case snd (P!c) of [] \<Rightarrow> False | b#rest \<Rightarrow>
      fst e=fst (fst (P!c)) \<and> fst b=fst e \<and>
      length (snd e)=length (snd (fst (P!c))) \<and>
      length (snd b)=length (snd e) \<and>
      lp_dn_positions_list (snd (fst (P!c))) (snd b) Is Is \<and>
      list_all (\<lambda>k. k\<in>set Is \<or>
        (snd e!k\<cdot>lp_trace_subst sb=snd (fst (P!c))!k \<and>
         snd b!k\<cdot>lp_trace_subst rb=snd (fst (P!c))!k)) [0..<length (snd e)]))"

lemma lp_dn_terminal_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_dn_terminal P e c Is sb rb"
  shows "\<not>SN_on (lp_ild P) {lp_atom_eval e LPIVar#tail}"
proof -
  obtain b rest where body: "snd (P!c)=b#rest" using ok
    unfolding lp_dn_terminal_def by (auto split: list.splits)
  obtain q es where e: "e=(q,es)" by (cases e) auto
  obtain hs where head: "fst (P!c)=(q,hs)" using ok
    unfolding lp_dn_terminal_def by (cases "fst (P!c)") (auto simp: body e)
  obtain bs where b: "b=(q,bs)" using ok
    unfolding lp_dn_terminal_def by (cases b) (auto simp: body e head)
  have c: "c<length P" and len: "length hs=length bs" "length es=length hs"
    and dn: "lp_dn_positions_list hs bs Is Is"
    and eq: "\<And>k. k<length hs \<Longrightarrow> k\<notin>set Is \<Longrightarrow>
      es!k\<cdot>lp_trace_subst sb=hs!k \<and> bs!k\<cdot>lp_trace_subst rb=hs!k"
    using ok unfolding lp_dn_terminal_def by (auto simp: body e head b list_all_iff)
  show ?thesis unfolding e
    by (rule lp_dn_finite_entry[OF c head body[unfolded b] len lp_dn_positions_list_sound[OF dn]])
      (use eq in auto)
qed

definition lp_source_neutral_check where
  "lp_source_neutral_check P q n positions a0 entry_steps c Is sb rb =
    (fst a0=q \<and> length (snd a0)=n \<and>
     list_all (\<lambda>i. i<n \<and> ground (snd a0!i)) positions \<and>
     (case lp_unify_run P [a0] entry_steps of Some (e#tail) \<Rightarrow>
       lp_dn_terminal P e c Is sb rb | _ \<Rightarrow> False))"

theorem lp_source_neutral_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_source_neutral_check P q n positions a0 entry_steps c Is sb rb"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  obtain e tail where entry: "lp_unify_run P [a0] entry_steps=Some (e#tail)"
    and terminal: "lp_dn_terminal P e c Is sb rb"
    and query: "fst a0=q" "length (snd a0)=n"
      "\<forall>i\<in>set positions. i<n \<and> ground (snd a0!i)"
    using ok unfolding lp_source_neutral_check_def
    by (auto simp: list_all_iff split: option.splits list.splits)
  obtain tail' where path: "([lp_atom_eval a0 LPIVar],
    map (\<lambda>a. lp_atom_eval a LPIVar) (e#tail) @ tail')\<in>(lp_ild P)\<^sup>*"
    using lp_unify_run_sound[OF entry, of "[]"] by auto
  have bad: "\<not>SN_on (lp_ild P) {[lp_atom_eval a0 LPIVar]}"
    using lp_dn_terminal_sound[OF terminal, of "map (\<lambda>a. lp_atom_eval a LPIVar) tail @ tail'"]
      lp_SN_reachable[OF _ path] by auto
  show ?thesis by (rule exI[of _ "snd a0"])
    (use query bad in \<open>simp add: lp_atom_eval_def\<close>)
qed

end
