theory LP_Finite_Neutral_Witness
  imports LP_Finite_Trace_Witness
begin
lemma lp_finite_eval_cong:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> sigma x=rho x) \<Longrightarrow> t\<cdot>sigma=t\<cdot>rho"
  by (induct t) auto
lemma lp_finite_eval_subst:
  "t\<cdot>rho\<cdot>sigma=t\<cdot>(\<lambda>x. rho x\<cdot>sigma)"
  by (induct t) (auto simp: map_map o_def)

lemma lp_finite_dn_update_head:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I"
    and var: "hs!i=Var x" and k: "k<length hs" "k\<noteq>i"
  shows "lp_finite_eval (hs!k) (\<rho>(x:=v)) = lp_finite_eval (hs!k) \<rho>"
proof (rule lp_finite_eval_cong)
  fix y assume y: "y\<in>vars_term (hs!k)"
  have "x\<notin>vars_term (hs!k)"
    using dn i var k unfolding lp_dn_positions_def by auto
  then show "(\<rho>(x:=v)) y=\<rho> y" using y by auto
qed


lemma lp_finite_dn_update_retained_body:
  assumes dn: "lp_dn_positions hs bs I J" and i: "i\<in>I"
    and var: "hs!i=Var x" and k: "k<length bs" "k\<notin>J"
  shows "lp_finite_eval (bs!k) (\<rho>(x:=v)) = lp_finite_eval (bs!k) \<rho>"
proof (rule lp_finite_eval_cong)
  fix y assume y: "y\<in>vars_term (bs!k)"
  have "x\<notin>vars_term (bs!k)"
    using dn i var k unfolding lp_dn_positions_def by auto
  then show "(\<rho>(x:=v)) y=\<rho> y" using y by auto
qed


lemma lp_finite_dn_env_retained:
  assumes dn: "lp_dn_positions hs bs I J" and k: "k<length bs" "k\<notin>J"
  shows "lp_finite_eval (bs!k) (lp_dn_env hs I vals \<rho>)=lp_finite_eval (bs!k) \<rho>"
proof (rule lp_finite_eval_cong)
  fix x assume x: "x\<in>vars_term (bs!k)"
  show "lp_dn_env hs I vals \<rho> x=\<rho> x"
  proof (rule lp_dn_env_outside)
    fix i assume i: "i\<in>I"
    show "hs!i\<noteq>Var x" using dn i k x unfolding lp_dn_positions_def by auto
  qed
qed


lemma lp_finite_dn_env_head:
  assumes dn: "lp_dn_positions hs bs I J" and k: "k<length hs"
  shows "lp_finite_eval (hs!k) (lp_dn_env hs I vals \<rho>) =
    (if k\<in>I then vals!k else lp_finite_eval (hs!k) \<rho>)"
proof (cases "k\<in>I")
  case True
  obtain x where var: "hs!k=Var x" using dn True unfolding lp_dn_positions_def by auto
  show ?thesis using lp_dn_env_selected[OF dn True var, of vals \<rho>] by (simp add: var True)
next
  case False
  have eq: "lp_finite_eval (hs!k) (lp_dn_env hs I vals \<rho>)=lp_finite_eval (hs!k) \<rho>"
  proof (rule lp_finite_eval_cong)
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


definition lp_finite_dn_agrees where
  "lp_finite_dn_agrees I bs us = (length us=length bs \<and>
    (\<forall>k<length bs. k\<notin>I \<longrightarrow> us!k=lp_finite_eval (bs!k) Var))"


lemma lp_finite_dn_step:
  fixes P :: "('f,'v) lp_clause list"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs" "length us=length hs"
    and dn: "lp_dn_positions hs bs I I"
    and matched: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_finite_eval (us!k) \<sigma> = lp_finite_eval (hs!k) Var"
  obtains vs tail' where
    "((q,us)#tail,(q,vs)#tail')\<in>lp_ld P" "lp_finite_dn_agrees I bs vs"
proof -
  let ?vals = "map (\<lambda>t. lp_finite_eval t \<sigma>) us"
  let ?env = "lp_dn_env hs I ?vals Var"
  have eq: "?vals=map (\<lambda>t. lp_finite_eval t ?env) hs"
  proof (rule nth_equalityI)
    show "length ?vals=length (map (\<lambda>t. lp_finite_eval t ?env) hs)" using len by simp
    fix k assume k: "k<length ?vals"
    have kh: "k<length hs" using k len by simp
    show "?vals!k=map (\<lambda>t. lp_finite_eval t ?env) hs!k"
      using lp_finite_dn_env_head[OF dn kh, of ?vals Var] matched[OF kh] k kh
      by (auto simp: nth_map)
  qed
  have match: "lp_atom_subst (q,us) \<sigma>=lp_finite_atom_eval (fst (P!c)) ?env"
    using eq by (simp add: head lp_atom_subst_def lp_atom_subst_def)
  let ?vs = "map (\<lambda>t. lp_finite_eval t ?env) bs"
  let ?tail = "map (\<lambda>a. lp_finite_atom_eval a ?env) rest @
    map (\<lambda>a. lp_atom_subst a \<sigma>) tail"
  have step: "((q,us)#tail,(q,?vs)#?tail)\<in>lp_ld P"
    using lp_ld.resolve[OF c match, of tail] by (simp add: body lp_atom_subst_def)
  have agrees: "lp_finite_dn_agrees I bs ?vs"
    unfolding lp_finite_dn_agrees_def
    using lp_finite_dn_env_retained[OF dn, of _ ?vals Var] by auto
  show thesis by (rule that[OF step agrees])
qed


theorem lp_finite_dn_binary_loop:
  fixes P :: "('f,'v) lp_clause list" and \<tau> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs"
    and dn: "lp_dn_positions hs bs I I"
    and repeat: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> bs!k\<cdot>\<tau>=hs!k"
    and entry: "lp_finite_dn_agrees I bs us"
  shows "\<not>SN_on (lp_ld P) {(q,us)#tail}"
proof (rule lp_serial_not_SN[where X="{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_finite_dn_agrees I bs us}"])
  show "(q,us)#tail\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_finite_dn_agrees I bs us}"
    using entry by auto
next
  fix gs assume member: "gs\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_finite_dn_agrees I bs us}"
  then obtain us tail where gs: "gs=(q,us)#tail" and agrees: "lp_finite_dn_agrees I bs us" by auto
  let ?sigma = "\<lambda>x. lp_finite_eval (\<tau> x) Var"
  have length: "length us=length hs" using agrees len unfolding lp_finite_dn_agrees_def by simp
  have match: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_finite_eval (us!k) ?sigma=lp_finite_eval (hs!k) Var"
  proof -
    fix k assume k: "k<length hs" "k\<notin>I"
    have us: "us!k=lp_finite_eval (bs!k) Var" using agrees k len unfolding lp_finite_dn_agrees_def by auto
    show "lp_finite_eval (us!k) ?sigma=lp_finite_eval (hs!k) Var"
      using arg_cong[OF repeat[OF k], of "\<lambda>t. lp_finite_eval t Var"]
      by (simp add: us lp_finite_eval_subst lp_finite_eval_subst)
  qed
  obtain vs tail' where step: "((q,us)#tail,(q,vs)#tail')\<in>lp_ld P"
    and closed: "lp_finite_dn_agrees I bs vs"
    by (rule lp_finite_dn_step[OF c head body len length dn match]) auto
  show "\<exists>t\<in>{gs. \<exists>us tail. gs=(q,us)#tail \<and> lp_finite_dn_agrees I bs us}. (gs,t)\<in>lp_ld P"
    using step closed unfolding gs by auto
qed


theorem lp_finite_dn_finite_entry:
  fixes P :: "('f,'v) lp_clause list" and \<tau> \<sigma> :: "'v\<Rightarrow>('f,'v) term"
  assumes c: "c<length P" and head: "fst (P!c)=(q,hs)"
    and body: "snd (P!c)=(q,bs)#rest"
    and len: "length hs=length bs" "length es=length hs"
    and dn: "lp_dn_positions hs bs I I"
    and repeat: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> bs!k\<cdot>\<tau>=hs!k"
    and enter: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow> es!k\<cdot>\<sigma>=hs!k"
  shows "\<not>SN_on (lp_ld P) {lp_finite_atom_eval (q,es) Var#tail}"
proof -
  let ?us = "map (\<lambda>t. lp_finite_eval t Var) es"
  let ?sigma = "\<lambda>x. lp_finite_eval (\<sigma> x) Var"
  have length: "length ?us=length hs" using len by simp
  have match: "\<And>k. k<length hs \<Longrightarrow> k\<notin>I \<Longrightarrow>
      lp_finite_eval (?us!k) ?sigma=lp_finite_eval (hs!k) Var"
  proof -
    fix k assume k: "k<length hs" "k\<notin>I"
    show "lp_finite_eval (?us!k) ?sigma=lp_finite_eval (hs!k) Var"
      using arg_cong[OF enter[OF k], of "\<lambda>t. lp_finite_eval t Var"] k len
      by (simp add: lp_finite_eval_subst lp_finite_eval_subst)
  qed
  obtain vs tail' where step: "((q,?us)#tail,(q,vs)#tail')\<in>lp_ld P"
    and closed: "lp_finite_dn_agrees I bs vs"
    by (rule lp_finite_dn_step[OF c head body len(1) length dn match]) auto
  have bad: "\<not>SN_on (lp_ld P) {(q,vs)#tail'}"
    by (rule lp_finite_dn_binary_loop[OF c head body len(1) dn repeat closed])
  show ?thesis using bad lp_SN_reachable[OF _ r_into_rtrancl[OF step]]
    by (auto simp: lp_atom_subst_def)
qed


lemma lp_finite_dn_terminal_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_dn_terminal P e c Is sb rb"
  shows "\<not>SN_on (lp_ld P) {lp_finite_atom_eval e Var#tail}"
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
    by (rule lp_finite_dn_finite_entry[OF c head body[unfolded b] len lp_dn_positions_list_sound[OF dn]])
      (use eq in auto)
qed


theorem lp_finite_source_neutral_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_source_neutral_check P q n positions a0 entry_steps c Is sb rb"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> (\<forall>i\<in>set positions. i<n \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  obtain e tail where entry: "lp_unify_run P [a0] entry_steps=Some (e#tail)"
    and terminal: "lp_dn_terminal P e c Is sb rb"
    and query: "fst a0=q" "length (snd a0)=n"
      "\<forall>i\<in>set positions. i<n \<and> ground (snd a0!i)"
    using ok unfolding lp_source_neutral_check_def
    by (auto simp: list_all_iff split: option.splits list.splits)
  obtain tail' where path: "([lp_finite_atom_eval a0 Var],
    map (\<lambda>a. lp_finite_atom_eval a Var) (e#tail) @ tail')\<in>(lp_ld P)\<^sup>*"
    using lp_finite_unify_run_sound[OF entry, of "[]"] by auto
  have bad: "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval a0 Var]}"
    using lp_finite_dn_terminal_sound[OF terminal, of "map (\<lambda>a. lp_finite_atom_eval a Var) tail @ tail'"]
      lp_SN_reachable[OF _ path] by auto
  show ?thesis by (rule exI[of _ "snd a0"])
    (use query bad in \<open>simp add: lp_atom_subst_def\<close>)
qed


end
