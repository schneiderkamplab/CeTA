theory LP_PiDP_Source
  imports LP_PiDP_Narrowing LP_Infinite_Resolution
begin

text \<open>The finite continuation stack, not the possibly infinite data,
  supplies the minimality argument for source-to-chain extraction.\<close>

inductive_set lp_itop :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v,'w) lp_iconfig rel"
  for P where
  fact: "c < length P \<Longrightarrow> snd (P!c) = [] \<Longrightarrow>
    (LPICall (lp_atom_eval (fst (P!c)) \<rho>),
     LPIDone (lp_atom_eval (fst (P!c)) \<rho>)) \<in> lp_itop P"
| enter: "c < length P \<Longrightarrow> snd (P!c) \<noteq> [] \<Longrightarrow>
    (LPICall (lp_atom_eval (fst (P!c)) \<rho>),
     LPIWait c 0 \<rho> (LPICall (lp_atom_eval (snd (P!c)!0) \<rho>))) \<in> lp_itop P"
| advance: "c < length P \<Longrightarrow> Suc i < length (snd (P!c)) \<Longrightarrow>
    (LPIWait c i \<rho> (LPIDone (lp_atom_eval (snd (P!c)!i) \<rho>)),
     LPIWait c (Suc i) \<rho> (LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>))) \<in> lp_itop P"
| leave: "c < length P \<Longrightarrow> i < length (snd (P!c)) \<Longrightarrow>
    Suc i = length (snd (P!c)) \<Longrightarrow>
    (LPIWait c i \<rho> (LPIDone (lp_atom_eval (snd (P!c)!i) \<rho>)),
     LPIDone (lp_atom_eval (fst (P!c)) \<rho>)) \<in> lp_itop P"

definition lp_iroot :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v,'w) lp_iconfig rel" where
  "lp_iroot P = {(s,t). \<exists>\<sigma>. (lp_iconfig_subst s \<sigma>,t) \<in> lp_itop P}"

definition lp_iframe :: "('f,'v) lp_clause list \<Rightarrow> ('f,'v,'w) lp_iconfig rel" where
  "lp_iframe P = {(s,t). \<exists>c i \<rho> k k' \<sigma>.
    s = LPIWait c i \<rho> k \<and>
    t = LPIWait c i (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) k' \<and>
    (lp_iconfig_subst k \<sigma>,k') \<in> lp_ilocal P}"

lemma lp_itop_local: "(s,t) \<in> lp_itop P \<Longrightarrow> (s,t) \<in> lp_ilocal P"
  by (induct rule: lp_itop.induct) (auto intro: lp_ilocal.intros)

lemma lp_ilocal_top_or_frame:
  assumes "(s,t) \<in> lp_ilocal P"
  shows "(s,t) \<in> lp_itop P \<or> (\<exists>c i \<rho> k k'.
    s = LPIWait c i \<rho> k \<and> t = LPIWait c i \<rho> k' \<and> (k,k') \<in> lp_ilocal P)"
  using assms by (cases rule: lp_ilocal.cases) (auto intro: lp_itop.intros)

lemma lp_imachine_decompose:
  fixes P :: "('f,'v) lp_clause list"
  shows "(lp_imachine P :: ('f,'v,'w) lp_iconfig rel) = lp_iroot P \<union> lp_iframe P"
proof (rule Set.set_eqI)
  fix z :: "('f,'v,'w) lp_iconfig \<times> ('f,'v,'w) lp_iconfig"
  obtain s t where z: "z=(s,t)" by (cases z) auto
  show "z \<in> lp_imachine P \<longleftrightarrow> z \<in> lp_iroot P \<union> lp_iframe P"
    unfolding z
  proof
    assume "(s,t) \<in> lp_imachine P"
    then obtain \<sigma> where st: "(lp_iconfig_subst s \<sigma>,t) \<in> lp_ilocal P"
      unfolding lp_imachine_def by blast
    from lp_ilocal_top_or_frame[OF st] show "(s,t) \<in> lp_iroot P \<union> lp_iframe P"
      unfolding lp_iroot_def lp_iframe_def by (cases s) auto
  next
    assume "(s,t) \<in> lp_iroot P \<union> lp_iframe P"
    then show "(s,t) \<in> lp_imachine P"
      unfolding lp_iroot_def lp_iframe_def lp_imachine_def
      by (auto intro: lp_itop_local lp_ilocal.frame; blast intro: lp_ilocal.frame)
  qed
qed

fun lp_iactive_child where
  "lp_iactive_child (LPIWait c i \<rho> k) = k"
| "lp_iactive_child s = s"

lemma lp_iframe_child:
  "(s,t) \<in> lp_iframe P \<Longrightarrow>
    (lp_iactive_child s,lp_iactive_child t) \<in> lp_imachine P"
  unfolding lp_iframe_def lp_imachine_def by auto

lemma lp_iframe_SN:
  assumes "SN_on (lp_imachine P) {k}"
  shows "SN_on (lp_iframe P) {LPIWait c i \<rho> k}"
proof (rule SN_onI)
  fix f assume start: "f 0 \<in> {LPIWait c i \<rho> k}" and ch: "chain (lp_iframe P) f"
  have c: "chain (lp_imachine P) (\<lambda>n. lp_iactive_child (f n))"
    using ch lp_iframe_child unfolding chain_def by blast
  have s: "lp_iactive_child (f 0) = k" using start by simp
  have witness: "\<exists>g. g 0 \<in> {k} \<and> chain (lp_imachine P) g"
    by (rule exI[where x="\<lambda>n. lp_iactive_child (f n)"]) (use c s in auto)
  show False using assms witness unfolding SN_on_def by blast
qed

lemma lp_done_SN: "SN_on (lp_imachine P) {LPIDone a}"
proof (rule SN_onI)
  fix f assume start: "f 0 \<in> {LPIDone a}" and ch: "chain (lp_imachine P) f"
  have step: "(f 0,f (Suc 0)) \<in> lp_imachine P" using ch by auto
  obtain \<sigma> where "(lp_iconfig_subst (LPIDone a) \<sigma>, f 1) \<in> lp_ilocal P"
    using start step unfolding lp_imachine_def by auto
  then show False by (auto elim: lp_ilocal.cases)
qed

definition lp_iminimal where
  "lp_iminimal P s = (\<not> SN_on (lp_imachine P) {s} \<and>
    (case s of LPIWait c i \<rho> k \<Rightarrow> SN_on (lp_imachine P) {k} | _ \<Rightarrow> True))"

lemma lp_iminimal_frame_SN:
  "lp_iminimal P s \<Longrightarrow> SN_on (lp_iframe P) {s}"
proof (cases s)
  case (LPIWait c i \<rho> k)
  then show "lp_iminimal P s \<Longrightarrow> SN_on (lp_iframe P) {s}"
    using lp_iframe_SN unfolding lp_iminimal_def by auto
qed (auto simp: lp_iframe_def SN_on_def chain_def intro!: exI[where x=0])

lemma lp_iminimal_first_root:
  assumes minimal: "lp_iminimal P s"
  obtains a b where "(s,a) \<in> (lp_iframe P)\<^sup>*" "(a,b) \<in> lp_iroot P"
    "\<not> SN_on (lp_imachine P) {b}"
proof -
  obtain f where start: "f 0 = s" and steps: "\<forall>i. (f i,f (Suc i)) \<in> lp_imachine P"
    using minimal unfolding lp_iminimal_def by auto
  have fsn: "SN_on (lp_iframe P) {f 0}"
    using lp_iminimal_frame_SN[OF minimal] start by simp
  obtain i where root: "(f i,f (Suc i)) \<in> lp_iroot P"
    and before: "\<And>j. j<i \<Longrightarrow> (f j,f (Suc j)) \<in> lp_iframe P"
    using chain_Un_SN_on_imp_first_step[OF steps[unfolded lp_imachine_decompose] fsn] by blast
  have path: "(s,f i) \<in> (lp_iframe P)\<^sup>*"
    unfolding rtrancl_fun_conv using start before by blast
  have tail: "chain (lp_imachine P) (\<lambda>n. f (Suc i+n))"
    using steps unfolding chain_def by simp
  have witness: "\<exists>g. g 0 \<in> {f (Suc i)} \<and> chain (lp_imachine P) g"
    by (rule exI[where x="\<lambda>n. f (Suc i+n)"]) (use tail in auto)
  have bad: "\<not> SN_on (lp_imachine P) {f (Suc i)}"
    using witness unfolding SN_on_def by blast
  show ?thesis by (rule that[OF path root bad])
qed

fun lp_mark where
  "lp_mark sharp (Var x) = Var x"
| "lp_mark sharp (Fun f ts) = Fun (sharp f) ts"

lemma lp_choose_bad_wait:
  assumes "\<not> SN_on (lp_imachine P) {LPIWait c i \<rho> (LPICall a)}"
  shows "lp_iminimal P (LPIWait c i \<rho> (LPICall a)) \<or> lp_iminimal P (LPICall a)"
  using assms unfolding lp_iminimal_def by auto

context lp_translation
begin

fun mencode where
  "mencode sharp (LPICall a) = lp_itag (sharp \<circ> inp) a"
| "mencode sharp (LPIDone a) = lp_itag (sharp \<circ> out) a"
| "mencode sharp (LPIWait c i \<rho> k) =
    LPIFun (sharp (u c i)) (iencode k # map \<rho> (lp_saved_vars (P!c) i))"

lemma mencode_subst:
  "mencode sharp (lp_iconfig_subst s \<sigma>) = lp_isubst (mencode sharp s) \<sigma>"
  by (cases s) (simp_all add: iencode_subst o_def)

definition entry_pairs where
  "entry_pairs c = (if snd (P!c)=[] then [] else
    [(lp_tag inp (fst (P!c)), wrap c 0 (lp_tag inp (snd (P!c)!0))),
     (lp_tag inp (fst (P!c)), lp_tag inp (snd (P!c)!0))])"

definition return_pairs where
  "return_pairs c i = (if Suc i < length (snd (P!c)) then
    [(wrap c i (lp_tag out (snd (P!c)!i)), wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))),
     (wrap c i (lp_tag out (snd (P!c)!i)), lp_tag inp (snd (P!c)!Suc i))] else [])"

definition pi_pairs where
  "pi_pairs sharp = map (\<lambda>(l,r). (lp_mark sharp l,lp_mark sharp r))
    (concat (map (\<lambda>c. entry_pairs c @ concat (map (return_pairs c) [0..<length (snd (P!c))])) [0..<length P]))"

lemma entry_pair_member:
  "c<length P \<Longrightarrow> (l,r)\<in>set (entry_pairs c) \<Longrightarrow>
    (lp_mark sharp l,lp_mark sharp r) \<in> set (pi_pairs sharp)"
  unfolding pi_pairs_def by force

lemma return_pair_member:
  "c<length P \<Longrightarrow> i<length (snd (P!c)) \<Longrightarrow> (l,r)\<in>set (return_pairs c i) \<Longrightarrow>
    (lp_mark sharp l,lp_mark sharp r) \<in> set (pi_pairs sharp)"
  unfolding pi_pairs_def by force

lemma top_bad_pair:
  assumes top: "(s,t) \<in> lp_itop P" and bad: "\<not> SN_on (lp_imachine P) {t}"
  obtains l r \<rho> k where "(l,r) \<in> set (pi_pairs sharp)"
    "mencode sharp s = lp_ieval l \<rho>" "mencode sharp k = lp_ieval r \<rho>"
    "lp_iminimal P k"
  using top bad
proof (cases rule: lp_itop.cases)
  case (fact c \<rho>)
  then show ?thesis using bad lp_done_SN by blast
next
  case (enter c \<rho>)
  let ?l = "lp_tag inp (fst (P!c))"
  let ?r = "wrap c 0 (lp_tag inp (snd (P!c)!0))"
  let ?b = "lp_tag inp (snd (P!c)!0)"
  have p1: "(lp_mark sharp ?l,lp_mark sharp ?r) \<in> set (pi_pairs sharp)"
    by (rule entry_pair_member[OF enter(3)]) (simp add: entry_pairs_def enter(4))
  have p2: "(lp_mark sharp ?l,lp_mark sharp ?b) \<in> set (pi_pairs sharp)"
    by (rule entry_pair_member[OF enter(3)]) (simp add: entry_pairs_def enter(4))
  have choice: "lp_iminimal P t \<or> lp_iminimal P (LPICall (lp_atom_eval (snd (P!c)!0) \<rho>))"
    using lp_choose_bad_wait[OF bad[unfolded enter(2)]] enter(2) by simp
  from choice show ?thesis
    using that[OF p1, of \<rho> t] that[OF p2, of \<rho> "LPICall (lp_atom_eval (snd (P!c)!0) \<rho>)"]
    by (auto simp: enter(1,2) lp_tag_def lp_itag_def lp_atom_eval_def wrap_def env_def o_def)
next
  case (advance c i \<rho>)
  let ?l = "wrap c i (lp_tag out (snd (P!c)!i))"
  let ?r = "wrap c (Suc i) (lp_tag inp (snd (P!c)!Suc i))"
  let ?b = "lp_tag inp (snd (P!c)!Suc i)"
  have ib: "i<length (snd (P!c))" using advance(4) by simp
  have p1: "(lp_mark sharp ?l,lp_mark sharp ?r) \<in> set (pi_pairs sharp)"
    by (rule return_pair_member[OF advance(3) ib]) (simp add: return_pairs_def advance(4))
  have p2: "(lp_mark sharp ?l,lp_mark sharp ?b) \<in> set (pi_pairs sharp)"
    by (rule return_pair_member[OF advance(3) ib]) (simp add: return_pairs_def advance(4))
  have choice: "lp_iminimal P t \<or> lp_iminimal P (LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>))"
    using lp_choose_bad_wait[OF bad[unfolded advance(2)]] advance(2) by simp
  from choice show ?thesis
    using that[OF p1, of \<rho> t] that[OF p2, of \<rho> "LPICall (lp_atom_eval (snd (P!c)!Suc i) \<rho>)"]
    by (auto simp: advance(1,2) lp_tag_def lp_itag_def lp_atom_eval_def wrap_def env_def o_def)
next
  case (leave c i \<rho>)
  then show ?thesis using bad lp_done_SN by blast
qed

lemma iframe_marked_link:
  assumes "(s,t) \<in> lp_iframe P"
  shows "(mencode sharp s,mencode sharp t) \<in> (lp_pi_link (set translated))\<^sup>*"
proof -
  obtain c i \<rho> k k' \<sigma> where s: "s=LPIWait c i \<rho> k"
    and t: "t=LPIWait c i (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) k'"
    and local: "(lp_iconfig_subst k \<sigma>,k') \<in> lp_ilocal P"
    using assms unfolding lp_iframe_def by blast
  have active: "(iencode (lp_iconfig_subst k \<sigma>),iencode k') \<in> lp_irewrite (set translated)"
    by (rule lp_iactive_irewrite[OF ilocal_simulation[OF local]])
  have lifted: "(lp_isubst (mencode sharp s) \<sigma>,mencode sharp t) \<in> lp_irewrite (set translated)"
    using lp_irewrite.arg[of 0 "iencode (lp_iconfig_subst k \<sigma>) # map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) (lp_saved_vars (P!c) i)"
      "iencode k'" "set translated" "sharp (u c i)"] active
    by (simp add: s t iencode_subst o_def)
  have first: "(mencode sharp s,lp_isubst (mencode sharp s) \<sigma>) \<in> lp_pi_link (set translated)"
    unfolding lp_pi_link_def by blast
  have second: "(lp_isubst (mencode sharp s) \<sigma>,mencode sharp t) \<in> lp_pi_link (set translated)"
    using lifted unfolding lp_pi_link_def by blast
  show ?thesis by (rule rtrancl_into_rtrancl[OF r_into_rtrancl[OF first] second])
qed

lemma iframes_marked_links:
  "(s,t) \<in> (lp_iframe P)\<^sup>* \<Longrightarrow>
    (mencode sharp s,mencode sharp t) \<in> (lp_pi_link (set translated))\<^sup>*"
  by (induct rule: rtrancl_induct) (auto intro: rtrancl_trans iframe_marked_link)

lemma minimal_next_pair:
  fixes a :: "('f,'v) term"
  assumes minimal: "lp_iminimal P s" and pr: "lp_iproject \<pi> (mencode sharp s) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  obtains l r \<rho> k where "(l,r)\<in>set (pi_pairs sharp)"
    "(mencode sharp s,lp_ieval l \<rho>)\<in>(lp_pi_link (set translated))\<^sup>*"
    "mencode sharp k=lp_ieval r \<rho>" "lp_iminimal P k"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b"
    "\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b"
proof -
  obtain x y where path: "(s,x)\<in>(lp_iframe P)\<^sup>*" and root: "(x,y)\<in>lp_iroot P"
    and bad: "\<not> SN_on (lp_imachine P) {y}"
    by (rule lp_iminimal_first_root[OF minimal]) blast
  obtain \<sigma> where top: "(lp_iconfig_subst x \<sigma>,y)\<in>lp_itop P"
    using root unfolding lp_iroot_def by blast
  obtain l r \<rho> k where pair: "(l,r)\<in>set (pi_pairs sharp)"
    and left: "mencode sharp (lp_iconfig_subst x \<sigma>)=lp_ieval l \<rho>"
    and right: "mencode sharp k=lp_ieval r \<rho>" and min: "lp_iminimal P k"
    by (rule top_bad_pair[OF top bad]) blast
  have inst0: "(mencode sharp x,lp_isubst (mencode sharp x) \<sigma>)\<in>lp_pi_link (set translated)"
    unfolding lp_pi_link_def by blast
  have inst: "(mencode sharp x,lp_ieval l \<rho>)\<in>lp_pi_link (set translated)"
    using inst0 left by (simp add: mencode_subst)
  have links: "(mencode sharp s,lp_ieval l \<rho>)\<in>(lp_pi_link (set translated))\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF iframes_marked_links[OF path] inst])
  obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (lp_ieval l \<rho>) b"
    by (rule lp_pi_links_projection[OF links pr rv]) blast
  obtain c :: "('f,'v) term" where pc: "lp_iproject \<pi> (lp_ieval r \<rho>) c"
    by (rule lp_infinite_rule_projection[OF pb dv[OF pair] pair]) blast
  show ?thesis by (rule that[OF pair links right min]) (use pb pc in blast)+
qed

theorem source_to_pi_chain:
  fixes s :: "('f,'v,'w) lp_iconfig" and a :: "('f,'v) term"
  assumes minimal: "lp_iminimal P s" and pr: "lp_iproject \<pi> (mencode sharp s) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "\<exists>ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm). lp_pi_narrow_chain (set (pi_pairs sharp)) (set translated) \<pi> ls rs valuations"
proof -
  let ?good = "\<lambda>(l,r,(\<rho>::'v\<Rightarrow>('f,'w) lp_iterm),k). (l,r)\<in>set (pi_pairs sharp) \<and>
    mencode sharp k=lp_ieval r \<rho> \<and> lp_iminimal P k \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval l \<rho>) b) \<and>
    (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval r \<rho>) b)"
  let ?edge = "\<lambda>(l,r,\<rho>,k) (l',r',\<rho>',k').
    (mencode sharp k,lp_ieval l' \<rho>')\<in>(lp_pi_link (set translated))\<^sup>*"
  have initial: "\<exists>z::('f,'v) term \<times> ('f,'v) term \<times> ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'v,'w) lp_iconfig. ?good z"
  proof -
    obtain l r and \<rho> :: "'v\<Rightarrow>('f,'w) lp_iterm" and k where g: "?good (l,r,\<rho>,k)"
      by (rule minimal_next_pair[OF minimal pr rv dv]) auto
    show ?thesis by (rule exI[where x="(l,r,\<rho>,k)"], rule g)
  qed
  have progress: "\<And>z. ?good z \<Longrightarrow> \<exists>z'. ?good z' \<and> ?edge z z'"
  proof -
    fix z :: "('f,'v) term \<times> ('f,'v) term \<times> ('v\<Rightarrow>('f,'w) lp_iterm) \<times> ('f,'v,'w) lp_iconfig"
    assume g: "?good z"
    obtain l r \<rho> k where z: "z=(l,r,\<rho>,k)" by (cases z) auto
    have min: "lp_iminimal P k" and right: "mencode sharp k=lp_ieval r \<rho>"
      using g by (simp_all add: z)
    obtain b :: "('f,'v) term" where pb: "lp_iproject \<pi> (mencode sharp k) b"
      using g right by (auto simp: z)
    obtain l' r' \<rho>' k' where g': "?good (l',r',\<rho>',k')" and e: "?edge z (l',r',\<rho>',k')"
      by (rule minimal_next_pair[OF min pb rv dv]) (auto simp: z)
    show "\<exists>z'. ?good z' \<and> ?edge z z'"
      by (rule exI[where x="(l',r',\<rho>',k')"]) (use g' e in simp)
  qed
  have seq: "\<exists>z. \<forall>i::nat. ?good (z i) \<and> ?edge (z i) (z (Suc i))"
    by (rule dependent_nat_choice[where P="\<lambda>n z. ?good z" and Q="\<lambda>n z z'. ?edge z z'", OF initial])
       (rule progress)
  obtain z where seq_z: "\<forall>i::nat. ?good (z i) \<and> ?edge (z i) (z (Suc i))"
    using seq by (rule exE)
  have good: "\<And>i::nat. ?good (z i)" and edge: "\<And>i::nat. ?edge (z i) (z (Suc i))"
    using seq_z by simp_all
  let ?ls = "\<lambda>i. fst (z i)"
  let ?rs = "\<lambda>i. fst (snd (z i))"
  let ?vals = "\<lambda>i. fst (snd (snd (z i)))"
  have chain: "lp_pi_narrow_chain (set (pi_pairs sharp)) (set translated) \<pi> ?ls ?rs ?vals"
    unfolding lp_pi_narrow_chain_def
  proof (intro allI)
    fix i
    show "(?ls i,?rs i)\<in>set (pi_pairs sharp) \<and>
      (lp_ieval (?rs i) (?vals i),lp_ieval (?ls (Suc i)) (?vals (Suc i)))\<in>(lp_pi_link (set translated))\<^sup>* \<and>
      (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval (?ls i) (?vals i)) b) \<and>
      (\<exists>b::('f,'v) term. lp_iproject \<pi> (lp_ieval (?rs i) (?vals i)) b)"
      using good[of i] edge[of i] by (auto simp: case_prod_beta)
  qed
  show ?thesis by (rule exI[of _ ?ls], rule exI[of _ ?rs], rule exI[of _ ?vals], rule chain)
qed

corollary pi_chains_imply_source_termination:
  fixes a :: "('f,'v) term" and query :: "('f,'w) lp_iatom"
  assumes no_chain: "\<And>ls rs (valuations::nat\<Rightarrow>'v\<Rightarrow>('f,'w) lp_iterm). \<not> lp_pi_narrow_chain (set (pi_pairs sharp)) (set translated) \<pi> ls rs valuations"
    and pr: "lp_iproject \<pi> (mencode sharp (LPICall query)) a"
    and rv: "\<And>l r. (l,r)\<in>set translated \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
    and dv: "\<And>l r. (l,r)\<in>set (pi_pairs sharp) \<Longrightarrow> vars_term (af_term \<pi> r) \<subseteq> vars_term (af_term \<pi> l)"
  shows "SN_on (lp_ild P) {[query]}"
proof -
  have machine: "SN_on (lp_imachine P) {LPICall query}"
  proof (rule ccontr)
    assume "\<not> SN_on (lp_imachine P) {LPICall query}"
    then have min: "lp_iminimal P (LPICall query)" unfolding lp_iminimal_def by simp
    show False using source_to_pi_chain[OF min pr rv dv] no_chain by blast
  qed
  show ?thesis using lp_imachine_implies_ld_termination[OF machine] by simp
qed

end

declare lp_translation.entry_pairs_def[code]
declare lp_translation.return_pairs_def[code]
declare lp_translation.pi_pairs_def[code]

end
