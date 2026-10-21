theory LP_Source_Tree
  imports LP_Source_Loop
begin

definition lp_equations where
  "lp_equations es \<rho> = list_all (\<lambda>(s,t). lp_ieval s \<rho> = lp_ieval t \<rho>) es"

fun lp_eliminate where
  "lp_eliminate x t y = (if x=y then t else Var y)"

fun lp_normalize_goals where
  "lp_normalize_goals 0 es gs = None"
| "lp_normalize_goals (Suc fuel) [] gs = Some (Some gs)"
| "lp_normalize_goals (Suc fuel) ((Var x,t)#es) gs =
    (if t=Var x then lp_normalize_goals fuel es gs else
      lp_normalize_goals fuel (map (\<lambda>(l,r). (l\<cdot>lp_eliminate x t,r\<cdot>lp_eliminate x t)) es)
        (map (\<lambda>a. lp_atom_subst a (lp_eliminate x t)) gs))"
| "lp_normalize_goals (Suc fuel) ((Fun f ss,Var x)#es) gs =
    lp_normalize_goals fuel ((Var x,Fun f ss)#es) gs"
| "lp_normalize_goals (Suc fuel) ((Fun f ss,Fun g ts)#es) gs =
    (if f=g \<and> length ss=length ts then lp_normalize_goals fuel (zip ss ts@es) gs else Some None)"

declare lp_normalize_goals.simps[code del]

lemma lp_normalize_goals_code[code]:
  "lp_normalize_goals fuel es gs = (if fuel=0 then None else
    case es of []\<Rightarrow>Some (Some gs) | (s,t)#rest\<Rightarrow>
      (case s of Var x\<Rightarrow>
        (if t=Var x then lp_normalize_goals (fuel-1) rest gs else
          lp_normalize_goals (fuel-1)
            (map (\<lambda>(l,r). (l\<cdot>lp_eliminate x t,r\<cdot>lp_eliminate x t)) rest)
            (map (\<lambda>a. lp_atom_subst a (lp_eliminate x t)) gs))
      | Fun f ss\<Rightarrow>(case t of Var x\<Rightarrow>
          lp_normalize_goals (fuel-1) ((Var x,Fun f ss)#rest) gs
        | Fun g ts\<Rightarrow>(if f=g \<and> length ss=length ts then
          lp_normalize_goals (fuel-1) (zip ss ts@rest) gs else Some None))))"
  by (cases fuel; cases es) (auto split: term.splits prod.splits)

lemma lp_ieval_finite_subst:
  "lp_ieval (s\<cdot>\<sigma>) \<rho> = lp_ieval s (\<lambda>x. lp_ieval (\<sigma> x) \<rho>)"
  by (induct s) (auto intro!: map_cong)

lemma lp_eliminate_eval:
  assumes "\<rho> x = lp_ieval t \<rho>"
  shows "lp_ieval (s\<cdot>lp_eliminate x t) \<rho> = lp_ieval s \<rho>"
proof -
  have "(\<lambda>y. lp_ieval (lp_eliminate x t y) \<rho>) = \<rho>"
    by (rule ext) (use assms in auto)
  then show ?thesis by (simp add: lp_ieval_finite_subst)
qed

lemma lp_eliminate_atom:
  assumes "\<rho> x = lp_ieval t \<rho>"
  shows "lp_atom_eval (lp_atom_subst a (lp_eliminate x t)) \<rho> = lp_atom_eval a \<rho>"
  using assms by (simp add: lp_atom_eval_def lp_atom_subst_def map_map o_def lp_eliminate_eval)

theorem lp_normalize_goals_sound:
  assumes checked: "lp_normalize_goals fuel es gs = Some result"
    and eqs: "lp_equations es \<rho>"
  shows "\<exists>hs. result=Some hs \<and> map (\<lambda>a. lp_atom_eval a \<rho>) hs = map (\<lambda>a. lp_atom_eval a \<rho>) gs"
  using checked eqs
proof (induct fuel es gs arbitrary: result rule: lp_normalize_goals.induct)
  case (1 es gs) then show ?case by simp
next
  case (2 fuel gs) then show ?case by auto
next
  case (3 fuel x t es gs)
  have eq: "\<rho> x=lp_ieval t \<rho>" and rest: "lp_equations es \<rho>"
    using "3.prems"(2) by (simp_all add: lp_equations_def)
  have replaced: "lp_equations (map (\<lambda>(l,r). (l\<cdot>lp_eliminate x t,r\<cdot>lp_eliminate x t)) es) \<rho>"
    using rest by (simp add: lp_equations_def list_all_iff lp_eliminate_eval[OF eq] case_prod_unfold)
  show ?case
    using "3.hyps" "3.prems"(1) rest replaced
    by (cases "t=Var x") (auto simp: o_def lp_eliminate_atom[OF eq])
next
  case (4 fuel f ss x es gs)
  have "lp_equations ((Var x,Fun f ss)#es) \<rho>"
    using "4.prems"(2) by (auto simp: lp_equations_def)
  then show ?case using "4.hyps" "4.prems"(1) by simp
next
  case (5 fuel f ss g ts es gs)
  have fg: "f=g" and len: "length ss=length ts"
    and maps: "map (\<lambda>t. lp_ieval t \<rho>) ss = map (\<lambda>t. lp_ieval t \<rho>) ts"
    and rest: "lp_equations es \<rho>"
    using "5.prems"(2) by (auto simp: lp_equations_def dest: arg_cong[where f=length])
  have same: "\<And>i. i<length ts \<Longrightarrow> lp_ieval (ss!i) \<rho> = lp_ieval (ts!i) \<rho>"
  proof -
    fix i assume "i<length ts"
    then show "lp_ieval (ss!i) \<rho> = lp_ieval (ts!i) \<rho>"
      using arg_cong[OF maps, of "\<lambda>xs. xs!i"] len by simp
  qed
  have "lp_equations (zip ss ts@es) \<rho>"
    using same len rest by (auto simp: lp_equations_def list_all_iff set_zip)
  then show ?case using "5.hyps" "5.prems"(1) fg len by simp
qed

definition lp_prefix where "lp_prefix k x = replicate k (CHR ''$'') @ x"
definition lp_rename_atom where
  "lp_rename_atom k a = lp_atom_subst a (\<lambda>x. Var (lp_prefix k x))"
definition lp_short_goals where
  "lp_short_goals k gs = list_all (\<lambda>a. list_all (\<lambda>t.
    \<forall>x\<in>vars_term t. length x<k) (snd a)) gs"

lemma lp_ieval_cong:
  "(\<And>x. x\<in>vars_term t \<Longrightarrow> \<rho> x=\<sigma> x) \<Longrightarrow> lp_ieval t \<rho>=lp_ieval t \<sigma>"
  by (induct t) (auto intro!: map_cong)

lemma lp_fresh_atom_eval:
  "lp_atom_eval (lp_rename_atom k a) (\<lambda>x. if length x<k then \<rho> x else \<sigma> (drop k x)) = lp_atom_eval a \<sigma>"
  by (simp add: lp_rename_atom_def lp_atom_eval_finite_subst lp_prefix_def)

lemma lp_old_goals_eval:
  assumes "lp_short_goals k gs"
  shows "map (\<lambda>a. lp_atom_eval a (\<lambda>x. if length x<k then \<rho> x else \<sigma> (drop k x))) gs = map (\<lambda>a. lp_atom_eval a \<rho>) gs"
  using assms unfolding lp_short_goals_def lp_atom_eval_def
  by (auto simp: list_all_iff intro!: map_cong lp_ieval_cong)

definition lp_symbolic_sn :: "('f,string) lp_clause list \<Rightarrow> ('f,string) lp_atom list \<Rightarrow> bool" where
  "lp_symbolic_sn P gs = (\<forall>\<rho>::string\<Rightarrow>('f,string) lp_iterm. SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) gs})"

lemma lp_symbolic_empty: "lp_symbolic_sn P []"
  unfolding lp_symbolic_sn_def list.map
  by (intro allI, rule step_reflects_SN_on) (auto elim: lp_ild.cases)

lemma lp_ild_cons_cases:
  assumes "(a#gs,hs)\<in>lp_ild P"
  obtains c \<sigma> \<nu> where "c<length P"
    "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) gs"
  using assms by (cases rule: lp_ild.cases) auto

definition lp_source_branch where
  "lp_source_branch fuel k gs c = (case gs of []\<Rightarrow>None | a#rest\<Rightarrow>
    lp_normalize_goals fuel [(lp_tag id a,lp_tag id (lp_rename_atom k (fst c)))]
      (map (lp_rename_atom k) (snd c) @ rest))"

theorem lp_symbolic_resolve:
  fixes P :: "('f,string) lp_clause list"
  assumes fresh: "lp_short_goals k gs"
    and checked: "\<And>c. c\<in>set P \<Longrightarrow> \<exists>result. lp_source_branch fuel k gs c=Some result \<and>
      (\<forall>hs. result=Some hs \<longrightarrow> lp_symbolic_sn P hs)"
    and nonempty: "gs\<noteq>[]"
  shows "lp_symbolic_sn P gs"
proof (unfold lp_symbolic_sn_def, intro allI)
  fix \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  show "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) gs}"
  proof (rule step_reflects_SN_on)
    fix hs assume step: "(map (\<lambda>a. lp_atom_eval a \<rho>) gs,hs)\<in>lp_ild P"
    obtain a rest where gs: "gs=a#rest" using nonempty by (cases gs) auto
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
      using arg_cong[OF head, of "lp_itag id"]
      by (simp add: lp_equations_def lp_itag_eval)
    obtain result where check: "lp_source_branch fuel k gs (P!c)=Some result"
      and sn: "\<And>xs. result=Some xs \<Longrightarrow> lp_symbolic_sn P xs"
      using checked[OF nth_mem[OF c]] by blast
    have normalized: "lp_normalize_goals fuel
      [(lp_tag id a,lp_tag id (lp_rename_atom k (fst (P!c))))]
      (map (lp_rename_atom k) (snd (P!c)) @ rest) = Some result"
      using check by (simp only: lp_source_branch_def gs list.case)
    obtain xs where result: "result=Some xs"
      and projected: "map (\<lambda>b. lp_atom_eval b ?env) xs =
        map (\<lambda>b. lp_atom_eval b ?env) (map (lp_rename_atom k) (snd (P!c)) @ rest)"
      using lp_normalize_goals_sound[OF normalized equations] by blast
    have target: "map (\<lambda>b. lp_atom_eval b ?env) xs = hs"
      using projected old lp_fresh_atom_eval[of k _ ?old \<nu>]
      by (auto simp: gs hs o_def)
    have "SN_on (lp_ild P) {map (\<lambda>b. lp_atom_eval b ?env) xs}"
      using sn[OF result, unfolded lp_symbolic_sn_def] by (rule spec)
    then show "SN_on (lp_ild P) {hs}" by (simp only: target)
  qed
qed

datatype lp_source_tree = LPSourceNode nat "lp_source_tree option list"

fun lp_check_source_tree where
  "lp_check_source_tree 0 fuel P gs tree = False"
| "lp_check_source_tree (Suc budget) fuel P gs (LPSourceNode k children) =
    (if gs=[] then children=[] else lp_short_goals k gs \<and> length children=length P \<and>
      list_all (\<lambda>i. case lp_source_branch fuel k gs (P!i) of
        None\<Rightarrow>False
      | Some None\<Rightarrow>children!i=None
      | Some (Some hs)\<Rightarrow>(case children!i of None\<Rightarrow>False | Some child\<Rightarrow>
          lp_check_source_tree budget fuel P hs child)) [0..<length P])"

theorem lp_check_source_tree_sound:
  "lp_check_source_tree budget fuel P gs tree \<Longrightarrow> lp_symbolic_sn P gs"
proof (induct budget arbitrary: gs tree)
  case 0 then show ?case by simp
next
  case (Suc budget)
  obtain k children where tree: "tree=LPSourceNode k children" by (cases tree) auto
  show ?case
  proof (cases "gs=[]")
    case True then show ?thesis by (simp add: lp_symbolic_empty)
  next
    case False
    have fresh: "lp_short_goals k gs" and len: "length children=length P"
      and all: "\<And>i. i<length P \<Longrightarrow> (case lp_source_branch fuel k gs (P!i) of
        None\<Rightarrow>False | Some None\<Rightarrow>children!i=None |
        Some (Some hs)\<Rightarrow>(case children!i of None\<Rightarrow>False | Some child\<Rightarrow>
          lp_check_source_tree budget fuel P hs child))"
      using Suc.prems by (auto simp: tree False list_all_iff)
    show ?thesis
    proof (rule lp_symbolic_resolve[OF fresh _ False])
      fix c assume "c\<in>set P"
      then obtain i where i: "i<length P" "P!i=c" by (auto simp: in_set_conv_nth)
      show "\<exists>result. lp_source_branch fuel k gs c=Some result \<and>
        (\<forall>hs. result=Some hs \<longrightarrow> lp_symbolic_sn P hs)"
        using all[OF i(1)] Suc.hyps
        by (cases "lp_source_branch fuel k gs c"; cases "children!i")
          (auto simp: i(2) split: option.splits)
    qed
  qed
qed

end
