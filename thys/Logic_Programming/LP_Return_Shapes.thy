theory LP_Return_Shapes
  imports LP_Answer_Groundness
begin

text \<open>Observations of actual successful returns may retain a finite
constructor spine while leaving other fields unconstrained. These predicates
use the existing infinitary runtime terms and successful-answer semantics.
An unconstrained field may contain a rational cycle. Recursive shape evidence
is inductive: a finite representation of a cycle is not a finite spine.\<close>

datatype lp_return_shape = LPReturnAny | LPReturnGround | LPReturnShape nat

type_synonym 'f lp_return_grammar = "('f \<times> lp_return_shape list) list list"

inductive lp_return_shape_holds ::
  "'f lp_return_grammar \<Rightarrow> lp_return_shape \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> bool"
  for G where
  any: "lp_return_shape_holds G LPReturnAny t"
| ground: "lp_seg_ground t \<Longrightarrow> lp_return_shape_holds G LPReturnGround t"
| node: "i<length G \<Longrightarrow> (f,shapes)\<in>set (G!i) \<Longrightarrow>
    length shapes=length ts \<Longrightarrow>
    (\<And>j. j<length ts \<Longrightarrow> lp_return_shape_holds G (shapes!j) (ts!j)) \<Longrightarrow>
    lp_return_shape_holds G (LPReturnShape i) (LPIFun f ts)"

lemma lp_return_ground_exact:
  "lp_return_shape_holds G LPReturnGround t \<longleftrightarrow> lp_seg_ground t"
  by (auto elim: lp_return_shape_holds.cases intro: lp_return_shape_holds.ground)

lemma lp_return_shape_node:
  "lp_return_shape_holds G (LPReturnShape i) t \<Longrightarrow>
   \<exists>f shapes ts. t=LPIFun f ts \<and> i<length G \<and>
     (f,shapes)\<in>set (G!i) \<and> length shapes=length ts \<and>
     (\<forall>j<length ts. lp_return_shape_holds G (shapes!j) (ts!j))"
  by (cases rule: lp_return_shape_holds.cases) auto

lemma lp_return_shape_subst:
  fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  shows "lp_return_shape_holds G shape t \<Longrightarrow>
   lp_return_shape_holds G shape (lp_isubst t sigma)"
proof (induct rule: lp_return_shape_holds.induct)
  case (any t)
  then show ?case by (rule lp_return_shape_holds.any)
next
  case (ground t)
  then show ?case by (simp add: lp_seg_ground_subst lp_return_ground_exact)
next
  case (node i f shapes ts)
  show ?case
    by (simp only: lp_isubst_Fun; rule lp_return_shape_holds.node)
      (use node in auto)
qed

definition lp_return_shape_known where
  "lp_return_shape_known G known rho =
    (\<forall>(shape,x)\<in>set known. lp_return_shape_holds G shape (rho x))"

fun lp_return_shape_check where
  "lp_return_shape_check 0 G known shape t = False"
| "lp_return_shape_check (Suc fuel) G known LPReturnAny t = True"
| "lp_return_shape_check (Suc fuel) G known LPReturnGround t =
    (\<forall>x\<in>vars_term t. (LPReturnGround,x)\<in>set known)"
| "lp_return_shape_check (Suc fuel) G known (LPReturnShape i) (Var x) =
    ((LPReturnShape i,x)\<in>set known)"
| "lp_return_shape_check (Suc fuel) G known (LPReturnShape i) (Fun f ts) =
    (i<length G \<and> list_ex (\<lambda>(g,shapes). f=g \<and>
      list_all2 (lp_return_shape_check fuel G known) shapes ts) (G!i))"

theorem lp_return_shape_check_sound:
  assumes checked: "lp_return_shape_check fuel G known shape t"
    and known: "lp_return_shape_known G known rho"
  shows "lp_return_shape_holds G shape (lp_ieval t rho)"
  using checked
proof (induct fuel arbitrary: shape t)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases shape)
    case LPReturnAny
    show ?thesis unfolding LPReturnAny by (rule lp_return_shape_holds.any)
  next
    case LPReturnGround
    have ground: "lp_seg_ground (rho x)" if "x\<in>vars_term t" for x
      using known Suc.prems that LPReturnGround
      by (fastforce simp: lp_return_shape_known_def lp_return_ground_exact)
    show ?thesis using ground LPReturnGround
      by (simp add: lp_return_ground_exact lp_seg_ground_eval)
  next
    case (LPReturnShape i)
    show ?thesis
    proof (cases t)
      case (Var x)
      then show ?thesis using known Suc.prems LPReturnShape
        by (fastforce simp: lp_return_shape_known_def)
    next
      case (Fun f ts)
      obtain shapes where index: "i<length G" and member: "(f,shapes)\<in>set (G!i)"
        and children: "list_all2 (lp_return_shape_check fuel G known) shapes ts"
        using Suc.prems LPReturnShape Fun by (auto simp: list_ex_iff)
      have lengths: "length shapes=length ts" using children by (rule list_all2_lengthD)
      have child: "lp_return_shape_holds G (shapes!j) (lp_ieval (ts!j) rho)"
        if "j<length ts" for j
        using Suc.hyps children that by (auto simp: list_all2_conv_all_nth)
      show ?thesis unfolding LPReturnShape Fun
        by (simp only: lp_ieval.simps; rule lp_return_shape_holds.node[OF index member])
          (use lengths child in auto)
    qed
  qed
qed

text \<open>These contracts describe only successful answers. They do not
assert termination of a helper or authorize omitting later answers.\<close>
definition lp_return_shape_contract where
  "lp_return_shape_contract G inputs outputs a =
    (length inputs=length (snd a) \<and> length outputs=length (snd a) \<and>
      (list_all2 (lp_return_shape_holds G) inputs (snd a) \<longrightarrow>
       list_all2 (lp_return_shape_holds G) outputs (snd a)))"

definition lp_return_contracts where
  "lp_return_contracts G contracts a =
    (\<forall>(f,inputs,outputs)\<in>set contracts. fst a=f \<longrightarrow>
      lp_return_shape_contract G inputs outputs a)"

definition lp_return_shape_model ::
  "('f,'v) lp_clause list \<Rightarrow> 'f lp_return_grammar \<Rightarrow>
    ('f \<times> lp_return_shape list \<times> lp_return_shape list) list \<Rightarrow> bool" where
  "lp_return_shape_model P G contracts =
    (\<forall>a::('f,'v) lp_iatom. lp_answer_model P a \<longrightarrow> lp_return_contracts G contracts a)"

definition lp_return_shape_clause ::
  "'f lp_return_grammar \<Rightarrow> ('f \<times> lp_return_shape list \<times> lp_return_shape list) list \<Rightarrow>
    ('f,'v) lp_clause \<Rightarrow> bool" where
  "lp_return_shape_clause G contracts c = (\<forall>rho::'v \<Rightarrow> ('f,'v) lp_iterm.
    (\<forall>b\<in>set (snd c). lp_return_contracts G contracts (lp_atom_eval b rho)) \<longrightarrow>
      lp_return_contracts G contracts (lp_atom_eval (fst c) rho))"

theorem lp_return_shape_clause_cover_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes covered: "\<And>c. c\<in>set P \<Longrightarrow> lp_return_shape_clause G contracts c"
  shows "lp_return_shape_model P G contracts"
proof -
  have "lp_answer_model P a \<Longrightarrow> lp_return_contracts G contracts a" for a :: "('f,'v) lp_iatom"
  proof (induct rule: lp_answer_model.induct)
    case (clause c rho)
    have local: "lp_return_shape_clause G contracts (P!c)"
      by (rule covered) (use clause.hyps(1) in simp)
    show ?case using local clause.hyps
      by (fastforce simp: lp_return_shape_clause_def)
  qed
  then show ?thesis by (simp add: lp_return_shape_model_def)
qed

ML \<open>
val audited = [@{thm lp_return_ground_exact}, @{thm lp_return_shape_subst}, @{thm lp_return_shape_check_sound},
  @{thm lp_return_shape_clause_cover_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted successful-return shape dependency" else ();
\<close>

end
