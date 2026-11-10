theory LP_Prolog_Control_Return_Paths
 imports LP_Prolog_Control_Return_Model
begin

text \<open>Logical path extraction is separate from source execution. Both
conditional alternatives are covered, while their substitutions are never
mixed. Equality is retained as a relation and revisited after returned values
are known. The fuel bounds certificate construction, not source execution.\<close>

definition lpp_control_equality where
  "lpp_control_equality = ''2:prolog_data_0070726f6c6f672e72657475726e3a657175616c''"

definition lpp_control_equality_clause :: "string lpp_success_clause" where
  "lpp_control_equality_clause = ((lpp_control_equality,[Var ''x'',Var ''x'']),[],[])"

definition lpp_control_product where
  "lpp_control_product xs ys = concat (map (\<lambda>x. map (\<lambda>y. x@y) ys) xs)"

definition lpp_control_goal_paths ::
  "(string lpc_term lp_cut_goal list \<Rightarrow> string lpc_term lp_cut_goal list list option) \<Rightarrow>
    string lpc_term lp_cut_goal \<Rightarrow> string lpc_term lp_cut_goal list list option" where
  "lpp_control_goal_paths recurse g = (case g of
       LPCTrue \<Rightarrow> Some [[]]
     | LPCCut m \<Rightarrow> Some [[]]
     | LPCFail \<Rightarrow> Some []
     | LPCUnify a b \<Rightarrow> Some [[LPCAtom (Fun (LPCUser lpp_control_equality) [a,b])]]
     | LPCMeta t \<Rightarrow> None
     | LPCExpand c m \<Rightarrow> None
     | LPCAtom t \<Rightarrow> (case t of Fun (LPCUser f) ts \<Rightarrow>
         (if f=''2:;'' then
           (case ts of [Fun (LPCUser arrow) [c,y],z] \<Rightarrow>
             (if arrow=''2:->'' then
               (case (lpp_branch_lower_term c,lpp_branch_lower_term y,lpp_branch_lower_term z) of
                 (Some cs,Some ys,Some zs) \<Rightarrow>
                   (case (recurse (cs@ys),recurse zs) of
                     (Some left,Some right) \<Rightarrow> Some (left@right) | _ \<Rightarrow> None)
               | _ \<Rightarrow> None)
              else None)
           | _ \<Rightarrow> None)
          else if f=''3:subtract'' then
            (if length ts=3 then Some [[LPCAtom (Fun (LPCUser lpp_subtract_library) ts)]] else None)
          else Some [[g]])
       | _ \<Rightarrow> None))"

primrec lpp_control_paths :: "nat \<Rightarrow> string lpc_term lp_cut_goal list \<Rightarrow>
    string lpc_term lp_cut_goal list list option" where
  "lpp_control_paths 0 = (\<lambda>gs. None)"
| "lpp_control_paths (Suc fuel) = (\<lambda>whole. case whole of [] \<Rightarrow> Some [[]] | g#gs \<Rightarrow>
    (case (lpp_control_goal_paths (lpp_control_paths fuel) g,lpp_control_paths fuel gs) of
      (Some left,Some right) \<Rightarrow> Some (lpp_control_product left right) | _ \<Rightarrow> None))"

fun lpp_control_is_equation where
  "lpp_control_is_equation (LPCAtom (Fun (LPCUser f) ts)) = (f=lpp_control_equality)"
| "lpp_control_is_equation _ = False"

definition lpp_control_completed_path where
  "lpp_control_completed_path gs = gs @ filter lpp_control_is_equation gs"

lemma lpp_control_equality_model:
  assumes clause: "lpp_control_equality_clause\<in>set SP"
    and equal: "a=b"
  shows "lpp_inline_return_model SP E (LPIFun (LPCUser lpp_control_equality) [a,b])"
proof -
  have success: "lpp_guarded_success SP E
    (lpp_success_atom_eval (lpp_control_equality,[Var ''x'',Var ''x'']) (\<lambda>_. a))"
    by (rule lpp_guarded_success.clause)
      (use clause in \<open>auto simp: lpp_control_equality_clause_def\<close>)
  show ?thesis using success equal
    by (simp add: lpp_success_atom_eval_def lpp_control_equality_def)
qed

lemma lpp_control_conditional_paths:
  assumes checked: "lpp_control_goal_paths recurse (LPCAtom (Fun (LPCUser ''2:;'') ts))=Some paths"
  shows "\<exists>c y z cs ys zs left right.
    ts=[Fun (LPCUser ''2:->'') [c,y],z] \<and>
    lpp_branch_lower_term c=Some cs \<and> lpp_branch_lower_term y=Some ys \<and>
    lpp_branch_lower_term z=Some zs \<and>
    recurse (cs@ys)=Some left \<and> recurse zs=Some right \<and> paths=left@right"
  using checked by (auto simp: lpp_control_goal_paths_def
    split: list.splits term.splits lp_cut_symbol.splits option.splits prod.splits if_splits)

lemma lpp_control_goal_paths_complete:
  assumes equation: "\<And>a. M (LPIFun (LPCUser lpp_control_equality) [a,a])"
    and recursion: "\<And>gs paths. recurse gs=Some paths \<Longrightarrow>
      list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) \<Longrightarrow>
      \<exists>path\<in>set paths. list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) path)"
    and checked: "lpp_control_goal_paths recurse g=Some paths"
    and modeled: "lpc_model_goal (lpp_control_return_model M)
      (lp_cut_map (\<lambda>t. lp_ieval t eta) g)"
  shows "\<exists>path\<in>set paths. list_all (lpc_model_goal (lpp_control_return_model M))
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) path)"
proof (cases g)
  case (LPCAtom t)
  obtain f ts where t: "t=Fun (LPCUser f) ts"
    using checked LPCAtom by (cases t)
      (auto simp: lpp_control_goal_paths_def split: lp_cut_symbol.splits)
  have model: "lpp_control_return_model M (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t eta) ts))"
    using modeled by (simp add: LPCAtom t)
  show ?thesis
  proof (cases "f=''2:;''")
    case conditional: True
    obtain c y z cs ys zs left right where shape: "ts=[Fun (LPCUser ''2:->'') [c,y],z]"
      and lower: "lpp_branch_lower_term c=Some cs" "lpp_branch_lower_term y=Some ys" "lpp_branch_lower_term z=Some zs"
      and left: "recurse (cs@ys)=Some left" and right: "recurse zs=Some right"
      and paths: "paths=left@right"
      using lpp_control_conditional_paths[of recurse ts paths] checked LPCAtom t conditional by auto
    have selected: "lpp_control_return_model M (LPIFun (LPCUser ''2:;'')
      [LPIFun (LPCUser ''2:->'') [lp_ieval c eta,lp_ieval y eta],lp_ieval z eta])"
      using model by (simp add: conditional shape)
    have alternatives: "list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (cs@ys)) \<or>
      list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) zs)"
      using lpp_control_return_conditional[OF
        lpp_branch_lower_term_sound[where eta=eta, OF lower(1)]
        lpp_branch_lower_term_sound[where eta=eta, OF lower(2)]
        lpp_branch_lower_term_sound[where eta=eta, OF lower(3)] selected] by simp
    show ?thesis using recursion[OF left] recursion[OF right] alternatives by (auto simp: paths)
  next
    case no_conditional: False
    show ?thesis
    proof (cases "f=''3:subtract''")
      case True
      have paths: "paths=[[LPCAtom (Fun (LPCUser lpp_subtract_library) ts)]]"
        using checked by (auto simp: LPCAtom t lpp_control_goal_paths_def True split: if_splits)
      have library: "lpp_control_return_model M
          (LPIFun (LPCUser lpp_subtract_library) (map (\<lambda>t. lp_ieval t eta) ts))"
        by (rule lpp_control_return_delegate) (use model True in simp)
      show ?thesis using library by (simp add: paths)
    next
      case False
      have paths: "paths=[[g]]"
        using checked no_conditional False by (simp add: LPCAtom t lpp_control_goal_paths_def)
      show ?thesis using modeled by (simp add: paths)
    qed
  qed
next
  case (LPCUnify a b)
  have equal: "lp_ieval a eta=lp_ieval b eta" using modeled by (simp add: LPCUnify)
  have base: "M (LPIFun (LPCUser lpp_control_equality) [lp_ieval a eta,lp_ieval b eta])"
    using equation[of "lp_ieval a eta"] equal by simp
  have relation: "lpp_control_return_model M
      (LPIFun (LPCUser lpp_control_equality) [lp_ieval a eta,lp_ieval b eta])"
    by (rule lpp_control_return_model.ordinary) (use base in \<open>simp_all add: lpp_control_equality_def\<close>)
  show ?thesis using checked relation by (auto simp: LPCUnify lpp_control_goal_paths_def)
qed (use checked modeled in \<open>auto simp: lpp_control_goal_paths_def\<close>)

lemma lpp_control_paths_complete:
  assumes equation: "\<And>a. M (LPIFun (LPCUser lpp_control_equality) [a,a])"
    and checked: "lpp_control_paths fuel gs=Some paths"
    and modeled: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  shows "\<exists>path\<in>set paths. list_all (lpc_model_goal (lpp_control_return_model M))
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) path)"
  using checked modeled
proof (induction fuel arbitrary: gs paths)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases gs)
    case Nil then show ?thesis using Suc.prems by auto
  next
    case (Cons g rest)
    obtain left right where left: "lpp_control_goal_paths (lpp_control_paths fuel) g=Some left"
      and right: "lpp_control_paths fuel rest=Some right" and paths: "paths=lpp_control_product left right"
      using Suc.prems(1) by (auto simp: Cons split: option.splits prod.splits)
    have first: "lpc_model_goal (lpp_control_return_model M) (lp_cut_map (\<lambda>t. lp_ieval t eta) g)"
      and tail: "list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
      using Suc.prems(2) by (simp_all add: Cons)
    obtain a where a: "a\<in>set left" "list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) a)"
      using lpp_control_goal_paths_complete[where recurse="lpp_control_paths fuel"
        and M=M and eta=eta and g=g and paths=left, OF equation _ left first]
        Suc.IH by blast
    obtain b where b: "b\<in>set right" "list_all (lpc_model_goal (lpp_control_return_model M))
        (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) b)"
      using Suc.IH[OF right tail] by blast
    show ?thesis by (rule bexI[of _ "a@b"])
      (use a b in \<open>auto simp: paths lpp_control_product_def\<close>)
  qed
qed

end
