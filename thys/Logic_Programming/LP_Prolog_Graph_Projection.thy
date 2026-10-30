theory LP_Prolog_Graph_Projection
  imports LP_Infinite_Terms
begin

text \<open>A graph is an observation of a rational runtime value, not a finite
termination measure. Only the selected projection is required to be finite.
Absent nodes denote variables; they cannot justify a retained ground measure.
The checker follows the selected edges, so an unselected cycle is harmless.\<close>

type_synonym 'f lpp_value_graph = "('f \<times> nat list) option list"

primcorec lpp_graph_value :: "'f lpp_value_graph \<Rightarrow> nat \<Rightarrow> ('f,nat) lp_iterm" where
  "lpp_graph_value G i = (case (if i<length G then G!i else None) of
     None \<Rightarrow> LPIVar i
   | Some (f,js) \<Rightarrow> LPIFun f (map (lpp_graph_value G) js))"

fun lpp_check_graph_projection ::
  "nat \<Rightarrow> 'f lpp_value_graph \<Rightarrow> 'f afs \<Rightarrow> nat \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
  "lpp_check_graph_projection 0 G flt i t = False"
| "lpp_check_graph_projection (Suc fuel) G flt i t =
   (i<length G \<and> (case G!i of None \<Rightarrow> False | Some (f,js) \<Rightarrow>
     (case afs flt (f,length js) of
       AFList ks \<Rightarrow> (case t of Var x \<Rightarrow> False | Fun g ts \<Rightarrow>
         f=g \<and> list_all2 (\<lambda>k u. k<length js \<and>
           lpp_check_graph_projection fuel G flt (js!k) u) ks ts)
     | Collapse k \<Rightarrow> k<length js \<and> lpp_check_graph_projection fuel G flt (js!k) t)))"

lemma lpp_graph_value_node:
  "i<length G \<Longrightarrow> G!i=Some (f,js) \<Longrightarrow>
   lpp_graph_value G i=LPIFun f (map (lpp_graph_value G) js)"
  by (subst lpp_graph_value.code) simp

theorem lpp_check_graph_projection_sound:
  "lpp_check_graph_projection fuel G flt i t \<Longrightarrow>
   lp_iproject flt (lpp_graph_value G i) t"
proof (induct fuel arbitrary: i t)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  obtain f js where node: "i<length G" "G!i=Some (f,js)"
    using Suc.prems by (auto split: option.splits)
  show ?case
  proof (cases "afs flt (f,length js)")
    case (AFList ks)
    obtain ts where shape: "t=Fun f ts" and children:
      "list_all2 (\<lambda>k u. k<length js \<and> lpp_check_graph_projection fuel G flt (js!k) u) ks ts"
      using Suc.prems node AFList by (auto split: term.splits)
    have projected: "list_all2 (\<lambda>k u. k<length (map (lpp_graph_value G) js) \<and>
        lp_iproject flt ((map (lpp_graph_value G) js)!k) u) ks ts"
      using children Suc.hyps by (auto simp: list_all2_conv_all_nth)
    show ?thesis unfolding lpp_graph_value_node[OF node] shape
      by (rule lp_iproject.list) (use AFList projected in auto)
  next
    case (Collapse k)
    have index: "k<length js" and child: "lpp_check_graph_projection fuel G flt (js!k) t"
      using Suc.prems node Collapse by auto
    show ?thesis unfolding lpp_graph_value_node[OF node]
      by (rule lp_iproject.collapse[where i=k]) (use Collapse index Suc.hyps[OF child] in auto)
  qed
qed

corollary lpp_checked_graph_projection_ground:
  "lpp_check_graph_projection fuel G flt i t \<Longrightarrow> ground t"
  using lpp_check_graph_projection_sound lp_iproject_ground by blast

corollary lpp_checked_graph_projection_substitution:
  "lpp_check_graph_projection fuel G flt i t \<Longrightarrow>
   lp_iproject flt (lp_isubst (lpp_graph_value G i) sigma) t"
  using lpp_check_graph_projection_sound lp_iproject_subst by blast


text \<open>Relational lowering records graph edges as rational-unification
constraints. These constraints have a simultaneous solution even for cyclic
graphs. Arbitrary values may instantiate the unconstrained nodes.\<close>

definition lpp_graph_equations where
  "lpp_graph_equations G rho = (\<forall>i<length G. case G!i of None \<Rightarrow> True
    | Some (f,js) \<Rightarrow> rho i = LPIFun f (map rho js))"

theorem lpp_graph_equations_solution:
  "lpp_graph_equations G (\<lambda>i. lp_isubst (lpp_graph_value G i) sigma)"
  unfolding lpp_graph_equations_def
  by (intro allI impI; case_tac "G!i")
    (auto simp: lpp_graph_value_node split: prod.splits)

corollary lpp_graph_equations_satisfiable:
  "\<exists>rho. lpp_graph_equations G rho"
  using lpp_graph_equations_solution by blast

end
