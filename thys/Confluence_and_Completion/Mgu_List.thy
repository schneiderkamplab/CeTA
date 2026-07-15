(* an mgu-function for lists of pairs of terms *)

(* TODO: merge into AFP-entry *)

theory Mgu_List
imports
  First_Order_Terms.Unification
begin
text \<open>Computing the mgu of a list of term pairs.\<close>
definition mgu_list :: "(('f, 'v) term \<times> ('f,'v) term) list \<Rightarrow> ('f, 'v) subst option" where
  "mgu_list pairs = map_option subst_of (unify pairs [])" 

lemma mgu_list_None: "mgu_list pairs = None \<Longrightarrow> unifiers (set pairs) = {}"
  unfolding mgu_list_def by (intro unify_complete, auto)

lemma mgu_list_Some: "mgu_list pairs = Some \<tau> \<Longrightarrow> is_imgu \<tau> (set pairs)" 
  unfolding mgu_list_def using unify_sound by blast
end