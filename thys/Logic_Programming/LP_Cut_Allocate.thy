theory LP_Cut_Allocate
  imports LP_Cut_Scopes
begin

lemma lp_cut_goal_scopes_map[simp]:
  "lp_cut_goal_scopes (lp_cut_map f g) = lp_cut_goal_scopes g"
  by (cases g) simp_all

lemma lp_cut_entry_scopes_map[simp]:
  "lp_cut_entry_scopes (lp_cut_entry_map f e) = lp_cut_entry_scopes e"
  by (cases e) (simp_all add: image_image)

lemma lp_cut_fresh_state_map[simp]:
  "lp_cut_fresh m (lp_cut_state_map f es) = lp_cut_fresh m es"
  by (simp add: lp_cut_fresh_def lp_cut_state_map_def image_image)

definition lp_cut_check_case where
  "lp_cut_check_case P m f ts gs es next =
    (lp_cut_fresh m (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) \<and>
     next=map (\<lambda>c. LPCClause (LPCAtom (Fun (LPCUser f) ts)#gs) c m)
       (lp_cut_slice P (LPCUser f) (length ts)) @ LPCBarrier m#es)"

theorem lp_cut_checked_case_covers:
  assumes checked: "lp_cut_check_case P m f ts gs es next"
    and step: "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es) \<eta>,t)
      \<in>lp_cut_source P"
  shows "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n)) (lp_cut_state_eval next \<eta>)"
proof -
  let ?a = "LPIFun (LPCUser f) (map (\<lambda>u. lp_ieval u \<eta>) ts)"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?es = "lp_cut_state_eval es \<eta>"
  let ?cs = "lp_cut_slice P (LPCUser f) (length ts)"
  have source: "(LPCGoals (LPCAtom ?a#?gs)#?es,t)\<in>lp_cut_source P"
    using step by (simp add: lp_cut_state_map_def)
  then obtain n where fresh: "lp_cut_fresh n (LPCGoals (LPCAtom ?a#?gs)#?es)"
    and successor: "t=map (\<lambda>c. LPCClause (LPCAtom ?a#?gs) c n) ?cs @ LPCBarrier n#?es"
    by (cases rule: lp_cut_source.cases) auto
  have chosen: "lp_cut_fresh m (LPCGoals (LPCAtom ?a#?gs)#?es)"
    using checked lp_cut_fresh_state_map[of m "\<lambda>u. lp_ieval u \<eta>"
      "LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs)#es"]
    by (simp add: lp_cut_check_case_def lp_cut_state_map_def)
  have represented: "lp_cut_state_eval next \<eta> =
      map (\<lambda>c. LPCClause (LPCAtom ?a#?gs) c m) ?cs @ LPCBarrier m#?es"
    using checked by (simp add: lp_cut_check_case_def lp_cut_state_map_def map_map o_def)
  show ?thesis
    by (rule exI[of _ n])
      (simp only: represented successor lp_cut_fresh_swap_call[OF chosen fresh])
qed

definition lp_cut_check_meta where
  "lp_cut_check_meta m a gs es body =
    (lp_cut_fresh m (LPCGoals (LPCMeta a#gs)#es) \<and>
      lp_cut_lower_finite m a=Some body)"

theorem lp_cut_checked_meta_covers:
  assumes checked: "lp_cut_check_meta m a gs es body"
    and step: "(lp_cut_state_eval (LPCGoals (LPCMeta a#gs)#es) \<eta>,t)\<in>lp_cut_source P"
  shows "\<exists>n. t=map (lp_cut_scope_entry (lp_cut_scope_swap m n))
    (lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta>)"
proof -
  let ?a = "lp_ieval a \<eta>"
  let ?gs = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) gs"
  let ?body = "map (lp_cut_map (\<lambda>u. lp_ieval u \<eta>)) body"
  let ?es = "lp_cut_state_eval es \<eta>"
  have source: "(LPCGoals (LPCMeta ?a#?gs)#?es,t)\<in>lp_cut_source P"
    using step by (simp add: lp_cut_state_map_def)
  have lowered: "lp_cut_lower m ?a ?body"
    by (rule lp_cut_lower_finite_sound) (use checked in \<open>simp add: lp_cut_check_meta_def\<close>)
  from source obtain n bs where fresh: "lp_cut_fresh n (LPCGoals (LPCMeta ?a#?gs)#?es)"
    and actual: "lp_cut_lower n ?a bs"
    and successor: "t=LPCGoals (bs@?gs)#LPCBarrier n#?es"
    using lowered by (cases rule: lp_cut_source.cases) auto
  have chosen: "lp_cut_fresh m (LPCGoals (LPCMeta ?a#?gs)#?es)"
    using checked lp_cut_fresh_state_map[of m "\<lambda>u. lp_ieval u \<eta>"
      "LPCGoals (LPCMeta a#gs)#es"]
    by (simp add: lp_cut_check_meta_def lp_cut_state_map_def)
  have represented: "lp_cut_state_eval (LPCGoals (body@gs)#LPCBarrier m#es) \<eta> =
      LPCGoals (?body@?gs)#LPCBarrier m#?es"
    by (simp add: lp_cut_state_map_def)
  show ?thesis
    by (rule exI[of _ n])
      (simp only: represented successor lp_cut_fresh_swap_meta[OF chosen fresh lowered actual])
qed

lemma reusing_live_cut_scope_is_rejected:
  "\<not>lp_cut_check_case P m f ts [LPCCut m] es next"
  by (simp add: lp_cut_check_case_def lp_cut_fresh_def)

lemma unknown_callable_cannot_be_certified_by_lowering:
  "\<not>lp_cut_check_meta m (Var x) gs es body"
  by (simp add: lp_cut_check_meta_def)

end
