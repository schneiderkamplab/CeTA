theory Sparse_Tiling_Processor
  imports Framework.QDP_Framework_Impl
    "Sparse_Tiling_Source.Sparse_Tiling_Encoding"
begin

datatype ('f,'v) sparse_tiling_info = Sparse_Tiling_Info
  "'f list" "'f list" "'f list list"
  "('f list list \<times> 'f list list) list" "('f list \<times> 'f) list" "('f,'v) rules"

fun sparse_tiling_tt where
  "sparse_tiling_tt I (Sparse_Tiling_Info q z tiles tiled_rules table S) tp =
    check_return (do {
      check (tp_ops.Q I tp = []) (showsl_lit (STR ''sparse tiling requires empty Q''));
      check (tp_ops.Rw I tp = []) (showsl_lit (STR ''sparse tiling requires no weak rules''));
      check (sparse_check_encoded_tiling q z tiles tiled_rules table (tp_ops.R I tp) S)
        (showsl_lit (STR ''invalid sparse tiling closure, encoding or source correspondence''))
    }) (tp_ops.mk I False [] S [])"

lemma (in tp_spec) sparse_tiling_tt_sound:
  "sound_tt_impl (sparse_tiling_tt I info)"
proof
  fix tp tp'
  assume step: "sparse_tiling_tt I info tp = return tp'"
    and fin: "SN_qrel (qreltrs tp')"
  obtain q z tiles tiled_rules table S where info:
    "info = Sparse_Tiling_Info q z tiles tiled_rules table S" by (cases info) auto
  from step have Q: "Q tp = []" and W: "Rw tp = []"
    and checked: "sparse_check_encoded_tiling q z tiles tiled_rules table (R tp) S"
    and target: "tp' = mk False [] S []"
    unfolding info by auto
  from fin have "SN (rstep (set S))" unfolding target mk_sound by simp
  from sparse_check_encoded_tiling_sound[OF checked this]
  show "SN_qrel (qreltrs tp)" unfolding qreltrs_sound Q W by simp
qed

end
