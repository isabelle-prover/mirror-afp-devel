section\<open>Automatic relativization of terms and formulas\<close>

text\<open>Relativization of terms and formulas. Relativization of formulas shares relativized terms as
far as possible; assuming that the witnesses for the relativized terms are always unique.\<close>

theory Relativization
  imports
    "Eclose_Absolute"
    Higher_Order_Constructs
  keywords
    "relativize" :: thy_decl % "ML"
    and
    "relativize_tm" :: thy_decl % "ML"
    and
    "reldb_add" :: thy_decl % "ML"
    and
    "reldb_rem" :: thy_decl % "ML"
    and
    "relationalize" :: thy_decl % "ML"
    and
    "rel_closed" :: thy_goal_stmt % "ML"
    and
    "is_iff_rel" :: thy_goal_stmt % "ML"
    and
    "univalent" :: thy_goal_stmt % "ML"
    and
    "absolute"
    and
    "functional"
    and
    "relational"
    and
    "external"
    and
    "for"

begin

ML_file\<open>Relativization_Database.ml\<close>

ML\<open>
structure Absoluteness = Named_Thms
  (val name = @{binding "absolut"}
   val description = "Theorems of absoulte terms and predicates.")
\<close>
setup\<open>Absoluteness.setup\<close>

lemmas relative_abs =
  M_trans.empty_abs
  M_trans.pair_abs
  M_trivial.cartprod_abs
  M_trans.union_abs
  M_trans.inter_abs
  M_trans.setdiff_abs
  M_trans.Union_abs
  M_trivial.cons_abs
  (*M_trans.upair_abs*)
  M_trivial.successor_abs
  M_trans.Collect_abs
  M_trans.Replace_abs
  M_trivial.lambda_abs2
  M_trans.image_abs
  (*M_trans.powerset_abs*)
  M_trivial.nat_case_abs
  (*
  M_trans.transitive_set_abs
  M_trans.ordinal_abs
  M_trivial.limit_ordinal_abs
  M_trivial.successor_ordinal_abs
  M_trivial.finite_ordinal_abs
*)
  M_trivial.omega_abs
  M_basic.sum_abs
  M_trivial.Inl_abs
  M_trivial.Inr_abs
  M_basic.converse_abs
  M_basic.vimage_abs
  M_trans.domain_abs
  M_trans.range_abs
  M_basic.field_abs
  (* M_basic.apply_abs *)
  (*
  M_trivial.typed_function_abs
  M_basic.injection_abs
  M_basic.surjection_abs
  M_basic.bijection_abs
  *)
  M_basic.composition_abs
  M_trans.restriction_abs
  M_trans.Inter_abs
  M_trivial.bool_of_o_abs
  M_trivial.not_abs
  M_trivial.and_abs
  M_trivial.or_abs
  M_trivial.Nil_abs
  M_trivial.Cons_abs
  (*M_trivial.quasilist_abs*)
  M_trivial.list_case_abs
  M_trivial.hd_abs
  M_trivial.tl_abs
  M_trivial.least_abs'
  M_eclose.transrec_abs
  M_trans.If_abs
  M_trans.The_abs
  M_eclose.recursor_abs
  M_trancl.trans_wfrec_abs
  M_trancl.trans_wfrec_on_abs

lemmas datatype_abs =
  M_eclose.is_eclose_n_abs
  M_eclose.eclose_abs
  M_trivial.Member_abs
  M_trivial.Equal_abs
  M_trivial.Nand_abs
  M_trivial.Forall_abs

declare relative_abs[absolut]

ML_file\<open>Relativization.ml\<close>

setup\<open>Relativization.init_db Relativization.db \<close>

declare relative_abs[Rel]
(*TODO: check all the duplicate cases here.*)
declare datatype_abs[Rel]

ML\<open>
val db = Relativization.get_db @{context}
\<close>

end
