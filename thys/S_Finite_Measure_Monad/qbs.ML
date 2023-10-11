(*  Title:   qbs.ML
    Author:  Yasuhiko Minamide, Michikazu Hirata, Tokyo Institute of Technology
    qbs prover
*)

signature QBS = 
sig

  val get : Context.generic -> thm list
  val qbs_add: attribute
  val qbs_del: attribute

  val qbs_tac: Proof.context -> thm list -> tactic
  val simproc : Proof.context -> cterm -> thm option
end ;

structure Qbs : QBS =
struct

structure Data = Generic_Data
(
  type T = thm list
  val empty: T = []
  val merge = Thm.merge_thms
);

val get = Data.get

fun add thm = Data.map (Thm.add_thm thm)

val qbs_add = Thm.declaration_attribute add;
val qbs_del = Thm.declaration_attribute (Data.map o Thm.del_thm);

fun instantiate ctxt (Abs (n, T, t1 $ t2)) =
  let val (T1, T2) = @{Type_fn \<open>fun A B => \<open>(A,B)\<close>\<close>} (type_of1([T] ,t1))
      val t1' = Abs (n, T, t1)
      val t2' = Abs (n, T, t2)
  in
      Thm.instantiate'
           (map (Option.map (Thm.ctyp_of ctxt)) [SOME T, SOME T1, SOME T2])
           (map (Option.map (Thm.cterm_of ctxt)) [SOME t1', NONE, NONE, NONE, SOME t2'])
           @{thm qbs_morphism_app}
  end
| instantiate _ (Abs (_, _, Abs _)) = @{thm curry_preserves_morphisms}
| instantiate ctxt (t1 $ t2) =
  let val (T1, T2) = @{Type_fn \<open>fun A B => \<open>(A,B)\<close>\<close>} (type_of1 ([], t1)) in
    Thm.instantiate'
      (map (Option.map (Thm.ctyp_of ctxt))  [SOME T1, SOME T2])
      (map (Option.map (Thm.cterm_of ctxt)) [SOME t1, NONE, NONE, SOME t2])
      @{thm qbs_morphism_space}
  end
| instantiate _ t = raise (TERM (("instantiate"), [t]))


fun qbs_tac ctxt facts =
  let  val instantiate_tac =
        SUBGOAL (fn (t,i) =>
          (case HOLogic.dest_Trueprop t of
             \<^Const_>\<open>Set.member _ for f \<^Const_>\<open>qbs_space _ for _\<close>\<close> =>
             resolve_tac ctxt [instantiate ctxt f] i
           | _ => raise (TERM ("not a qbs_space predicate", [t])))
        handle TERM _ => no_tac) 1
       val thms = facts @ get (Context.Proof ctxt)
       val single_step_tac =
         CHANGED (asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps ((map (Simplifier.norm_hhf ctxt) thms))) 1)
         ORELSE resolve_tac ctxt thms 1
         ORELSE instantiate_tac
   in
    REPEAT single_step_tac
   end

fun simproc ctxt redex =
  let
    val t = HOLogic.mk_Trueprop (Thm.term_of redex);
    fun tac {context = ctxt, prems = _ } =
      SOLVE (qbs_tac ctxt (Simplifier.prems_of ctxt));
  in \<^try>\<open>Goal.prove ctxt [] [] t tac RS @{thm Eq_TrueI}\<close> end;

end