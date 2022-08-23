theory Subst_Mod_Mult_AC
imports Main
begin

(* By Manuel Eberl *)

ML \<open>

signature SUBST_MOD_MULT_AC = sig

val tac : Proof.context -> thm -> int -> tactic

end


structure Subst_Mod_Mult_Ac : SUBST_MOD_MULT_AC = struct

datatype factor_tree = Base of term | Mult of factor_tree * factor_tree
datatype delete_result = Empty | Deleted of factor_tree | Not_Present

fun factor_tree (Const (\<^const_name>\<open>Groups.times\<close>, _) $ a $ b) = Mult (factor_tree a, factor_tree b)
  | factor_tree t = Base t

fun flatten_factor_tree (Base t) = [t]
  | flatten_factor_tree (Mult (l, r)) = flatten_factor_tree l @ flatten_factor_tree r


fun mk_one T = Const (\<^const_name>\<open>Groups.one\<close>, T)
fun mk_mult_const T = Const (\<^const_name>\<open>Groups.times\<close>, T --> T --> T)
fun mk_mult t1 t2 = mk_mult_const (fastype_of t1) $ t1 $ t2

fun mk_mult' t1 NONE = t1
  | mk_mult' t1 (SOME t2) = mk_mult t1 t2

fun term_of_factor_tree (Base t) = t
  | term_of_factor_tree (Mult (l, r)) = mk_mult (term_of_factor_tree l) (term_of_factor_tree r)

fun delete_factor_tree t tr =
  let
    fun aux (Base t') =
          if Envir.beta_eta_contract t aconv Envir.beta_eta_contract t' then Empty else Not_Present
      | aux (Mult (l, r)) =
          case aux l of
            Empty => Deleted r
          | Deleted l' => Deleted (Mult (l', r))
          | Not_Present => (
              case aux r of
                Empty => Deleted l
              | Deleted r' => Deleted (Mult (l, r'))
              | Not_Present => Not_Present)
  in
    aux tr
  end

fun delete_all_factor_tree [] tr = Deleted tr
  | delete_all_factor_tree (t :: ts) tr =
      case delete_factor_tree t tr of
        Empty => if null ts then Empty else Not_Present
      | Not_Present => Not_Present
      | Deleted tr' => delete_all_factor_tree ts tr'

val trans_thm = @{lemma "lhs \<equiv> rhs \<Longrightarrow> a \<equiv> lhs \<Longrightarrow> a \<equiv> rhs" by simp}
val lift_thm = @{lemma "lhs \<equiv> rhs \<Longrightarrow> a \<equiv> lhs * x \<Longrightarrow> a \<equiv> rhs * x" by simp}

fun subst_mod_mult_ac ctxt eq_thm ct =
  let
    val t = Thm.term_of ct
    val T = fastype_of t
    val (lhs, _) = Logic.dest_equals (Thm.concl_of eq_thm)
    fun err () = raise CTERM ("subst_mod_mult_ac", [ct, Thm.dest_equals_lhs (Thm.cconcl_of eq_thm)])
    val _ = if fastype_of lhs <> T then err () else ()
    val factors_t = factor_tree t
    val factors_lhs = factor_tree lhs
    val factors_t' =
      case delete_all_factor_tree (flatten_factor_tree factors_lhs) factors_t of
        Empty => NONE
      | Deleted tr => SOME tr
      | Not_Present => err ()
    val is_empty = not (Option.isSome factors_t')
    val t' = mk_mult' lhs (Option.map term_of_factor_tree factors_t')
    fun tac {context: Proof.context, ...} =
      HEADGOAL (Simplifier.simp_tac (put_simpset HOL_ss context addsimps @{thms "mult_ac"}))
    val eq_thm1 = Goal.prove ctxt [] [] (Logic.mk_equals (t, t')) tac
    val thm = if is_empty then trans_thm OF [eq_thm, eq_thm1] else lift_thm OF [eq_thm, eq_thm1]
  in
    thm
  end

fun subst_mod_mult_ac_tac_here ctxt eq_thm ct i =
  EqSubst.eqsubst_tac ctxt [0] [subst_mod_mult_ac ctxt eq_thm ct] i
    handle CTERM _ => no_tac

fun subst_mod_mult_ac_tac ctxt eq_thm i =
  let
    val eq_thm =
      case Thm.concl_of eq_thm of
        Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => eq_thm
      | \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) => eq_thm RS @{thm eq_reflection}
      | _ => raise THM ("subst_mod_mult_ac_tac", 1, [eq_thm])
    fun tac {context: Proof.context, concl: cterm, ...} =
    let
      fun tac' ct =
        subst_mod_mult_ac_tac_here context eq_thm ct i
        ORELSE
          (case Thm.term_of ct of
             _ $ _ => tac' (Thm.dest_fun ct) ORELSE tac' (Thm.dest_arg ct)
           | _ => no_tac)
    in
      tac' concl
    end
  in
    Subgoal.FOCUS_PARAMS tac ctxt i
  end

val tac = subst_mod_mult_ac_tac

end

\<close>

method_setup subst_mod_mult_ac =
  \<open>Attrib.thm >> (fn eq_thm => fn ctxt => SIMPLE_METHOD' (Subst_Mod_Mult_Ac.tac ctxt eq_thm))\<close>



(* now a demo *)
locale demo =
  fixes a::"'a::{comm_monoid_mult}"
  and b::"'a::{comm_monoid_mult}"
  and c::"'a::{comm_monoid_mult}"
  and d::"'a::{comm_monoid_mult}"
  and e::"'a::{comm_monoid_mult}"
  and gee
  assumes foo: "a*b = c"
  and geh: "gee a = true"
  and bar: "gee a \<Longrightarrow> gee b \<Longrightarrow> a * b = c"
begin


(* our method in action *)
lemma "a * b = c"
      "b * a = c"
      "b * d * a = c * d"
      "d * b * a = c * d"
  by (subst_mod_mult_ac foo, rule refl)+

lemma "gee a \<Longrightarrow> a * b = c"
  by (subst_mod_mult_ac foo, rule refl)

(* handling of assumptions in the rewrite rule *)
lemma "d * b * a = c * d"
  apply (subst_mod_mult_ac bar)
  oops

(* backtracking *)
lemma "f (a * b) (a * b) = rhs"
  apply (subst_mod_mult_ac foo)
  back
  oops

end
end