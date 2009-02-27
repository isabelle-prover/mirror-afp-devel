(*  ID:         $Id: QEdlo_ex.thy,v 1.3 2009-02-27 17:46:41 nipkow Exp $
    Author:     Tobias Nipkow, 2007
*)

theory QEdlo_ex imports QEdlo
begin

(* ML"set NameSpace.short_names" *)

(* tweaking the reflection setup *)

definition "interpret" :: "atom fm \<Rightarrow> 'a::dlo list \<Rightarrow> bool" where
"interpret = Logic.interpret I\<^isub>d\<^isub>l\<^isub>o"

lemma interpret_Atoms:
  "interpret (Atom (Eq i j)) xs = (xs!i = xs!j)" 
  "interpret (Atom (Less i j)) xs = (xs!i < xs!j)"
by(simp_all add:interpret_def)

lemma interpret_others:
  "interpret (Neg(ExQ (Neg f))) xs = (\<forall>x. interpret f (x#xs))"
  "interpret (Or (Neg f1) f2) xs = (interpret f1 xs \<longrightarrow> interpret f2 xs)"
by(simp_all add:interpret_def)

lemmas reify_eqs[reify] =
  Logic.interpret.simps(1,2,4-7)[of I\<^isub>d\<^isub>l\<^isub>o, folded interpret_def]
  interpret_others interpret_Atoms

corollary [reflection]: "interpret (qe_dlo f) xs = interpret f xs"
by(simp add:I_qe_dlo interpret_def)

method_setup reify = {*
  fn src =>
    Method.syntax (Attrib.thms --
      Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")") )) src #>
  (fn ((eqs, to), ctxt) => Method.SIMPLE_METHOD' (Reflection.genreify_tac ctxt (eqs @ (fst (Reify_Data.get ctxt))) to
     THEN' simp_tac (HOL_basic_ss addsimps [@{thm"interpret_def"}])))
*} "dlo reification"

(* leave just enough equations in to convert back to True/False by eval *)
declare I\<^isub>d\<^isub>l\<^isub>o.simps(2)[code del]
declare Logic.interpret.simps[code del]
declare Logic.interpret.simps(1-2)[code]

subsection{* Examples *}

lemma "\<forall>x::real. \<not> x < x"
apply reify
apply(subst I_qe_dlo[symmetric])
by eval

lemma "\<forall>x y::real. \<exists>z. x < y \<longrightarrow> x < z & z < y"
apply reify
apply(subst I_qe_dlo[symmetric])
by eval

(* FIXME
lemma "\<forall> x y::real. \<exists> z. x < y \<longrightarrow> x < z & z < y"
by(reflection)

lemma "\<exists> x::real. a+b < x & x < c*d"
apply(reflection)
oops
*)

lemma "\<forall>x::real. \<not> x < x"
apply reify
apply(subst I_qe_dlo[symmetric])
by eval

lemma "\<forall>x y::real. \<exists>z. x < y \<longrightarrow> x < z & z < y"
apply reify
apply(subst I_qe_dlo[symmetric])
by eval

(* 160 secs *)
lemma "\<not>(\<exists>x y z. \<forall>u::real. x < x | \<not> x<u | x<y & y<z & \<not> x<z)"
apply reify
apply(subst I_qe_dlo[symmetric])
by eval

lemma "qe_dlo(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 1 0)))) = FalseF"
by eval

lemma "qe_dlo(AllQ(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 0 1))))) = TrueF"
by eval

lemma
  "qe_dlo(AllQ(ExQ(AllQ (And (Atom(Less 2 1)) (Atom(Less 1 0)))))) = FalseF"
by eval

lemma "qe_dlo(AllQ(ExQ(ExQ (And (Atom(Less 1 2)) (Atom(Less 2 0)))))) = TrueF"
by eval

lemma
  "qe_dlo(AllQ(AllQ(ExQ (And (Atom(Less 1 0)) (Atom(Less 0 2)))))) = FalseF"
by eval

lemma "qe_dlo(AllQ(AllQ(ExQ (Imp (Atom(Less 1 2)) (And (Atom(Less 1 0)) (Atom(Less 0 2))))))) = TrueF"
by eval

normal_form "qe_dlo(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 0 2))))"

end
