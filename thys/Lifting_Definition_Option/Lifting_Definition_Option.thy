(*  Title:       Lifting Definition Option
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
theory Lifting_Definition_Option
imports 
  Main
keywords "lift_definition_option" :: thy_decl
begin

ML {*
  (* add another ML-antiquotation in the style of ~~/src/Pure/ML/ml_antiquotations.ML,
     namely @{map_tuple n} = fn f => fn (x1, .., xn) => (f x1, ..., f xn).
     It can be used to avoid constructions like let [x1,...,xn] = map f [y1,...,yn] where
     a warning about non-exhaustive patterns is raised. This can now be written as
     let (x1,...,xn) = @{map_tuple n} f (y1,...,yn) *)
let 
  (* code copied from ml_antiquotations *)
  val parameter = Parse.position Parse.nat >> (fn (n, pos) =>
    if n > 1 then n else error ("Bad parameter: " ^ string_of_int n ^ Position.here pos));

  fun indices n = map string_of_int (1 upto n);
  val tuple = enclose "(" ")" o commas;
  fun tuple_vars x n = tuple (map (fn a => x ^ a) (indices n));

in

Theory.setup
 (ML_Antiquotation.value @{binding map_tuple}
    (Scan.lift parameter >> (fn n =>
      "(fn f => fn " ^ tuple_vars "x" n ^ " => " ^ tuple_vars "f x" n ^ ")")))
end
*}

lemma restrict_condI: assumes "a \<Longrightarrow> P b"
  shows "(if a then (b, True)
        else (c, False))
       \<in> {(b, c). c \<longrightarrow> P b}" using assms by auto

lemma simplify_cond: "(\<forall>x. P \<longrightarrow> Q x) = (P \<longrightarrow> (\<forall>x. Q x))" by blast

lemma snd_if: "snd (if b then (P,True) else (Q,False)) = b" by simp

lemma valid_definition: assumes 
  ab: "\<And> r. ab (base r) = r"
  and d: "d = (let rc = sc
     in if scb rc then Some (scs rc) else None)"
  and dS: "\<And> r. d = Some r \<Longrightarrow> base r = gen"
  and c: "scb sc = c"
  shows "d = (if c then Some (ab gen) else None)"
proof (cases "scb sc")
  case False
  thus ?thesis unfolding d Let_def c by simp
next
  case True
  with d[unfolded Let_def] have d: "d = Some (scs sc)" by auto
  from dS[OF this] have "gen = base (scs sc)" by simp
  thus ?thesis unfolding d using True[unfolded c]
    by (simp add: ab)
qed

ML_file "lifting_definition_option.ML" 

end

