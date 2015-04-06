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
theory Lifting_Definition_Option_Examples
imports  
  Lifting_Definition_Option
begin

section \<open>Examples\<close>

subsection \<open>A simple restricted type without type-parameters\<close>

typedef "restricted" = "{ i :: int. i mod 2 = 0}" morphisms base "restricted"
  by (intro exI[of _ 4]) auto
setup_lifting type_definition_restricted

text \<open>Let us start with just using a sufficient criterion for testing for even numbers,
  without actually generating them, i.e., where the generator is just the identity function.\<close>
lift_definition_option restricted_of_simple :: "int \<Rightarrow> restricted option" is 
  "\<lambda> x :: int. if x \<in> {0, 2, 4, 6} then Some x else None"
proof -
  fix x :: int
  assume "x \<in> {0, 2, 4, 6}"
  thus "x mod 2 = 0" by auto
qed

text \<open>We can also take several input arguments for the test, and generate a more complex value.\<close>
lift_definition_option restricted_of_many_args :: "nat \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> restricted option" is 
  "\<lambda> x y (b :: bool). if int x + y = 5 then Some ((int x + 1) * (y + 1)) else None"
proof -
  fix x y and b :: bool
  assume "int x + y = 5"
  from arg_cong[OF this, of "\<lambda> x. x mod 2"]
  have "int x mod 2 = 1 \<or> y mod 2 = 1" by (auto simp: field_simps)
  hence "(int x + 1) mod 2 = 0 \<or> (y + 1) mod 2 = 0" by presburger
  thus "((int x+1) * (y + 1)) mod 2 = 0" by auto
qed

text \<open>No problem to use type parameters.\<close>
lift_definition_option restricted_of_poly :: "'b list \<Rightarrow> restricted option" is 
  "\<lambda> xs :: 'b list. if length xs = 2 then Some (int (length (xs))) else None" 
proof -
  fix xs :: "'b list"
  assume "length xs = 2"
  thus "int (length xs) mod 2 = 0" by auto
qed

subsection \<open>Examples with type-parameters in the restricted type.\<close>

typedef 'f restrictedf = "{ xs :: 'f list. length xs < 3}" morphisms basef restrictedf 
  by (intro exI[of _ Nil]) auto
setup_lifting type_definition_restrictedf

text \<open>It does not matter, if we take the same or different type-parameters in the lift-definition.\<close>
lift_definition_option test1 :: "'g \<Rightarrow> nat \<Rightarrow> 'g restrictedf option" is 
  "\<lambda> (e :: 'g) x. if x < 2 then Some (replicate x e) else None"
proof -
  fix e :: 'g and x 
  show "x < 2 \<Longrightarrow> length (replicate x e) < 3" by auto
qed

lift_definition_option test2 :: "'f \<Rightarrow> nat \<Rightarrow> 'f restrictedf option" is 
  "\<lambda> (e :: 'f) x. if x < 2 then Some (replicate x e) else None"
proof -
  fix e :: 'f and x 
  show "x < 2 \<Longrightarrow> length (replicate x e) < 3" by auto
qed

text \<open>Tests with multiple type-parameters.\<close>
 
typedef ('a,'f) restr = "{ (xs :: 'a list,ys :: 'f list) . length xs = length ys}" 
  morphisms base' restr
  by (rule exI[of _ "([], [])"], auto) 
setup_lifting type_definition_restr

lift_definition_option restr_of_pair :: "'g \<Rightarrow> 'e list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('e,nat) restr option" is
  "\<lambda> (z :: 'g) (xs :: 'e list) (y :: nat) n. if length xs = n then Some (xs,replicate n y) else None"
proof -
  fix xs :: "'e list" and y :: nat and n
  assume "length xs = n"
  thus "case (xs, replicate n y) of (xs, ys) \<Rightarrow> length xs = length ys"
    by auto
qed

subsection \<open>Example from \isafor/\ceta\<close>

text \<open>An argument filter is a mapping @{term \<pi>} from n-ary function symbols into 
lists of positions, i.e., where each position is between 0 and n-1. In \isafor,
(Isabelle's Formalization of Rewriting) and \ceta 
\cite{DBLP:conf/tphol/ThiemannS09}, the corresponding certifier for 
term rewriting related properties,
this is modelled as follows, where a partial argument filter in a map is extended to a full one 
by means of an default filter.\<close>

typedef 'f af = "{ (\<pi> :: 'f \<times> nat \<Rightarrow> nat list). (\<forall> f n. set (\<pi> (f,n)) \<subseteq> {0 ..< n})}" 
  morphisms af Abs_af by (rule exI[of _ "\<lambda> _. []"], auto)

setup_lifting type_definition_af

type_synonym 'f af_impl = "(('f \<times> nat) \<times> nat list)list"


fun fun_of_map_fun :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where 
  "fun_of_map_fun m f a = (case m a of Some b \<Rightarrow> b | None \<Rightarrow> f a)"

lift_definition_option af_of :: "'f af_impl \<Rightarrow> 'f af option" is
  "\<lambda> s :: 'f af_impl. if (\<forall> fidx \<in> set s. (\<forall> i \<in> set (snd fidx). i < snd (fst fidx)))
     then Some (fun_of_map_fun (map_of s) (\<lambda> (f,n). [0 ..< n])) else None" 
proof (intro allI)
  fix pi :: "'f af_impl" and f n
  let ?pi = "fun_of_map_fun (map_of pi) (\<lambda> (f,n). [0 ..< n])"
  assume *: "\<forall>fidx\<in>set pi. \<forall>i\<in>set (snd fidx). i < snd (fst fidx)"
  show "set (?pi (f, n)) \<subseteq> {0..<n}"
  proof (cases "map_of pi (f,n)")
    case (Some idx)
    from map_of_SomeD[OF Some] Some
    have "?pi (f,n) = idx" "((f, n), idx) \<in> set pi" by auto
    with * Some show ?thesis by auto
  qed auto
qed

subsection \<open>Code generation tests and derived theorems\<close>
export_code 
  restricted_of_many_args
  restricted_of_simple
  restricted_of_poly
  test1
  test2
  restr_of_pair
  af_of
in Haskell

thm 
  restricted_of_many_args_Some restricted_of_many_args
  restricted_of_simple_Some restricted_of_simple
  restricted_of_poly_Some restricted_of_poly
  test1_Some test1
  test2_Some test2
  restr_of_pair_Some restr_of_pair
  af_of_Some af_of

end
