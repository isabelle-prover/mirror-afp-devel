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
theory Lifting_Definition_Option_Explanation
imports 
  Lifting_Definition_Option
  Rat
begin

section \<open>Introduction\<close>

text \<open>Often algorithms expect that their input satisfies some specific property @{term P}.
For example, some algorithms require lists as input which have to be sorted, 
or numbers which have to be positive,
or programs which have to be well-typed, etc. 
Here, there are at least two approaches how one can reason
about these algorithms. 

The first approach is to guard all soundness properties of the algorithm
by the additional precondition @{term "P input"}. 
So, as an example, a binary search algorithm might take arbitrary lists as input, but only
if the input list is sorted, then the result of the search is meaningful.
Whereas for binary search, this approach is reasonable, there might be problems that the
restriction on the input is even crucial for actually defining the algorithm, since without
the restriction the algorithm might be non-terminating, and thus, cannot be easily defined
using Isabelle's function-package \cite{DBLP:journals/jar/Krauss10}. 
As an example, consider an approximation algorithm for
$\sqrt{x}$, where the algorithm should stop once the current approximation $y$ satisfies
@{term "abs(x^2 - y^2) < \<delta>"}. Imagine now, that @{term \<delta>} is a negative number.


To this end, in the second approach the idea is to declare restricted types, 
so that the algorithms are only invoked with inputs which satisfy the property @{term P}. 
For example, using Isabelle's lifting- and transfer-package 
\cite{DBLP:conf/cpp/HuffmanK13},
one can easily define a dedicated type for positive numbers, 
and a function which accesses the internal number,
which is then guaranteed to be positive.
\<close>

typedef 'a pos_num = "{ x :: 'a :: linordered_field. x > 0}" morphisms num pos
  by (rule exI[of _ 1], auto)

setup_lifting type_definition_pos_num

lemma num_positive: "num x > 0"
  by (transfer, simp)

text \<open>Using these restricted types, it is often possible to define the desired algorithms
where non-termination because of invalid inputs is no longer possible, 
and where soundness properties
can be stated without additional preconditions. E.g., for the approximation algorithm, one
takes @{term "\<delta> :: rat pos_num"} as input, and the approximation stops, once 
@{term "abs(x^2 - y^2) < num \<delta>"} is satisfied.

One question in the second approach is how to actually generate elements of the restricted type.
Although one can perform the following definition,
\<close>

lift_definition create_pos_1 :: "'a :: linordered_field \<Rightarrow> 'a pos_num option" is
  "\<lambda> x. if x > 0 then Some x else None" 
  by auto

text \<open>\noindent the problem is that corresponding defining equation 
@{thm create_pos_1.abs_eq} is not amenable for code-generation,
as it uses the abstraction function @{term pos} in a way which
is not admitted for code-equations 
\cite{DBLP:conf/itp/HaftmannKKN13, DBLP:conf/flops/HaftmannN10}.

To overcome this problem, Joachim Breitner proposed the following 
workaround\footnote{@{url "http://stackoverflow.com/questions/16273812/working-with-isabelles-code-generator-data-refinement-and-higher-order-functio"}},
which requires an additional type definition, and some auxiliary definitions,
to in the end define @{term create_pos} in a way that is amenable for code-generation.
\<close>

typedef 'a num_bit = "{ (x :: 'a :: linordered_field, b). b \<longrightarrow> x > 0}" by auto

setup_lifting type_definition_num_bit

lift_definition num_bit_bit :: "('a :: linordered_field) num_bit \<Rightarrow> bool" is snd .
lift_definition num_bit_num :: "('a :: linordered_field) num_bit \<Rightarrow> 'a pos_num" is
  "\<lambda> (x,b). if b then x else 42" by auto

lift_definition num_bit :: "'a :: linordered_field \<Rightarrow> 'a num_bit" is
  "\<lambda> x. if x > 0 then (x, True) else (42, False)" by auto

definition create_pos_2 :: "'a :: linordered_field \<Rightarrow> 'a pos_num option" where
  "create_pos_2 x \<equiv> let nb = num_bit x
    in if num_bit_bit nb then Some (num_bit_num nb) else None"

lemma create_pos_2: "create_pos_2 x = Some p \<Longrightarrow> num p = x"
  unfolding create_pos_2_def Let_def by (transfer, simp split: if_splits)

export_code create_pos_2 in Haskell

text \<open>Breitner's construction has the advantage that the invariant @{term "x > 0"} only
  has to be evaluated once (when invoking @{term num_bit}). 
  Hence, the construction allows to create data for types with
  invariants in an efficient, executable, and canonical way.

In this AFP entry we now turned this canonical way into a dedicated method 
(\ldo) which automatically
generates the types and auxiliary functions of Breitner's construction. As a result it suffices
to write:\<close>

lift_definition_option create_pos :: "'a :: linordered_field \<Rightarrow> 'a pos_num option" is
  "\<lambda> x :: 'a. if x > 0 then Some x else None" 
  by auto

text \<open>Afterwards, we can directly generate code.\<close>

export_code create_pos in Haskell

text \<open>Moreover, we automatically generate two soundness theorems, 
that the generated number is the intended one:
@{thm create_pos} and @{thm create_pos_Some}. Here, the morphisms from the type-definitions 
reappear, i.e., @{term num} and @{term pos} in the example.\<close>

section \<open>Usage and limitations\<close>

text \<open>The command \ldo{} 
is useful to generate elements of
some restricted type (say @{typ 'restricted}) which has been defined as
@{term "{x. P x}"} for some property @{term P} of type @{typ "'base \<Rightarrow> bool"}. 
It expects three arguments, namely
\begin{itemize}
\item The name of the definition, e.g., @{term create_pos}.
\item The type of the definition, which must be of the form 
  @{typ "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'a_dots \<Rightarrow> 'a_n \<Rightarrow> 'restricted option"}
\item The right-hand side of the definition which must be of the shape
  @{term "\<lambda> x1 x2 x_dots x_n. if check x1 x2 x_dots x_n then Some (generate x1 x2 x_dots x_n) else None"} 
  where @{term generate} is of type @{typ "'a1 \<Rightarrow> 'a2 \<Rightarrow> 'a_dots \<Rightarrow> 'a_n \<Rightarrow> 'base option"}
\end{itemize}

After providing the three arguments, a proof of 
  @{term "check x1 x2 x_dots x_n \<Longrightarrow> P (generate x1 x2 x_dots x_n)"} has to be provided.
Then, code-equations will be derived and registered, and in addition two
soundness theorems are generated. These are accessible under the names @{term "def_name"} 
and @{term "def_name_Some"},
provided that the lifting definition uses @{term "def_name"} as first argument.

Note, that @{term P} is automatically extracted from the type-definition 
of @{typ 'restricted}. Similarly, the default value (42 in the @{typ "'a pos_num"}-example)
is generated automatically.

To mention a further limitation besides the strict syntactic structure for the right-hand side, 
it is sometimes required, 
to add explicit type-annotations in the right-hand-side and the selector, e.g., 
the @{typ "'a"} in @{term   "\<lambda> x :: 'a :: linordered_field. if x > 0 then Some x else None"}.
\<close>

end
