(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

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

theory Corder_Generator
imports Container_Generator_Aux
  "../Containers/Collection_Order"
  "Order_Generator"
begin

subsection {* Generator for the @{class corder}-class *}

text {*
This generator registers itself at the derive-manager for the class
@{class corder}. To be more precise, one can choose whether one does not want to
support a linear order by passing parameter "no", one wants to register an arbitrary type which
is already in class @{class linorder} using parameter "linorder", or
one wants to generate a new linear order by passing no parameter.
In the last case, one demands that the type is a datatype
and that all non-recursive types of that datatype are in class @{class linorder}. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (no) corder}
\item \texttt{instantiation type :: (linorder,\ldots,linorder) corder}
\item \texttt{instantiation datatype :: (linorder,\ldots,linorder) (linorder) corder}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{term is_corder}-theorem is automatically generated and attributed with 
\texttt{[simp, code-post]}.
*}


text {* 
To create a new ordering, we just invoke the functionality provided by the order generator.
The only difference is the boilerplate-code, which for the order generator has to perform
the class instantiation for an order, whereas here we have to invoke the methods to 
satisfy the corresponding locale for linear orders.
*}

text {*
This generator can be used for arbitrary types, not just datatypes. 
When passing no parameters, we get same limitation as for the order generator.
For mutual recursive datatypes, only for the first mentioned datatype the instantiations 
of the @{class corder} classes are derived.
*}

lemma corder_intro: "class.linorder le lt \<Longrightarrow> a = Some (le, lt)\<Longrightarrow> a = Some (le',lt') \<Longrightarrow>
  class.linorder le' lt'" by auto

ML_file "corder_generator.ML"

setup {*
  Corder_Generator.setup
*}


end
