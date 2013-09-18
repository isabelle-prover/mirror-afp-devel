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

theory Set_Impl_Generator
imports 
  Container_Generator_Aux
  "../Containers/Set_Impl"
begin

subsection {* Generator for the @{class set_impl}-class of the container framework *}

text {*
This generator registers itself at the derive-manager for the classes @{class set_impl}.
Here, one can choose
the desired implementation via the parameter. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (rbt,dlist,collect,monad,choose) set-impl}
\end{itemize}
*}


text {*
This generator can be used for arbitrary types, not just datatypes. 
*}

ML_file "set_impl_generator.ML" 

setup {*
  Set_Impl_Generator.setup
*}

end
