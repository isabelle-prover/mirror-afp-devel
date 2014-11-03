(*  
    Title:      Rank.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section{*Rank of a matrix*}

theory Rank
imports 
      "../Rank_Nullity_Theorem/Dim_Formula"
begin

subsection{*Row rank, column rank and rank*}

text{*Definitions of row rank, column rank and rank*}

definition row_rank :: "'a::{field}^'n^'m=>nat"
  where "row_rank A = vec.dim (row_space A)"

definition col_rank :: "'a::{field}^'n^'m=>nat"
  where "col_rank A = vec.dim (col_space A)"

definition rank :: "'a::{field}^'n^'m=>nat"
  where "rank A = row_rank A"

subsection{*Properties*}

lemma rrk_is_preserved:
fixes A::"'a::{field}^'cols^'rows::{finite, wellorder}"
  and P::"'a::{field}^'rows::{finite, wellorder}^'rows::{finite, wellorder}"
assumes inv_P: "invertible P"
shows "row_rank A = row_rank (P**A)"
by (metis row_space_is_preserved row_rank_def inv_P)

lemma crk_is_preserved:
fixes A::"'a::{field}^'cols::{finite, wellorder}^'rows"
  and P::"'a::{field}^'rows^'rows"
assumes inv_P: "invertible P"
shows "col_rank A = col_rank (P**A)"
  using rank_nullity_theorem_matrices unfolding ncols_def 
  by (metis col_rank_def inv_P nat_add_left_cancel null_space_is_preserved) 

end

