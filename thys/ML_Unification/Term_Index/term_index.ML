(*  Title: Term_Index/term_index.ML
    Author: Kevin Kappelmann, Sebastian Willenbrink

Signatures for term indexes. For a brief overview, see:
https://en.wikipedia.org/wiki/Term_indexing
*)
signature TERM_INDEX_BASE =
sig
  exception INSERT
  exception DELETE
end

structure Term_Index_Base : TERM_INDEX_BASE =
struct
  exception INSERT
  exception DELETE
end

signature TERM_INDEX =
sig
  type 'a term_index
  val empty : 'a term_index
  val is_empty : 'a term_index -> bool
  val content : 'a term_index -> 'a list

  (*puts a term into normal form as required by the index structure*)
  val norm_term : Term_Normalisation.term_normaliser
  (*first argument decides which values should be considered as duplicates;
  raises Term_Index_Base.INSERT if the term, value pair is already inserted*)
  val insert : ('a -> bool) -> (term * 'a) -> 'a term_index -> 'a term_index
  val insert_safe : ('a -> bool) -> (term * 'a) -> 'a term_index -> 'a term_index

  (*first argument selects which values for the given term should be removed;
  raises Term_Index_Base.DELETE if no value is deleted*)
  val delete : ('a -> bool) -> term -> 'a term_index -> 'a term_index
  val delete_safe : ('a -> bool) -> term -> 'a term_index -> 'a term_index

  type 'a retrieval = 'a term_index -> term -> 'a list
  val variants : 'a retrieval
  val generalisations : 'a retrieval
  val instances : 'a retrieval
  val unifiables : 'a retrieval

  (*first argument is the equality test for values*)
  val merge : (('a * 'a) -> bool) -> 'a term_index -> 'a term_index -> 'a term_index
end