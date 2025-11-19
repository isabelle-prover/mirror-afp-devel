(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* sets with universal set representation *)
signature UNIV_SET =
sig
  structure Key: KEY
  type elem
  type T
  val empty: T
  val build: (T -> T) -> T
  val univ: T
  val is_empty: T -> bool
  val is_univ: T -> bool
  val fold: 'a (* for universal set *) -> (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val fold_rev: 'a (* for universal set *) -> (elem -> 'a -> 'a) -> T -> 'a -> 'a
  val size: T -> int option (* NONE for universal set *)
  val dest: T -> elem list option (* NONE for universal set *)
  val min: T -> elem option
  val max: T -> elem option
  val exists: bool (* for universal set *) -> (elem -> bool) -> T -> bool
  val forall: bool (* for universal set *) -> (elem -> bool) -> T -> bool
  val get_first: (elem -> 'a option) -> T -> 'a option
  val member: T -> elem -> bool
  val subset: T * T -> bool
  val eq_set: T * T -> bool
  val ord: T ord
  val insert: elem -> T -> T
  val make: elem list -> T
  val merge: T * T -> T
  val merges: T list -> T
  val inter: T -> T -> T
  val union: T -> T -> T
  val remove: elem -> T -> T option
  val subtract: T -> T -> T option
end

functor Univ_Set(Key: KEY): UNIV_SET =
struct
  structure Key = Key;
  type elem = Key.key;
  structure Set = Set(Key)
  datatype T =
  Univ | Set of Set.T

val empty = Set Set.empty
fun build (f: T -> T) = f empty;

val univ = Univ
fun is_empty Univ = false
  | is_empty (Set x) = Set.is_empty x
fun is_univ Univ = true
  | is_univ (Set _) = false
      
fun fold_top_set t _ Univ _ = t
  | fold_top_set _ f (Set x) acc = Set.fold f x acc
fun fold_top_set_rev t _ Univ _ = t
  | fold_top_set_rev _ f (Set x) acc = Set.fold_rev f x acc

fun size Univ = NONE
  | size (Set s) = SOME (Set.size s)

fun dest Univ = NONE
  | dest (Set s) = SOME (Set.dest s)

fun min Univ = NONE
  | min (Set s) = Set.min s

fun max Univ = NONE
  | max (Set s) = Set.max s

fun member Univ _ = true
  | member (Set s) x = Set.member s x

fun subset (_, Univ) = true
  | subset (Univ, Set _) = false
  | subset (Set x, Set y) = Set.subset (x, y)

fun eq_set (Univ, Univ) = true
  | eq_set (Set x, Set y) = Set.eq_set (x, y)
  | eq_set (_, _) = false

val fold = fold_top_set
val fold_rev = fold_top_set_rev

fun ord (Univ, Univ) = EQUAL
  | ord (Set _, Univ) = LESS
  | ord (Univ, Set _) = GREATER
  | ord (Set x, Set y) = Set.ord (x, y)

fun insert _ Univ = Univ
  | insert x (Set s) = Set (Set.insert x s)

val make = Set o Set.make
fun merge (Set x, Set y) = Set (Set.merge (x, y))
  | merge (_, _) = Univ
fun merges [] = empty
  | merges (x::xs) = merge (x, merges xs)

fun inter (Set x) (Set y) = Set (Set.inter x y)
  | inter x Univ = x
  | inter Univ x = x

fun union (Set x) (Set y) = Set (Set.union x y)
  | union _ Univ = Univ
  | union Univ _ = Univ

fun remove _ Univ = NONE
  | remove x (Set s) = SOME (Set (Set.remove x s))

fun subtract Univ _ = SOME empty
  | subtract (Set x) (Set y) = SOME (Set (Set.subtract x y))
  | subtract (Set _) Univ = NONE

fun exists _ p (Set x) = Set.exists p x
  | exists d _ (Univ) = d

fun forall _ p (Set x) = Set.forall p x
  | forall d _ Univ = d

fun get_first f Univ = NONE
  | get_first f (Set x) = Set.get_first f x

val _ = 
  ML_system_pp (fn depth => fn _ => 
    (fn Univ => ML_Pretty.str "Univ" 
  | Set x => ML_Pretty.enum "," "{" "}" ML_system_pretty (Set.dest x, depth)));
end

structure Intuset = Univ_Set (Inttab.Key);
structure Symuset = Univ_Set (Symtab.Key);