(*  Title: Term_Index/discrimination_tree.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory,
                Sebastian Willenbrink, Kevin Kappelmann, TU Munich

Discrimination trees based on Pure/net.ML.
Requires operands to be beta-eta-short normalised.
*)
structure Discrimination_Tree : TERM_INDEX =
struct

structure TIB = Term_Index_Base

val norm_term = Term_Normalisation.beta_eta_short

datatype key = CombK | VarK | AtomK of string

(*Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
Any term whose head is a Var is regarded entirely as a Var.
Abstractions are also regarded as Vars; this covers eta-conversion and "near"
eta-conversions such as %x. ?P (?f x).*)
fun add_key_of_terms (t, ks) =
  let fun rands (t, ks) = case t of
    (*other cases impossible due to beta-eta-short norm*)
      t1 $ t2 => CombK :: rands (t1, add_key_of_terms (t2, ks))
    | Const (n, _) => AtomK n :: ks
    | Free (n, _) => AtomK n :: ks
    | Bound i => AtomK (Name.bound i) :: ks
    in case head_of t of
        Var _ => VarK :: ks
      | Abs _ => VarK :: ks
      | _ => rands (t, ks)
  end

(*convert a term to a list of keys*)
fun key_of_term t = add_key_of_terms (t, [])

(*Trees indexed by key lists: each arc is labelled by a key.
Each node contains a list of values, and arcs to children.
The empty key addresses the entire tree.
Lookup functions preserve order of values stored at same level.*)
datatype 'a term_index =
    Leaf of 'a list
  | Tree of {comb: 'a term_index, var: 'a term_index, atoms: 'a term_index Symtab.table}

val empty = Leaf []

fun is_empty (Leaf []) = true
  | is_empty _ = false

val empty_tree = Tree {comb=empty, var=empty, atoms=Symtab.empty}

(* insert *)

(*Adds value x to the list at the node addressed by the keys.
Creates node if not already present.
is_dup decides whether a value is a duplicate.
The empty list of keys generates a Leaf node, others a Tree node.*)
fun insert_keys is_dup x ksdtp = case ksdtp of
    ([], Leaf xs) => if exists is_dup xs then raise TIB.INSERT else Leaf (x :: xs)
  | (keys, Leaf []) => insert_keys is_dup x (keys, empty_tree) (*expand the tree*)
  | (CombK :: keys, Tree {comb, var, atoms}) =>
      Tree {comb=insert_keys is_dup x (keys, comb), var=var, atoms=atoms}
  | (VarK :: keys, Tree {comb, var, atoms}) =>
      Tree {comb=comb, var=insert_keys is_dup x (keys, var), atoms=atoms}
  | (AtomK a :: keys, Tree {comb, var, atoms}) =>
      let val atoms' = Symtab.map_default (a, empty) (fn dt' => insert_keys is_dup x (keys, dt')) atoms
      in Tree {comb=comb, var=var, atoms=atoms'} end

fun insert is_dup (t, x) dt = insert_keys is_dup x (key_of_term t, dt)
fun insert_safe is_dup entry dt = insert is_dup entry dt handle TIB.INSERT => dt

(* delete *)

(*Create a new Tree node if it would be nonempty*)
fun new_tree (args as {comb, var, atoms}) =
  if is_empty comb andalso is_empty var andalso Symtab.is_empty atoms then empty
  else Tree args

(*Deletes values from the list at the node addressed by the keys.
Raises DELETE if absent. Collapses the tree if possible.
sel is the selector for values to be deleted.*)
fun delete_keys sel ksdtp = case ksdtp of
    ([], Leaf xs) => if exists sel xs then Leaf (filter_out sel xs) else raise TIB.DELETE
  | (_, Leaf []) => raise TIB.DELETE
  | (CombK :: keys, Tree {comb, var, atoms}) =>
      new_tree {comb=delete_keys sel (keys,comb), var=var, atoms=atoms}
  | (VarK :: keys, Tree {comb, var, atoms}) =>
      new_tree {comb=comb, var=delete_keys sel (keys,var), atoms=atoms}
  | (AtomK a :: keys, Tree {comb, var, atoms}) =>
      let val atoms' = (case Symtab.lookup atoms a of
          NONE => raise TIB.DELETE
        | SOME dt' =>
            (case delete_keys sel (keys, dt') of
              Leaf [] => Symtab.delete a atoms
            | dt'' => Symtab.update (a, dt'') atoms))
      in new_tree {comb=comb, var=var, atoms=atoms'} end

fun delete eq t dt = delete_keys eq (key_of_term t, dt)
fun delete_safe eq t dt = delete eq t dt handle TIB.DELETE => dt

(* retrievals *)
type 'a retrieval = 'a term_index -> term -> 'a list

fun variants_keys dt keys = case (dt, keys) of
    (Leaf xs, []) => xs
  | (Leaf _, (_ :: _)) => [] (*non-empty keys and empty dt*)
  | (Tree {comb, ...}, (CombK :: keys)) => variants_keys comb keys
  | (Tree {var, ...}, (VarK :: keys)) => variants_keys var keys
  | (Tree {atoms, ...}, (AtomK a :: keys)) =>
      case Symtab.lookup atoms a of
        SOME dt => variants_keys dt keys
      | NONE => []

fun variants dt t = variants_keys dt (key_of_term t)

(*Skipping a term in a tree. Recursively skip 2 levels if a combination*)
fun tree_skip (Leaf _) dts = dts
  | tree_skip (Tree {comb, var, atoms}) dts =
      var :: dts
      |> Symtab.fold (fn (_, dt) => fn dts => dt :: dts) atoms
      (* tree_skip comb [] only skips first term, so another skip is required *)
      |> fold_rev tree_skip (tree_skip comb [])

(*conses the linked tree, if present, to dts*)
fun look1 (atoms, a) dts = case Symtab.lookup atoms a of
    NONE => dts
  | SOME dt => dt :: dts

datatype query = Instances | Generalisations | Unifiables

(*Return the nodes accessible from the term (cons them before trees)
Var in tree matches any term.
Abs or Var in object: for unification, regarded as a wildcard; otherwise only matches a variable.*)
fun query q t dt dts =
  let
    fun rands _ (Leaf _) dts = dts
      | rands t (Tree {comb, atoms, ...}) dts = case t of
            f $ t => fold_rev (query q t) (rands f comb []) dts
          | Const (n, _) => look1 (atoms, n) dts
          | Free (n, _) => look1 (atoms, n) dts
          | Bound i => look1 (atoms, Name.bound i) dts
  in case dt of
      Leaf _ => dts
    | Tree {var, ...} => case (head_of t, q) of
          (Var _, Generalisations) => var :: dts (*only matches Var in dt*)
        | (Var _, _) => tree_skip dt dts
        | (Abs _, Generalisations) => var :: dts (*only a Var can match*)
        (*A var instantiation in the abstraction could allow
        an eta-reduction, so regard the abstraction as a wildcard.*)
        | (Abs _, _) => tree_skip dt dts
        | (_, Instances) => rands t dt dts
        | (_, _) => rands t dt (var :: dts) (*var could also match*)
  end

fun extract_leaves ls = maps (fn Leaf xs => xs) ls

fun generalisations dt t = query Generalisations t dt [] |> extract_leaves
fun unifiables dt t = query Unifiables t dt [] |> extract_leaves
fun instances dt t = query Instances t dt [] |> extract_leaves

(* merge *)

fun cons_fst x (xs, y) = (x :: xs, y)

fun dest (Leaf xs) = map (pair []) xs
  | dest (Tree {comb, var, atoms}) = flat [
      map (cons_fst CombK) (dest comb),
      map (cons_fst VarK) (dest var),
      maps (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) (Symtab.dest atoms)
    ]

fun content dt = map #2 (dest dt)

fun merge eq dt1 dt2 =
  if pointer_eq (dt1, dt2) then dt1
  else if is_empty dt1 then dt2
  else fold (fn (ks, v) => fn dt => insert_keys (curry eq v) v (ks, dt)) (dest dt2) dt1

end
