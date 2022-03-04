signature Database =
  sig
    type db
    val empty : db
    type mode
    val abs2is : mode
    val abs2rel : mode
    val rel2is : mode
    val lookup : mode -> term -> db -> term option
    val insert : mode -> term * term -> db -> db
    val remove_abs : term -> db -> db
    val remove_rel : term -> db -> db
    val remove_is : term -> db -> db
    val merge : db * db -> db

    (* INVARIANTS *)
    (* \<forall> db : db, \<forall> t, t' : term, \<forall> m : mode, lookup m t db = lookup m t' db \<noteq> NONE \<Longrightarrow> t = t' *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2rel t db = SOME v \<and> lookup rel2is v db = SOME u \<Longrightarrow> lookup abs2is t db = SOME u *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2is t db = SOME u \<and> lookup rel2is v db = SOME u \<Longrightarrow> lookup abs2rel t db = SOME v *)
    (* \<forall> db : db, \<forall> t, u, v : term, lookup abs2rel t db = SOME u \<and> lookup abs2is t db = SOME v \<Longrightarrow> lookup rel2is u db = SOME v *)
  end

structure Database : Database = struct
  type db = { ar : (term * term) list
            , af : (term * term) list
            , fr : (term * term) list
            }

  val empty = { ar = []
              , af = []
              , fr = []
              }

  datatype singlemode = Absolute | Relational | Functional

  type mode = singlemode * singlemode

  val abs2is = (Absolute, Relational)

  val abs2rel = (Absolute, Functional)

  val rel2is = (Functional, Relational)

  infix 6 &&&
  val op &&& = Utils.&&&

  infix 5 |||
  fun op ||| (x, y) = fn t =>
    case x t of
      SOME a => SOME a
    | NONE => y t

  infix 5 >>=
  fun op >>= (m, f) =
    case m of
      SOME x => f x
    | NONE => NONE

  infix 6 COMP
  fun op COMP (xs, ys) = fn t => AList.lookup (op aconv) ys t >>= AList.lookup (op aconv) xs

  val transpose = map (#2 &&& #1)

  fun lookup (Absolute, Relational) t db = (#fr db COMP #af db ||| AList.lookup (op aconv) (#ar db)) t
    | lookup (Absolute, Functional) t db = AList.lookup (op aconv) (#af db) t
    | lookup (Functional, Relational) t db = AList.lookup (op aconv) (#fr db) t
    | lookup (Relational, Absolute) t db = (transpose (#af db) COMP transpose (#fr db) ||| AList.lookup (op aconv) (transpose (#ar db))) t
    | lookup (Functional, Absolute) t db = AList.lookup (op aconv) (transpose (#af db)) t
    | lookup (Relational, Functional) t db = AList.lookup (op aconv) (transpose (#fr db)) t
    | lookup _ _ _ = error "lookup: unreachable clause"

  fun insert' warn (mode as (Absolute, Relational)) (t, u) db =
      (case lookup mode t db of
        SOME _ => (warn ("insert abs2is: duplicate entry for " ^ (@{make_string} t)); db)
      | NONE => case lookup (Relational, Functional) u db of
                  SOME v => if is_none (lookup (Functional, Absolute) v db)
                              then { ar = #ar db
                                   , af = AList.update (op aconv) (t, v) (#af db)
                                   , fr = #fr db
                                   }
                              else error "invariant violation, insert abs2is"
                | NONE => case lookup (Absolute, Functional) t db of
                            SOME v => { ar = #ar db
                                      , af = #af db
                                      , fr = AList.update (op aconv) (v, u) (#fr db)
                                      }
                          | NONE => { ar = AList.update (op aconv) (t, u) (#ar db)
                                    , af = #af db
                                    , fr = #fr db
                                    }
      )
    | insert' warn (mode as (Absolute, Functional)) (t, v) db =
      (case lookup mode t db of
        SOME _ => (warn ("insert abs2rel: duplicate entry for " ^ (@{make_string} t)); db)
      | NONE => case lookup (Functional, Relational) v db of
                  SOME u => (case lookup (Relational, Absolute) u db of
                              NONE => { ar = #ar db
                                      , af = AList.update (op aconv) (t, v) (#af db)
                                      , fr = #fr db
                                      }
                            | SOME t' => if t = t'
                                           then { ar = AList.delete (op aconv) t (#ar db)
                                                , af = AList.update (op aconv) (t, v) (#af db)
                                                , fr = #fr db
                                                }
                                           else error "invariant violation, insert abs2rel"
                            )
                | NONE => case lookup (Absolute, Relational) t db of
                            SOME u => { ar = AList.delete (op aconv) t (#ar db)
                                      , af = AList.update (op aconv) (t, v) (#af db)
                                      , fr = AList.update (op aconv) (v, u) (#fr db)
                                      }
                          | NONE => { ar = #ar db
                                    , af = AList.update (op aconv) (t, v) (#af db)
                                    , fr = #fr db
                                    }
      )
    | insert' warn (mode as (Functional, Relational)) (v, u) db =
      (case lookup mode v db of
        SOME _ => (warn ("insert rel2is: duplicate entry for " ^ (@{make_string} v)); db)
      | NONE => case (lookup (Functional, Absolute) v db, lookup (Relational, Absolute) u db) of
                  (SOME t, SOME t') => if t = t'
                                         then { ar = AList.delete (op aconv) t (#ar db)
                                              , af = #af db
                                              , fr = AList.update (op aconv) (v, u) (#fr db)
                                              }
                                         else error ("invariant violation, insert rel2is: " ^ (@{make_string} (v, u, t, t')))
                | (SOME _, NONE) => { ar = #ar db
                                    , af = #af db
                                    , fr = AList.update (op aconv) (v, u) (#fr db)
                                    }
                | (NONE, SOME t') => { ar = AList.delete (op aconv) t' (#ar db)
                                     , af = AList.update (op aconv) (t', v) (#af db)
                                     , fr = AList.update (op aconv) (v, u) (#fr db)
                                     }
                | (NONE, NONE) => { ar = #ar db
                                  , af = #af db
                                  , fr = AList.update (op aconv) (v, u) (#fr db)
                                  }
      )
    | insert' _ _ _ _ = error "insert: unreachable clause"

  val insert = insert' warning

  fun remove Absolute t db = { ar = AList.delete (op aconv) t (#ar db)
                             , af = AList.delete (op aconv) t (#af db)
                             , fr = #fr db
                             }
    | remove Functional v db =
      (case lookup (Functional, Absolute) v db of
        SOME t => (case lookup (Functional, Relational) v db of
                    SOME u => { ar = AList.update (op aconv) (t, u) (#ar db)
                              , af = transpose (AList.delete (op aconv) v (transpose (#af db)))
                              , fr = AList.delete (op aconv) v (#fr db)
                              }
                  | NONE => { ar = #ar db
                            , af = transpose (AList.delete (op aconv) v (transpose (#af db)))
                            , fr = #fr db
                            }
                  )
      | NONE => { ar = #ar db
                , af = #af db
                , fr = AList.delete (op aconv) v (#fr db)
                }
      )
    | remove Relational u db = { ar = transpose (AList.delete (op aconv) u (transpose (#ar db)))
                               , af = #af db
                               , fr = transpose (AList.delete (op aconv) u (transpose (#fr db)))
                               }

  val remove_abs = remove Absolute

  val remove_rel = remove Functional

  val remove_is = remove Relational

  fun merge (db, db') =
    let
      val modes = [(abs2rel, #af db'), (rel2is, #fr db'), (abs2is, #ar db)]
    in
      List.foldr (fn ((m, db'), db) => List.foldr (uncurry (insert' (K ())  m)) db db') db modes
    end
end (* structure Database : Database *)