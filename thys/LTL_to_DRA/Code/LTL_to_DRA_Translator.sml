structure LTL_to_DRA_Translator : sig
  datatype 'a ltl = LTLTrue | LTLFalse | LTLProp of 'a | LTLPropNeg of 'a |
    LTLAnd of 'a ltl * 'a ltl | LTLOr of 'a ltl * 'a ltl | LTLNext of 'a ltl |
    LTLGlobal of 'a ltl | LTLFinal of 'a ltl | LTLUntil of 'a ltl * 'a ltl
  datatype 'a set = Set of 'a list | Coset of 'a list
  datatype ('a, 'b) mapping = Mapping of ('a * 'b) list
  datatype 'a ltl_prop_equiv_quotient = Abs of 'a ltl
  datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc
    | LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
    LTLcImplies of 'a ltlc * 'a ltlc | LTLcIff of 'a ltlc * 'a ltlc |
    LTLcNext of 'a ltlc | LTLcFinal of 'a ltlc | LTLcGlobal of 'a ltlc |
    LTLcUntil of 'a ltlc * 'a ltlc | LTLcRelease of 'a ltlc * 'a ltlc
  val ltlc_to_rabin :
    string ltlc ->
      ((string ltl_prop_equiv_quotient *
         (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
        (string set *
          (string ltl_prop_equiv_quotient *
            (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
        set *
        ((string ltl_prop_equiv_quotient *
           (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
          (((string ltl_prop_equiv_quotient *
              (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
             (string set *
               (string ltl_prop_equiv_quotient *
                 (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
             set *
            ((string ltl_prop_equiv_quotient *
               (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
              (string set *
                (string ltl_prop_equiv_quotient *
                  (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
              set
              set)
            set)
  val ltlc_to_rabin_UU :
    string ltlc ->
      ((string ltl_prop_equiv_quotient *
         (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
        (string set *
          (string ltl_prop_equiv_quotient *
            (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
        set *
        ((string ltl_prop_equiv_quotient *
           (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
          (((string ltl_prop_equiv_quotient *
              (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
             (string set *
               (string ltl_prop_equiv_quotient *
                 (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
             set *
            ((string ltl_prop_equiv_quotient *
               (string ltl, (string ltl_prop_equiv_quotient list)) mapping) *
              (string set *
                (string ltl_prop_equiv_quotient *
                  (string ltl, (string ltl_prop_equiv_quotient list)) mapping)))
              set
              set)
            set)
end = struct

datatype 'a ltl = LTLTrue | LTLFalse | LTLProp of 'a | LTLPropNeg of 'a |
  LTLAnd of 'a ltl * 'a ltl | LTLOr of 'a ltl * 'a ltl | LTLNext of 'a ltl |
  LTLGlobal of 'a ltl | LTLFinal of 'a ltl | LTLUntil of 'a ltl * 'a ltl;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_ltla A_ (LTLFinal x9) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLFinal x9) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLNext x7) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLNext x7) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLProp x3) (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) (LTLProp x3) = false
  | equal_ltla A_ LTLFalse (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) LTLFalse = false
  | equal_ltla A_ LTLFalse (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) LTLFalse = false
  | equal_ltla A_ LTLTrue (LTLUntil (x101, x102)) = false
  | equal_ltla A_ (LTLUntil (x101, x102)) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLFinal x9) = false
  | equal_ltla A_ (LTLFinal x9) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLGlobal x8) = false
  | equal_ltla A_ (LTLGlobal x8) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLNext x7) = false
  | equal_ltla A_ (LTLNext x7) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLOr (x61, x62)) = false
  | equal_ltla A_ (LTLOr (x61, x62)) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLAnd (x51, x52)) = false
  | equal_ltla A_ (LTLAnd (x51, x52)) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLPropNeg x4) = false
  | equal_ltla A_ (LTLPropNeg x4) LTLTrue = false
  | equal_ltla A_ LTLTrue (LTLProp x3) = false
  | equal_ltla A_ (LTLProp x3) LTLTrue = false
  | equal_ltla A_ LTLTrue LTLFalse = false
  | equal_ltla A_ LTLFalse LTLTrue = false
  | equal_ltla A_ (LTLUntil (x101, x102)) (LTLUntil (y101, y102)) =
    equal_ltla A_ x101 y101 andalso equal_ltla A_ x102 y102
  | equal_ltla A_ (LTLFinal x9) (LTLFinal y9) = equal_ltla A_ x9 y9
  | equal_ltla A_ (LTLGlobal x8) (LTLGlobal y8) = equal_ltla A_ x8 y8
  | equal_ltla A_ (LTLNext x7) (LTLNext y7) = equal_ltla A_ x7 y7
  | equal_ltla A_ (LTLOr (x61, x62)) (LTLOr (y61, y62)) =
    equal_ltla A_ x61 y61 andalso equal_ltla A_ x62 y62
  | equal_ltla A_ (LTLAnd (x51, x52)) (LTLAnd (y51, y52)) =
    equal_ltla A_ x51 y51 andalso equal_ltla A_ x52 y52
  | equal_ltla A_ (LTLPropNeg x4) (LTLPropNeg y4) = eq A_ x4 y4
  | equal_ltla A_ (LTLProp x3) (LTLProp y3) = eq A_ x3 y3
  | equal_ltla A_ LTLFalse LTLFalse = true
  | equal_ltla A_ LTLTrue LTLTrue = true;

fun equal_ltl A_ = {equal = equal_ltla A_} : 'a ltl equal;

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun pred_list p [] = true
  | pred_list p (x :: xs) = p x andalso pred_list p xs;

datatype 'a set = Set of 'a list | Coset of 'a list;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun less_eq_set A_ (Coset []) (Set []) = false
  | less_eq_set A_ a (Coset ys) = pred_list (fn y => not (member A_ y a)) ys
  | less_eq_set A_ (Set xs) b = pred_list (fn x => member A_ x b) xs;

fun equal_seta A_ a b = less_eq_set A_ a b andalso less_eq_set A_ b a;

fun equal_set A_ = {equal = equal_seta A_} : 'a set equal;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun fst (x1, x2) = x1;

datatype ('a, 'b) mapping = Mapping of ('a * 'b) list;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun equal_mappinga A_ B_ (Mapping xs) (Mapping ys) =
  let
    val ks = map fst xs;
    val ls = map fst ys;
  in
    pred_list (membera A_ ks) ls andalso
      pred_list
        (fn k =>
          membera A_ ls k andalso
            equal_option B_ (map_of A_ xs k) (map_of A_ ys k))
        ks
  end;

fun equal_mapping A_ B_ = {equal = equal_mappinga A_ B_} :
  ('a, 'b) mapping equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype 'a ifex = Trueif | Falseif | IF of 'a * 'a ifex * 'a ifex;

fun equal_ifex A_ Falseif (IF (x31, x32, x33)) = false
  | equal_ifex A_ (IF (x31, x32, x33)) Falseif = false
  | equal_ifex A_ Trueif (IF (x31, x32, x33)) = false
  | equal_ifex A_ (IF (x31, x32, x33)) Trueif = false
  | equal_ifex A_ Trueif Falseif = false
  | equal_ifex A_ Falseif Trueif = false
  | equal_ifex A_ (IF (x31, x32, x33)) (IF (y31, y32, y33)) =
    eq A_ x31 y31 andalso (equal_ifex A_ x32 y32 andalso equal_ifex A_ x33 y33)
  | equal_ifex A_ Falseif Falseif = true
  | equal_ifex A_ Trueif Trueif = true;

fun mkIF A_ x t1 t2 = (if equal_ifex A_ t1 t2 then t1 else IF (x, t1, t2));

fun reduce_alist A_ xs (IF (x, t1, t2)) =
  (case map_of A_ xs x
    of NONE =>
      mkIF A_ x (reduce_alist A_ ((x, true) :: xs) t1)
        (reduce_alist A_ ((x, false) :: xs) t2)
    | SOME b => reduce_alist A_ xs (if b then t1 else t2))
  | reduce_alist A_ uu Trueif = Trueif
  | reduce_alist A_ uu Falseif = Falseif;

fun normif_alist A_ xs Trueif t1 t2 = reduce_alist A_ xs t1
  | normif_alist A_ xs Falseif t1 t2 = reduce_alist A_ xs t2
  | normif_alist A_ xs (IF (x, t1, t2)) t3 t4 =
    (case map_of A_ xs x
      of NONE =>
        mkIF A_ x (normif_alist A_ ((x, true) :: xs) t1 t3 t4)
          (normif_alist A_ ((x, false) :: xs) t2 t3 t4)
      | SOME true => normif_alist A_ xs t1 t3 t4
      | SOME false => normif_alist A_ xs t2 t3 t4);

fun equiv_test B_ ifex_of b1 b2 =
  let
    val t1 = ifex_of b1;
    val t2 = ifex_of b2;
  in
    equal_ifex B_ Trueif
      (normif_alist B_ [] t1 t2 (normif_alist B_ [] t2 Falseif Trueif))
  end;

fun ifex_of_ltl A_ LTLTrue = Trueif
  | ifex_of_ltl A_ LTLFalse = Falseif
  | ifex_of_ltl A_ (LTLAnd (phi, psi)) =
    normif_alist (equal_ltl A_) [] (ifex_of_ltl A_ phi) (ifex_of_ltl A_ psi)
      Falseif
  | ifex_of_ltl A_ (LTLOr (phi, psi)) =
    normif_alist (equal_ltl A_) [] (ifex_of_ltl A_ phi) Trueif
      (ifex_of_ltl A_ psi)
  | ifex_of_ltl A_ (LTLProp v) = IF (LTLProp v, Trueif, Falseif)
  | ifex_of_ltl A_ (LTLPropNeg v) = IF (LTLPropNeg v, Trueif, Falseif)
  | ifex_of_ltl A_ (LTLNext v) = IF (LTLNext v, Trueif, Falseif)
  | ifex_of_ltl A_ (LTLGlobal v) = IF (LTLGlobal v, Trueif, Falseif)
  | ifex_of_ltl A_ (LTLFinal v) = IF (LTLFinal v, Trueif, Falseif)
  | ifex_of_ltl A_ (LTLUntil (v, va)) = IF (LTLUntil (v, va), Trueif, Falseif);

fun ltl_prop_equiv A_ phi psi =
  equiv_test (equal_ltl A_) (ifex_of_ltl A_) phi psi;

datatype 'a ltl_prop_equiv_quotient = Abs of 'a ltl;

fun ltl_prop_equiv_quotient_eq_test A_ (Abs xb) (Abs x) =
  ltl_prop_equiv A_ xb x;

fun equal_ltl_prop_equiv_quotienta A_ = ltl_prop_equiv_quotient_eq_test A_;

fun equal_ltl_prop_equiv_quotient A_ =
  {equal = equal_ltl_prop_equiv_quotienta A_} :
  'a ltl_prop_equiv_quotient equal;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a ltlc = LTLcTrue | LTLcFalse | LTLcProp of 'a | LTLcNeg of 'a ltlc |
  LTLcAnd of 'a ltlc * 'a ltlc | LTLcOr of 'a ltlc * 'a ltlc |
  LTLcImplies of 'a ltlc * 'a ltlc | LTLcIff of 'a ltlc * 'a ltlc |
  LTLcNext of 'a ltlc | LTLcFinal of 'a ltlc | LTLcGlobal of 'a ltlc |
  LTLcUntil of 'a ltlc * 'a ltlc | LTLcRelease of 'a ltlc * 'a ltlc;

fun id x = (fn xa => xa) x;

fun unf (LTLFinal phi) = LTLOr (LTLFinal phi, unf phi)
  | unf (LTLGlobal phi) = LTLAnd (LTLGlobal phi, unf phi)
  | unf (LTLUntil (phi, psi)) =
    LTLOr (LTLAnd (LTLUntil (phi, psi), unf phi), unf psi)
  | unf (LTLAnd (phi, psi)) = LTLAnd (unf phi, unf psi)
  | unf (LTLOr (phi, psi)) = LTLOr (unf phi, unf psi)
  | unf LTLTrue = LTLTrue
  | unf LTLFalse = LTLFalse
  | unf (LTLProp v) = LTLProp v
  | unf (LTLPropNeg v) = LTLPropNeg v
  | unf (LTLNext v) = LTLNext v;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun ball (Set xs) p = pred_list p xs;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun image f (Set xs) = Set (map f xs);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun union A_ = fold (inserta A_);

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun gen_dfs succs ins memb s (x :: xs) =
  (if memb x s then gen_dfs succs ins memb s xs
    else gen_dfs succs ins memb (ins x s) (succs x @ xs))
  | gen_dfs succs ins memb s [] = s;

fun and_absa (Abs xa) (Abs x) = Abs (LTLAnd (xa, x));

fun and_abs xs = foldl and_absa (Abs LTLTrue) xs;

fun remove_constants_P (LTLAnd (phi, psi)) =
  (case remove_constants_P phi of LTLTrue => remove_constants_P psi
    | LTLFalse => LTLFalse
    | LTLProp a =>
      (case remove_constants_P psi of LTLTrue => LTLProp a
        | LTLFalse => LTLFalse | LTLProp aa => LTLAnd (LTLProp a, LTLProp aa)
        | LTLPropNeg aa => LTLAnd (LTLProp a, LTLPropNeg aa)
        | LTLAnd (ltl1, ltl2) => LTLAnd (LTLProp a, LTLAnd (ltl1, ltl2))
        | LTLOr (ltl1, ltl2) => LTLAnd (LTLProp a, LTLOr (ltl1, ltl2))
        | LTLNext ltl => LTLAnd (LTLProp a, LTLNext ltl)
        | LTLGlobal ltl => LTLAnd (LTLProp a, LTLGlobal ltl)
        | LTLFinal ltl => LTLAnd (LTLProp a, LTLFinal ltl)
        | LTLUntil (ltl1, ltl2) => LTLAnd (LTLProp a, LTLUntil (ltl1, ltl2)))
    | LTLPropNeg a =>
      (case remove_constants_P psi of LTLTrue => LTLPropNeg a
        | LTLFalse => LTLFalse | LTLProp aa => LTLAnd (LTLPropNeg a, LTLProp aa)
        | LTLPropNeg aa => LTLAnd (LTLPropNeg a, LTLPropNeg aa)
        | LTLAnd (ltl1, ltl2) => LTLAnd (LTLPropNeg a, LTLAnd (ltl1, ltl2))
        | LTLOr (ltl1, ltl2) => LTLAnd (LTLPropNeg a, LTLOr (ltl1, ltl2))
        | LTLNext ltl => LTLAnd (LTLPropNeg a, LTLNext ltl)
        | LTLGlobal ltl => LTLAnd (LTLPropNeg a, LTLGlobal ltl)
        | LTLFinal ltl => LTLAnd (LTLPropNeg a, LTLFinal ltl)
        | LTLUntil (ltl1, ltl2) => LTLAnd (LTLPropNeg a, LTLUntil (ltl1, ltl2)))
    | LTLAnd (ltl1, ltl2) =>
      (case remove_constants_P psi of LTLTrue => LTLAnd (ltl1, ltl2)
        | LTLFalse => LTLFalse
        | LTLProp a => LTLAnd (LTLAnd (ltl1, ltl2), LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLAnd (ltl1, ltl2), LTLPropNeg a)
        | LTLAnd (ltl1a, ltl2a) =>
          LTLAnd (LTLAnd (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
        | LTLOr (ltl1a, ltl2a) =>
          LTLAnd (LTLAnd (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
        | LTLNext ltl => LTLAnd (LTLAnd (ltl1, ltl2), LTLNext ltl)
        | LTLGlobal ltl => LTLAnd (LTLAnd (ltl1, ltl2), LTLGlobal ltl)
        | LTLFinal ltl => LTLAnd (LTLAnd (ltl1, ltl2), LTLFinal ltl)
        | LTLUntil (ltl1a, ltl2a) =>
          LTLAnd (LTLAnd (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))
    | LTLOr (ltl1, ltl2) =>
      (case remove_constants_P psi of LTLTrue => LTLOr (ltl1, ltl2)
        | LTLFalse => LTLFalse
        | LTLProp a => LTLAnd (LTLOr (ltl1, ltl2), LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLOr (ltl1, ltl2), LTLPropNeg a)
        | LTLAnd (ltl1a, ltl2a) =>
          LTLAnd (LTLOr (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
        | LTLOr (ltl1a, ltl2a) =>
          LTLAnd (LTLOr (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
        | LTLNext ltl => LTLAnd (LTLOr (ltl1, ltl2), LTLNext ltl)
        | LTLGlobal ltl => LTLAnd (LTLOr (ltl1, ltl2), LTLGlobal ltl)
        | LTLFinal ltl => LTLAnd (LTLOr (ltl1, ltl2), LTLFinal ltl)
        | LTLUntil (ltl1a, ltl2a) =>
          LTLAnd (LTLOr (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))
    | LTLNext ltl =>
      (case remove_constants_P psi of LTLTrue => LTLNext ltl
        | LTLFalse => LTLFalse | LTLProp a => LTLAnd (LTLNext ltl, LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLNext ltl, LTLPropNeg a)
        | LTLAnd (ltl1, ltl2) => LTLAnd (LTLNext ltl, LTLAnd (ltl1, ltl2))
        | LTLOr (ltl1, ltl2) => LTLAnd (LTLNext ltl, LTLOr (ltl1, ltl2))
        | LTLNext ltla => LTLAnd (LTLNext ltl, LTLNext ltla)
        | LTLGlobal ltla => LTLAnd (LTLNext ltl, LTLGlobal ltla)
        | LTLFinal ltla => LTLAnd (LTLNext ltl, LTLFinal ltla)
        | LTLUntil (ltl1, ltl2) => LTLAnd (LTLNext ltl, LTLUntil (ltl1, ltl2)))
    | LTLGlobal ltl =>
      (case remove_constants_P psi of LTLTrue => LTLGlobal ltl
        | LTLFalse => LTLFalse | LTLProp a => LTLAnd (LTLGlobal ltl, LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLGlobal ltl, LTLPropNeg a)
        | LTLAnd (ltl1, ltl2) => LTLAnd (LTLGlobal ltl, LTLAnd (ltl1, ltl2))
        | LTLOr (ltl1, ltl2) => LTLAnd (LTLGlobal ltl, LTLOr (ltl1, ltl2))
        | LTLNext ltla => LTLAnd (LTLGlobal ltl, LTLNext ltla)
        | LTLGlobal ltla => LTLAnd (LTLGlobal ltl, LTLGlobal ltla)
        | LTLFinal ltla => LTLAnd (LTLGlobal ltl, LTLFinal ltla)
        | LTLUntil (ltl1, ltl2) =>
          LTLAnd (LTLGlobal ltl, LTLUntil (ltl1, ltl2)))
    | LTLFinal ltl =>
      (case remove_constants_P psi of LTLTrue => LTLFinal ltl
        | LTLFalse => LTLFalse | LTLProp a => LTLAnd (LTLFinal ltl, LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLFinal ltl, LTLPropNeg a)
        | LTLAnd (ltl1, ltl2) => LTLAnd (LTLFinal ltl, LTLAnd (ltl1, ltl2))
        | LTLOr (ltl1, ltl2) => LTLAnd (LTLFinal ltl, LTLOr (ltl1, ltl2))
        | LTLNext ltla => LTLAnd (LTLFinal ltl, LTLNext ltla)
        | LTLGlobal ltla => LTLAnd (LTLFinal ltl, LTLGlobal ltla)
        | LTLFinal ltla => LTLAnd (LTLFinal ltl, LTLFinal ltla)
        | LTLUntil (ltl1, ltl2) => LTLAnd (LTLFinal ltl, LTLUntil (ltl1, ltl2)))
    | LTLUntil (ltl1, ltl2) =>
      (case remove_constants_P psi of LTLTrue => LTLUntil (ltl1, ltl2)
        | LTLFalse => LTLFalse
        | LTLProp a => LTLAnd (LTLUntil (ltl1, ltl2), LTLProp a)
        | LTLPropNeg a => LTLAnd (LTLUntil (ltl1, ltl2), LTLPropNeg a)
        | LTLAnd (ltl1a, ltl2a) =>
          LTLAnd (LTLUntil (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
        | LTLOr (ltl1a, ltl2a) =>
          LTLAnd (LTLUntil (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
        | LTLNext ltl => LTLAnd (LTLUntil (ltl1, ltl2), LTLNext ltl)
        | LTLGlobal ltl => LTLAnd (LTLUntil (ltl1, ltl2), LTLGlobal ltl)
        | LTLFinal ltl => LTLAnd (LTLUntil (ltl1, ltl2), LTLFinal ltl)
        | LTLUntil (ltl1a, ltl2a) =>
          LTLAnd (LTLUntil (ltl1, ltl2), LTLUntil (ltl1a, ltl2a))))
  | remove_constants_P (LTLOr (phi, psi)) =
    (case remove_constants_P phi of LTLTrue => LTLTrue
      | LTLFalse => remove_constants_P psi
      | LTLProp a =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLProp a | LTLProp aa => LTLOr (LTLProp a, LTLProp aa)
          | LTLPropNeg aa => LTLOr (LTLProp a, LTLPropNeg aa)
          | LTLAnd (ltl1, ltl2) => LTLOr (LTLProp a, LTLAnd (ltl1, ltl2))
          | LTLOr (ltl1, ltl2) => LTLOr (LTLProp a, LTLOr (ltl1, ltl2))
          | LTLNext ltl => LTLOr (LTLProp a, LTLNext ltl)
          | LTLGlobal ltl => LTLOr (LTLProp a, LTLGlobal ltl)
          | LTLFinal ltl => LTLOr (LTLProp a, LTLFinal ltl)
          | LTLUntil (ltl1, ltl2) => LTLOr (LTLProp a, LTLUntil (ltl1, ltl2)))
      | LTLPropNeg a =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLPropNeg a
          | LTLProp aa => LTLOr (LTLPropNeg a, LTLProp aa)
          | LTLPropNeg aa => LTLOr (LTLPropNeg a, LTLPropNeg aa)
          | LTLAnd (ltl1, ltl2) => LTLOr (LTLPropNeg a, LTLAnd (ltl1, ltl2))
          | LTLOr (ltl1, ltl2) => LTLOr (LTLPropNeg a, LTLOr (ltl1, ltl2))
          | LTLNext ltl => LTLOr (LTLPropNeg a, LTLNext ltl)
          | LTLGlobal ltl => LTLOr (LTLPropNeg a, LTLGlobal ltl)
          | LTLFinal ltl => LTLOr (LTLPropNeg a, LTLFinal ltl)
          | LTLUntil (ltl1, ltl2) =>
            LTLOr (LTLPropNeg a, LTLUntil (ltl1, ltl2)))
      | LTLAnd (ltl1, ltl2) =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLAnd (ltl1, ltl2)
          | LTLProp a => LTLOr (LTLAnd (ltl1, ltl2), LTLProp a)
          | LTLPropNeg a => LTLOr (LTLAnd (ltl1, ltl2), LTLPropNeg a)
          | LTLAnd (ltl1a, ltl2a) =>
            LTLOr (LTLAnd (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
          | LTLOr (ltl1a, ltl2a) =>
            LTLOr (LTLAnd (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
          | LTLNext ltl => LTLOr (LTLAnd (ltl1, ltl2), LTLNext ltl)
          | LTLGlobal ltl => LTLOr (LTLAnd (ltl1, ltl2), LTLGlobal ltl)
          | LTLFinal ltl => LTLOr (LTLAnd (ltl1, ltl2), LTLFinal ltl)
          | LTLUntil (ltl1a, ltl2a) =>
            LTLOr (LTLAnd (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))
      | LTLOr (ltl1, ltl2) =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLOr (ltl1, ltl2)
          | LTLProp a => LTLOr (LTLOr (ltl1, ltl2), LTLProp a)
          | LTLPropNeg a => LTLOr (LTLOr (ltl1, ltl2), LTLPropNeg a)
          | LTLAnd (ltl1a, ltl2a) =>
            LTLOr (LTLOr (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
          | LTLOr (ltl1a, ltl2a) =>
            LTLOr (LTLOr (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
          | LTLNext ltl => LTLOr (LTLOr (ltl1, ltl2), LTLNext ltl)
          | LTLGlobal ltl => LTLOr (LTLOr (ltl1, ltl2), LTLGlobal ltl)
          | LTLFinal ltl => LTLOr (LTLOr (ltl1, ltl2), LTLFinal ltl)
          | LTLUntil (ltl1a, ltl2a) =>
            LTLOr (LTLOr (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))
      | LTLNext ltl =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLNext ltl
          | LTLProp a => LTLOr (LTLNext ltl, LTLProp a)
          | LTLPropNeg a => LTLOr (LTLNext ltl, LTLPropNeg a)
          | LTLAnd (ltl1, ltl2) => LTLOr (LTLNext ltl, LTLAnd (ltl1, ltl2))
          | LTLOr (ltl1, ltl2) => LTLOr (LTLNext ltl, LTLOr (ltl1, ltl2))
          | LTLNext ltla => LTLOr (LTLNext ltl, LTLNext ltla)
          | LTLGlobal ltla => LTLOr (LTLNext ltl, LTLGlobal ltla)
          | LTLFinal ltla => LTLOr (LTLNext ltl, LTLFinal ltla)
          | LTLUntil (ltl1, ltl2) => LTLOr (LTLNext ltl, LTLUntil (ltl1, ltl2)))
      | LTLGlobal ltl =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLGlobal ltl
          | LTLProp a => LTLOr (LTLGlobal ltl, LTLProp a)
          | LTLPropNeg a => LTLOr (LTLGlobal ltl, LTLPropNeg a)
          | LTLAnd (ltl1, ltl2) => LTLOr (LTLGlobal ltl, LTLAnd (ltl1, ltl2))
          | LTLOr (ltl1, ltl2) => LTLOr (LTLGlobal ltl, LTLOr (ltl1, ltl2))
          | LTLNext ltla => LTLOr (LTLGlobal ltl, LTLNext ltla)
          | LTLGlobal ltla => LTLOr (LTLGlobal ltl, LTLGlobal ltla)
          | LTLFinal ltla => LTLOr (LTLGlobal ltl, LTLFinal ltla)
          | LTLUntil (ltl1, ltl2) =>
            LTLOr (LTLGlobal ltl, LTLUntil (ltl1, ltl2)))
      | LTLFinal ltl =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLFinal ltl
          | LTLProp a => LTLOr (LTLFinal ltl, LTLProp a)
          | LTLPropNeg a => LTLOr (LTLFinal ltl, LTLPropNeg a)
          | LTLAnd (ltl1, ltl2) => LTLOr (LTLFinal ltl, LTLAnd (ltl1, ltl2))
          | LTLOr (ltl1, ltl2) => LTLOr (LTLFinal ltl, LTLOr (ltl1, ltl2))
          | LTLNext ltla => LTLOr (LTLFinal ltl, LTLNext ltla)
          | LTLGlobal ltla => LTLOr (LTLFinal ltl, LTLGlobal ltla)
          | LTLFinal ltla => LTLOr (LTLFinal ltl, LTLFinal ltla)
          | LTLUntil (ltl1, ltl2) =>
            LTLOr (LTLFinal ltl, LTLUntil (ltl1, ltl2)))
      | LTLUntil (ltl1, ltl2) =>
        (case remove_constants_P psi of LTLTrue => LTLTrue
          | LTLFalse => LTLUntil (ltl1, ltl2)
          | LTLProp a => LTLOr (LTLUntil (ltl1, ltl2), LTLProp a)
          | LTLPropNeg a => LTLOr (LTLUntil (ltl1, ltl2), LTLPropNeg a)
          | LTLAnd (ltl1a, ltl2a) =>
            LTLOr (LTLUntil (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))
          | LTLOr (ltl1a, ltl2a) =>
            LTLOr (LTLUntil (ltl1, ltl2), LTLOr (ltl1a, ltl2a))
          | LTLNext ltl => LTLOr (LTLUntil (ltl1, ltl2), LTLNext ltl)
          | LTLGlobal ltl => LTLOr (LTLUntil (ltl1, ltl2), LTLGlobal ltl)
          | LTLFinal ltl => LTLOr (LTLUntil (ltl1, ltl2), LTLFinal ltl)
          | LTLUntil (ltl1a, ltl2a) =>
            LTLOr (LTLUntil (ltl1, ltl2), LTLUntil (ltl1a, ltl2a))))
  | remove_constants_P LTLTrue = LTLTrue
  | remove_constants_P LTLFalse = LTLFalse
  | remove_constants_P (LTLProp v) = LTLProp v
  | remove_constants_P (LTLPropNeg v) = LTLPropNeg v
  | remove_constants_P (LTLNext v) = LTLNext v
  | remove_constants_P (LTLGlobal v) = LTLGlobal v
  | remove_constants_P (LTLFinal v) = LTLFinal v
  | remove_constants_P (LTLUntil (v, va)) = LTLUntil (v, va);

fun in_and A_ x (LTLAnd (y, z)) = in_and A_ x y orelse in_and A_ x z
  | in_and A_ x LTLTrue = equal_ltla A_ x LTLTrue
  | in_and A_ x LTLFalse = equal_ltla A_ x LTLFalse
  | in_and A_ x (LTLProp v) = equal_ltla A_ x (LTLProp v)
  | in_and A_ x (LTLPropNeg v) = equal_ltla A_ x (LTLPropNeg v)
  | in_and A_ x (LTLOr (v, va)) = equal_ltla A_ x (LTLOr (v, va))
  | in_and A_ x (LTLNext v) = equal_ltla A_ x (LTLNext v)
  | in_and A_ x (LTLGlobal v) = equal_ltla A_ x (LTLGlobal v)
  | in_and A_ x (LTLFinal v) = equal_ltla A_ x (LTLFinal v)
  | in_and A_ x (LTLUntil (v, va)) = equal_ltla A_ x (LTLUntil (v, va));

fun mk_and B_ f x y =
  (case f x of LTLTrue => f y | LTLFalse => LTLFalse
    | LTLProp a =>
      (case f y of LTLTrue => LTLProp a | LTLFalse => LTLFalse
        | LTLProp aa =>
          (if in_and B_ (LTLProp a) (LTLProp aa) then LTLProp aa
            else (if in_and B_ (LTLProp aa) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLProp aa)))
        | LTLPropNeg aa =>
          (if in_and B_ (LTLProp a) (LTLPropNeg aa) then LTLPropNeg aa
            else (if in_and B_ (LTLPropNeg aa) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLPropNeg aa)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_and B_ (LTLProp a) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_and B_ (LTLProp a) (LTLOr (ltl1, ltl2)) then LTLOr (ltl1, ltl2)
            else (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLOr (ltl1, ltl2))))
        | LTLNext ltl =>
          (if in_and B_ (LTLProp a) (LTLNext ltl) then LTLNext ltl
            else (if in_and B_ (LTLNext ltl) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_and B_ (LTLProp a) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_and B_ (LTLGlobal ltl) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_and B_ (LTLProp a) (LTLFinal ltl) then LTLFinal ltl
            else (if in_and B_ (LTLFinal ltl) (LTLProp a) then LTLProp a
                   else LTLAnd (LTLProp a, LTLFinal ltl)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_and B_ (LTLProp a) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLProp a)
                   then LTLProp a
                   else LTLAnd (LTLProp a, LTLUntil (ltl1, ltl2)))))
    | LTLPropNeg a =>
      (case f y of LTLTrue => LTLPropNeg a | LTLFalse => LTLFalse
        | LTLProp aa =>
          (if in_and B_ (LTLPropNeg a) (LTLProp aa) then LTLProp aa
            else (if in_and B_ (LTLProp aa) (LTLPropNeg a) then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLProp aa)))
        | LTLPropNeg aa =>
          (if in_and B_ (LTLPropNeg a) (LTLPropNeg aa) then LTLPropNeg aa
            else (if in_and B_ (LTLPropNeg aa) (LTLPropNeg a) then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLPropNeg aa)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_and B_ (LTLPropNeg a) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_and B_ (LTLPropNeg a) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLOr (ltl1, ltl2))))
        | LTLNext ltl =>
          (if in_and B_ (LTLPropNeg a) (LTLNext ltl) then LTLNext ltl
            else (if in_and B_ (LTLNext ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_and B_ (LTLPropNeg a) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_and B_ (LTLGlobal ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_and B_ (LTLPropNeg a) (LTLFinal ltl) then LTLFinal ltl
            else (if in_and B_ (LTLFinal ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLFinal ltl)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_and B_ (LTLPropNeg a) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLAnd (LTLPropNeg a, LTLUntil (ltl1, ltl2)))))
    | LTLAnd (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLAnd (ltl1, ltl2) | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_and B_ (LTLAnd (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_and B_ (LTLOr (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_and B_ (LTLNext ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_and B_ (LTLGlobal ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_and B_ (LTLFinal ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_and B_ (LTLUntil (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLAnd (LTLAnd (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))))
    | LTLOr (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLOr (ltl1, ltl2) | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_and B_ (LTLAnd (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_and B_ (LTLOr (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_and B_ (LTLNext ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_and B_ (LTLGlobal ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_and B_ (LTLFinal ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_and B_ (LTLUntil (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLAnd (LTLOr (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))))
    | LTLNext ltl =>
      (case f y of LTLTrue => LTLNext ltl | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLNext ltl) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLNext ltl) then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLNext ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLNext ltl) then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_and B_ (LTLNext ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_and B_ (LTLNext ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_and B_ (LTLNext ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_and B_ (LTLNext ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_and B_ (LTLNext ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_and B_ (LTLGlobal ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_and B_ (LTLNext ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_and B_ (LTLFinal ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_and B_ (LTLNext ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLAnd (LTLNext ltl, LTLUntil (ltl1, ltl2)))))
    | LTLGlobal ltl =>
      (case f y of LTLTrue => LTLGlobal ltl | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLGlobal ltl) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLGlobal ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_and B_ (LTLGlobal ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_and B_ (LTLGlobal ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_and B_ (LTLGlobal ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_and B_ (LTLNext ltla) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_and B_ (LTLGlobal ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_and B_ (LTLGlobal ltla) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_and B_ (LTLGlobal ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_and B_ (LTLFinal ltla) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_and B_ (LTLGlobal ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLAnd (LTLGlobal ltl, LTLUntil (ltl1, ltl2)))))
    | LTLFinal ltl =>
      (case f y of LTLTrue => LTLFinal ltl | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLFinal ltl) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLFinal ltl) then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLFinal ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLFinal ltl) then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_and B_ (LTLFinal ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_and B_ (LTLAnd (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_and B_ (LTLFinal ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_and B_ (LTLOr (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_and B_ (LTLFinal ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_and B_ (LTLNext ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_and B_ (LTLFinal ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_and B_ (LTLGlobal ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_and B_ (LTLFinal ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_and B_ (LTLFinal ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_and B_ (LTLFinal ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLAnd (LTLFinal ltl, LTLUntil (ltl1, ltl2)))))
    | LTLUntil (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLUntil (ltl1, ltl2) | LTLFalse => LTLFalse
        | LTLProp a =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_and B_ (LTLProp a) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_and B_ (LTLPropNeg a) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_and B_ (LTLAnd (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_and B_ (LTLOr (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_and B_ (LTLNext ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLGlobal ltl)
            then LTLGlobal ltl
            else (if in_and B_ (LTLGlobal ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_and B_ (LTLFinal ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd (LTLUntil (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_and B_ (LTLUntil (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_and B_ (LTLUntil (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLAnd
                          (LTLUntil (ltl1, ltl2), LTLUntil (ltl1a, ltl2a))))));

fun in_or A_ x (LTLOr (y, z)) = in_or A_ x y orelse in_or A_ x z
  | in_or A_ x LTLTrue = equal_ltla A_ x LTLTrue
  | in_or A_ x LTLFalse = equal_ltla A_ x LTLFalse
  | in_or A_ x (LTLProp v) = equal_ltla A_ x (LTLProp v)
  | in_or A_ x (LTLPropNeg v) = equal_ltla A_ x (LTLPropNeg v)
  | in_or A_ x (LTLAnd (v, va)) = equal_ltla A_ x (LTLAnd (v, va))
  | in_or A_ x (LTLNext v) = equal_ltla A_ x (LTLNext v)
  | in_or A_ x (LTLGlobal v) = equal_ltla A_ x (LTLGlobal v)
  | in_or A_ x (LTLFinal v) = equal_ltla A_ x (LTLFinal v)
  | in_or A_ x (LTLUntil (v, va)) = equal_ltla A_ x (LTLUntil (v, va));

fun mk_or B_ f x y =
  (case f x of LTLTrue => LTLTrue | LTLFalse => f y
    | LTLProp a =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLProp a
        | LTLProp aa =>
          (if in_or B_ (LTLProp a) (LTLProp aa) then LTLProp aa
            else (if in_or B_ (LTLProp aa) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLProp aa)))
        | LTLPropNeg aa =>
          (if in_or B_ (LTLProp a) (LTLPropNeg aa) then LTLPropNeg aa
            else (if in_or B_ (LTLPropNeg aa) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLPropNeg aa)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_or B_ (LTLProp a) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_or B_ (LTLProp a) (LTLOr (ltl1, ltl2)) then LTLOr (ltl1, ltl2)
            else (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLOr (ltl1, ltl2))))
        | LTLNext ltl =>
          (if in_or B_ (LTLProp a) (LTLNext ltl) then LTLNext ltl
            else (if in_or B_ (LTLNext ltl) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_or B_ (LTLProp a) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_or B_ (LTLGlobal ltl) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_or B_ (LTLProp a) (LTLFinal ltl) then LTLFinal ltl
            else (if in_or B_ (LTLFinal ltl) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLFinal ltl)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_or B_ (LTLProp a) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLProp a) then LTLProp a
                   else LTLOr (LTLProp a, LTLUntil (ltl1, ltl2)))))
    | LTLPropNeg a =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLPropNeg a
        | LTLProp aa =>
          (if in_or B_ (LTLPropNeg a) (LTLProp aa) then LTLProp aa
            else (if in_or B_ (LTLProp aa) (LTLPropNeg a) then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLProp aa)))
        | LTLPropNeg aa =>
          (if in_or B_ (LTLPropNeg a) (LTLPropNeg aa) then LTLPropNeg aa
            else (if in_or B_ (LTLPropNeg aa) (LTLPropNeg a) then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLPropNeg aa)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_or B_ (LTLPropNeg a) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_or B_ (LTLPropNeg a) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLOr (ltl1, ltl2))))
        | LTLNext ltl =>
          (if in_or B_ (LTLPropNeg a) (LTLNext ltl) then LTLNext ltl
            else (if in_or B_ (LTLNext ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_or B_ (LTLPropNeg a) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_or B_ (LTLGlobal ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_or B_ (LTLPropNeg a) (LTLFinal ltl) then LTLFinal ltl
            else (if in_or B_ (LTLFinal ltl) (LTLPropNeg a) then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLFinal ltl)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_or B_ (LTLPropNeg a) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLPropNeg a)
                   then LTLPropNeg a
                   else LTLOr (LTLPropNeg a, LTLUntil (ltl1, ltl2)))))
    | LTLAnd (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLAnd (ltl1, ltl2)
        | LTLProp a =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_or B_ (LTLAnd (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_or B_ (LTLOr (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_or B_ (LTLNext ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_or B_ (LTLGlobal ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_or B_ (LTLFinal ltl) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_or B_ (LTLUntil (ltl1a, ltl2a)) (LTLAnd (ltl1, ltl2))
                   then LTLAnd (ltl1, ltl2)
                   else LTLOr (LTLAnd (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))))
    | LTLOr (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLOr (ltl1, ltl2)
        | LTLProp a =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_or B_ (LTLAnd (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_or B_ (LTLOr (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_or B_ (LTLNext ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLGlobal ltl) then LTLGlobal ltl
            else (if in_or B_ (LTLGlobal ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_or B_ (LTLFinal ltl) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_or B_ (LTLUntil (ltl1a, ltl2a)) (LTLOr (ltl1, ltl2))
                   then LTLOr (ltl1, ltl2)
                   else LTLOr (LTLOr (ltl1, ltl2), LTLUntil (ltl1a, ltl2a)))))
    | LTLNext ltl =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLNext ltl
        | LTLProp a =>
          (if in_or B_ (LTLNext ltl) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLNext ltl) then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLNext ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLNext ltl) then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_or B_ (LTLNext ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_or B_ (LTLNext ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_or B_ (LTLNext ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_or B_ (LTLNext ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_or B_ (LTLNext ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_or B_ (LTLGlobal ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_or B_ (LTLNext ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_or B_ (LTLFinal ltla) (LTLNext ltl) then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_or B_ (LTLNext ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLNext ltl)
                   then LTLNext ltl
                   else LTLOr (LTLNext ltl, LTLUntil (ltl1, ltl2)))))
    | LTLGlobal ltl =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLGlobal ltl
        | LTLProp a =>
          (if in_or B_ (LTLGlobal ltl) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLGlobal ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_or B_ (LTLGlobal ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_or B_ (LTLGlobal ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_or B_ (LTLGlobal ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_or B_ (LTLNext ltla) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_or B_ (LTLGlobal ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_or B_ (LTLGlobal ltla) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_or B_ (LTLGlobal ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_or B_ (LTLFinal ltla) (LTLGlobal ltl) then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_or B_ (LTLGlobal ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLGlobal ltl)
                   then LTLGlobal ltl
                   else LTLOr (LTLGlobal ltl, LTLUntil (ltl1, ltl2)))))
    | LTLFinal ltl =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLFinal ltl
        | LTLProp a =>
          (if in_or B_ (LTLFinal ltl) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLFinal ltl) then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLFinal ltl) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLFinal ltl) then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLPropNeg a)))
        | LTLAnd (ltl1, ltl2) =>
          (if in_or B_ (LTLFinal ltl) (LTLAnd (ltl1, ltl2))
            then LTLAnd (ltl1, ltl2)
            else (if in_or B_ (LTLAnd (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLAnd (ltl1, ltl2))))
        | LTLOr (ltl1, ltl2) =>
          (if in_or B_ (LTLFinal ltl) (LTLOr (ltl1, ltl2))
            then LTLOr (ltl1, ltl2)
            else (if in_or B_ (LTLOr (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLOr (ltl1, ltl2))))
        | LTLNext ltla =>
          (if in_or B_ (LTLFinal ltl) (LTLNext ltla) then LTLNext ltla
            else (if in_or B_ (LTLNext ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLNext ltla)))
        | LTLGlobal ltla =>
          (if in_or B_ (LTLFinal ltl) (LTLGlobal ltla) then LTLGlobal ltla
            else (if in_or B_ (LTLGlobal ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLGlobal ltla)))
        | LTLFinal ltla =>
          (if in_or B_ (LTLFinal ltl) (LTLFinal ltla) then LTLFinal ltla
            else (if in_or B_ (LTLFinal ltla) (LTLFinal ltl) then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLFinal ltla)))
        | LTLUntil (ltl1, ltl2) =>
          (if in_or B_ (LTLFinal ltl) (LTLUntil (ltl1, ltl2))
            then LTLUntil (ltl1, ltl2)
            else (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLFinal ltl)
                   then LTLFinal ltl
                   else LTLOr (LTLFinal ltl, LTLUntil (ltl1, ltl2)))))
    | LTLUntil (ltl1, ltl2) =>
      (case f y of LTLTrue => LTLTrue | LTLFalse => LTLUntil (ltl1, ltl2)
        | LTLProp a =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLProp a) then LTLProp a
            else (if in_or B_ (LTLProp a) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLProp a)))
        | LTLPropNeg a =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLPropNeg a) then LTLPropNeg a
            else (if in_or B_ (LTLPropNeg a) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLPropNeg a)))
        | LTLAnd (ltl1a, ltl2a) =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLAnd (ltl1a, ltl2a))
            then LTLAnd (ltl1a, ltl2a)
            else (if in_or B_ (LTLAnd (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLAnd (ltl1a, ltl2a))))
        | LTLOr (ltl1a, ltl2a) =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLOr (ltl1a, ltl2a))
            then LTLOr (ltl1a, ltl2a)
            else (if in_or B_ (LTLOr (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLOr (ltl1a, ltl2a))))
        | LTLNext ltl =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLNext ltl) then LTLNext ltl
            else (if in_or B_ (LTLNext ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLNext ltl)))
        | LTLGlobal ltl =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLGlobal ltl)
            then LTLGlobal ltl
            else (if in_or B_ (LTLGlobal ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLGlobal ltl)))
        | LTLFinal ltl =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLFinal ltl) then LTLFinal ltl
            else (if in_or B_ (LTLFinal ltl) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2), LTLFinal ltl)))
        | LTLUntil (ltl1a, ltl2a) =>
          (if in_or B_ (LTLUntil (ltl1, ltl2)) (LTLUntil (ltl1a, ltl2a))
            then LTLUntil (ltl1a, ltl2a)
            else (if in_or B_ (LTLUntil (ltl1a, ltl2a)) (LTLUntil (ltl1, ltl2))
                   then LTLUntil (ltl1, ltl2)
                   else LTLOr (LTLUntil (ltl1, ltl2),
                                LTLUntil (ltl1a, ltl2a))))));

fun step_simp A_ (LTLProp a) nu = (if member A_ a nu then LTLTrue else LTLFalse)
  | step_simp A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | step_simp A_ (LTLAnd (phi, psi)) nu =
    mk_and A_ id (step_simp A_ phi nu) (step_simp A_ psi nu)
  | step_simp A_ (LTLOr (phi, psi)) nu =
    mk_or A_ id (step_simp A_ phi nu) (step_simp A_ psi nu)
  | step_simp A_ (LTLNext phi) nu = remove_constants_P phi
  | step_simp A_ LTLTrue nu = LTLTrue
  | step_simp A_ LTLFalse nu = LTLFalse
  | step_simp A_ (LTLGlobal v) nu = LTLGlobal v
  | step_simp A_ (LTLFinal v) nu = LTLFinal v
  | step_simp A_ (LTLUntil (v, va)) nu = LTLUntil (v, va);

fun step_abs A_ (Abs phi) nu = Abs (step_simp A_ phi nu);

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun theG (LTLGlobal x8) = x8;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun keys (Mapping xs) = Set (map fst xs);

fun map_ran f = map (fn (k, v) => (k, f k v));

val bot_set : 'a set = Set [];

fun q_L B_ sigma delta q_0 =
  (if not (null sigma)
    then gen_dfs (fn q => map (delta q) sigma) (insert B_) (member B_) bot_set
           [q_0]
    else bot_set);

fun sublists [] = [[]]
  | sublists (x :: xs) = let
                           val xss = sublists xs;
                         in
                           map (fn a => x :: a) xss @ xss
                         end;

fun lookup A_ (Mapping xs) = map_of A_ xs;

fun updatea A_ k v (Mapping xs) = Mapping (update A_ k v xs);

fun unf_G (LTLFinal phi) = LTLOr (LTLFinal phi, unf_G phi)
  | unf_G (LTLGlobal phi) = LTLGlobal phi
  | unf_G (LTLUntil (phi, psi)) =
    LTLOr (LTLAnd (LTLUntil (phi, psi), unf_G phi), unf_G psi)
  | unf_G (LTLAnd (phi, psi)) = LTLAnd (unf_G phi, unf_G psi)
  | unf_G (LTLOr (phi, psi)) = LTLOr (unf_G phi, unf_G psi)
  | unf_G LTLTrue = LTLTrue
  | unf_G LTLFalse = LTLFalse
  | unf_G (LTLProp v) = LTLProp v
  | unf_G (LTLPropNeg v) = LTLPropNeg v
  | unf_G (LTLNext v) = LTLNext v;

fun product_abs f (Mapping xs) c =
  Mapping (map_ran (fn a => fn b => f a b c) xs);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nat x;

fun card A_ (Set xs) = size_list (remdups A_ xs);

fun g_list A_ (LTLAnd (phi, psi)) =
  union (equal_ltl A_) (g_list A_ phi) (g_list A_ psi)
  | g_list A_ (LTLOr (phi, psi)) =
    union (equal_ltl A_) (g_list A_ phi) (g_list A_ psi)
  | g_list A_ (LTLFinal phi) = g_list A_ phi
  | g_list A_ (LTLGlobal phi) =
    inserta (equal_ltl A_) (LTLGlobal phi) (g_list A_ phi)
  | g_list A_ (LTLNext phi) = g_list A_ phi
  | g_list A_ (LTLUntil (phi, psi)) =
    union (equal_ltl A_) (g_list A_ phi) (g_list A_ psi)
  | g_list A_ LTLTrue = []
  | g_list A_ LTLFalse = []
  | g_list A_ (LTLProp v) = []
  | g_list A_ (LTLPropNeg v) = [];

fun mk_ora x y =
  (case y of LTLTrue => LTLTrue | LTLFalse => x | LTLProp _ => LTLOr (x, y)
    | LTLPropNeg _ => LTLOr (x, y) | LTLAnd (_, _) => LTLOr (x, y)
    | LTLOr (_, _) => LTLOr (x, y) | LTLNext _ => LTLOr (x, y)
    | LTLGlobal _ => LTLOr (x, y) | LTLFinal _ => LTLOr (x, y)
    | LTLUntil (_, _) => LTLOr (x, y));

fun eval_G A_ s (LTLAnd (phi, psi)) = LTLAnd (eval_G A_ s phi, eval_G A_ s psi)
  | eval_G A_ s (LTLOr (phi, psi)) = LTLOr (eval_G A_ s phi, eval_G A_ s psi)
  | eval_G A_ s (LTLGlobal phi) =
    (if member (equal_ltl A_) (LTLGlobal phi) s then LTLTrue else LTLFalse)
  | eval_G A_ s LTLTrue = LTLTrue
  | eval_G A_ s LTLFalse = LTLFalse
  | eval_G A_ s (LTLProp v) = LTLProp v
  | eval_G A_ s (LTLPropNeg v) = LTLPropNeg v
  | eval_G A_ s (LTLNext v) = LTLNext v
  | eval_G A_ s (LTLFinal v) = LTLFinal v
  | eval_G A_ s (LTLUntil (v, va)) = LTLUntil (v, va);

fun mk_anda x y =
  (case y of LTLTrue => x | LTLFalse => LTLFalse | LTLProp _ => LTLAnd (x, y)
    | LTLPropNeg _ => LTLAnd (x, y) | LTLAnd (_, _) => LTLAnd (x, y)
    | LTLOr (_, _) => LTLAnd (x, y) | LTLNext _ => LTLAnd (x, y)
    | LTLGlobal _ => LTLAnd (x, y) | LTLFinal _ => LTLAnd (x, y)
    | LTLUntil (_, _) => LTLAnd (x, y));

fun tabulate ks f = Mapping (map (fn k => (k, f k)) ks);

fun af_letter_simp A_ LTLTrue nu = LTLTrue
  | af_letter_simp A_ LTLFalse nu = LTLFalse
  | af_letter_simp A_ (LTLProp a) nu =
    (if member A_ a nu then LTLTrue else LTLFalse)
  | af_letter_simp A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_letter_simp A_ (LTLAnd (phi, psi)) nu =
    (case phi of LTLTrue => af_letter_simp A_ psi nu | LTLFalse => LTLFalse
      | LTLProp a =>
        (if member A_ a nu then af_letter_simp A_ psi nu else LTLFalse)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then af_letter_simp A_ psi nu else LTLFalse)
      | LTLAnd (_, _) =>
        mk_and A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_and A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLNext _ =>
        mk_and A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLGlobal phia =>
        let
          val phiaa = af_letter_simp A_ phia nu;
          val psia = af_letter_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_anda (LTLGlobal phia) phiaa
            else mk_and A_ id (mk_anda (LTLGlobal phia) phiaa) psia)
        end
      | LTLFinal _ =>
        mk_and A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLUntil (_, _) =>
        mk_and A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu))
  | af_letter_simp A_ (LTLOr (phi, psi)) nu =
    (case phi of LTLTrue => LTLTrue | LTLFalse => af_letter_simp A_ psi nu
      | LTLProp a =>
        (if member A_ a nu then LTLTrue else af_letter_simp A_ psi nu)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then LTLTrue else af_letter_simp A_ psi nu)
      | LTLAnd (_, _) =>
        mk_or A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_or A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLNext _ =>
        mk_or A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_or A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu)
      | LTLFinal phia =>
        let
          val phiaa = af_letter_simp A_ phia nu;
          val psia = af_letter_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) =>
        mk_or A_ id (af_letter_simp A_ phi nu) (af_letter_simp A_ psi nu))
  | af_letter_simp A_ (LTLNext phi) nu = phi
  | af_letter_simp A_ (LTLGlobal phi) nu =
    mk_anda (LTLGlobal phi) (af_letter_simp A_ phi nu)
  | af_letter_simp A_ (LTLFinal phi) nu =
    mk_ora (LTLFinal phi) (af_letter_simp A_ phi nu)
  | af_letter_simp A_ (LTLUntil (phi, psi)) nu =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (af_letter_simp A_ phi nu))
      (af_letter_simp A_ psi nu);

fun remove_and_or A_ (LTLOr (z, y)) =
  (case z of LTLTrue => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLFalse => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLProp _ => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLPropNeg _ => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLTrue, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLFalse, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLProp _, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLPropNeg _, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLAnd (_, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLTrue, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLFalse, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLProp _, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLPropNeg _, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLAnd (za, xa), ya), x) =>
      (if equal_ltla A_ x xa andalso equal_ltla A_ y ya
        then LTLOr (LTLAnd (za, xa), ya)
        else LTLOr (remove_and_or A_ z, remove_and_or A_ y))
    | LTLAnd (LTLOr (LTLOr (_, _), _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLNext _, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLGlobal _, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLFinal _, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLOr (LTLUntil (_, _), _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLNext _, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLGlobal _, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLFinal _, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLAnd (LTLUntil (_, _), _) =>
      LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLOr (_, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLNext _ => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLGlobal _ => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLFinal _ => LTLOr (remove_and_or A_ z, remove_and_or A_ y)
    | LTLUntil (_, _) => LTLOr (remove_and_or A_ z, remove_and_or A_ y))
  | remove_and_or A_ (LTLAnd (x, y)) =
    LTLAnd (remove_and_or A_ x, remove_and_or A_ y)
  | remove_and_or A_ LTLTrue = LTLTrue
  | remove_and_or A_ LTLFalse = LTLFalse
  | remove_and_or A_ (LTLProp v) = LTLProp v
  | remove_and_or A_ (LTLPropNeg v) = LTLPropNeg v
  | remove_and_or A_ (LTLNext v) = LTLNext v
  | remove_and_or A_ (LTLGlobal v) = LTLGlobal v
  | remove_and_or A_ (LTLFinal v) = LTLFinal v
  | remove_and_or A_ (LTLUntil (v, va)) = LTLUntil (v, va);

fun af_letter_abs A_ (Abs phi) nu =
  Abs (remove_and_or A_ (af_letter_simp A_ phi nu));

fun unf_simp A_ (LTLAnd (phi, psi)) =
  (case phi of LTLTrue => unf_simp A_ psi | LTLFalse => LTLFalse
    | LTLProp _ => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLPropNeg _ => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLAnd (_, _) => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLOr (_, _) => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLNext _ => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLGlobal phia =>
      let
        val phiaa = unf_simp A_ phia;
        val psia = unf_simp A_ psi;
      in
        (if equal_ltla A_ phiaa psia then mk_anda (LTLGlobal phia) phiaa
          else mk_and A_ id (mk_anda (LTLGlobal phia) phiaa) psia)
      end
    | LTLFinal _ => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi)
    | LTLUntil (_, _) => mk_and A_ id (unf_simp A_ phi) (unf_simp A_ psi))
  | unf_simp A_ (LTLOr (phi, psi)) =
    (case phi of LTLTrue => LTLTrue | LTLFalse => unf_simp A_ psi
      | LTLProp _ => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLPropNeg _ => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLAnd (_, _) => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLOr (_, _) => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLNext _ => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLGlobal _ => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi)
      | LTLFinal phia =>
        let
          val phiaa = unf_simp A_ phia;
          val psia = unf_simp A_ psi;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) => mk_or A_ id (unf_simp A_ phi) (unf_simp A_ psi))
  | unf_simp A_ (LTLGlobal phi) = mk_anda (LTLGlobal phi) (unf_simp A_ phi)
  | unf_simp A_ (LTLFinal phi) = mk_ora (LTLFinal phi) (unf_simp A_ phi)
  | unf_simp A_ (LTLUntil (phi, psi)) =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (unf_simp A_ phi)) (unf_simp A_ psi)
  | unf_simp A_ LTLTrue = LTLTrue
  | unf_simp A_ LTLFalse = LTLFalse
  | unf_simp A_ (LTLProp v) = LTLProp v
  | unf_simp A_ (LTLPropNeg v) = LTLPropNeg v
  | unf_simp A_ (LTLNext v) = LTLNext v;

fun remdups_fwd_acc A_ acc [] = []
  | remdups_fwd_acc A_ acc (x :: xs) =
    (if member A_ x acc then [] else [x]) @
      remdups_fwd_acc A_ (insert A_ x acc) xs;

fun remdups_fwd A_ xs = remdups_fwd_acc A_ bot_set xs;

fun the (SOME x2) = x2;

fun simple_product delta_1 delta_2 =
  (fn (q_1, q_2) => fn nu => (delta_1 q_1 nu, delta_2 q_2 nu));

fun vars_list A_ (LTLAnd (phi, psi)) =
  union A_ (vars_list A_ phi) (vars_list A_ psi)
  | vars_list A_ (LTLOr (phi, psi)) =
    union A_ (vars_list A_ phi) (vars_list A_ psi)
  | vars_list A_ (LTLFinal phi) = vars_list A_ phi
  | vars_list A_ (LTLGlobal phi) = vars_list A_ phi
  | vars_list A_ (LTLNext phi) = vars_list A_ phi
  | vars_list A_ (LTLUntil (phi, psi)) =
    union A_ (vars_list A_ phi) (vars_list A_ psi)
  | vars_list A_ (LTLProp a) = [a]
  | vars_list A_ (LTLPropNeg a) = [a]
  | vars_list A_ LTLTrue = []
  | vars_list A_ LTLFalse = [];

fun af_G_letter_simp A_ LTLTrue nu = LTLTrue
  | af_G_letter_simp A_ LTLFalse nu = LTLFalse
  | af_G_letter_simp A_ (LTLProp a) nu =
    (if member A_ a nu then LTLTrue else LTLFalse)
  | af_G_letter_simp A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_G_letter_simp A_ (LTLAnd (phi, psi)) nu =
    (case phi of LTLTrue => af_G_letter_simp A_ psi nu | LTLFalse => LTLFalse
      | LTLProp a =>
        (if member A_ a nu then af_G_letter_simp A_ psi nu else LTLFalse)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then af_G_letter_simp A_ psi nu else LTLFalse)
      | LTLAnd (_, _) =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLNext _ =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLFinal _ =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLUntil (_, _) =>
        mk_and A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu))
  | af_G_letter_simp A_ (LTLOr (phi, psi)) nu =
    (case phi of LTLTrue => LTLTrue | LTLFalse => af_G_letter_simp A_ psi nu
      | LTLProp a =>
        (if member A_ a nu then LTLTrue else af_G_letter_simp A_ psi nu)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then LTLTrue else af_G_letter_simp A_ psi nu)
      | LTLAnd (_, _) =>
        mk_or A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_or A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLNext _ =>
        mk_or A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_or A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu)
      | LTLFinal phia =>
        let
          val phiaa = af_G_letter_simp A_ phia nu;
          val psia = af_G_letter_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) =>
        mk_or A_ id (af_G_letter_simp A_ phi nu) (af_G_letter_simp A_ psi nu))
  | af_G_letter_simp A_ (LTLNext phi) nu = phi
  | af_G_letter_simp A_ (LTLGlobal phi) nu = LTLGlobal phi
  | af_G_letter_simp A_ (LTLFinal phi) nu =
    mk_ora (LTLFinal phi) (af_G_letter_simp A_ phi nu)
  | af_G_letter_simp A_ (LTLUntil (phi, psi)) nu =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (af_G_letter_simp A_ phi nu))
      (af_G_letter_simp A_ psi nu);

fun af_G_letter_abs A_ (Abs phi) nu =
  Abs (remove_and_or A_ (af_G_letter_simp A_ phi nu));

fun delta_L A_ B_ sigma delta q_0 =
  let
    val start = map (fn nu => (q_0, (nu, delta q_0 nu))) sigma;
    val succ = (fn (_, (_, q)) => map (fn nu => (q, (nu, delta q nu))) sigma);
  in
    gen_dfs succ (insert (equal_prod B_ (equal_prod A_ B_)))
      (member (equal_prod B_ (equal_prod A_ B_))) bot_set start
  end;

fun eval_G_abs A_ xa (Abs x) = Abs (eval_G A_ xa x);

fun impl_test B_ ifex_of b1 b2 =
  equal_ifex B_ (normif_alist B_ [] (ifex_of b1) (ifex_of b2) Trueif) Trueif;

fun ltl_prop_implies A_ phi psi =
  impl_test (equal_ltl A_) (ifex_of_ltl A_) phi psi;

fun index_option A_ n [] y = NONE
  | index_option A_ n (x :: xs) y =
    (if eq A_ x y then SOME n else index_option A_ (suc n) xs y);

fun rk A_ xs x = index_option A_ zero_nat xs x;

fun af_letter_opt_simp A_ LTLTrue nu = LTLTrue
  | af_letter_opt_simp A_ LTLFalse nu = LTLFalse
  | af_letter_opt_simp A_ (LTLProp a) nu =
    (if member A_ a nu then LTLTrue else LTLFalse)
  | af_letter_opt_simp A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_letter_opt_simp A_ (LTLAnd (phi, psi)) nu =
    (case phi of LTLTrue => af_letter_opt_simp A_ psi nu | LTLFalse => LTLFalse
      | LTLProp a =>
        (if member A_ a nu then af_letter_opt_simp A_ psi nu else LTLFalse)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then af_letter_opt_simp A_ psi nu
          else LTLFalse)
      | LTLAnd (_, _) =>
        mk_and A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_and A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLNext _ =>
        mk_and A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLGlobal phia =>
        let
          val phiaa = unf_simp A_ phia;
          val psia = af_letter_opt_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_anda (LTLGlobal phia) phiaa
            else mk_and A_ id (mk_anda (LTLGlobal phia) phiaa) psia)
        end
      | LTLFinal _ =>
        mk_and A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLUntil (_, _) =>
        mk_and A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu))
  | af_letter_opt_simp A_ (LTLOr (phi, psi)) nu =
    (case phi of LTLTrue => LTLTrue | LTLFalse => af_letter_opt_simp A_ psi nu
      | LTLProp a =>
        (if member A_ a nu then LTLTrue else af_letter_opt_simp A_ psi nu)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then LTLTrue else af_letter_opt_simp A_ psi nu)
      | LTLAnd (_, _) =>
        mk_or A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_or A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLNext _ =>
        mk_or A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_or A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu)
      | LTLFinal phia =>
        let
          val phiaa = unf_simp A_ phia;
          val psia = af_letter_opt_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) =>
        mk_or A_ id (af_letter_opt_simp A_ phi nu)
          (af_letter_opt_simp A_ psi nu))
  | af_letter_opt_simp A_ (LTLNext phi) nu = unf_simp A_ phi
  | af_letter_opt_simp A_ (LTLGlobal phi) nu =
    mk_anda (LTLGlobal phi) (unf_simp A_ phi)
  | af_letter_opt_simp A_ (LTLFinal phi) nu =
    mk_ora (LTLFinal phi) (unf_simp A_ phi)
  | af_letter_opt_simp A_ (LTLUntil (phi, psi)) nu =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (unf_simp A_ phi)) (unf_simp A_ psi);

fun af_letter_abs_opt A_ (Abs phi) nu =
  Abs (remove_and_or A_ (af_letter_opt_simp A_ phi nu));

fun sink B_ sigma delta q_0 q =
  not (eq B_ q_0 q) andalso ball sigma (fn nu => eq B_ (delta q nu) q);

fun nxt B_ sigma delta q_0 =
  (fn qs => fn nu =>
    remdups_fwd B_
      (filtera (fn q => not (sink B_ sigma delta q_0 q))
         (map (fn q => delta q nu) qs) @
        [q_0]));

fun init q_0 = [q_0];

fun unf_G_simp A_ (LTLAnd (phi, psi)) =
  mk_and A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
  | unf_G_simp A_ (LTLOr (phi, psi)) =
    (case phi of LTLTrue => LTLTrue | LTLFalse => unf_G_simp A_ psi
      | LTLProp _ => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLPropNeg _ => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLAnd (_, _) => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLOr (_, _) => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLNext _ => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLGlobal _ => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi)
      | LTLFinal phia =>
        let
          val phiaa = unf_G_simp A_ phia;
          val psia = unf_G_simp A_ psi;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) => mk_or A_ id (unf_G_simp A_ phi) (unf_G_simp A_ psi))
  | unf_G_simp A_ (LTLFinal phi) = mk_ora (LTLFinal phi) (unf_G_simp A_ phi)
  | unf_G_simp A_ (LTLUntil (phi, psi)) =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (unf_G_simp A_ phi))
      (unf_G_simp A_ psi)
  | unf_G_simp A_ LTLTrue = LTLTrue
  | unf_G_simp A_ LTLFalse = LTLFalse
  | unf_G_simp A_ (LTLProp v) = LTLProp v
  | unf_G_simp A_ (LTLPropNeg v) = LTLPropNeg v
  | unf_G_simp A_ (LTLNext v) = LTLNext v
  | unf_G_simp A_ (LTLGlobal v) = LTLGlobal v;

fun af_G_letter_opt_simp A_ LTLTrue nu = LTLTrue
  | af_G_letter_opt_simp A_ LTLFalse nu = LTLFalse
  | af_G_letter_opt_simp A_ (LTLProp a) nu =
    (if member A_ a nu then LTLTrue else LTLFalse)
  | af_G_letter_opt_simp A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_G_letter_opt_simp A_ (LTLAnd (phi, psi)) nu =
    (case phi of LTLTrue => af_G_letter_opt_simp A_ psi nu
      | LTLFalse => LTLFalse
      | LTLProp a =>
        (if member A_ a nu then af_G_letter_opt_simp A_ psi nu else LTLFalse)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then af_G_letter_opt_simp A_ psi nu
          else LTLFalse)
      | LTLAnd (_, _) =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLNext _ =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLFinal _ =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLUntil (_, _) =>
        mk_and A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu))
  | af_G_letter_opt_simp A_ (LTLOr (phi, psi)) nu =
    (case phi of LTLTrue => LTLTrue | LTLFalse => af_G_letter_opt_simp A_ psi nu
      | LTLProp a =>
        (if member A_ a nu then LTLTrue else af_G_letter_opt_simp A_ psi nu)
      | LTLPropNeg a =>
        (if not (member A_ a nu) then LTLTrue
          else af_G_letter_opt_simp A_ psi nu)
      | LTLAnd (_, _) =>
        mk_or A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLOr (_, _) =>
        mk_or A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLNext _ =>
        mk_or A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLGlobal _ =>
        mk_or A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu)
      | LTLFinal phia =>
        let
          val phiaa = unf_G_simp A_ phia;
          val psia = af_G_letter_opt_simp A_ psi nu;
        in
          (if equal_ltla A_ phiaa psia then mk_ora (LTLFinal phia) phiaa
            else mk_or A_ id (mk_ora (LTLFinal phia) phiaa) psia)
        end
      | LTLUntil (_, _) =>
        mk_or A_ id (af_G_letter_opt_simp A_ phi nu)
          (af_G_letter_opt_simp A_ psi nu))
  | af_G_letter_opt_simp A_ (LTLNext phi) nu = unf_G_simp A_ phi
  | af_G_letter_opt_simp A_ (LTLGlobal phi) nu = LTLGlobal phi
  | af_G_letter_opt_simp A_ (LTLFinal phi) nu =
    mk_ora (LTLFinal phi) (unf_G_simp A_ phi)
  | af_G_letter_opt_simp A_ (LTLUntil (phi, psi)) nu =
    mk_ora (mk_anda (LTLUntil (phi, psi)) (unf_G_simp A_ phi))
      (unf_G_simp A_ psi);

fun af_G_letter_abs_opt A_ (Abs phi) nu =
  Abs (remove_and_or A_ (af_G_letter_opt_simp A_ phi nu));

fun ltl_prop_entailment A_ a LTLTrue = true
  | ltl_prop_entailment A_ a LTLFalse = false
  | ltl_prop_entailment A_ a (LTLAnd (phi, psi)) =
    ltl_prop_entailment A_ a phi andalso ltl_prop_entailment A_ a psi
  | ltl_prop_entailment A_ a (LTLOr (phi, psi)) =
    ltl_prop_entailment A_ a phi orelse ltl_prop_entailment A_ a psi
  | ltl_prop_entailment A_ a (LTLProp v) = member (equal_ltl A_) (LTLProp v) a
  | ltl_prop_entailment A_ a (LTLPropNeg v) =
    member (equal_ltl A_) (LTLPropNeg v) a
  | ltl_prop_entailment A_ a (LTLNext v) = member (equal_ltl A_) (LTLNext v) a
  | ltl_prop_entailment A_ a (LTLGlobal v) =
    member (equal_ltl A_) (LTLGlobal v) a
  | ltl_prop_entailment A_ a (LTLFinal v) = member (equal_ltl A_) (LTLFinal v) a
  | ltl_prop_entailment A_ a (LTLUntil (v, va)) =
    member (equal_ltl A_) (LTLUntil (v, va)) a;

fun ltl_prop_entails_abs A_ xb (Abs x) = ltl_prop_entailment A_ xb x;

fun ltl_prop_implies_abs A_ (Abs xb) (Abs x) = ltl_prop_implies A_ xb x;

fun max_rank_of_C A_ delta_M q_0_M sigma psi =
  card (equal_ltl_prop_equiv_quotient A_)
    (filter
      (not o
        sink (equal_ltl_prop_equiv_quotient A_) (Set sigma) delta_M
          (q_0_M (theG psi)))
      (q_L (equal_ltl_prop_equiv_quotient A_) sigma delta_M
        (q_0_M (theG psi))));

fun succeed_filt A_ delta q_0 f i (r, (nu, uu)) =
  list_ex
    (fn q =>
      let
        val qa = delta q nu;
      in
        equal_option equal_nat (rk A_ r q) (SOME i) andalso
          ((not (f q) orelse eq A_ q q_0) andalso f qa)
      end)
    r;

fun acc_inf_C A_ delta_M q_0_M pi chi ((uu, m), (nu, uv)) =
  let
    val t = (the (lookup (equal_ltl A_) m chi), (nu, []));
    val g = keys pi;
  in
    succeed_filt (equal_ltl_prop_equiv_quotient A_) delta_M (q_0_M (theG chi))
      (ltl_prop_entails_abs A_ g) (the (lookup (equal_ltl A_) pi chi)) t
  end;

fun merge_filt A_ delta q_0 f i (r, (nu, uu)) =
  list_ex
    (fn q =>
      let
        val qa = delta q nu;
      in
        less_nat (the (rk A_ r q)) i andalso
          (not (f qa) andalso
            (list_ex (fn qb => not (eq A_ qb q) andalso eq A_ (delta qb nu) qa)
               r orelse
              eq A_ qa q_0))
      end)
    r;

fun fail_filt B_ sigma delta q_0 f (r, (nu, uu)) =
  list_ex (fn q => let
                     val qa = delta q nu;
                   in
                     not (f qa) andalso sink B_ sigma delta q_0 qa
                   end)
    r;

fun acc_fin_C A_ delta_M q_0_M sigma pi chi ((uu, m), (nu, uv)) =
  let
    val t = (the (lookup (equal_ltl A_) m chi), (nu, []));
    val g = keys pi;
  in
    fail_filt (equal_ltl_prop_equiv_quotient A_) sigma delta_M
      (q_0_M (theG chi)) (ltl_prop_entails_abs A_ g) t orelse
      merge_filt (equal_ltl_prop_equiv_quotient A_) delta_M (q_0_M (theG chi))
        (ltl_prop_entails_abs A_ g) (the (lookup (equal_ltl A_) pi chi)) t
  end;

fun mapping_generator_list A_ v [] = [Mapping []]
  | mapping_generator_list A_ v (k :: ks) =
    maps (fn m => map (fn va => updatea A_ k va m) (v k))
      (mapping_generator_list A_ v ks);

fun ltl_to_generalized_rabin_C A_ delta delta_M q_0 q_0_M m_fin_C sigma phi =
  let
    val delta_LTS =
      delta_L (equal_set A_)
        (equal_prod (equal_ltl_prop_equiv_quotient A_)
          (equal_mapping (equal_ltl A_)
            (equal_list (equal_ltl_prop_equiv_quotient A_))))
        sigma
        (simple_product delta
          (product_abs
            (nxt (equal_ltl_prop_equiv_quotient A_) (Set sigma) delta_M o
               q_0_M o
              theG)))
        (q_0 phi, tabulate (g_list A_ phi) (init o q_0_M o theG));
    val alpha_fin_filter =
      (fn pi => fn t =>
        m_fin_C phi pi t orelse
          bex (keys pi)
            (fn chi => acc_fin_C A_ delta_M q_0_M (Set sigma) pi chi t));
    val to_pair =
      (fn pi =>
        (filter (alpha_fin_filter pi) delta_LTS,
          image (fn chi => filter (acc_inf_C A_ delta_M q_0_M pi chi) delta_LTS)
            (keys pi)));
    val alpha =
      image to_pair
        let
          val gs = g_list A_ phi;
          val max_rank =
            lookup (equal_ltl A_)
              (tabulate gs (max_rank_of_C A_ delta_M q_0_M sigma));
        in
          Set (maps (mapping_generator_list (equal_ltl A_)
                      (fn x => upt zero_nat (the (max_rank x))))
                (sublists gs))
        end;
  in
    (delta_LTS,
      ((q_0 phi, tabulate (g_list A_ phi) (init o q_0_M o theG)), alpha))
  end;

fun m_fin_C_af A_ phia pi ((phi, m), uu) =
  not (ltl_prop_implies_abs A_
        let
          val g = keys pi;
          val g_L =
            filtera (fn x => member (equal_ltl A_) x g) (g_list A_ phia);
          val mk_conj =
            (fn chi =>
              foldl (fn a => fn x => and_absa a (eval_G_abs A_ g x)) (Abs chi)
                (drop (the (lookup (equal_ltl A_) pi chi))
                  (the (lookup (equal_ltl A_) m chi))));
        in
          and_abs (map mk_conj g_L)
        end
        phi);

fun ltl_to_generalized_rabin_C_af A_ =
  ltl_to_generalized_rabin_C A_ (af_letter_abs A_) (af_G_letter_abs A_) Abs Abs
    (m_fin_C_af A_);

fun ltl_to_generalized_rabin_C_af_simp A_ phi =
  ltl_to_generalized_rabin_C_af A_ (map Set (sublists (vars_list A_ phi))) phi;

fun ltlc_to_ltl false LTLcTrue = LTLTrue
  | ltlc_to_ltl false LTLcFalse = LTLFalse
  | ltlc_to_ltl false (LTLcProp q) = LTLProp q
  | ltlc_to_ltl false (LTLcNeg phi) = ltlc_to_ltl true phi
  | ltlc_to_ltl false (LTLcAnd (phi, psi)) =
    LTLAnd (ltlc_to_ltl false phi, ltlc_to_ltl false psi)
  | ltlc_to_ltl false (LTLcOr (phi, psi)) =
    LTLOr (ltlc_to_ltl false phi, ltlc_to_ltl false psi)
  | ltlc_to_ltl false (LTLcImplies (phi, psi)) =
    LTLOr (ltlc_to_ltl true phi, ltlc_to_ltl false psi)
  | ltlc_to_ltl false (LTLcIff (phi, psi)) =
    LTLAnd
      (LTLOr (ltlc_to_ltl true phi, ltlc_to_ltl false psi),
        LTLOr (ltlc_to_ltl false phi, ltlc_to_ltl true psi))
  | ltlc_to_ltl false (LTLcFinal phi) = LTLFinal (ltlc_to_ltl false phi)
  | ltlc_to_ltl false (LTLcGlobal phi) = LTLGlobal (ltlc_to_ltl false phi)
  | ltlc_to_ltl false (LTLcUntil (phi, psi)) =
    LTLUntil (ltlc_to_ltl false phi, ltlc_to_ltl false psi)
  | ltlc_to_ltl false (LTLcRelease (phi, psi)) =
    LTLOr (LTLGlobal (ltlc_to_ltl false psi),
            LTLUntil
              (ltlc_to_ltl false psi,
                LTLAnd (ltlc_to_ltl false phi, ltlc_to_ltl false psi)))
  | ltlc_to_ltl true LTLcTrue = LTLFalse
  | ltlc_to_ltl true LTLcFalse = LTLTrue
  | ltlc_to_ltl true (LTLcProp q) = LTLPropNeg q
  | ltlc_to_ltl true (LTLcNeg phi) = ltlc_to_ltl false phi
  | ltlc_to_ltl true (LTLcAnd (phi, psi)) =
    LTLOr (ltlc_to_ltl true phi, ltlc_to_ltl true psi)
  | ltlc_to_ltl true (LTLcOr (phi, psi)) =
    LTLAnd (ltlc_to_ltl true phi, ltlc_to_ltl true psi)
  | ltlc_to_ltl true (LTLcImplies (phi, psi)) =
    LTLAnd (ltlc_to_ltl false phi, ltlc_to_ltl true psi)
  | ltlc_to_ltl true (LTLcIff (phi, psi)) =
    LTLOr (LTLAnd (ltlc_to_ltl true phi, ltlc_to_ltl false psi),
            LTLAnd (ltlc_to_ltl false phi, ltlc_to_ltl true psi))
  | ltlc_to_ltl true (LTLcFinal phi) = LTLGlobal (ltlc_to_ltl true phi)
  | ltlc_to_ltl true (LTLcGlobal phi) = LTLFinal (ltlc_to_ltl true phi)
  | ltlc_to_ltl true (LTLcUntil (phi, psi)) =
    LTLOr (LTLGlobal (ltlc_to_ltl true psi),
            LTLUntil
              (ltlc_to_ltl true psi,
                LTLAnd (ltlc_to_ltl true phi, ltlc_to_ltl true psi)))
  | ltlc_to_ltl true (LTLcRelease (phi, psi)) =
    LTLUntil (ltlc_to_ltl true phi, ltlc_to_ltl true psi)
  | ltlc_to_ltl b (LTLcNext phi) = LTLNext (ltlc_to_ltl b phi);

fun ltlc_to_rabin phi =
  ltl_to_generalized_rabin_C_af_simp equal_literal (ltlc_to_ltl false phi);

fun m_fin_C_af_UU A_ phia pi ((phi, m), (nu, uu)) =
  not (ltl_prop_implies_abs A_
        let
          val g = keys pi;
          val g_L =
            filtera (fn x => member (equal_ltl A_) x g) (g_list A_ phia);
          val mk_conj =
            (fn chi =>
              foldl (fn a => fn x =>
                      and_absa a
                        ((eval_G_abs A_ g o (fn q => step_abs A_ q nu)) x))
                (and_absa (Abs chi) (eval_G_abs A_ g (Abs (theG chi))))
                (drop (the (lookup (equal_ltl A_) pi chi))
                  (the (lookup (equal_ltl A_) m chi))));
        in
          and_abs (map mk_conj g_L)
        end
        (step_abs A_ phi nu));

fun ltl_to_generalized_rabin_C_af_UU A_ =
  ltl_to_generalized_rabin_C A_ (af_letter_abs_opt A_) (af_G_letter_abs_opt A_)
    (Abs o unf) (Abs o unf_G) (m_fin_C_af_UU A_);

fun ltl_to_generalized_rabin_C_af_UU_simp A_ phi =
  ltl_to_generalized_rabin_C_af_UU A_ (map Set (sublists (vars_list A_ phi)))
    phi;

fun ltlc_to_rabin_UU phi =
  ltl_to_generalized_rabin_C_af_UU_simp equal_literal (ltlc_to_ltl false phi);

end; (*struct LTL_to_DRA_Translator*)
