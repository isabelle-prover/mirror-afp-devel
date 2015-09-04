structure LTL_to_DRA_Translator : sig
  type 'a ltl
  type 'a set
  type ('a, 'b) mapping
  type 'a ltl_prop_equiv_quotient
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

datatype 'a bool_expr = Const_bool_expr of bool | Atom_bool_expr of 'a |
  Neg_bool_expr of 'a bool_expr | And_bool_expr of 'a bool_expr * 'a bool_expr |
  Or_bool_expr of 'a bool_expr * 'a bool_expr |
  Imp_bool_expr of 'a bool_expr * 'a bool_expr |
  Iff_bool_expr of 'a bool_expr * 'a bool_expr;

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

fun reduce A_ env (IF (x, t1, t2)) =
  (case map_of A_ env x
    of NONE =>
      mkIF A_ x (reduce A_ ((x, true) :: env) t1)
        (reduce A_ ((x, false) :: env) t2)
    | SOME b => reduce A_ env (if b then t1 else t2))
  | reduce A_ uu Trueif = Trueif
  | reduce A_ uu Falseif = Falseif;

fun normif A_ env Trueif t1 t2 = reduce A_ env t1
  | normif A_ env Falseif t1 t2 = reduce A_ env t2
  | normif A_ env (IF (x, t1, t2)) t3 t4 =
    (case map_of A_ env x
      of NONE =>
        mkIF A_ x (normif A_ ((x, true) :: env) t1 t3 t4)
          (normif A_ ((x, false) :: env) t2 t3 t4)
      | SOME true => normif A_ env t1 t3 t4
      | SOME false => normif A_ env t2 t3 t4);

fun ifex_of A_ (Const_bool_expr b) = (if b then Trueif else Falseif)
  | ifex_of A_ (Atom_bool_expr x) = IF (x, Trueif, Falseif)
  | ifex_of A_ (Neg_bool_expr b) = normif A_ [] (ifex_of A_ b) Falseif Trueif
  | ifex_of A_ (And_bool_expr (b1, b2)) =
    normif A_ [] (ifex_of A_ b1) (ifex_of A_ b2) Falseif
  | ifex_of A_ (Or_bool_expr (b1, b2)) =
    normif A_ [] (ifex_of A_ b1) Trueif (ifex_of A_ b2)
  | ifex_of A_ (Imp_bool_expr (b1, b2)) =
    normif A_ [] (ifex_of A_ b1) (ifex_of A_ b2) Trueif
  | ifex_of A_ (Iff_bool_expr (b1, b2)) =
    let
      val t1 = ifex_of A_ b1;
      val t2 = ifex_of A_ b2;
    in
      normif A_ [] t1 t2 (normif A_ [] t2 Falseif Trueif)
    end;

fun taut_test A_ b = equal_ifex A_ (ifex_of A_ b) Trueif;

fun equiv_test A_ b1 b2 = taut_test A_ (Iff_bool_expr (b1, b2));

fun bool_expr_of_ltl LTLTrue = Const_bool_expr true
  | bool_expr_of_ltl LTLFalse = Const_bool_expr false
  | bool_expr_of_ltl (LTLAnd (phi, psi)) =
    And_bool_expr (bool_expr_of_ltl phi, bool_expr_of_ltl psi)
  | bool_expr_of_ltl (LTLOr (phi, psi)) =
    Or_bool_expr (bool_expr_of_ltl phi, bool_expr_of_ltl psi)
  | bool_expr_of_ltl (LTLProp v) = Atom_bool_expr (LTLProp v)
  | bool_expr_of_ltl (LTLPropNeg v) = Atom_bool_expr (LTLPropNeg v)
  | bool_expr_of_ltl (LTLNext v) = Atom_bool_expr (LTLNext v)
  | bool_expr_of_ltl (LTLGlobal v) = Atom_bool_expr (LTLGlobal v)
  | bool_expr_of_ltl (LTLFinal v) = Atom_bool_expr (LTLFinal v)
  | bool_expr_of_ltl (LTLUntil (v, va)) = Atom_bool_expr (LTLUntil (v, va));

fun ltl_prop_equiv A_ phi psi =
  equiv_test (equal_ltl A_) (bool_expr_of_ltl phi) (bool_expr_of_ltl psi);

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

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun theG (LTLGlobal x8) = x8;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun keys (Mapping xs) = Set (map fst xs);

fun af_letter A_ LTLTrue nu = LTLTrue
  | af_letter A_ LTLFalse nu = LTLFalse
  | af_letter A_ (LTLProp a) nu = (if member A_ a nu then LTLTrue else LTLFalse)
  | af_letter A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_letter A_ (LTLAnd (phi, psi)) nu =
    LTLAnd (af_letter A_ phi nu, af_letter A_ psi nu)
  | af_letter A_ (LTLOr (phi, psi)) nu =
    LTLOr (af_letter A_ phi nu, af_letter A_ psi nu)
  | af_letter A_ (LTLNext phi) nu = phi
  | af_letter A_ (LTLGlobal phi) nu =
    LTLAnd (LTLGlobal phi, af_letter A_ phi nu)
  | af_letter A_ (LTLFinal phi) nu = LTLOr (LTLFinal phi, af_letter A_ phi nu)
  | af_letter A_ (LTLUntil (phi, psi)) nu =
    LTLOr (LTLAnd (LTLUntil (phi, psi), af_letter A_ phi nu),
            af_letter A_ psi nu);

fun map_ran f = map (fn (k, v) => (k, f k v));

val bot_set : 'a set = Set [];

fun q_L B_ sigma delta q_0 =
  (if not (null sigma)
    then gen_dfs (fn q => map (delta q) sigma) (insert B_) (member B_) bot_set
           [q_0]
    else bot_set);

fun sublists [] = [[]]
  | sublists (x :: xs) =
    let
      val xss = sublists xs;
    in
      map (fn a => x :: a) xss @ xss
    end;

val empty : ('a, 'b) mapping = Mapping [];

fun lookup A_ (Mapping xs) = map_of A_ xs;

fun updatea A_ k v (Mapping xs) = Mapping (update A_ k v xs);

fun af_G_letter A_ LTLTrue nu = LTLTrue
  | af_G_letter A_ LTLFalse nu = LTLFalse
  | af_G_letter A_ (LTLProp a) nu =
    (if member A_ a nu then LTLTrue else LTLFalse)
  | af_G_letter A_ (LTLPropNeg a) nu =
    (if not (member A_ a nu) then LTLTrue else LTLFalse)
  | af_G_letter A_ (LTLAnd (phi, psi)) nu =
    LTLAnd (af_G_letter A_ phi nu, af_G_letter A_ psi nu)
  | af_G_letter A_ (LTLOr (phi, psi)) nu =
    LTLOr (af_G_letter A_ phi nu, af_G_letter A_ psi nu)
  | af_G_letter A_ (LTLNext phi) nu = phi
  | af_G_letter A_ (LTLGlobal phi) nu = LTLGlobal phi
  | af_G_letter A_ (LTLFinal phi) nu =
    LTLOr (LTLFinal phi, af_G_letter A_ phi nu)
  | af_G_letter A_ (LTLUntil (phi, psi)) nu =
    LTLOr (LTLAnd (LTLUntil (phi, psi), af_G_letter A_ phi nu),
            af_G_letter A_ psi nu);

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

fun tabulate ks f = Mapping (map (fn k => (k, f k)) ks);

fun sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun remdups_fwd_acc A_ acc [] = []
  | remdups_fwd_acc A_ acc (x :: xs) =
    (if member A_ x acc then [] else [x]) @
      remdups_fwd_acc A_ (sup_set A_ acc (insert A_ x bot_set)) xs;

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

fun delta_L A_ B_ sigma delta q_0 =
  let
    val start = map (fn nu => (q_0, (nu, delta q_0 nu))) sigma;
    val succ = (fn (_, (_, q)) => map (fn nu => (q, (nu, delta q nu))) sigma);
  in
    gen_dfs succ (insert (equal_prod B_ (equal_prod A_ B_)))
      (member (equal_prod B_ (equal_prod A_ B_))) bot_set start
  end;

fun eval_G_abs A_ xa (Abs x) = Abs (eval_G A_ xa x);

fun ltl_prop_implies A_ phi psi =
  taut_test (equal_ltl A_)
    (Imp_bool_expr (bool_expr_of_ltl phi, bool_expr_of_ltl psi));

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

fun af_G_letter_abs A_ (Abs phi) nu =
  Abs (remove_constants_P (af_G_letter A_ phi nu));

fun af_letter_abs A_ (Abs phi) nu =
  Abs (remove_constants_P (af_letter A_ phi nu));

fun sink B_ sigma delta q_0 q =
  not (eq B_ q_0 q) andalso ball sigma (fn nu => eq B_ (delta q nu) q);

fun nxt B_ sigma delta q_0 =
  (fn qs => fn nu =>
    remdups_fwd B_
      (filtera (fn q => not (sink B_ sigma delta q_0 q))
         (map (fn q => delta q nu) qs) @
        [q_0]));

fun delta A_ sigma =
  simple_product (af_letter_abs A_)
    (product_abs
      (nxt (equal_ltl_prop_equiv_quotient A_) sigma (af_G_letter_abs A_) o Abs o
        theG));

fun find_first_index A_ [] n = (fn _ => NONE)
  | find_first_index A_ (x :: xs) n =
    (fn q => (if eq A_ q x then SOME n else find_first_index A_ xs (suc n) q));

fun rk A_ qs = find_first_index A_ qs zero_nat;

fun init q_0 = [q_0];

fun initial A_ phi = (Abs phi, tabulate (g_list A_ phi) (init o Abs o theG));

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

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun mapping_generator_list A_ [] v = [empty]
  | mapping_generator_list A_ (k :: ks) v =
    maps (fn m => map (fn va => updatea A_ k va m) (v k))
      (mapping_generator_list A_ ks v);

fun mapping_generator A_ k v = Set (mapping_generator_list A_ k v);

fun max_rank_of A_ sigma psi =
  card (equal_ltl_prop_equiv_quotient A_)
    (filter
      (not o
        sink (equal_ltl_prop_equiv_quotient A_) (Set sigma) (af_G_letter_abs A_)
          (Abs psi))
      (q_L (equal_ltl_prop_equiv_quotient A_) sigma (af_G_letter_abs A_)
        (Abs psi)));

fun mappings A_ sigma phi =
  let
    val gs = g_list A_ phi;
    val max_rank =
      lookup (equal_ltl A_) (tabulate gs (max_rank_of A_ sigma o theG));
  in
    sup_seta (equal_mapping (equal_ltl A_) equal_nat)
      (Set (map (fn xs =>
                  mapping_generator (equal_ltl A_) xs
                    (fn x => upt zero_nat (the (max_rank x))))
             (sublists gs)))
  end;

fun ltl_prop_entails_abs A_ xb (Abs x) = ltl_prop_entailment A_ xb x;

fun ltl_prop_implies_abs A_ (Abs xb) (Abs x) = ltl_prop_implies A_ xb x;

fun reachable_transitions A_ sigma phi =
  delta_L (equal_set A_)
    (equal_prod (equal_ltl_prop_equiv_quotient A_)
      (equal_mapping (equal_ltl A_)
        (equal_list (equal_ltl_prop_equiv_quotient A_))))
    sigma (delta A_ (Set sigma)) (initial A_ phi);

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

fun acc_inf_filter_exec A_ pi chi ((uu, m), (nu, uv)) =
  let
    val t = (the (lookup (equal_ltl A_) m chi), (nu, []));
    val g = keys pi;
  in
    succeed_filt (equal_ltl_prop_equiv_quotient A_) (af_G_letter_abs A_)
      (Abs (theG chi)) (ltl_prop_entails_abs A_ g)
      (the (lookup (equal_ltl A_) pi chi)) t
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
  list_ex
    (fn q =>
      let
        val qa = delta q nu;
      in
        not (f qa) andalso sink B_ sigma delta q_0 qa
      end)
    r;

fun acc_fin_filter_exec A_ sigma pi chi ((uu, m), (nu, uv)) =
  let
    val t = (the (lookup (equal_ltl A_) m chi), (nu, []));
    val g = keys pi;
  in
    fail_filt (equal_ltl_prop_equiv_quotient A_) sigma (af_G_letter_abs A_)
      (Abs (theG chi)) (ltl_prop_entails_abs A_ g) t orelse
      merge_filt (equal_ltl_prop_equiv_quotient A_) (af_G_letter_abs A_)
        (Abs (theG chi)) (ltl_prop_entails_abs A_ g)
        (the (lookup (equal_ltl A_) pi chi)) t
  end;

fun m_fin_filter_exec A_ phia pi ((phi, m), uu) =
  let
    val ma = lookup (equal_ltl A_) m;
    val g = keys pi;
    val g_L = filtera (fn x => member (equal_ltl A_) x g) (g_list A_ phia);
  in
    not (ltl_prop_implies_abs A_
          (and_abs
            (map Abs g_L @
              map (eval_G_abs A_ g)
                (foldl
                  (fn a => fn x =>
                    a @ drop (the (lookup (equal_ltl A_) pi x)) (the (ma x)))
                  [] g_L)))
          phi)
  end;

fun ltl_to_rabin_exec A_ sigma phi =
  let
    val delta_LTS = reachable_transitions A_ sigma phi;
    val alpha_fin_filter =
      (fn pi => fn t =>
        m_fin_filter_exec A_ phi pi t orelse
          bex (keys pi)
            (fn chi => acc_fin_filter_exec A_ (Set sigma) pi chi t));
    val to_pair =
      (fn pi =>
        (filter (alpha_fin_filter pi) delta_LTS,
          image (fn chi => filter (acc_inf_filter_exec A_ pi chi) delta_LTS)
            (keys pi)));
    val alpha = image to_pair (mappings A_ sigma phi);
  in
    (delta_LTS, (initial A_ phi, alpha))
  end;

fun ltl_to_rabin_exec_simp A_ phi =
  ltl_to_rabin_exec A_ (map Set (sublists (vars_list A_ phi))) phi;

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
  ltl_to_rabin_exec_simp equal_literal (ltlc_to_ltl false phi);

end; (*struct LTL_to_DRA_Translator*)
