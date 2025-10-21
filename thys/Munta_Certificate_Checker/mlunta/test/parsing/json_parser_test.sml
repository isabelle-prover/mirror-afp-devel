structure JsonParserTest : TESTSUITE = struct
open Either
open SMLUnit

fun mk_test name input f expected =  name >+ assert_equal (f input) expected
fun test expected f name input = mk_test name input f expected

structure ErrorUtil = struct
fun unit_result x = mapR (K ()) x
fun assert_err p =
    unit_result #> mapL (List.exists p)
fun test_left_of p =
    test (Left true) p


end


structure ParserUtil = struct
fun assert_err p =
    JsonP.parse #> ErrorUtil.assert_err p

fun test name input =
    ErrorUtil.test_left_of (assert_err Error.is_parsing_err) name input
end

structure JsonUtil = struct
fun parse_bind f =
    JsonP.parse #> Either.bindR f
fun test_right name input f =
    mk_test name input (parse_bind f)

fun assert_json_err f p =
    parse_bind f #> ErrorUtil.assert_err p

fun test find p =
    ErrorUtil.test_left_of (assert_json_err find p)

fun wrong_ty find =
    test find Error.json_err_wrong_ty

fun not_in find =
    test find Error.json_err_not_in

end
(* XXX: Rename those helper functions *)

(* Parsing Error Utils *)

(* Json Error Utils *)

(* Tests that should Fail: *)
val test_trailing = ParserUtil.test "JsonTrailing blob"
                                        "{ \"a\" : 1} covefe"

val test_k_not_str = ParserUtil.test
                             "JsonWrongKeyNotStr" "{ a : 1 }"

val test_wrong_k_ty = JsonUtil.wrong_ty
                          (JsonP.find_int "a") "JsonWrongKeyTy" "{ \"a\": \"hi\"}"


val test_notin = JsonUtil.not_in
                     (JsonP.find_int "a") "JsonIntX" "{ \"b\": \"hi\"}"

val test_arr_fail = ParserUtil.test "JsonArr3"
                            "{ \"a\" : [ {\"b\": 1} {\"c\" : 2}]}"

val tests_fail =
    [test_trailing, test_k_not_str, test_wrong_k_ty, test_notin, test_arr_fail]

(* The Tests that should pass:  *)
val testInt = JsonUtil.test_right  "JsonInt" "{ \"a\": 1}" (JsonP.find_int "a")
                       (Right 1)

val testStr = JsonUtil.test_right "JsonStr" "{ \"a\": \"hi\"}"
                      (JsonP.find_str "a") (Right "hi")

val testArr1 = JsonUtil.test_right "JsonArr1" "{ \"a\" : [ {\"b\": 1}]}"
                                      ((JsonP.find_arr "a" #> mapR hd)
                                      #> bindR (JsonP.find_int "b"))
                                      (Right 1)
val testArr2 =
    JsonUtil.test_right "JsonArr2"
                    "{ \"a\" : [ {\"b\": 1}, {\"c\" : 2}]}"
            (JsonP.find_arr "a"
            #> mapR (List.exists (fn obj => JsonP.find_int "c" obj = Right 2)))
            (Right true)
(* XXX: Tests for reals the question is how to compare for right results meeh*)
(* JsonP.parse "{ \"a\" : 1.99 }\n" *)
(* JsonP.parse "{ \"a\" : -1.99 }\n" *)

val tests_pass = [
    testInt, testStr, testArr1, testArr2
]

(* Combining the tests *)
fun tests name = name >++ (tests_fail @ tests_pass)

(* Testsuite function *)
fun check name =
    run_test (tests name)
end
