(*  Title:      Zippy/df_postorder_enumerate_alternating_zipper.ML
    Author:     Kevin Kappelmann
*)
(*preconditions:
1) Down{i}.morph moves to leftmost, topmost child*)
functor \<^eval>\<open>mk_name ["DF_Postorder_Enumerate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure E{i} : \<^eval>\<open>sfx_T_nargs "ENUMERATE_ZIPPER"\<close>
    sharing type E{i}.Z.zipper = Z.Z{i}.zipper
    sharing type E{i}.Z.M.t = Z.M.t
    sharing type E{i}.Co.acoroutine = E1.Co.acoroutine
    sharing type E{i}.Co.AE.exn = E1.Co.AE.exn\<close>\<close>
  ) : \<^eval>\<open>mk_name ["ENUMERATE", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
  =
struct

structure Z = Z; open Z
structure Co = E1.Co

local
  open Co.AE
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z.K); open SC
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(Z.M); open M
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(Co.AE); open A
in

fun gen_enum_zipper enum_zipper down back_up enum_zipper_down =
  let
    fun enum co = Co.resume co >>> catch'
      (fn (z, co) => down z
        >>= enum_zipper_down
        >>= second (arr (fn co1 => Co.append_co co1 (back_up >>> enum co |> Co.coroutine))))
      (fn (z, co) => enum co z)
  in enum enum_zipper end
fun enum_zipper1 mk_exn =
  let
    val back_up = \<^imap>\<open>\<open>{j}\<close> =>\<open>Up\<^eval>\<open>ML_Gen.sub_mod_nzippers' 1 ({j} - 1) ^ "."\<close>morph\<close>
      sep: ">>>"\<close>
    fun enum co = Co.resume co >>> catch'
      (fn (z, co) => Down1.morph z
        >>= enum_zipper2 mk_exn
        >>= second (arr (fn co1 => Co.append_co co1 (Co.cons back_up (enum co |> Co.coroutine)))))
      (second (arr (enum #> Co.coroutine)))
  in enum (E1.enum_zipper mk_exn) |> Co.coroutine end
\<^imap>\<open>\<open>{i}\<close> => \<open>
and enum_zipper{i} mk_exn =
  let val back_up = \<^imap>\<open>\<open>{j}\<close> =>\<open>Up\<^eval>\<open>ML_Gen.sub_mod_nzippers' 1 ({j} - {i}) ^ "."\<close>morph\<close>
    start: {i} sep: ">>>"\<close>
  in
    gen_enum_zipper (E{i}.enum_zipper mk_exn) Down{i}.morph back_up
      (enum_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close> mk_exn)
  end
\<close> start: 2 stop: \<^eval>\<open>string_of_int (ML_Gen.nzippers () - 1)\<close>\<close>
and \<^eval>\<open>"enum_zipper" ^ ML_Gen.nzippers' ()\<close> mk_exn =
  gen_enum_zipper (\<^eval>\<open>implode ["E", ML_Gen.nzippers' (), ".enum_zipper"]\<close> mk_exn)
    \<^eval>\<open>implode ["Down", ML_Gen.nzippers' (), ".morph"]\<close> Up1.morph
    (Co.resume (enum_zipper1 mk_exn))

end

end
