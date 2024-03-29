(*  Title:      SpecCheck/property.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

The base module of testable properties.
A property is the type of values that SpecCheck knows how to test.
Properties not only test whether a given predicate holds, but, for example, can also have
preconditions.
*)

signature SPECCHECK_PROPERTY =
sig

  type 'a pred = 'a -> bool
  (*the type of values testable by SpecCheck*)
  type 'a prop
  (*transforms a predicate into a testable property*)
  val prop : 'a pred -> 'a prop
  (*implication for properties: if the first argument evaluates to false, the test case is
    discarded*)
  val implies : 'a pred -> 'a prop -> 'a prop
  (*convenient notation for `implies` working on predicates*)
  val ==> : 'a pred * 'a pred -> 'a prop
  val expect_failure : exn -> ('a -> 'b) -> 'a prop

end

structure SpecCheck_Property : SPECCHECK_PROPERTY =
struct

type 'a pred = 'a -> bool
type 'a prop = 'a -> SpecCheck_Base.result_single

fun apply f x = \<^try>\<open>SpecCheck_Base.Result (f x) catch exn => SpecCheck_Base.Exception exn\<close>

fun prop f x = apply f x

fun implies cond prop x =
  if cond x
  then prop x
  else SpecCheck_Base.Discard

fun ==> (p1, p2) = implies p1 (prop p2)

fun eq_exn (exn, exn') = exnName exn = exnName exn' andalso exnMessage exn = exnMessage exn'

fun expect_failure exp_exn f = prop (fn x =>
    \<^try>\<open>(f x; false) catch exn => eq_exn (exn, exp_exn)\<close>)

end
