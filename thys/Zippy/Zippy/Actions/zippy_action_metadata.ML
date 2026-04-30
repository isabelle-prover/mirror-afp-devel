(*  Title:      Zippy/zippy_action_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_ACTION_METADATA =
sig
  type description = string Lazy.lazy

  type metadata
  val metadata : Identifier.id * description -> metadata
  val no_descr : Identifier.id -> metadata
  val pretty_metadata : metadata SpecCheck_Show.show

  structure Id : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = Identifier.id

  structure Descr : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = description
end

structure Zippy_Action_Metadata : ZIPPY_ACTION_METADATA =
struct

structure Show = SpecCheck_Show_Base

type description = string Lazy.lazy

datatype metadata = Metadata of {
  id : Identifier.id,
  description : description
}

fun metadata (id, description) = Metadata {id = id, description = description}
fun no_descr id = metadata (id, Lazy.value "")

fun pretty_metadata (Metadata {id, description}) = Show.record [
    ("id", Identifier.pretty id),
    ("description", Show.string (Lazy.force description))
  ]

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
structure Base = struct open L; type @{AllT_args} container = metadata end
structure Id =
struct
  open Base
  type @{AllT_args} data = Identifier.id
  fun getter (Metadata {id,...}) = id
  fun modifier (f, (Metadata {id, description})) = Metadata {id = f id, description = description}
  fun lens _ = L.mk_lens getter modifier
end

structure Descr =
struct
  open Base
  type @{AllT_args} data = description
  fun getter (Metadata {description,...}) = description
  fun modifier (f, (Metadata {id, description})) = Metadata {id = id, description = f description}
  fun lens _ = L.mk_lens getter modifier
end

end
