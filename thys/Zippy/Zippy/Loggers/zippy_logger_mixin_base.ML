(*  Title:      Zippy/zippy_logger_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LOGGER_MIXIN_BASE = HAS_LOGGER

functor Zippy_Logger_Mixin_Base(
    val parent_logger : Logger.logger_binding
    val name : Logger.logger_name
  ) : ZIPPY_LOGGER_MIXIN_BASE =
struct
val logger = Logger.setup_new_logger parent_logger name
end