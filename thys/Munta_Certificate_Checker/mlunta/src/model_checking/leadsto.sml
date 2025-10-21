functor LeadstoChecker(Setup : CHECKING_SETUP) = struct
structure Checker = LeadsTo(Setup)
fun check system =
      case Checker.check system of
          (trace, true) => Property.Satisfied trace |
          (trace, _) => Property.Unsatisfied trace
end
