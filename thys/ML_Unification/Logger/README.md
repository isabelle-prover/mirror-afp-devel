A hierarchical logger for Isabelle/ML.
See `ML_Logger_Examples.thy` for a quick overview.

Features:
1. Per logger configuration, including, among other things,
    1. output function (e.g. print to console or file)
    2. log level: suppress and enable log messages based on severity
    3. message filter: suppress and enable log messages based on a filter function
2. Hierarchical configuration: set options based on logger name spaces;
   for example, disable logging for all loggers registered below `Root.Unification.*`
3. Logging antiquotation to optionally print positional information of logging message
4. Commands and attributes to setup and configure loggers with ML code.
