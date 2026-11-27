package gezi.hotspot

/** The baselines of the cache service and of the tiering policy:
  * [[ConcurrentMapCacheProvider]], a thread safe provider in the process that
  * allows duplicate computation and clears when a round starts;
  * [[BaselineCaches]], which builds the provider the judge uses; and
  * [[WholeBudgetInterpretation]], a tiering policy that always interprets with
  * the whole budget. The module depends on `hotspot` alone.
  */
package object baselines
